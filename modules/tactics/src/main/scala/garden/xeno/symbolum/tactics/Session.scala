package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Chain, Essay, Library, Signature}

/**
 * A development written one command at a time, where the order of the commands is the development.
 *
 * This is the model under the interface the plan asks for, and the interface is a client of it. The
 * page, the terminal and anything else that drives this all fold the same commands over the same
 * state, so what a reader sees is a function of the transcript and of nothing else.
 *
 * == Why a session is append-only, and why that is the whole soundness argument ==
 *
 * `SoundnessAttackSpec` derives `|- F` in six lines, and the shape it needs is **two theories at
 * once**: `Theory.declareConstant` writes nothing into `origins`, so a constant declared and never
 * defined carries `origin = None`, two theories that each declare `p : bool` build the *same*
 * constant, and a `Kernel.Thm` carries no theory of its own, so an axiom from one meets the
 * negation of it from the other inside a single rule. That is not an exotic case: it is what
 * `Real.scala` is made of, since `+`, `*`, `neg`, `inv`, `<`, `0` and `1` are declared and take
 * their meaning from an axiom.
 *
 * A notebook whose cells re-run in any order **is** the caller that attack needs, and it builds one
 * without anybody intending it: cell 3 declares `p` and assumes it, cell 3 is edited to assume the
 * negation and re-run, and the theorem the first version produced is still in the reader's hands.
 * Two theories, one name, both live.
 *
 * So a session holds exactly one theory. Commands extend it in order, [[Session.truncate]] is the
 * only way back, and re-running a command means truncating to before it and running forward again,
 * which throws away every theorem that was derived from what is being replaced. The enforcement is
 * not a rule of this file: a second `declare p` in one session is refused by the kernel's own
 * `AlreadyDeclared`, because there is only ever one theory to declare it in. `SessionSpec` puts
 * the attack itself through this surface and shows it cannot be assembled.
 *
 * The price is stated where a user meets it rather than hidden: editing cell 3 of a forty-cell
 * session discards thirty-seven results, and they are recomputed by replaying. The measurement that
 * makes that bearable is in [[Session.of]]: building the chain is the expensive part and it is done
 * once, and a claim answered against a chain already up costs single-digit to low-hundred
 * milliseconds.
 *
 * == What a cell is not allowed to hide ==
 *
 * Every outcome that produces a theorem carries [[Entry.restsOn]], the axioms the theorem reaches
 * that the foundation does not hold, which is `Derivation.foreignTo` asked at the boundary between
 * what this session assumed and what the repository already believed. A session that assumes
 * something in cell 3 and proves a theorem in cell 7 gets cell 7 answered with cell 3's assumption
 * named on it. That is the one thing a notebook makes easy to lose and it is the reason this is a
 * field of the record rather than a report a caller may forget to ask for.
 */
final class Session private (
  /** The foundation every session starts from, built once and shared by every state. */
  val base: Chain,
  /** What has been run, in order. The last one's state is the session's state. */
  val entries: Vector[Session.Entry],
  private val surface: Session.Surface
) {

  /** The theory, notation and names as they stand after everything run so far. */
  def state: Session.State = entries.lastOption.map(_.state).getOrElse(Session.State.of(base))

  /** The commands, which are the session: everything else here is a function of these. */
  def commands: Vector[Session.Command] = entries.map(_.command)

  /** Run one more command against the current state. */
  def run(command: Session.Command): Session = {
    val (outcome, next) = surface.apply(state, command)
    new Session(base, entries :+ Session.Entry(entries.size + 1, command, outcome, next), surface)
  }

  /** Read a line and run it, so that a client can hand over what a user typed. */
  def run(line: String): Session =
    Session.Command.read(line) match {
      case Right(command) => run(command)
      case Left(reason) =>
        val entry =
          Session.Entry(entries.size + 1, Session.Command.Unreadable(line), Session.Outcome.Refused(reason, None), state)
        new Session(base, entries :+ entry, surface)
    }

  /**
   * The session as it was after `count` commands.
   *
   * The only way backwards, and it takes the theory back with it: the state of the truncated
   * session is the state that command left, not the current one with entries hidden.
   */
  def truncate(count: Int): Session =
    new Session(base, entries.take(count.max(0)), surface)

  /**
   * Replace the command at `position` (one-based) and run forward from there.
   *
   * Everything after it is discarded rather than kept, which is the rule the class comment argues
   * for. The commands that followed are returned to the caller so that a client can offer to replay
   * them, which is a different act from having never dropped them.
   */
  def replace(position: Int, command: Session.Command): (Session, Vector[Session.Command]) = {
    val discarded = commands.drop(position)
    (truncate(position - 1).run(command), discarded)
  }

  /** Run a list of commands in order, which is what replaying a transcript is. */
  def runAll(lines: Vector[String]): Session = lines.foldLeft(this)((session, line) => session.run(line))

  /** What this session has assumed of its own, which is what its theorems are believed on. */
  def assumptions: Vector[(String, Term)] = state.assumed

  /** The transcript, which is the whole session: replaying it reproduces every state. */
  def transcript: String = entries.map(entry => Session.Command.write(entry.command)).mkString("\n")

  /** The session as a reader sees it, command and answer in order. */
  def render: String =
    if (entries.isEmpty) "nothing run yet"
    else entries.map(_.render(state)).mkString("\n\n")
}

object Session {

  /** A session over the standard chain, which is the one a caller almost always wants. */
  def standard: Session = of(Chain.standard)

  /**
   * A session over a chain of one's own.
   *
   * The chain is built by the caller and held for the life of the session, which is the reason a
   * server exists at all. Measured on 2026-09-13 on an idle machine: `Chain.standard` costs 6.9 s
   * on first touch and about 3 s to construct again in the same JVM, `Cost` over it 312 ms, and a
   * claim put to the whole tactic surface between 3 and 106 ms. The card that planned this work
   * carried 49 s, 69 s and 113 s for the same construction and concluded that a restart was a
   * coffee break; those three were taken with three JVMs competing for one laptop, and the figure
   * that belongs in a design is this one. Startup is a few seconds and a question is milliseconds,
   * so what a long-lived process buys is an interactive loop rather than a rescue from an
   * unaffordable one.
   */
  def of(chain: Chain): Session = new Session(chain, Vector.empty, Surface.of(chain))

  /**
   * What a user writes in a cell.
   *
   * Six that do something and one that failed to read. The language is the plan's, and it is
   * deliberately not Scala: a cell that evaluates arbitrary Scala can reach `Kernel.assertAxiom`
   * and `Term.variable`, both public and neither checked against anything a transcript records, and
   * then nothing on the page is a function of the page.
   */
  enum Command {

    /** `declare p : bool`, a constant with no definition, which is what an axiom will give meaning. */
    case Declare(name: String, schema: String)

    /** `define twice := \x:real. x + x`, conservative: it costs a name and no belief. */
    case Define(name: String, body: String)

    /** `assume NAME : claim`, the only command that adds to what has to be believed. */
    case Assume(name: String, claim: String)

    /** `prove NAME : claim`, put to the tactic surface and named if it settles. */
    case Prove(name: String, claim: String)

    /** `ask claim`, the cost report, which names nothing and changes no theory. */
    case Ask(claim: String)

    /** `find query`, the library's three questions. */
    case Find(query: String)

    /** `show NAME`, the generated page for a fact the library holds. */
    case Show(name: String)

    /** A line that did not read, kept as an entry so that the transcript is still the session. */
    case Unreadable(line: String)
  }

  object Command {

    /** The keyword of each command, which is also what [[write]] emits. */
    val Keywords: Vector[String] = Vector("declare", "define", "assume", "prove", "ask", "find", "show")

    /**
     * Read one line.
     *
     * `define` is separated by `:=` and the rest by the first `:`, which works because a name holds
     * no colon while a claim holds several: `prove SQ : !x:real. 0 <= x * x` splits after `SQ` and
     * the annotations inside the claim are left alone. A line whose keyword is unknown is refused
     * naming the seven rather than guessed at.
     */
    def read(line: String): Either[String, Command] = {
      val trimmed = line.trim
      val (keyword, rest) = trimmed.span(!_.isWhitespace) match {
        case (head, tail) => (head.toLowerCase, tail.trim)
      }

      def split(separator: String, shape: String): Either[String, (String, String)] = {
        val at = rest.indexOf(separator)
        if (at < 0) Left(s"$keyword is written `$shape`")
        else {
          val name = rest.take(at).trim
          val body = rest.drop(at + separator.length).trim
          if (name.isEmpty || body.isEmpty) Left(s"$keyword is written `$shape`") else Right((name, body))
        }
      }

      def nonEmpty(what: String): Either[String, String] =
        if (rest.isEmpty) Left(s"$keyword wants $what") else Right(rest)

      keyword match {
        case "" => Left("an empty line is not a command")
        case "declare" => split(":", "declare <name> : <type>").map(Declare.apply)
        case "define" => split(":=", "define <name> := <term>").map(Define.apply)
        case "assume" => split(":", "assume <NAME> : <claim>").map(Assume.apply)
        case "prove" => split(":", "prove <NAME> : <claim>").map(Prove.apply)
        case "ask" => nonEmpty("a claim").map(Ask.apply)
        case "find" => nonEmpty("a name or a shape").map(Find.apply)
        case "show" => nonEmpty("the name of a fact").map(Show.apply)
        case other => Left(s"no command `$other`; there are ${Keywords.mkString(", ")}")
      }
    }

    /** A command back as the line that reads to it, so that a transcript replays. */
    def write(command: Command): String = command match {
      case Declare(name, schema) => s"declare $name : $schema"
      case Define(name, body) => s"define $name := $body"
      case Assume(name, claim) => s"assume $name : $claim"
      case Prove(name, claim) => s"prove $name : $claim"
      case Ask(claim) => s"ask $claim"
      case Find(query) => s"find $query"
      case Show(name) => s"show $name"
      case Unreadable(line) => line
    }
  }

  /** What a command did. */
  enum Outcome {

    /** The theory grew, and by what: a constant, a definition or an axiom. */
    case Extended(what: String)

    /** A theorem, named, and held in the session from here on. */
    case Proved(name: String, theorem: Kernel.Thm)

    /** Text for the reader, changing nothing. */
    case Report(text: String)

    /**
     * Nothing happened, this is why, and this is the next step where there is one.
     *
     * The second field is `Remedy`, asked where the refusal is still a value rather than a
     * sentence. `RemedySpec` is what asked for it: every refusal a caller can receive has to have
     * a next step attached, and the first version of this file turned a `LogicError` into its
     * message at the point it arrived, so the page could never have offered what `Ask` already
     * offers for the same mistake.
     */
    case Refused(reason: String, next: Option[String])
  }

  /**
   * One command, what it did, and the state it left.
   *
   * The state is carried per entry rather than only at the end because [[Session.truncate]] has to
   * be able to hand back an earlier one, and because an entry a client renders has to show the
   * theory as it was when the command ran rather than as it is now.
   */
  final case class Entry(
    number: Int,
    command: Command,
    outcome: Outcome,
    state: State
  ) {

    /**
     * The axioms this entry's theorem reaches that the foundation does not hold.
     *
     * `Derivation.foreignTo` against the base chain's theory, so what comes back is exactly what
     * this session assumed and spent, and the empty set is the ordinary answer for a theorem of the
     * library. Named on every entry that has a theorem, because the alternative is a page that
     * looks the same whether or not the reader's own assumption is underneath it.
     */
    def restsOn(base: Chain): Set[Term] = outcome match {
      case Outcome.Proved(_, theorem) => Derivation.foreignTo(base.widest.theory, theorem).axioms
      case _ => Set.empty
    }

    /** The entry as a reader sees it. */
    def render(current: State): String = {
      val head = s"[$number] ${Command.write(command)}"
      val body = outcome match {
        case Outcome.Extended(what) => s"    $what"
        case Outcome.Proved(name, theorem) =>
          val statement = current.legible(theorem.conclusion).getOrElse(current.show(theorem.conclusion))
          s"    $name  |- $statement"
        case Outcome.Report(text) => text.linesIterator.map("    " + _).mkString("\n")
        case Outcome.Refused(reason, next) =>
          (s"    refused: $reason" +: next.map(step => s"    try: $step").toVector).mkString("\n")
      }
      s"$head\n$body"
    }
  }

  /**
   * The one theory a session holds, with what has been named in it.
   *
   * A `Signature`, so that everything in `modules/theories` and `modules/tactics` that reads a goal
   * or prints an answer takes it without knowing a session exists. It is the whole point of that
   * trait being measured rather than designed: a session is a development like any other, arrived
   * at by a different route.
   */
  final class State private[tactics] (
    val theory: Theory,
    val notation: Notation,
    val logic: Logic,
    /** What this session named, in the order it named it. */
    val named: Vector[(String, Kernel.Thm)],
    /** What this session assumed, which is what its theorems are believed on. */
    val assumed: Vector[(String, Term)]
  ) extends Signature {

    /** A theorem this session holds under that name. */
    def fact(name: String): Option[Kernel.Thm] = named.reverse.collectFirst { case (held, theorem) if held == name => theorem }

    private[tactics] def extended(
      theory: Theory = this.theory,
      logic: Logic = this.logic,
      named: Vector[(String, Kernel.Thm)] = this.named,
      assumed: Vector[(String, Term)] = this.assumed
    ): State = new State(theory, notation, logic, named, assumed)
  }

  object State {

    /** The state a session starts in: the chain's widest signature and nothing named yet. */
    def of(chain: Chain): State =
      new State(chain.widest.theory, chain.widest.notation, chain.widest.logic, Vector.empty, Vector.empty)
  }

  /**
   * What the commands are run against, built once per session.
   *
   * Held apart from [[State]] because these are the expensive, immutable halves: the library and
   * the tactic surface are functions of the base chain, and rebuilding either per command would put
   * the cost the class comment measures back into every cell.
   */
  private[tactics] final class Surface private (chain: Chain, library: Library, prove: Prove, cost: Cost) {

    def apply(state: State, command: Command): (Outcome, State) = command match {
      case Command.Declare(name, schema) => declare(state, name, schema)
      case Command.Define(name, body) => define(state, name, body)
      case Command.Assume(name, claim) => assume(state, name, claim)
      case Command.Prove(name, claim) => proving(state, name, claim)
      case Command.Ask(claim) => (report(Ask.of(state, cost, claim)), state)
      case Command.Find(query) => (report(Find.of(state, library, query)), state)
      case Command.Show(name) => (report(Essay.of(chain, name).fold(identity, identity)), state)
      case Command.Unreadable(line) => (Outcome.Refused(s"not a command: $line", None), state)
    }

    private def report(text: String): Outcome = Outcome.Report(text)

    /**
     * A refusal with its next step, asked of `Remedy` while the error is still a value.
     *
     * Three overloads because there are three refusal types and `Remedy` maps each; the kernel's
     * has no signature-taking form, and does not need one. Turning an error into its message before
     * this point is what `RemedySpec` exists to prevent, and it is what this file did first.
     */
    private def refusal(signature: Signature, error: LogicError): Outcome =
      Outcome.Refused(error.message, Some(Remedy.of(signature, error).message))

    private def refusal(signature: Signature, error: TacticError): Outcome =
      Outcome.Refused(error.message, Some(Remedy.of(signature, error).message))

    private def refusal(error: KernelError): Outcome =
      Outcome.Refused(error.message, Some(Remedy.of(error).message))

    /**
     * Declare a constant, which costs a name and no belief, and is half of the hazard.
     *
     * Conservative on its own: a theory with one more declared constant proves nothing new about
     * anything else. What makes it the hazard is the pair, a declaration and an axiom, and the pair
     * is safe here only because there is one theory to put both in. The comment is at the call site
     * rather than in the class doc because this is the line a reader will question.
     */
    private def declare(state: State, name: String, schema: String): (Outcome, State) =
      (for {
        parsed <- Parser.parseType(state.theory, schema).left.map(refusal(state, _))
        extended <- state.theory.declareConstant(name, parsed).left.map(refusal)
        widened <- state.logic.over(extended).left.map(refusal(state, _))
      } yield (Outcome.Extended(s"declared $name : ${schema.trim}"), state.extended(theory = extended, logic = widened)))
        .fold(refused => (refused, state), identity)

    private def define(state: State, name: String, body: String): (Outcome, State) =
      (for {
        term <- state.term(body).left.map(refusal(state, _))
        pair <- Kernel.defineConstant(state.theory, name, term).left.map(refusal)
        widened <- state.logic.over(pair._1).left.map(refusal(state, _))
      } yield (
        Outcome.Proved(name, pair._2),
        state.extended(theory = pair._1, logic = widened, named = state.named :+ (name -> pair._2))
      )).fold(refused => (refused, state), identity)

    /**
     * Assert an axiom, which is the only command that adds to what has to be believed.
     *
     * It is in the language rather than kept out of it, because a system whose whole promise is
     * accounting for what a conclusion rests on is exactly the one that can afford to let a user
     * assume something: `DomainTheorySpec` is that argument made as a test, and the four sentences
     * of an engineering handbook are asserted there for the same reason. What makes it safe to
     * offer is that every theorem downstream of it carries it in [[Entry.restsOn]].
     */
    private def assume(state: State, name: String, claim: String): (Outcome, State) =
      (for {
        proposition <- state.proposition(claim).left.map(refusal(state, _))
        pair <- Kernel.assertAxiom(state.theory, proposition).left.map(refusal)
      } yield (
        Outcome.Proved(name, pair._2),
        state.extended(
          theory = pair._1,
          named = state.named :+ (name -> pair._2),
          assumed = state.assumed :+ (name -> proposition)
        )
      )).fold(refused => (refused, state), identity)

    /**
     * Put a claim to the tactic surface and name it if it settles.
     *
     * The surface is built over the base chain, so a claim written in a vocabulary the session
     * added is one no tactic has anything to say about, and the refusal says that rather than
     * reporting a failure that reads like a defect. `docs/architecture.md` and this repository's
     * own `CLAUDE.md` both state the rule it follows from: a domain gets accounting, not search,
     * because `Ring` and `Linarith` decide fragments of the reals and have nothing to say about an
     * arbitrary axiom.
     */
    private def proving(state: State, name: String, claim: String): (Outcome, State) =
      state.proposition(claim) match {
        case Left(unreadable) => (refusal(state, unreadable), state)
        case Right(goal) =>
          val ownConstants = state.theory.constants.keySet -- chain.widest.theory.constants.keySet
          val named = Surface.constantsIn(goal).intersect(ownConstants)
          prove(goal) match {
            case Right(theorem) =>
              (Outcome.Proved(name, theorem), state.extended(named = state.named :+ (name -> theorem)))
            case Left(failure) if named.nonEmpty =>
              (
                Outcome.Refused(
                  s"${failure.message}; this claim names ${named.toVector.sorted.mkString(", ")}, which this " +
                    "session introduced, and no tactic here searches over a constant the chain never saw",
                  Some("derive it by hand from what you assumed, or state it over the chain's own constants")
                ),
                state
              )
            case Left(failure) => (refusal(state, failure), state)
          }
      }
  }

  private[tactics] object Surface {

    /** The constants a term names, which is how a session tells its own vocabulary from the chain's. */
    def constantsIn(term: Term): Set[String] = term match {
      case Const(name, _) => Set(name)
      case App(fn, argument) => constantsIn(fn) ++ constantsIn(argument)
      case Abs(_, body) => constantsIn(body)
      case _ => Set.empty
    }

    /** Everything a session runs against, built once. */
    def of(chain: Chain): Surface = {
      val prove = Prove
        .construct(chain)
        .fold(error => throw new IllegalStateException(s"the tactic surface does not build: ${error.message}"), identity)
      val cost = Cost
        .construct(chain)
        .fold(error => throw new IllegalStateException(s"the cost report does not build: ${error.message}"), identity)
      new Surface(chain, Library.of(chain), prove, cost)
    }
  }
}
