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
 * Every outcome that produces a theorem carries [[Session.Entry.restsOn]], the axioms the theorem
 * reaches that the foundation does not hold, which is `Derivation.foreignTo` asked at the boundary
 * between what this session assumed and what the repository already believed. A session that
 * assumes something in cell 3 and proves a theorem in cell 7 gets cell 7 answered with cell 3's
 * assumption named on it. That is the one thing a notebook makes easy to lose and it is the reason
 * this is a field of the record rather than a report a caller may forget to ask for.
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

  /**
   * Run a list of lines in order, which is what replaying a transcript is.
   *
   * A command is one line, except a `theorem` whose proof follows it, which runs to the `qed` that
   * closes it and is one command: `Document.extent` decides where it ends, by the same keywords the
   * checker reads, so a theorem pasted into a session is the theorem the checker would read.
   */
  def runAll(lines: Vector[String]): Session = {
    @annotation.tailrec
    def go(session: Session, position: Int): Session =
      if (position >= lines.size) session
      else {
        val keyword = lines(position).trim.takeWhile(!_.isWhitespace).toLowerCase
        val span = if (keyword == "theorem") Document.extent(lines, position) else 1
        go(session.run(lines.slice(position, position + span).mkString("\n")), position + span)
      }
    go(this, 0)
  }

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

  /** A session over the standard chain that imports from `source`, which answers a document's text. */
  def standard(source: String => Option[String]): Session = of(Chain.standard, source)

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
  def of(chain: Chain): Session = of(chain, _ => None)

  /**
   * A session whose `import` reads documents from `source`.
   *
   * A function for the reason `Workspace` takes one: which documents a session may import is the
   * caller's decision, and the caller that knows the published ones is a module above this one.
   * With nothing to read, an `import` is refused naming the document it did not find.
   */
  def of(chain: Chain, source: String => Option[String]): Session =
    new Session(chain, Vector.empty, Surface.of(chain, source))

  /**
   * What a user writes in a cell.
   *
   * One case per keyword in [[Command.Keywords]], and one for a line that failed to read. This
   * said "six that do something" while the enum held eight of them, which makes it the third
   * sentence in this repository to have survived `derive` landing, and it is the only one of the
   * three nothing had noticed. The count is deleted rather than corrected: what it was for is the
   * shape of the list below, which a reader can see by looking.
   *
   * The language is the plan's, and it is
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

    /**
     * `derive NAME : <step>`, one inference by hand over facts this session already holds.
     *
     * The command a session's own axiom needs in order to reach anything, and the reason it is a
     * cell rather than a tactic is in [[Session.Surface.deriving]].
     */
    case Derive(name: String, step: String)

    /**
     * `theorem NAME : CLAIM by METHOD`, or the same line followed by `proof ... qed`: a declaration
     * of the proof language, checked by the elaborator the checker uses, against this session's
     * theory and the facts it holds. The text is kept whole, proof included, because the text is
     * what a transcript replays.
     */
    case Theorem(text: String)

    /**
     * `import NAME`, a document's definitions made in this session's theory and its theorems held
     * as facts, with every document it imports in turn: all of it or, when anything is refused,
     * none of it.
     */
    case Import(name: String)

    /** A line that did not read, kept as an entry so that the transcript is still the session. */
    case Unreadable(line: String)
  }

  object Command {

    /** What a `theorem` cell is, for a refusal of one that is something else. */
    val TheoremShape: String = "theorem NAME : CLAIM by METHOD, or the same line followed by proof ... qed"

    /** The keyword of each command, which is also what [[write]] emits. */
    val Keywords: Vector[String] =
      Vector("declare", "define", "assume", "prove", "derive", "theorem", "import", "ask", "find", "show")

    /**
     * Read one line.
     *
     * `define` is separated by `:=` and the rest by the first `:`, which works because a name holds
     * no colon while a claim holds several: `prove SQ : !x:real. 0 <= x * x` splits after `SQ` and
     * the annotations inside the claim are left alone. A line whose keyword is unknown is refused by
     * printing [[Command.Keywords]] rather than guessed at, so what the refusal names cannot fall
     * behind the enum.
     *
     * This said "naming the seven" from the first commit of this history until 2026-09-16, and it
     * was true when it was written: the eighth keyword is `derive` and it landed afterwards. The
     * count is deleted rather than corrected, for the reason the one on the enum above already
     * gives: the only thing it stood for is the list the refusal prints, so a figure beside it is
     * a second copy of a live enumeration and nothing was comparing the two. It sat eight lines
     * below that enumeration and three readings of this file that were looking for exactly this
     * went past it, which is why the repair is deletion and not a better number.
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
        case "derive" => split(":", "derive <NAME> : <step>").map(Derive.apply)
        // Read whole by the document reader when it is run, which is where its errors are told.
        case "theorem" => Right(Theorem(trimmed))
        case "import" => nonEmpty("the name of a document").map(Import.apply)
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
      case Derive(name, step) => s"derive $name : $step"
      case Theorem(text) => text
      case Import(name) => s"import $name"
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
    /**
     * A theorem this session proved, and where a bound rather than the claim chose its price.
     *
     * `cutShort` is empty for every proof whose price is its own. Where it is set, the page says so
     * beside the theorem: `Derivation.axiomsOf` reports an axiom either way and cannot say which of
     * the two happened, which is what `docs/adr/0031` repairs one floor down in `Prove`.
     */
    case Proved(name: String, theorem: Kernel.Thm, cutShort: Option[String] = None, price: Option[Elaborate.Price] = None)

    /**
     * A theorem whose proof did not check, and every problem in it: where, why, what to try and the
     * goal at that point. The elaborator's report for one declaration, which is what makes the goal
     * visible in a session as it is in the checker's output.
     */
    case Incomplete(name: String, problems: Vector[Elaborate.Problem])

    /** Text for the reader, changing nothing. */
    case Report(text: String)

    /**
     * A **page** for the reader, in markdown, which is what `show` produces and nothing else does.
     *
     * Kept apart from [[Report]] because the two are different things to whoever is displaying
     * them, and collapsing them is what card 07a0d66b is about: a terminal prints both as they
     * stand, and a browser page prints a report as it stands and **renders** a page, which is why
     * the one command whose purpose is to be read was the only output on the page that was not
     * typeset. `Ask` and `Find` write lines; `Essay` writes a document with headings, a table, code
     * blocks and formulas in it.
     *
     * The markdown is carried rather than the HTML, and that is deliberate: `Essay` has one form
     * and this enum does not ask it for a second, so nothing here can disagree with the document a
     * generator writes. The display decides how to show it, which is where that decision belongs.
     */
    case Page(markdown: String)

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
      case Outcome.Proved(_, theorem, _, _) => Derivation.foreignTo(base.widest.theory, theorem).axioms
      case _ => Set.empty
    }

    /** The entry as a reader sees it. */
    def render(current: State): String = {
      val head = s"[$number] ${Command.write(command)}"
      val body = outcome match {
        case Outcome.Extended(what) => s"    $what"
        case Outcome.Proved(name, theorem, _, price) =>
          val statement = current.legible(theorem.conclusion).getOrElse(current.show(theorem.conclusion))
          (s"    $name  |- $statement" +: price.toVector.flatMap(Entry.priced).map("    " + _)).mkString("\n")
        case Outcome.Incomplete(name, problems) =>
          (s"    $name: not proved" +: problems.flatMap(Entry.problem).map("    " + _)).mkString("\n")
        case Outcome.Report(text) => text.linesIterator.map("    " + _).mkString("\n")

        // A terminal has no renderer and markdown was written to be readable without one, which is
        // the whole reason `Essay` produces it: here the two cases are the same thing.
        case Outcome.Page(markdown) => markdown.linesIterator.map("    " + _).mkString("\n")
        case Outcome.Refused(reason, next) =>
          (s"    refused: $reason" +: next.map(step => s"    try: $step").toVector).mkString("\n")
      }
      s"$head\n$body"
    }
  }

  object Entry {

    /** What a theorem the elaborator proved rests on and cost, a line each. */
    def priced(price: Elaborate.Price): Vector[String] =
      Vector(
        s"axioms: ${if (price.axioms.isEmpty) "none" else price.axioms.mkString(", ")}",
        s"library facts: ${if (price.facts.isEmpty) "none" else price.facts.mkString(", ")}"
      ) ++
        (if (price.document.nonEmpty) Vector(s"from this session: ${price.document.mkString(", ")}") else Vector.empty) ++
        (if (price.imported.nonEmpty) Vector(s"imported: ${price.imported.mkString(", ")}") else Vector.empty) ++
        Vector(s"inferences: ${price.inferences}") ++
        price.notes.map(note => s"note: $note")

    /** One problem of a proof, with the line it is on counted from the cell's first line. */
    def problem(problem: Elaborate.Problem): Vector[String] =
      Vector(s"line ${problem.line}: ${problem.reason}") ++
        problem.next.map(step => s"  try: $step").toVector ++
        problem.refuted.map(r => s"  ${if (r.refutes) "false" else "refutation"}: ${r.reason}").toVector ++
        problem.goal.toVector.flatMap(_.linesIterator.map("  " + _))
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
    val assumed: Vector[(String, Term)],
    /**
     * The account of every hand derivation this session has run, in order.
     *
     * Kept on the state rather than per entry because a derivation is written across cells: the
     * point of `derive` is that cell 9 cites what cell 7 produced, and an account per cell would
     * be nine accounts of one line each with nothing saying they are one argument. `Script.tidy`
     * is what stops a step cited twice from being printed twice.
     */
    val script: Script = Script.nothing,
    /**
     * The theorems of the documents this session imported, each under the document that holds it.
     * Apart from [[named]] because a price names them as `DOCUMENT.NAME`, which is how a reader
     * tells a fact this session proved from one it took.
     */
    val imported: Elaborate.Imported = Elaborate.Imported.none,
    /** The documents imported, in the order their definitions were made in [[theory]]. */
    val documents: Vector[String] = Vector.empty
  ) extends Signature {

    /** A theorem this session holds under that name: its own first, then one it imported. */
    def fact(name: String): Option[Kernel.Thm] =
      named.reverse.collectFirst { case (held, theorem) if held == name => theorem }
        .orElse(imported.facts.get(name).map(_.theorem))

    private[tactics] def extended(
      theory: Theory = this.theory,
      logic: Logic = this.logic,
      named: Vector[(String, Kernel.Thm)] = this.named,
      assumed: Vector[(String, Term)] = this.assumed,
      script: Script = this.script,
      imported: Elaborate.Imported = this.imported,
      documents: Vector[String] = this.documents
    ): State = new State(theory, notation, logic, named, assumed, script, imported, documents)
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
  private[tactics] final class Surface private (
    chain: Chain,
    library: Library,
    prove: Prove,
    cost: Cost,
    elaborate: Elaborate,
    source: String => Option[String]
  ) {

    def apply(state: State, command: Command): (Outcome, State) = command match {
      case Command.Declare(name, schema) => declare(state, name, schema)
      case Command.Define(name, body) => define(state, name, body)
      case Command.Assume(name, claim) => assume(state, name, claim)
      case Command.Prove(name, claim) => proving(state, name, claim)
      case Command.Derive(name, step) => deriving(state, name, step)
      case Command.Theorem(text) => theorem(state, text)
      case Command.Import(name) => importing(state, name)
      case Command.Ask(claim) => (report(Ask.of(state, cost, claim)), state)
      case Command.Find(query) => (report(Find.of(state, library, query)), state)
      case Command.Show(name) => (Outcome.Page(showing(state, name)), state)
      case Command.Unreadable(line) => (Outcome.Refused(s"not a command: $line", None), state)
    }

    private def report(text: String): Outcome = Outcome.Report(text)

    /**
     * `show NAME`, over what this session holds first and the library behind it.
     *
     * It read the library alone until 2026-09-18, and a name the session itself had just produced
     * came back as `no lemma named AT_TWO` three lines under the cell that produced it. The message
     * was true of `Library.of(chain)` and false of the session, and the reader it was written for
     * is the one who had watched the theorem appear: that collapse, of "I did not look there" into
     * "it does not exist", is the one `Refutation` keeps seven answers apart to avoid, made here in
     * the one command whose whole purpose is to be read.
     *
     * A session fact gets the **same** page a library lemma gets, from the same `Essay.of`, and the
     * three arguments that differ are what make it honest:
     *
     *  - the signature is the **session's**, so a constant this session declared prints as itself
     *    rather than being unreadable;
     *  - the library has the session's own facts in front of the chain's, so what the theorem rests
     *    on is **named** where the session named it. Without that an assumption of this session is
     *    an axiom the page cannot find, and the page says of an unnamed axiom that `Library.of`
     *    holds no classical axiom, which would be a sentence about the wrong thing;
     *  - the account is `Script.reaching`, the steps of this theorem rather than every step the
     *    transcript has recorded, which for a session is the account of every `derive` in it.
     */
    private def showing(state: State, name: String): String =
      state.fact(name) match {
        case Some(theorem) =>
          Essay.of(
            state,
            Library.of(Vector(Surface.Held -> state.named.toMap)) ++ library,
            name,
            theorem,
            Some(state.script.reaching(theorem).tidy)
          )

        case None => Essay.of(chain, name).fold(_ => absent(state, name), identity)
      }

    /**
     * The name nothing holds, with **both** places that were looked in named.
     *
     * The half of this that is worth having on its own, and the card that asked for it says so: a
     * refusal that names the set it read is right whatever is decided about what `show` reaches,
     * because the reader can then tell a name they spelled wrong from a name that is somewhere
     * else. The session's own names are listed rather than counted, since a transcript holds a
     * handful and the list is what answers the question a reader actually has.
     */
    private def absent(state: State, name: String): String = {
      val held = state.named.map(_._1).distinct

      val session =
        if (held.isEmpty) "this session holds no fact of its own"
        else s"this session holds ${held.mkString(", ")}"

      s"no fact named $name: $session, and the library under it has no lemma of that name"
    }

    /**
     * A refusal with its next step, asked of `Remedy` while the error is still a value.
     *
     * The reason is rendered with the session's own theory as well, and until 2026-09-28 it was
     * not: it was the error's `message`, which writes terms in the kernel's printing, so a `prove`
     * that LINARITH refused showed `found ((real_le real_one) ((real_mul x) x))` under a cell
     * reading `x * x >= 1`, while `ask` on the same claim was clean because it went through
     * `Remedy`. `SessionSpec` asserts the rendering on that cell. Turning an error into its message
     * before this point is what `RemedySpec` exists to prevent, and it is what this file did first.
     *
     * Three overloads because there are three refusal types and `Remedy` maps each. The kernel's has
     * no signature-taking form in `Remedy`, and does not need one; its reason is still rendered
     * with the theory, because a declaration the kernel refuses can name terms too.
     */
    private def refusal(signature: Signature, error: LogicError): Outcome =
      Outcome.Refused(error.render(signature.show), Some(Remedy.of(signature, error).message))

    private def refusal(signature: Signature, error: TacticError): Outcome =
      Outcome.Refused(error.render(signature.show), Some(Remedy.of(signature, error).message))

    private def refusal(signature: Signature, error: KernelError): Outcome =
      Outcome.Refused(error.render(signature.show), Some(Remedy.of(error).message))

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
        extended <- state.theory.declareConstant(name, parsed).left.map(refusal(state, _))
        widened <- state.logic.over(extended).left.map(refusal(state, _))
      } yield (Outcome.Extended(s"declared $name : ${schema.trim}"), state.extended(theory = extended, logic = widened)))
        .fold(refused => (refused, state), identity)

    private def define(state: State, name: String, body: String): (Outcome, State) =
      (for {
        term <- state.term(body).left.map(refusal(state, _))
        pair <- Kernel.defineConstant(state.theory, name, term).left.map(refusal(state, _))
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
        pair <- Kernel.assertAxiom(state.theory, proposition).left.map(refusal(state, _))
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
     * reporting a failure that reads like a defect. That is the whole reason and it is the
     * surface's rather than the domain's, which is worth saying because this comment used to give
     * the domain's: that a domain gets accounting and not search, cited to `docs/architecture.md`,
     * a document that does not contain the word. `DomainTheorySpec` settles a claim about an
     * invented domain through `Propositional`, so a procedure is not barred from a domain's
     * constants in principle; what it needs is the axiom instance specialised and detached by the
     * caller, and over a session that is `derive`, which [[Surface.deriving]] implements further
     * down this same object. This said "which is not written" for the day after it was written, in
     * the file that writes it, and what carried it that far is that nothing in the tree was being
     * compared with it. A figure is the easy case of that, because a test can recount one, and for
     * a while the only readings of `AGENTS.md` here did exactly that; `DocumentationSpec` now
     * compares a *list* in that document with [[Command.Keywords]], so what a watched sentence
     * needs is an anchor some test can find, and a number is one anchor rather than the only one.
     * A sentence offering neither is watched by nobody, which is what this one was.
     */
    private def proving(state: State, name: String, claim: String): (Outcome, State) =
      state.proposition(claim) match {
        case Left(unreadable) => (refusal(state, unreadable), state)
        case Right(goal) =>
          val ownConstants = state.theory.constants.keySet -- chain.widest.theory.constants.keySet
          val named = Surface.constantsIn(goal).intersect(ownConstants)
          prove(goal) match {
            case Right(outcome) =>
              val theorem = outcome.theorem
              // The sentence is `Cost.cutShortCaveat` rather than a literal here, and it stopped
              // being one on 2026-09-19 when `Cost.page` began saying it too. Two copies of one
              // sentence on two surfaces is the shape this repository calls a fact written twice,
              // and the copy that drifts is always the one nothing generates.
              val cutShort = outcome match {
                case Prove.Outcome.CutShort(_, search, depth) =>
                  Some(Cost.cutShortCaveat(search, depth))
                case Prove.Outcome.Settled(_) => None
              }
              (
                Outcome.Proved(name, theorem, cutShort),
                state.extended(named = state.named :+ (name -> theorem))
              )
            case Left(failure) if named.nonEmpty =>
              (
                Outcome.Refused(
                  s"${failure.render(state.show)}; this claim names ${named.toVector.sorted.mkString(", ")}, which this " +
                    "session introduced, and no tactic here searches over a constant the chain never saw",
                  Some("derive it by hand from what you assumed, or state it over the chain's own constants")
                ),
                state
              )
            case Left(failure) => (refusal(state, failure), state)
          }
      }

    /**
     * One inference by hand, over facts this session already holds.
     *
     * The command the accounting promise needed and did not have. `prove` puts a claim to the
     * tactic surface, and that surface is built over the base chain, so a claim written in a
     * vocabulary the session added is one no procedure has a reading of: a session that declares a
     * domain, assumes its axioms and asks for a consequence is refused, correctly, by every tactic
     * there is. That refusal already named this command as the way out and this command did not
     * exist, so the promise "assume something and every theorem downstream carries it" was true of
     * theorems nobody could reach.
     *
     * It changes no theory, and that is structural rather than a rule observed here. Every branch
     * below returns `state.extended(named = ..., script = ...)`, so `theory` and `logic` are the
     * ones it was given. A session holds one theory because the falsity `SoundnessAttackSpec`
     * derives needs two, and a command that could build a second would reopen that whatever else
     * it did; this one cannot reach `declareConstant` or `assertAxiom` at all.
     *
     * Every step goes through [[Recorder]] rather than through `Rules`, so the account exists as a
     * side product and the theorem is the one the rule would have returned either way. The
     * recorder is built per command because it is a wrapper over `state.logic.rules` and the
     * notation, and both are already on the state.
     */
    private def deriving(state: State, name: String, step: String): (Outcome, State) = {
      val recorder = new Recorder(state.logic.rules, state.notation)

      /**
       * A fact by the name this session knows it under, then by the library's.
       *
       * The session first, because a name it introduced is the one the reader just typed. The
       * library second and only when the name resolves to ONE statement: `Library.named` returns
       * every entry of that name and its own docstring says three names are held by two
       * developments each, so picking the first would pick by map iteration order.
       */
      def fact(reference: String): Either[String, Kernel.Thm] =
        state.fact(reference) match {
          case Some(theorem) => Right(theorem)
          case None =>
            library.named(reference).map(_.theorem).distinct match {
              case Vector(one) => Right(one)
              case Vector() =>
                Left(s"no fact named $reference: this session holds ${held(state)}")
              case several =>
                Left(
                  s"$reference names ${several.size} different statements across the library's " +
                    "developments, so this cannot tell which was meant"
                )
            }
        }

      /**
       * The types the leading quantifiers of a statement bind, outermost first.
       *
       * Read so that an argument of `specialise` is elaborated against the binder it is going to
       * instantiate. Without it `specialise RULE at 1` is refused, correctly and uselessly: a
       * numeral whose type nothing determines is ambiguous between `real` and `num`, and the thing
       * that determines it is the quantifier, which is in the caller's hand and not in the text.
       * This is `Signature.term(text, expected)` used where the expectation actually lives, which
       * is the rule `Parser.term`'s own docstring states for a caller that knows the type.
       */
      def binders(proposition: Term): Vector[Type] = proposition match {
        case App(Const(Logic.Universal, _), Abs(binderType, body)) => binderType +: binders(body)
        case _ => Vector.empty
      }

      def term(text: String, expected: Option[Type]): Either[String, Term] =
        expected.fold(state.term(text))(state.term(text, _)).left.map(_.render(state.show))

      def terms(text: String, expected: Vector[Type]): Either[String, List[Term]] =
        text.split(",").toVector.map(_.trim).filter(_.nonEmpty) match {
          case Vector() => Left("specialise wants at least one term after `at`")
          case parts =>
            parts.zipWithIndex
              .foldLeft[Either[String, List[Term]]](Right(Nil)) { case (found, (part, position)) =>
                for { so <- found; one <- term(part, expected.lift(position)) } yield so :+ one
              }
        }

      def two(shape: String)(use: (Kernel.Thm, Kernel.Thm) => Recorded[Kernel.Thm]): Either[String, Recorded[Kernel.Thm]] =
        step.trim.split("\\s+").toVector.drop(1) match {
          case Vector(left, right) => for { a <- fact(left); b <- fact(right) } yield use(a, b)
          case _ => Left(s"written `$shape`")
        }

      def one(shape: String)(use: Kernel.Thm => Recorded[Kernel.Thm]): Either[String, Recorded[Kernel.Thm]] =
        step.trim.split("\\s+").toVector.drop(1) match {
          case Vector(only) => fact(only).map(use)
          case _ => Left(s"written `$shape`")
        }

      val (operation, rest) = step.trim.span(!_.isWhitespace) match {
        case (head, tail) => (head.toLowerCase, tail.trim)
      }

      val attempted: Either[String, Recorded[Kernel.Thm]] = operation match {
        case "specialise" =>
          // The FIRST ` at `, because a term can contain the word and a name cannot contain a space.
          val marker = rest.indexOf(" at ")
          if (marker < 0) Left("written `specialise <FACT> at <term>[, <term>]`")
          else
            for {
              theorem <- fact(rest.take(marker).trim)
              arguments <- terms(rest.drop(marker + 4), binders(theorem.conclusion))
            } yield recorder.specialise(theorem, arguments)
        case "mp" => two("mp <IMPLICATION> <ANTECEDENT>")(recorder.modusPonens)
        case "left" => one("left <CONJUNCTION>")(recorder.firstHalf)
        case "right" => one("right <CONJUNCTION>")(recorder.secondHalf)
        case "both" => two("both <FACT> <FACT>")(recorder.both)
        case other =>
          Left(s"no inference `$other`; there are ${Surface.Inferences.mkString(", ")}")
      }

      attempted match {
        case Left(reason) =>
          (
            Outcome.Refused(
              s"derive $name: $reason",
              Some(s"the inferences are ${Surface.Inferences.mkString(", ")}, over facts this session holds")
            ),
            state
          )
        case Right(recorded) =>
          recorded.both match {
            case Left(error) => (refusal(state, error), state)
            case Right((theorem, account)) =>
              (
                Outcome.Proved(name, theorem),
                state.extended(
                  named = state.named :+ (name -> theorem),
                  script = Script(state.script.steps ++ account.steps).tidy
                )
              )
          }
      }
    }

    /**
     * A theorem of the proof language, checked by the elaborator against this session.
     *
     * The text is read by the document reader and must be one theorem: [[Session.runAll]] cuts a
     * submission so that it is, and a cell that is something else is refused saying what it is.
     * What the elaborator answers is kept whole, the price on a theorem it proved and every problem
     * of one it did not, each with its goal, so a session shows what the checker shows.
     */
    private def theorem(state: State, text: String): (Outcome, State) = {
      val parsed = Document.read(text)
      val report = elaborate.within(Elaborate.Scope(state.theory, state.notation, state.logic), state.named, state.imported, parsed)
      val syntax = parsed.errors.map(e => Elaborate.Problem(e.line, e.reason, None, None))
      report.entries match {
        case Vector(entry) if entry.kind == Elaborate.Kind.Theorem =>
          (entry.status, entry.theorem) match {
            case (Elaborate.Status.Proved, Some(proved)) if syntax.isEmpty && report.imports.isEmpty =>
              (Outcome.Proved(entry.name, proved, None, entry.price), state.extended(named = state.named :+ (entry.name -> proved)))
            case _ => (Outcome.Incomplete(entry.name, syntax ++ report.imports ++ entry.problems), state)
          }
        case Vector() if syntax.nonEmpty =>
          (Outcome.Refused(syntax.map(p => s"line ${p.line}: ${p.reason}").mkString("; "), Some(Command.TheoremShape)), state)
        case _ =>
          (Outcome.Refused("a `theorem` cell holds one theorem and nothing else", Some(Command.TheoremShape)), state)
      }
    }

    /**
     * A document's definitions made in this session's theory, and its theorems held as facts,
     * with every document it imports in turn.
     *
     * All or nothing. The documents are checked by `Workspace` over the chain, as the checker checks
     * them, and then their definitions are made again here, in the order they were checked; a
     * definition made again is the same constant (`docs/adr/0008`), so a theorem proved where its
     * document was checked is about the constant this session reads. Anything refused on the way,
     * a document that does not check, a name this session already uses, leaves the session as it
     * was, because a session that took half a document would hold theorems about constants it does
     * not have.
     *
     * A document already imported, directly or by another import, is not made twice.
     */
    private def importing(state: State, name: String): (Outcome, State) = {
      val checked = new Workspace(elaborate, source).check(Vector(name))
      val failing = checked.done.filterNot(_.report.ok)
      if (checked.find(name).isEmpty)
        (Outcome.Refused(s"no document named $name", Some("a session imports the documents its command can read: the published ones")), state)
      else if (failing.nonEmpty)
        (Outcome.Refused(failing.map(d => s"${d.name} does not check:\n${d.report.render}").mkString("\n"),
          Some("check it with the checker command and repair it")), state)
      else {
        val fresh = checked.done.filterNot(done => state.documents.contains(done.name))
        val taken = state.named.map(_._1).toSet ++ state.imported.facts.keySet
        val made = fresh.foldLeft[Either[String, State]](Right(state)) { (acc, done) =>
          acc.flatMap { current =>
            val definitions = done.report.entries.filter(_.status == Elaborate.Status.Defined)
            val widened = definitions.foldLeft[Either[String, State]](Right(current)) { (inner, entry) =>
              inner.flatMap { here =>
                entry.theorem.flatMap(t => Term.destEq(t.conclusion)) match {
                  case None => Left(s"${done.name}: ${entry.name} is defined and its defining theorem is not an equation")
                  case Some((_, body)) =>
                    (for {
                      pair <- LogicError.lift(Kernel.defineConstant(here.theory, entry.name, body))
                      logic <- here.logic.over(pair._1)
                    } yield here.extended(theory = pair._1, logic = logic)).left.map(error =>
                      s"${entry.name}, defined in ${done.name}, cannot be defined in this session: ${error.render(here.show)}")
                }
              }
            }
            val facts = done.report.entries.collect { case entry if entry.theorem.isDefined => entry.name -> entry.theorem.get }
            widened.flatMap { here =>
              facts.find { case (fact, _) => taken.contains(fact) || here.imported.facts.contains(fact) } match {
                case Some((fact, _)) => Left(s"$fact, declared in ${done.name}, is a name this session already holds")
                case None =>
                  val held = facts.map { case (fact, theorem) => fact -> Elaborate.Imported.Fact(done.name, Kernel.cite(fact, theorem)) }
                  Right(here.extended(
                    imported = here.imported.copy(facts = here.imported.facts ++ held),
                    documents = here.documents :+ done.name
                  ))
              }
            }
          }
        }
        made match {
          case Left(reason) => (Outcome.Refused(reason, Some("nothing was imported; rename the clashing name or import the other document")), state)
          case Right(next) =>
            val added = next.documents.drop(state.documents.size)
            val what =
              if (added.isEmpty) s"$name is already imported"
              else s"imported ${added.mkString(", ")}: ${next.imported.facts.size - state.imported.facts.size} facts"
            (Outcome.Extended(what), next)
        }
      }
    }

    /** What a session holds, for a refusal that would otherwise say only that a name is unknown. */
    private def held(state: State): String =
      if (state.named.isEmpty) "nothing yet"
      else state.named.map(_._1).mkString(", ")
  }

  private[tactics] object Surface {

    /** What a session's own facts are filed under on a page that shows one. */
    val Held: String = "this session"

    /**
     * The inferences `derive` offers, each one a [[Recorder]] operation and nothing else.
     *
     * The set is measured rather than chosen. `DomainTheorySpec` is the one hand derivation of a
     * claim about an invented domain that this repository has, and its operations are conjunction
     * elimination five times, negation elimination three, specialisation twice, modus ponens twice,
     * generalisation twice, disjunction elimination twice, and one each of negation introduction
     * and discharge. What is offered here is the part of that list whose arguments are **names of
     * facts this session already holds**, plus terms for the one operation that instantiates.
     *
     * That criterion is the cut, and it is worth stating because the obvious cut is "the common
     * ones". Negation elimination, disjunction elimination and discharge each take a TERM as a
     * premise rather than a named fact, so offering them means deciding how a notebook line
     * elaborates a term in the middle of an inference, which is a second decision and not this
     * one. Generalisation takes a free VARIABLE, which is the same problem in a smaller costume.
     * They are absent and named absent, rather than approximated.
     *
     * `Recorder.step` is deliberately not reachable from here at all. It is the facade's escape
     * hatch, it takes the name of a rule as a string, and a cell that reached it would let a
     * reader write a line claiming any inference at all into an account that is read as a record
     * of what happened.
     */
    val Inferences: Vector[String] = Vector("specialise", "mp", "left", "right", "both")

    /** The constants a term names, which is how a session tells its own vocabulary from the chain's. */
    def constantsIn(term: Term): Set[String] = term match {
      case Const(name, _) => Set(name)
      case App(fn, argument) => constantsIn(fn) ++ constantsIn(argument)
      case Abs(_, body) => constantsIn(body)
      case _ => Set.empty
    }

    /** Everything a session runs against, built once. */
    def of(chain: Chain, source: String => Option[String]): Surface = {
      val prove = Prove
        .construct(chain)
        .fold(error => throw new IllegalStateException(s"the tactic surface does not build: ${error.message}"), identity)
      val cost = Cost
        .construct(chain)
        .fold(error => throw new IllegalStateException(s"the cost report does not build: ${error.message}"), identity)
      new Surface(chain, Library.of(chain), prove, cost, Elaborate.of(chain), source)
    }
  }
}
