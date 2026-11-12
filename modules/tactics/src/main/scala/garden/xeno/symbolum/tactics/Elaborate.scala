package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Chain, Library, Natural, NaturalLinear, Peano, Reach, Real, Signature}

/**
 * A proof document checked: each declaration elaborated into kernel calls, and what became of it.
 *
 * The arrangement is LCF's and the trust argument is the one this repository already makes for
 * `tactics`: nothing here constructs a theorem. Every step of a structured proof turns into calls to
 * `Rules`, `Conv`, `Rewrite`, `Apply`, `Classical` and the decision procedures, and the theorem a
 * declaration ends with is the kernel's. An elaborator that is wrong refuses a correct proof or
 * reports a theorem other than the one written, and the second is checked on every declaration: the
 * conclusion must be the claim as read and the hypotheses must be empty, or the declaration is not
 * proved whatever its steps said.
 *
 * == Recovery ==
 *
 * One failed step does not end the checking, which is the property `docs/adr/0070` puts second on
 * the list a proof language has to meet. A failed `have` leaves its claim in the context as an
 * assumption, so the steps after it are still checked against the fact they were written to use,
 * and what they build is then discarded; every branch of a split is checked whether or not another
 * branch failed; a failed declaration leaves every later declaration checked, and a later one that
 * cites it is told the name's proof failed rather than that the name does not exist. Each problem
 * is reported with its line, the refusal, the next step `Remedy` offers, the goal as it stood, and,
 * where a method was asked and refused, what `Refutation` says about whether the goal is false.
 *
 * A declaration with any problem is **incomplete** and contributes nothing: its name is not a fact of
 * the document, and nothing downstream can rest on it. That is the line between this and Lean's
 * `sorry`, which lets a later proof rest on a hole and marks it with a warning. Here a hole is not a
 * theorem, so there is nothing to warn about downstream.
 *
 * == No state ==
 *
 * Every step returns a [[Elaborate.Checked]]: the theorem when there is one, the problems met on the
 * way, and the notes a price depends on. Problems travel in the value rather than into a collection
 * somebody appends to, so a step that is retried, as an alternative of `first` is, contributes
 * exactly what it returned and nothing else.
 */
final class Elaborate private (
  val chain: Chain,
  private val prove: Prove,
  private val library: Library,
  private val arithmetic: NaturalLinear,
  /** Where a claim that did not settle is asked whether it is false. */
  private val refutation: Refutation,
  /**
   * The library labelled for pricing, `Reach.library`, which unlike `Library.of` carries the
   * classical axioms and the naturals' one, so a price can name every axiom it reaches.
   */
  private val priced: Library
) {
  import Elaborate.*
  import Document.{Justification, Method, Step}

  /** Check a document read from text. */
  def check(text: String): Report = check(Document.read(text))

  /**
   * Check a document already read, on its own.
   *
   * Its imports resolve to nothing here, and each is reported as a problem rather than dropped: a
   * document whose imports were silently ignored would be told that every name it imports does not
   * exist, which sends its writer looking for a typo.
   */
  def check(document: Document.Parsed): Report = {
    val report = check(document, Imported.none)
    val unresolved = document.imports.map(taken =>
      Problem(taken.line, s"`import ${taken.name}` resolves to nothing: this document was checked on its own",
        Some("check it with `Check FILE`, which reads an import from beside the file, or through `Workspace`"), None))
    report.copy(imports = unresolved ++ report.imports)
  }

  /**
   * Check a document against what it imports.
   *
   * The theory it is read in is the chain's widest, with the imported definitions made again in
   * the order given, and the facts it may cite are the imported theorems beside the library. A
   * definition made again is the same constant, because a defined constant carries its definition
   * (`docs/adr/0008`), so a theorem proved where the import was checked is about the constant this
   * document reads. A definition that cannot be made again, because two imported documents define
   * one name, is a problem of this document's imports and the rest is still checked.
   *
   * Which documents those are, and in which order, is not decided here: `Workspace` resolves the
   * names an `import` gives, and a document checked through this method on its own gets whatever
   * the caller hands it.
   */
  def check(document: Document.Parsed, imported: Imported): Report = {
    val base = Scope(chain.widest.theory, chain.widest.notation, chain.widest.logic)
    val (start, refusals) = imported.definitions.foldLeft((base, Vector.empty[Problem])) {
      case ((scope, problems), definition) =>
        val made = for {
          pair <- LogicError.lift(Kernel.defineConstant(scope.theory, definition.name, definition.body))
          logic <- scope.logic.over(pair._1)
        } yield Scope(pair._1, scope.notation, logic)
        made match {
          case Right(wider) => (wider, problems)
          case Left(error) =>
            (scope, problems :+ Problem(definition.line,
              s"${definition.name}, defined in ${definition.document}, cannot be defined here: ${error.render(scope.show)}",
              Some("two documents this one imports define the same name; one of them has to rename it"), None))
        }
    }
    Report(declarations(document, start, Held.empty, imported), document.errors, refusals)
  }

  /**
   * Check a document in a theory somebody else built, against facts it already holds: a notebook
   * session's, which is the second front end `docs/adr/0070` puts on this elaborator.
   *
   * The theory is the session's as it stands, with whatever it declared, defined and assumed, so a
   * claim about a constant the session introduced reads, and a proof may cite an assumption by
   * name. The facts are the session's named ones, held as this document's own earlier theorems
   * are, which is as citations: a price stops at them and names them, and what they rest on still
   * reaches the theorem through the citation. `imported` carries the facts of the documents the
   * session imported, whose definitions are already in `scope`, so its definitions are not made
   * again here.
   *
   * An `import` inside the text is refused on its line rather than resolved: in a session an
   * import changes the one theory every later cell is read in, which makes it a command of its
   * own and not part of one theorem.
   */
  def within(scope: Scope, facts: Vector[(String, Kernel.Thm)], imported: Imported, document: Document.Parsed): Report = {
    val held = facts.foldLeft(Held.empty.copy(holder = "this session")) { case (acc, (name, theorem)) => acc.proved(name, theorem) }
    val refused = document.imports.map(taken =>
      Problem(taken.line, s"`import ${taken.name}` inside a cell: in a session an import is a command of its own",
        Some(s"run `import ${taken.name}` on a line of its own"), None))
    Report(declarations(document, scope, held, imported.copy(definitions = Vector.empty)), document.errors, refused)
  }

  /** Every declaration, in order, each in the scope and with the facts the ones before it left. */
  private def declarations(document: Document.Parsed, start: Scope, held: Held, imported: Imported): Vector[Entry] =
    document.declarations.foldLeft((Vector.empty[Entry], start, held)) {
      case ((done, scope, facts), declaration) =>
        val (entry, nextScope, nextHeld) = declare(scope, facts, imported, declaration)
        (done :+ entry, nextScope, nextHeld)
    }._1

  /** Every axiom of the pricing library by statement, for printing a price as names. */
  private lazy val axiomNames: Map[Term, String] =
    priced.entries.reverse.filter(_.theorem.hypotheses.isEmpty).map(e => e.theorem.conclusion -> e.name).toMap

  /** The statements of every named fact, where the walk that finds what a proof cites stops. */
  private lazy val named: Set[Term] = priced.entries.map(_.theorem.conclusion).toSet

  /* ------------------------------------------------------------------ declarations */

  /**
   * Why `name` cannot be given to a declaration of this document, if it cannot.
   *
   * A name is a fact once declared, and a fact is looked up in the proof, then the document, then
   * its imports, then the library. A document's theorem named like a library lemma or an imported
   * theorem would therefore hide the other one from every later proof that cites it, and the proof
   * would read as citing the lemma a reader knows while it rested on something else. So the name is
   * refused rather than shadowed.
   */
  private def taken(held: Held, imported: Imported, name: String): Option[(String, String)] =
    if (held.has(name)) Some((s"${held.holder} already declares $name", "give it a name of its own"))
    else
      imported.facts.get(name).map(_.document).orElse(imported.failures.get(name).map(_.document)) match {
        case Some(document) =>
          Some((s"$name is declared in $document, which this document imports", "give it a name of its own"))
        case None =>
          library.named(name).headOption.map { entry =>
            (s"$name is a lemma of the library (${entry.development})",
              "give it a name of its own: a proof citing the name would otherwise reach this declaration and not the lemma")
          }
      }

  private def declare(scope: Scope, held: Held, imported: Imported, declaration: Document.Declaration): (Entry, Scope, Held) =
    declaration match {
      case Document.Declaration.Define(line, name, body) if taken(held, imported, name).isDefined =>
        val (reason, next) = taken(held, imported, name).get
        (Entry(name, line, Kind.Definition, Status.Refused, body, Vector(Problem(line, reason, Some(next), None)), None), scope, held)

      case Document.Declaration.Define(line, name, body) =>
        val outcome = for {
          term <- Parser.term(scope.theory, scope.notation, body)
          pair <- LogicError.lift(Kernel.defineConstant(scope.theory, name, term))
          logic <- scope.logic.over(pair._1)
        } yield (pair._2, Scope(pair._1, scope.notation, logic))
        outcome match {
          case Right((definition, wider)) =>
            (Entry(name, line, Kind.Definition, Status.Defined, wider.show(definition.conclusion), Vector.empty, Some(definition)),
              wider, held.proved(name, definition))
          case Left(error) =>
            (Entry(name, line, Kind.Definition, Status.Refused, body, Vector(problem(scope, line, error, None)), None),
              scope, held.failed(name, line))
        }

      case Document.Declaration.Theorem(line, name, claimText, proof) =>
        taken(held, imported, name) match {
          case Some((reason, next)) =>
            (Entry(name, line, Kind.Theorem, Status.Refused, claimText, Vector(Problem(line, reason, Some(next), None)), None),
              scope, held)
          case None =>
          Parser.proposition(scope.theory, scope.notation, claimText) match {
            case Left(error) =>
              (Entry(name, line, Kind.Theorem, Status.Refused, claimText, Vector(problem(scope, line, error, None)), None),
                scope, held.failed(name, line))
            case Right(claim) =>
              val checked = new Run(scope, held, imported).establish(Context.empty, claim, proof).flatMap { theorem =>
                if (theorem.conclusion != claim)
                  Checked.failed(Problem(line, s"the proof ends with ${scope.show(theorem.conclusion)}, and the claim is ${scope.show(claim)}",
                    None, None))
                else if (theorem.hypotheses.nonEmpty)
                  Checked.failed(Problem(line, s"the proof still rests on ${theorem.hypotheses.map(scope.show).mkString(", ")}",
                    Some("a hypothesis is discharged by the step that assumed it; one left over was never discharged"), None))
                else Checked.ok(theorem)
              }
              checked.value.filter(_ => checked.problems.isEmpty) match {
                case Some(theorem) =>
                  (Entry(name, line, Kind.Theorem, Status.Proved, scope.show(claim), Vector.empty, Some(theorem),
                    Some(price(scope, held, imported, theorem, checked.notes))),
                    scope, held.proved(name, theorem))
                case None =>
                  (Entry(name, line, Kind.Theorem, Status.Incomplete, scope.show(claim), checked.problems, None),
                    scope, held.failed(name, line))
              }
          }
        }
    }

  /**
   * What a proved theorem asks a reader to believe, and what it was built from.
   *
   * Three readings of one derivation, kept apart because they answer different questions.
   * `axioms` is every axiom the derivation reaches, walking all the way down, which is what the
   * theorem is believed on. `facts` is the library lemmas the proof cites, the walk stopping at each
   * named fact, which is what a person checking the proof reads it against: the transitive closure
   * would list the construction of `num` under every lemma about addition. `document` is this
   * document's own theorems it cites, which no library holds, and `imported` is the theorems of
   * the documents it imports that it cites, each written `DOCUMENT.NAME`.
   */
  private def price(scope: Scope, held: Held, imported: Imported, theorem: Kernel.Thm, notes: Vector[String]): Price = {
    // The document's facts and the imported ones are citations, and the walk stops at them: what
    // they were proved from is in their own price, not this one's. They are told apart by the name
    // the citation carries and not by their statement, because two of them can state one thing.
    val boundary = held.facts.values.map(_.conclusion).toSet ++ imported.facts.values.map(_.theorem.conclusion)
    val cited = Derivation.cited(theorem)
    Price(
      axioms = Derivation.axiomsOf(theorem).toVector.map(a => axiomNames.getOrElse(a, scope.show(a))).distinct.sorted,
      facts = priced.restingOn(theorem, named ++ boundary).map(_.name).distinct.sorted,
      document = held.facts.keys.filter(cited.contains).toVector.sorted,
      inferences = Derivation.size(theorem),
      notes = notes.distinct,
      imported = imported.facts.collect { case (name, fact) if cited.contains(name) => s"${fact.document}.$name" }.toVector.sorted
    )
  }

  /* ------------------------------------------------------------------ one proof */

  /** The checking of one declaration's proof. Every method is a function of its arguments. */
  private final class Run(scope: Scope, held: Held, imported: Imported) {

    private def rules: Rules = scope.logic.rules
    private def logic: Logic = scope.logic

    private def at(line: Int, context: Context, goal: Term, message: String, next: Option[String] = None): Problem =
      Problem(line, message, next, Some(context.render(scope, goal)))

    private def refuse(line: Int, context: Context, goal: Term, message: String, next: Option[String] = None): Checked[Nothing] =
      Checked.failed(at(line, context, goal, message, next))

    /** A logic step's result, or its refusal with the goal it was taken at. */
    private def attempt[A](line: Int, context: Context, goal: Term)(result: Either[LogicError, A]): Checked[A] =
      result.fold(error => Checked.failed(problem(scope, line, error, Some(context.render(scope, goal)))), Checked.ok)

    /** A claim read with the proof's fixed variables at the types they were fixed at. */
    private def read(line: Int, context: Context, goal: Term, text: String, expected: Option[Type]): Checked[Term] =
      attempt(line, context, goal)(Parser.term(scope.theory, scope.notation, text, expected, context.types))

    /**
     * Whether a goal that did not settle is false, asked of `Refutation` with the proof's facts as
     * premises and the goal as the conclusion.
     *
     * The answer is attached to the refusal and never replaces it: the method refused either way,
     * and what this adds is which situation the refusal is in. Only a found or a solved point says
     * the goal is false; a goal that survived the points where its facts held is evidence and not a
     * decision, and a goal no point could be asked about is neither, nor is one whose facts failed at
     * every point that answered. That is `docs/adr/0005`, with `docs/adr/0077` for the last, and it
     * is the reason the kind is carried as a field rather than folded into a sentence.
     */
    private def refute(context: Context, goal: Term): Refuted = {
      // A conjunction is two facts, and is handed over as two: `Refutation` reads a premise set, and
      // `x < 0 /\ 0 < x` as one premise is an atom it samples rather than two constraints it can
      // see are contradictory.
      def split(term: Term): Vector[Term] = logic.destConj(term) match {
        case Some((left, right)) => split(left) ++ split(right)
        case None => Vector(term)
      }
      val premises = context.facts.map(_._2.conclusion).filter(Term.isProposition).flatMap(split).distinct
      val outcome = refutation.counterexample(premises, goal)
      Refuted(Refuted.kind(outcome), Remedy.of(outcome).message)
    }

    /** A fact by name: the proof's own, the document's, its imports', then the library's. */
    private def lookup(line: Int, context: Context, goal: Term, name: String): Either[Problem, Kernel.Thm] =
      context.facts.reverseIterator.collectFirst { case (known, theorem) if known == name => theorem }
        .orElse(held.facts.get(name))
        .orElse(imported.facts.get(name).map(_.theorem))
        .orElse(library.named(name).headOption.map(_.theorem)) match {
        case Some(theorem) => Right(theorem)
        case None =>
          held.failures.get(name).map(declared => s"on line $declared")
            .orElse(imported.failures.get(name).map(failure => s"in ${failure.document} on line ${failure.line}")) match {
            case Some(where) =>
              Left(at(line, context, goal, s"$name is declared $where and its proof did not check, so it is not a fact",
                Some(s"repair $name first; a later proof cannot rest on one that failed")))
            case None =>
              val local = context.facts.map(_._1).distinct
              val here = if (local.isEmpty) "this proof holds no fact of its own" else s"this proof holds ${local.mkString(", ")}"
              Left(at(line, context, goal,
                s"no fact named $name: $here, this document declares none of that name" +
                  (if (imported.documents.isEmpty) "" else s", nor does any document it imports (${imported.documents.mkString(", ")})") +
                  ", and the library has no lemma of that name",
                Some("`find` searches the library by name and by shape")))
          }
      }

    private def fact(line: Int, context: Context, goal: Term, name: String): Checked[Kernel.Thm] =
      lookup(line, context, goal, name).fold(Checked.failed, Checked.ok)

    /** `goal` by `proof`, in `context`. */
    def establish(context: Context, goal: Term, proof: Justification): Checked[Kernel.Thm] =
      proof match {
        case Justification.By(line, method) => settle(line, context, goal, method)
        case Justification.Block(_, steps, closed) => run(context, goal, steps.toList, closed)
      }

    /* -------------------------------------------------------------- steps */

    /** The steps of one block, applied to `goal` in order, ending with one that closes it. */
    private def run(context: Context, goal: Term, steps: List[Step], end: Int): Checked[Kernel.Thm] =
      steps match {
        case Nil =>
          Checked.failed(at(end, context, goal, "the block ends with the goal still open",
            Some("close it with `by METHOD`, `show CLAIM by METHOD` or a step that splits it"))
            .copy(refuted = Some(refute(context, goal))))

        case Step.Fix(line, names) :: rest =>
          names.toList match {
            case Nil => run(context, goal, rest, end)
            case name :: more =>
              for {
                opened <- open(line, context, goal, name, "fix")
                inner <- run(context.fix(opened._1), opened._2, Step.Fix(line, more.toVector) :: rest, end)
                general <- attempt(line, context, goal)(rules.gen(opened._1, inner))
              } yield general
          }

        case Step.Assume(line, names) :: rest =>
          names.toList match {
            case Nil => run(context, goal, rest, end)
            case name :: more =>
              logic.destImp(goal) match {
                case None => refuse(line, context, goal, s"`assume $name` wants a goal of the form A ==> B")
                case Some((antecedent, consequent)) =>
                  for {
                    assumed <- attempt(line, context, goal)(LogicError.lift(Kernel.assume(antecedent)))
                    inner <- run(context.know(name, assumed), consequent, Step.Assume(line, more.toVector) :: rest, end)
                    discharged <- attempt(line, context, goal)(rules.disch(antecedent, inner))
                  } yield discharged
              }
          }

        case Step.Have(line, name, text, proof) :: rest =>
          read(line, context, goal, text, Some(Type.Bool)).flatMap { claim =>
            val proved = establish(context, claim, proof)
            proved.value match {
              case Some(theorem) => proved.andThen(run(context.know(name, theorem), goal, rest, end))
              case None =>
                // A failed `have` still puts its claim in the context, as an assumption, so the steps
                // after it are checked against the fact they were written to use and their own
                // problems are reported. What they build rests on the assumption and is discarded:
                // returned, every step above this one would fail on that hypothesis with a message
                // about the wrong thing, as `gen` did before this was written so.
                Kernel.assume(claim) match {
                  case Right(placeholder) => proved.andThen(run(context.know(name, placeholder), goal, rest, end)).discard
                  case Left(_) => proved
                }
            }
          }

        case Step.Show(line, claim, proof) :: rest =>
          unreachable(line, rest).andThen(claim match {
            case None => establish(context, goal, proof)
            case Some(text) =>
              read(line, context, goal, text, Some(Type.Bool)).flatMap { written =>
                if (written != goal) refuse(line, context, goal, s"`show` names ${scope.show(written)}, and the goal is ${scope.show(goal)}")
                else establish(context, goal, proof)
              }
          })

        case Step.Obtain(line, name, hypothesis, from) :: rest =>
          for {
            existential <- fact(line, context, goal, from)
            predicate <- logic.destExistsPredicate(existential.conclusion).fold(
              refuse(line, context, goal, s"$from is ${scope.show(existential.conclusion)}, which is not an existential"))(Checked.ok)
            opened <- instantiate(line, context, goal, predicate, name)
            assumed <- attempt(line, context, goal)(LogicError.lift(Kernel.assume(opened._2)))
            inner <- run(context.fix(opened._1).know(hypothesis, assumed), goal, rest, end)
            eliminated <- attempt(line, context, goal)(rules.existsElim(existential, opened._1, inner))
          } yield eliminated

        case Step.Cases(line, name, text, branches) :: rest =>
          unreachable(line, rest).andThen(for {
            claim <- read(line, context, goal, text, Some(Type.Bool))
            negation <- attempt(line, context, goal)(logic.mkNot(claim))
            grouped <- labelled(line, context, goal, branches, Vector("pos", "neg"))
            proved <- Checked.all(Vector(branch(context, goal, grouped(0), Some(name -> claim)), branch(context, goal, grouped(1), Some(name -> negation))))
            split <- attempt(line, context, goal)(chain.classical.cases(claim, proved(0), proved(1)))
          } yield split)

        case Step.CasesFrom(line, name, from, branches) :: rest =>
          unreachable(line, rest).andThen(for {
            disjunction <- fact(line, context, goal, from)
            sides <- logic.destDisj(disjunction.conclusion) match {
              case Some(found) => Checked.ok(found)
              case None =>
                refuse(line, context, goal, s"`cases $name from $from` wants $from to be a disjunction A \\/ B, and it is ${scope.show(disjunction.conclusion)}",
                  Some("a case split on a proposition is `cases NAME : CLAIM`, which needs no fact"))
            }
            grouped <- labelled(line, context, goal, branches, Vector("left", "right"))
            proved <- Checked.all(Vector(branch(context, goal, grouped(0), Some(name -> sides._1)), branch(context, goal, grouped(1), Some(name -> sides._2))))
            split <- attempt(line, context, goal)(rules.disjElim(disjunction, proved(0), proved(1)))
          } yield split)

        case Step.Induction(line, name, using, branches) :: rest =>
          unreachable(line, rest).andThen(induction(line, context, goal, name, using, branches))

        case Step.Split(line, branches) :: rest =>
          unreachable(line, rest).andThen(logic.destConj(goal) match {
            case None => refuse(line, context, goal, "`split` wants a goal of the form A /\\ B")
            case Some((left, right)) =>
              for {
                grouped <- labelled(line, context, goal, branches, Vector("left", "right"))
                proved <- Checked.all(Vector(branch(context, left, grouped(0), None), branch(context, right, grouped(1), None)))
                both <- attempt(line, context, goal)(rules.conjIntro(proved(0), proved(1)))
              } yield both
          })

        case Step.Choose(line, isLeft) :: rest =>
          logic.destDisj(goal) match {
            case None => refuse(line, context, goal, s"`${if (isLeft) "left" else "right"}` wants a goal of the form A \\/ B")
            case Some((left, right)) =>
              if (isLeft) run(context, left, rest, end).flatMap(t => attempt(line, context, goal)(rules.disjIntro1(right, t)))
              else run(context, right, rest, end).flatMap(t => attempt(line, context, goal)(rules.disjIntro2(left, t)))
          }

        case Step.Witness(line, text) :: rest =>
          logic.destExistsPredicate(goal).flatMap(p => Type.destFun(Term.typeOf(p)).map(f => (p, f._1))) match {
            case None => refuse(line, context, goal, "`witness` wants a goal of the form ?x. P x")
            case Some((predicate, domain)) =>
              for {
                witness <- read(line, context, goal, text, Some(domain))
                body <- reduce(line, context, goal, predicate, witness)
                inner <- run(context, body, rest, end)
                introduced <- attempt(line, context, goal)(rules.existsIntro(predicate, witness, inner))
              } yield introduced
          }

        case Step.Rewrite(line, names) :: rest =>
          for {
            equations <- Checked.all(names.map(fact(line, context, goal, _)))
            moved <- rewritten(line, context, goal, names, equations)
            result <-
              if (closes(moved._2)) unreachable(line, rest).andThen(closeBy(line, context, goal, moved._1, moved._2))
              else run(context, moved._2, rest, end).flatMap(inner => carry(line, context, goal, moved._1, inner))
          } yield result

        case Step.Apply(line, name, branches) :: rest =>
          for {
            lemma <- fact(line, context, goal, name)
            application <- attempt(line, context, goal)(Apply.to(logic, lemma, goal))
            result <- applied(line, context, goal, name, application, branches, rest, end)
          } yield result

        case Step.Calc(line, links) :: rest =>
          unreachable(line, rest).andThen(calc(line, context, goal, links))
      }

    /** A step that closes the goal followed by more steps: they are reported, never silently dropped. */
    private def unreachable(line: Int, rest: List[Step]): Checked[Unit] =
      rest.headOption match {
        case Some(next) =>
          Checked.warned(Problem(next.line, s"the goal is closed on line $line, so this step and the ones after it have nothing to prove", None, None))
        case None => Checked.ok(())
      }

    /** `!x. P` opened at a fixed variable of the name written. */
    private def open(line: Int, context: Context, goal: Term, name: String, step: String): Checked[(FVar, Term)] =
      logic.destForallPredicate(goal) match {
        case None => refuse(line, context, goal, s"`$step $name` wants a goal of the form !x. P x")
        case Some(predicate) => instantiate(line, context, goal, predicate, name)
      }

    /** A predicate applied to a new variable of the name written, and reduced. */
    private def instantiate(line: Int, context: Context, goal: Term, predicate: Term, name: String): Checked[(FVar, Term)] =
      Type.destFun(Term.typeOf(predicate)) match {
        case None => refuse(line, context, goal, s"${scope.show(predicate)} is not a predicate")
        case Some((domain, _)) =>
          if (scope.theory.constants.contains(name))
            refuse(line, context, goal, s"$name is a constant of the theory, so it cannot also name a variable here")
          else if (context.fixed.exists(_.name == name) || context.mentions(name) || Term.freeVariables(goal).exists(_.name == name))
            refuse(line, context, goal, s"$name already names something in this proof", Some("choose a name the proof has not used"))
          else {
            val variable = Term.variable(name, domain)
            reduce(line, context, goal, predicate, variable).map(body => (variable, body))
          }
      }

    private def reduce(line: Int, context: Context, goal: Term, predicate: Term, argument: Term): Checked[Term] =
      attempt(line, context, goal) {
        for {
          applied <- LogicError.lift(Term.app(predicate, argument))
          reduced <- Term.betaReduce(applied).toRight(NotOfForm("a redex", applied))
        } yield reduced
      }

    /** Branches matched to the labels a step produces, in that order, each exactly once. */
    private def labelled(
      line: Int,
      context: Context,
      goal: Term,
      branches: Vector[Document.Branch],
      labels: Vector[String]
    ): Checked[Vector[Document.Branch]] = {
      val numbered = labels.indices.map(i => (i + 1).toString)
      def index(branch: Document.Branch): Int = {
        val found = labels.indexOf(branch.label)
        if (found >= 0) found else numbered.indexOf(branch.label)
      }
      val unknown = branches.filter(index(_) < 0)
      val positions = branches.map(index)
      val repeated = positions.diff(positions.distinct).distinct
      val missing = labels.indices.filterNot(positions.contains)
      val expected = labels.zip(numbered).map { case (l, n) => if (l == n) l else s"$l (or $n)" }.mkString(", ")
      if (unknown.nonEmpty)
        refuse(unknown.head.line, context, goal, s"no case `${unknown.head.label}` here; the cases are $expected")
      else if (repeated.nonEmpty)
        refuse(line, context, goal, s"the case `${labels(repeated.head)}` is written twice")
      else if (missing.nonEmpty)
        refuse(line, context, goal, s"the case `${labels(missing.head)}` is missing; the cases are $expected")
      else Checked.ok(labels.indices.map(i => branches(positions.indexOf(i))).toVector)
    }

    /**
     * One branch: its header names introduced, an optional hypothesis the step supplies, then its steps.
     *
     * The names in `case succ m ih:` are read against the branch's goal one at a time: a universal is
     * opened at the name, an implication is assumed under it. So the header says what the branch
     * calls the things its case binds, which is what Lean's `| succ m ih =>` says, and a header with
     * more names than the case binds is refused rather than ignored.
     */
    private def branch(context: Context, goal: Term, branch: Document.Branch, hypothesis: Option[(String, Term)]): Checked[Kernel.Thm] =
      hypothesis match {
        case Some((name, claim)) =>
          attempt(branch.line, context, goal)(LogicError.lift(Kernel.assume(claim)))
            .flatMap(assumed => introduce(branch, context.know(name, assumed), goal, branch.names.toList))
        case None => introduce(branch, context, goal, branch.names.toList)
      }

    private def introduce(branch: Document.Branch, context: Context, goal: Term, names: List[String]): Checked[Kernel.Thm] =
      names match {
        case Nil => run(context, goal, branch.steps.toList, branch.steps.lastOption.map(_.line).getOrElse(branch.line))
        case name :: more =>
          if (logic.destForallPredicate(goal).isDefined)
            for {
              opened <- open(branch.line, context, goal, name, s"case ${branch.label}")
              inner <- introduce(branch, context.fix(opened._1), opened._2, more)
              general <- attempt(branch.line, context, goal)(rules.gen(opened._1, inner))
            } yield general
          else
            logic.destImp(goal) match {
              case Some((antecedent, consequent)) =>
                for {
                  assumed <- attempt(branch.line, context, goal)(LogicError.lift(Kernel.assume(antecedent)))
                  inner <- introduce(branch, context.know(name, assumed), consequent, more)
                  discharged <- attempt(branch.line, context, goal)(rules.disch(antecedent, inner))
                } yield discharged
              case None =>
                refuse(branch.line, context, goal, s"`case ${branch.label}` names $name, and its goal binds nothing more")
            }
      }

    /* -------------------------------------------------------------- induction */

    /**
     * Induction over a fixed variable, with the principle the variable's type has or the one named.
     *
     * The goal is generalised over the variable, the principle is specialised at the predicate that
     * generalisation is, and each conjunct of the principle's premise is a branch. Facts of the proof
     * that mention the variable are refused rather than carried into the goal, because carrying them
     * changes the induction hypothesis and the writer should see that in the claim they write.
     */
    private def induction(
      line: Int,
      context: Context,
      goal: Term,
      name: String,
      using: Option[String],
      branches: Vector[Document.Branch]
    ): Checked[Kernel.Thm] =
      context.fixed.find(_.name == name) match {
        case None => refuse(line, context, goal, s"induction is over a fixed variable, and $name is not one", Some(s"`fix $name` first"))
        case Some(variable) =>
          val mentioning = context.facts.filter { case (_, t) => (t.conclusion +: t.hypotheses).exists(Term.occursFree(variable, _)) }
          if (mentioning.nonEmpty)
            refuse(line, context, goal,
              s"the facts ${mentioning.map(_._1).distinct.mkString(", ")} mention $name, and induction over $name would leave them behind",
              Some(s"state them as hypotheses of the goal before `fix $name`, so the induction carries them"))
          else {
            val principle: Checked[(String, Kernel.Thm, Vector[String])] = using match {
              case Some(lemma) => fact(line, context, goal, lemma).map(t => (lemma, t, Vector.empty))
              case None =>
                Defaults.get(variable.ty) match {
                  case Some((lemma, labels)) => fact(line, context, goal, lemma).map(t => (lemma, t, labels))
                  case None =>
                    refuse(line, context, goal, s"no default induction principle for ${Show.show(variable.ty)}",
                      Some(s"name one: `induction $name using LEMMA`, where LEMMA concludes !x. P x"))
                }
            }
            val outer = context.unfix(variable)
            for {
              chosen <- principle
              general <- attempt(line, context, goal)(logic.mkForall(variable, goal))
              predicate <- logic.destForallPredicate(general).fold(refuse(line, context, goal, "the generalised goal is not a universal"))(Checked.ok)
              instance <- specialisePrinciple(line, context, goal, chosen._1, chosen._2, predicate, general)
              labels = if (chosen._3.size == instance._1.size) chosen._3 else instance._1.indices.map(i => (i + 1).toString).toVector
              grouped <- labelled(line, context, goal, branches, labels)
              proved <- Checked.all(instance._1.zip(grouped).map { case (premise, b) => branch(outer, premise, b, None) })
              joined <- attempt(line, context, goal)(conjoin(proved))
              all <- attempt(line, context, goal)(rules.mp(instance._2, joined))
              back <- attempt(line, context, goal)(rules.spec(variable, all))
              result <- if (back.conclusion == goal) Checked.ok(back) else attempt(line, context, goal)(normalised(back, goal))
            } yield result
          }
      }

    /**
     * The principle at the predicate: its premises, one per case, and `premise ==> !x. P x`.
     *
     * How many cases there are is read off the principle before it is instantiated, since a goal that
     * is itself a conjunction would otherwise be split into cases the principle never had.
     */
    private def specialisePrinciple(
      line: Int,
      context: Context,
      goal: Term,
      name: String,
      lemma: Kernel.Thm,
      predicate: Term,
      general: Term
    ): Checked[(Vector[Term], Kernel.Thm)] = {
      val shape = for {
        schematic <- logic.destForallPredicate(lemma.conclusion)
        binder <- Type.destFun(Term.typeOf(schematic)).map(_._1)
        types <- matchType(binder, Term.typeOf(predicate), Map.empty)
      } yield (schematic, binder, types)
      val notPrinciple = s"$name is not an induction principle over this variable's type: it should read !P. ... ==> (!x. P x)"
      shape match {
        case None => refuse(line, context, goal, notPrinciple)
        case Some((schematic, binder, types)) =>
          val atTypes = if (types.isEmpty) lemma else Kernel.instType(types, lemma)
          val cases = Term.app(Term.substituteTypes(types, schematic), Term.variable("P", Type.substitute(types, binder))).toOption
            .flatMap(Term.betaReduce).flatMap(logic.destImp).map { case (premise, _) => conjuncts(premise, Int.MaxValue).size }
          cases match {
            case None => refuse(line, context, goal, notPrinciple)
            case Some(count) =>
              for {
                specialised <- attempt(line, context, goal)(rules.spec(predicate, atTypes))
                equation <- attempt(line, context, goal)(Conv.betaNormalise(specialised.conclusion))
                reduced <- attempt(line, context, goal)(LogicError.lift(Kernel.eqMp(equation, specialised)))
                parts <- logic.destImp(reduced.conclusion).fold(refuse(line, context, goal, s"$name at this predicate is not an implication"))(Checked.ok)
                _ <-
                  if (parts._2 == general) Checked.ok(())
                  else refuse(line, context, goal, s"$name concludes ${scope.show(parts._2)} here, and the goal generalised is ${scope.show(general)}")
              } yield (conjuncts(parts._1, count), reduced)
          }
      }
    }

    /** At most `count` conjuncts of a right-nested conjunction, the last one holding the rest. */
    private def conjuncts(term: Term, count: Int): Vector[Term] =
      if (count <= 1) Vector(term)
      else logic.destConj(term) match {
        case Some((left, right)) => left +: conjuncts(right, count - 1)
        case None => Vector(term)
      }

    private def conjoin(theorems: Vector[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      theorems.reverse.toList match {
        case Nil => rules.truth
        case last :: before => before.foldLeft(Right(last): Either[LogicError, Kernel.Thm])((acc, t) => acc.flatMap(rules.conjIntro(t, _)))
      }

    /** `theorem` carried to `goal`, which it equals up to beta reduction. */
    private def normalised(theorem: Kernel.Thm, goal: Term): Either[LogicError, Kernel.Thm] =
      for {
        there <- Conv.betaNormalise(theorem.conclusion)
        here <- Conv.betaNormalise(goal)
        back <- Conv.sym(here)
        both <- Conv.trans(there, back)
        result <- LogicError.lift(Kernel.eqMp(both, theorem))
      } yield result

    /* -------------------------------------------------------------- apply, rewrite, calc */

    private def applied(
      line: Int,
      context: Context,
      goal: Term,
      name: String,
      application: Apply.Application,
      branches: Vector[Document.Branch],
      rest: List[Step],
      end: Int
    ): Checked[Kernel.Thm] = {
      val owed = application.obligations
      val inner: Checked[Vector[Kernel.Thm]] =
        if (owed.isEmpty)
          unreachable(line, rest).andThen(
            if (branches.nonEmpty) refuse(line, context, goal, s"$name owes nothing here, so it has no cases") else Checked.ok(Vector.empty))
        else if (owed.size == 1 && branches.isEmpty) run(context, owed.head, rest, end).map(Vector(_))
        else
          unreachable(line, rest).andThen(
            labelled(line, context, goal, branches, owed.indices.map(i => (i + 1).toString).toVector).flatMap { grouped =>
              Checked.all(owed.zip(grouped).map { case (obligation, b) => branch(context, obligation, b, None) })
            })
      inner.flatMap { proofs =>
        attempt(line, context, goal) {
          proofs.foldLeft(Right(application.theorem): Either[LogicError, Kernel.Thm])((acc, p) => acc.flatMap(rules.mp(_, p)))
            .flatMap(rules.genAll(_, application.generalising.toList))
        }
      }
    }

    /** Whether a rewritten goal is closed by what it became: `T`, or `t = t`. */
    private def closes(after: Term): Boolean =
      after == logic.truth || Term.destEq(after).exists { case (l, r) => l == r }

    /**
     * `|- goal = after` by the equations, when the rewriting finished and changed something.
     *
     * Asked through `Rewrite.rewriteReporting` and never `Rewrite.rewrite`, because the second hands
     * back the theorem it had when its step limit ran out and that theorem is true: a goal moved to
     * a waypoint would carry on as though it were a normal form. A walk the limit stopped or the
     * ceiling stopped is a refusal naming which, and a proof never continues from one.
     */
    private def rewriting(names: Vector[String], equations: Vector[Kernel.Thm], goal: Term): Either[(String, Option[String]), (Kernel.Thm, Term)] = {
      val written = names.mkString(", ")
      Rewrite.Rule.all(logic, equations).flatMap(Rewrite.rewriteReporting(_, goal)) match {
        case Left(error) => Left((error.render(scope.show), Some(Remedy.of(scope, error).message)))
        case Right((equation, stop)) =>
          stop match {
            case Rewrite.Stop.Steps =>
              Left((s"rewriting with $written did not finish: the step limit ran out, so what it reached is a waypoint and not a normal form",
                Some("the equations may undo each other; rewrite with fewer of them, or with one oriented the other way")))
            case Rewrite.Stop.Size(width) =>
              Left((s"rewriting with $written grew the goal past the ceiling, to $width nodes: the equations multiply the term",
                Some("rewrite with fewer equations")))
            case Rewrite.Stop.Settled =>
              Term.destEq(equation.conclusion).map(_._2) match {
                case None => Left(("the rewriter returned something other than an equation", None))
                case Some(after) if after == goal =>
                  Left((s"rewriting with $written changes nothing in the goal",
                    Some("an equation rewrites where its left side matches; `find` shows a lemma's statement")))
                case Some(after) => Right((equation, after))
              }
          }
      }
    }

    private def rewritten(line: Int, context: Context, goal: Term, names: Vector[String], equations: Vector[Kernel.Thm]): Checked[(Kernel.Thm, Term)] =
      rewriting(names, equations, goal).fold({ case (message, next) => refuse(line, context, goal, message, next) }, Checked.ok)

    /** `goal` from `|- goal = after`, where `after` is `T` or `t = t`. */
    private def closing(equation: Kernel.Thm, after: Term): Either[LogicError, Kernel.Thm] =
      for {
        proofOfAfter <- if (after == logic.truth) rules.truth else Right(Kernel.refl(Term.destEq(after).map(_._1).getOrElse(after)))
        back <- Conv.sym(equation)
        result <- LogicError.lift(Kernel.eqMp(back, proofOfAfter))
      } yield result

    private def closeBy(line: Int, context: Context, goal: Term, equation: Kernel.Thm, after: Term): Checked[Kernel.Thm] =
      attempt(line, context, goal)(closing(equation, after))

    /** `goal` from `|- goal = after` and a proof of `after`. */
    private def carrying(equation: Kernel.Thm, inner: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        back <- Conv.sym(equation)
        result <- LogicError.lift(Kernel.eqMp(back, inner))
      } yield result

    private def carry(line: Int, context: Context, goal: Term, equation: Kernel.Thm, inner: Kernel.Thm): Checked[Kernel.Thm] =
      attempt(line, context, goal)(carrying(equation, inner))

    /**
     * A chain of relations whose ends are the goal.
     *
     * Every link is checked whether or not another failed. Equations compose by transitivity. A chain
     * with an order in it composes by the procedure for its type, `LINARITH` over the reals and
     * linear arithmetic over the naturals, asked for the one implication from the two links to their
     * composite, so nothing about orders is decided here.
     */
    private def calc(line: Int, context: Context, goal: Term, links: Vector[Document.Link]): Checked[Kernel.Thm] =
      Checked.all(links.map { link =>
        read(link.line, context, goal, link.claim, Some(Type.Bool)).flatMap(claim => settle(link.line, context, claim, link.method))
      }).flatMap { theorems =>
        theorems.tail.foldLeft(Checked.ok(theorems.head): Checked[Kernel.Thm])((acc, next) => acc.flatMap(compose(line, context, goal, _, next)))
      }.flatMap { chained =>
        if (chained.conclusion == goal) Checked.ok(chained)
        else refuse(line, context, goal, s"the chain proves ${scope.show(chained.conclusion)}, and the goal is ${scope.show(goal)}")
      }

    private def compose(line: Int, context: Context, goal: Term, first: Kernel.Thm, second: Kernel.Thm): Checked[Kernel.Thm] =
      (relation(first.conclusion), relation(second.conclusion)) match {
        case (Some((r1, a, b)), Some((r2, b2, c))) if b == b2 =>
          (r1, r2) match {
            case (None, None) => attempt(line, context, goal)(Conv.trans(first, second))
            case _ =>
              // The stricter of the two relations, which is what the composite holds with.
              val composite = (r1, r2) match {
                case (Some(x), Some(y)) => if (strict(x)) x else y
                case (Some(x), None) => x
                case (None, Some(y)) => y
                case (None, None) => logic.truth
              }
              for {
                claim <- attempt(line, context, goal)(LogicError.lift(Term.appAll(composite, List(a, c))))
                joined <- attempt(line, context, goal)(byProcedure(Vector(first, second), claim))
              } yield joined
          }
        case _ =>
          refuse(line, context, goal, s"the links ${scope.show(first.conclusion)} and ${scope.show(second.conclusion)} do not meet")
      }

    /** `(relation, left, right)`, the relation `None` for an equation. */
    private def relation(term: Term): Option[(Option[Term], Term, Term)] =
      Term.destEq(term).map { case (l, r) => (Option.empty[Term], l, r) }.orElse(term match {
        case App(App(c @ Const(_, _), l), r) if Term.typeOf(term) == Type.Bool => Some((Some(c), l, r))
        case _ => None
      })

    private def strict(relation: Term): Boolean = relation match {
      case Const(name, _) => name == Real.Order || name == Peano.StrictOrder
      case _ => false
    }

    /** `claim` from `facts` by the procedure for the type it is about. */
    private def byProcedure(facts: Vector[Kernel.Thm], claim: Term): Either[LogicError, Kernel.Thm] =
      relation(claim).map(_._2).map(Term.typeOf) match {
        case Some(ty) if ty == Numbers => arithmetic(facts, claim)
        case _ => linearly(facts, claim)
      }

    /** `claim` by `LINARITH`, from `facts` conjoined as its hypotheses. */
    private def linearly(facts: Vector[Kernel.Thm], claim: Term): Either[LogicError, Kernel.Thm] =
      if (facts.isEmpty) prove.linarith.prove(claim)
      else
        for {
          joined <- conjoin(facts)
          implication <- logic.mkImp(joined.conclusion, claim)
          proved <- prove.linarith.prove(implication)
          result <- rules.mp(proved, joined)
        } yield result

    /* -------------------------------------------------------------- methods */

    /**
     * `goal` settled by one method, in `context`, with what `Refutation` says when it was not.
     *
     * What comes back is checked here and not trusted from the method: its conclusion must be the goal
     * as written, and its hypotheses must be ones the context holds. A method that proves something
     * else is refused with both statements printed, which is what keeps a procedure that normalised
     * the goal on its way from being read as having proved it.
     */
    private def settle(line: Int, context: Context, goal: Term, method: Method): Checked[Kernel.Thm] =
      outcome(line, context, goal, method) match {
        case Left(problem) => Checked.failed(problem.copy(refuted = Some(refute(context, goal))))
        case Right((theorem, notes)) => Checked(Some(theorem), Vector.empty, notes)
      }

    /** The theorem a method returns and the notes its price depends on, or its refusal. */
    private def outcome(line: Int, context: Context, goal: Term, method: Method): Either[Problem, (Kernel.Thm, Vector[String])] = {
      def here(message: String, next: Option[String] = None): Problem = at(line, context, goal, message, next)
      def fromLogic[A](result: Either[LogicError, A]): Either[Problem, A] =
        result.left.map(error => problem(scope, line, error, Some(context.render(scope, goal))))
      def fromTactic[A](result: Either[TacticError, A]): Either[Problem, A] =
        result.left.map(error => here(error.render(scope.show), Some(Remedy.of(scope, error).message)))
      def named(names: Vector[String]): Either[Problem, Vector[Kernel.Thm]] =
        names.foldLeft(Right(Vector.empty): Either[Problem, Vector[Kernel.Thm]]) { (acc, name) =>
          acc.flatMap(done => lookup(line, context, goal, name).map(done :+ _))
        }
      def checked(theorem: Kernel.Thm, notes: Vector[String] = Vector.empty): Either[Problem, (Kernel.Thm, Vector[String])] = {
        val extra = theorem.hypotheses.filterNot(context.hypotheses.contains)
        if (theorem.conclusion != goal) Left(here(s"the method proved ${scope.show(theorem.conclusion)}, which is not the goal"))
        else if (extra.nonEmpty)
          Left(here(s"the method's theorem rests on ${extra.map(scope.show).mkString(", ")}, which this proof does not hold"))
        else Right((theorem, notes))
      }

      method match {
        case Method.Auto(from) =>
          for {
            supplied <- named(from)
            implication <- fromLogic(supplied.foldRight(Right(goal): Either[LogicError, Term])((f, acc) => acc.flatMap(logic.mkImp(f.conclusion, _))))
            settled <- fromTactic(prove(implication))
            detached <- fromLogic(supplied.foldLeft(Right(settled.theorem): Either[LogicError, Kernel.Thm])((acc, f) => acc.flatMap(rules.mp(_, f))))
            notes = settled match {
              case Prove.Outcome.CutShort(_, search, depth) => Vector(Cost.cutShortCaveat(search, depth))
              case Prove.Outcome.Settled(_) => Vector.empty
            }
            result <- checked(detached, notes)
          } yield result

        case Method.Ring =>
          fromLogic(prove.ring.prove(goal)).flatMap(checked(_))

        case Method.Linarith(from) =>
          named(from).flatMap(supplied => fromLogic(linearly(supplied, goal))).flatMap(checked(_))

        case Method.Arith(from) =>
          named(from).flatMap(supplied => fromLogic(arithmetic(supplied, goal))).flatMap(checked(_))

        case Method.Rewrite(names) =>
          for {
            equations <- named(names)
            moved <- rewriting(names, equations, goal).left.map { case (message, next) => here(message, next) }
            result <-
              if (closes(moved._2)) fromLogic(closing(moved._1, moved._2)).flatMap(checked(_))
              else Left(here(s"rewriting with ${names.mkString(", ")} leaves ${scope.show(moved._2)}",
                Some("`rewrite ... then auto` hands what is left to the tactic surface")))
          } yield result

        case Method.Exact(name) =>
          named(Vector(name)).flatMap { supplied =>
            val theorem = supplied.head
            if (theorem.conclusion == goal) checked(theorem)
            else fromLogic(rules.specTo(theorem, goal)).flatMap(checked(_))
          }

        case Method.Apply(name) =>
          for {
            supplied <- named(Vector(name))
            application <- fromLogic(Apply.to(logic, supplied.head, goal))
            result <-
              if (application.obligations.nonEmpty)
                Left(here(s"$name leaves ${application.obligations.map(scope.show).mkString(", ")} to prove",
                  Some(s"the step `apply $name` makes each of them a goal")))
              else fromLogic(rules.genAll(application.theorem, application.generalising.toList)).flatMap(checked(_))
          } yield result

        case Method.Then(Method.Rewrite(names), second) =>
          for {
            equations <- named(names)
            moved <- rewriting(names, equations, goal).left.map { case (message, next) => here(message, next) }
            inner <- outcome(line, context, moved._2, second)
            carried <- fromLogic(carrying(moved._1, inner._1))
            result <- checked(carried, inner._2)
          } yield result

        case Method.Then(_, _) =>
          Left(here("only `rewrite` changes a goal and leaves something for `then`; the method before `then` here closes the goal or refuses"))

        case Method.First(alternatives) =>
          val tried = alternatives.map(outcome(line, context, goal, _))
          tried.collectFirst { case Right(settled) => settled } match {
            case Some(settled) => Right(settled)
            case None =>
              val reasons = tried.collect { case Left(p) => p.reason }
              Left(here(s"none of the alternatives settled the goal: ${reasons.mkString("; ")}"))
          }
      }
    }
  }
}

object Elaborate {

  /** The elaborator over the standard chain. */
  lazy val standard: Elaborate = of(Chain.standard)

  /** The elaborator over a chain, with the tactic surface, the arithmetic and the refutation built once. */
  def of(chain: Chain): Elaborate = {
    val prove = Prove.construct(chain)
      .fold(error => throw new IllegalStateException(s"the tactic surface does not build: ${error.message}"), identity)
    val arithmetic = NaturalLinear.of(chain)
      .fold(error => throw new IllegalStateException(s"linear arithmetic over the naturals does not build: ${error.message}"), identity)
    new Elaborate(chain, prove, Library.of(chain), arithmetic, Refutation(Evaluate.over(chain.reals, Model.Numbers)), Reach.library(chain))
  }

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  /** The default induction principle of a type, and its case labels. */
  private val Defaults: Map[Type, (String, Vector[String])] =
    Map(Numbers -> ("NUM_INDUCTION", Vector("zero", "succ")))

  /**
   * What one step of a proof produced: the theorem when there is one, the problems met on the way,
   * and the notes a price depends on.
   *
   * `flatMap` runs the next step only when this one produced a value, and keeps what both met, so a
   * proof read as a `for` stops at its first failure and reports it. A step whose parts are
   * independent, the branches of a split above all, uses [[Checked.all]] instead, which checks every
   * part and keeps every part's problems: recovery is a choice made where the parts are independent,
   * not a default that would check steps against goals nothing produced.
   */
  final case class Checked[+A](value: Option[A], problems: Vector[Problem], notes: Vector[String]) {
    def map[B](f: A => B): Checked[B] = Checked(value.map(f), problems, notes)

    def flatMap[B](f: A => Checked[B]): Checked[B] = value match {
      case Some(a) =>
        val next = f(a)
        Checked(next.value, problems ++ next.problems, notes ++ next.notes)
      case None => Checked(None, problems, notes)
    }

    /** What this met, then `other` in full. */
    def andThen[B](other: Checked[B]): Checked[B] = Checked(other.value, problems ++ other.problems, notes ++ other.notes)

    /** What this met, and no value. */
    def discard: Checked[Nothing] = Checked(None, problems, notes)
  }

  object Checked {
    def ok[A](value: A): Checked[A] = Checked(Some(value), Vector.empty, Vector.empty)
    def failed(problem: Problem): Checked[Nothing] = Checked(None, Vector(problem), Vector.empty)

    /** A problem that does not stop the step: the value carries on and the problem is reported. */
    def warned(problem: Problem): Checked[Unit] = Checked(Some(()), Vector(problem), Vector.empty)

    /** Every part checked, every part's problems kept, and a value only when every part has one. */
    def all[A](parts: Vector[Checked[A]]): Checked[Vector[A]] =
      Checked(
        if (parts.forall(_.value.isDefined)) Some(parts.flatMap(_.value)) else None,
        parts.flatMap(_.problems),
        parts.flatMap(_.notes)
      )
  }

  /** The signature a document is read against, which grows with its definitions. */
  final case class Scope(theory: Theory, notation: Notation, logic: Logic) extends Signature

  /**
   * What the document has proved so far, and the names whose proofs did not check. `holder` is
   * what holds them, as a refusal names it: a document, or the session a cell is checked in.
   */
  private final case class Held(facts: Map[String, Kernel.Thm], failures: Map[String, Int], holder: String = "this document") {
    def has(name: String): Boolean = facts.contains(name) || failures.contains(name)
    /**
     * `name` held as a fact, recorded as a citation of it (`Kernel.cite`, `docs/adr/0047`): a later
     * proof that uses it is priced at the name, as a proof citing a library lemma is, rather than
     * at everything its proof used.
     */
    def proved(name: String, theorem: Kernel.Thm): Held = copy(facts = facts + (name -> Kernel.cite(name, theorem)))
    def failed(name: String, line: Int): Held = copy(failures = failures + (name -> line))
  }

  private object Held {
    val empty: Held = Held(Map.empty, Map.empty)
  }

  /** The fixed variables and the named facts of one point of a proof. */
  private final case class Context(fixed: Vector[FVar], facts: Vector[(String, Kernel.Thm)]) {
    def fix(variable: FVar): Context = copy(fixed = fixed :+ variable)
    def unfix(variable: FVar): Context = copy(fixed = fixed.filterNot(_ == variable))
    def know(name: String, theorem: Kernel.Thm): Context = copy(facts = facts :+ (name -> theorem))
    def types: Map[String, Type] = fixed.map(v => v.name -> v.ty).toMap
    def mentions(name: String): Boolean = facts.exists(_._1 == name)
    def hypotheses: Set[Term] = facts.flatMap(_._2.hypotheses).toSet

    /** The goal as a reader is shown it: what is fixed, what is known, and what is to be proved. */
    def render(scope: Scope, goal: Term): String = {
      val variables = fixed.map(v => s"${v.name} : ${Show.show(v.ty)}")
      val known = facts.map { case (name, theorem) => s"$name : ${scope.show(theorem.conclusion)}" }
      (variables ++ known :+ s"|- ${scope.show(goal)}").mkString("\n")
    }
  }

  private object Context {
    val empty: Context = Context(Vector.empty, Vector.empty)
  }

  /** `pattern` against `ty`, binding the pattern's type variables, or nothing if they differ. */
  private def matchType(pattern: Type, ty: Type, bound: Map[String, Type]): Option[Map[String, Type]] =
    pattern match {
      case TyVar(name) =>
        bound.get(name) match {
          case Some(existing) => if (existing == ty) Some(bound) else None
          case None => Some(bound + (name -> ty))
        }
      case TyApp(operator, arguments) =>
        ty match {
          case TyApp(other, values) if other == operator && arguments.size == values.size =>
            arguments.zip(values).foldLeft(Option(bound)) { case (acc, (p, t)) => acc.flatMap(matchType(p, t, _)) }
          case _ => None
        }
    }

  private def problem(scope: Scope, line: Int, error: LogicError, goal: Option[String]): Problem =
    Problem(line, error.render(scope.show), Some(Remedy.of(scope, error).message), goal)

  /* ------------------------------------------------------------------ the report */

  /** One thing wrong, where it is, what to try, and the goal at that point when there was one. */
  final case class Problem(
    line: Int,
    reason: String,
    next: Option[String],
    goal: Option[String],
    /** Whether the goal that did not settle is false, where a method was asked and refused. */
    refuted: Option[Refuted] = None
  )

  /**
   * What `Refutation` said about a goal a method did not settle.
   *
   * `kind` is one word per outcome of `Refutation` and is the part a program reads: `found` and
   * `solved` say the goal is false at the point the message names; `contradictory` says the proof's
   * facts cannot all hold; `no-counterexample` says the linear question was decided and nothing
   * refutes the goal; `survived` says no sampled point where the facts held refuted it, which is
   * evidence; `never-asked` says no point could be evaluated; `premises-never-held` says the facts
   * failed at every point that answered, so the goal was tested at none; `undecided` says sampling
   * cannot settle a question of this shape.
   */
  final case class Refuted(kind: String, reason: String) {
    def refutes: Boolean = kind == "found" || kind == "solved"
  }

  object Refuted {
    def kind(outcome: Refutation.Outcome): String = outcome match {
      case _: Refutation.Found => "found"
      case _: Refutation.Solved => "solved"
      case _: Refutation.Contradictory => "contradictory"
      case _: Refutation.NoCounterexample => "no-counterexample"
      case _: Refutation.Survived => "survived"
      case _: Refutation.NeverAsked => "never-asked"
      case _: Refutation.PremisesNeverHeld => "premises-never-held"
      case _: Refutation.Undecided => "undecided"
    }
  }

  /** What a proved theorem rests on and what it cost. See `Elaborate.price`. */
  final case class Price(
    axioms: Vector[String],
    facts: Vector[String],
    document: Vector[String],
    inferences: Int,
    notes: Vector[String],
    imported: Vector[String] = Vector.empty
  )

  /**
   * What a document is checked against beyond the chain: the definitions and theorems of the
   * documents it imports, directly or through another import.
   *
   * `definitions` is in the order they are to be made again, which is the order of the documents
   * that made them. `failures` are the declarations of those documents that did not check, kept so
   * a proof citing one is told it failed rather than that the name does not exist, as it is inside
   * one document.
   */
  final case class Imported(
    definitions: Vector[Imported.Definition],
    facts: Map[String, Imported.Fact],
    failures: Map[String, Imported.Failure]
  ) {

    /** Every document this holds anything of, by name. */
    def documents: Vector[String] =
      (definitions.map(_.document) ++ facts.values.map(_.document) ++ failures.values.map(_.document)).distinct.sorted
  }

  object Imported {

    /** A definition of an imported document, and the line of the import that brought it. */
    final case class Definition(document: String, name: String, body: Term, line: Int)

    /** A theorem or a defining equation of an imported document. */
    final case class Fact(document: String, theorem: Kernel.Thm)

    /** A declaration of an imported document that did not check, on its line there. */
    final case class Failure(document: String, line: Int)

    /** Nothing imported. */
    val none: Imported = Imported(Vector.empty, Map.empty, Map.empty)
  }

  enum Kind { case Definition, Theorem }

  enum Status {

    /** The kernel holds the theorem, its conclusion is the claim, and it rests on no hypothesis. */
    case Proved

    /** A definition the kernel accepted. */
    case Defined

    /** The proof was read and some step of it did not check. */
    case Incomplete

    /** The declaration itself could not be read or taken: its claim, its body, or its name. */
    case Refused
  }

  /** One declaration and what became of it. */
  final case class Entry(
    name: String,
    line: Int,
    kind: Kind,
    status: Status,
    statement: String,
    problems: Vector[Problem],
    theorem: Option[Kernel.Thm],
    /** What a proved theorem rests on and what it cost; nothing for anything else. */
    price: Option[Price] = None
  )

  /**
   * A checked document.
   *
   * `imports` holds the problems of the document's imports rather than of any declaration: an
   * import naming no document, a cycle, an imported document that does not check, or two imported
   * definitions of one name.
   */
  final case class Report(entries: Vector[Entry], syntax: Vector[Document.Malformed], imports: Vector[Problem] = Vector.empty) {

    /** Every declaration proved or defined, nothing that failed to read, and every import resolved. */
    def ok: Boolean =
      syntax.isEmpty && imports.isEmpty && entries.forall(e => e.status == Status.Proved || e.status == Status.Defined)

    /** The report as a reader reads it. */
    def render: String = {
      def priced(price: Price): Vector[String] =
        Vector(
          if (price.axioms.isEmpty) "  axioms: none" else s"  axioms: ${price.axioms.mkString(", ")}",
          s"  library facts: ${if (price.facts.isEmpty) "none" else price.facts.mkString(", ")}"
        ) ++
          (if (price.document.nonEmpty) Vector(s"  from this document: ${price.document.mkString(", ")}") else Vector.empty) ++
          (if (price.imported.nonEmpty) Vector(s"  imported: ${price.imported.mkString(", ")}") else Vector.empty) ++
          Vector(s"  inferences: ${price.inferences}") ++
          price.notes.map(note => s"  note: $note")
      def problem(p: Problem): Vector[String] =
        Vector(s"  line ${p.line}: ${p.reason}") ++
          p.next.map(n => s"    try: $n").toVector ++
          p.refuted.map(r => s"    ${if (r.refutes) "false" else "refutation"}: ${r.reason}").toVector ++
          p.goal.toVector.flatMap(_.linesIterator.map(l => s"    $l"))
      def entry(e: Entry): Vector[String] = {
        val word = e.kind match { case Kind.Definition => "define"; case Kind.Theorem => "theorem" }
        val head = s"line ${e.line}: $word ${e.name}: ${e.status.toString.toLowerCase}"
        val body =
          if (e.status == Status.Proved || e.status == Status.Defined) s"  |- ${e.statement}" +: e.price.toVector.flatMap(priced)
          else Vector.empty
        (head +: body) ++ e.problems.flatMap(problem)
      }
      val proved = entries.count(_.status == Status.Proved)
      val defined = entries.count(_.status == Status.Defined)
      val failed = entries.count(e => e.status == Status.Incomplete || e.status == Status.Refused)
      val summary = s"${entries.size} declarations: $proved proved, $defined defined, $failed not proved" +
        (if (syntax.nonEmpty) s", ${syntax.size} syntax errors" else "") +
        (if (imports.nonEmpty) s", ${imports.size} import problems" else "")
      def imported(p: Problem): Vector[String] =
        Vector(s"line ${p.line}: import: ${p.reason}") ++ p.next.map(n => s"  try: $n").toVector
      (syntax.map(e => s"line ${e.line}: syntax: ${e.reason}") ++ imports.flatMap(imported) ++ entries.flatMap(entry) :+ summary)
        .mkString("\n")
    }

    /**
     * The report as structured data, for a program reading it rather than a person.
     *
     * A field with nothing in it is left out rather than written empty, so a reader asks whether a
     * key is present, which is the same question for every optional field here.
     */
    def json: String = {
      def string(text: String): String =
        "\"" + text.flatMap {
          case '"' => "\\\""
          case '\\' => "\\\\"
          case '\n' => "\\n"
          case '\r' => "\\r"
          case '\t' => "\\t"
          case c if c < ' ' => f"\\u${c.toInt}%04x"
          case c => c.toString
        } + "\""
      def strings(values: Vector[String]): String = values.map(string).mkString("[", ",", "]")
      def obj(fields: (String, Option[String])*): String =
        fields.collect { case (key, Some(value)) => s"${string(key)}:$value" }.mkString("{", ",", "}")
      def refuted(r: Refuted): String = obj("kind" -> Some(string(r.kind)), "message" -> Some(string(r.reason)))
      def problem(p: Problem): String =
        obj("line" -> Some(p.line.toString), "message" -> Some(string(p.reason)), "next" -> p.next.map(string),
          "goal" -> p.goal.map(string), "refutation" -> p.refuted.map(refuted))
      def price(p: Price): String =
        obj("axioms" -> Some(strings(p.axioms)), "facts" -> Some(strings(p.facts)), "document" -> Some(strings(p.document)),
          "inferences" -> Some(p.inferences.toString), "notes" -> Some(strings(p.notes)),
          "imported" -> Some(p.imported).filter(_.nonEmpty).map(strings))
      def entry(e: Entry): String =
        obj("name" -> Some(string(e.name)), "line" -> Some(e.line.toString), "kind" -> Some(string(e.kind.toString.toLowerCase)),
          "status" -> Some(string(e.status.toString.toLowerCase)), "statement" -> Some(string(e.statement)),
          "price" -> e.price.map(price), "problems" -> Some(e.problems.map(problem).mkString("[", ",", "]")))
      val errors = syntax.map(e => obj("line" -> Some(e.line.toString), "message" -> Some(string(e.reason))))
      obj("ok" -> Some(ok.toString), "declarations" -> Some(entries.map(entry).mkString("[", ",", "]")),
        "syntax" -> Some(errors.mkString("[", ",", "]")),
        "imports" -> Some(imports).filter(_.nonEmpty).map(_.map(problem).mkString("[", ",", "]")))
    }
  }
}
