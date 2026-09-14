package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * How far into miniF2F this prover reaches, counted rather than estimated.
 *
 * Track M of `docs/evaluation.md`, and the reason it exists is a sentence that used to stand in that
 * document without a measurement behind it: *"a run would still produce parse errors, not failed
 * proofs"*. That was written when the theory had no naturals and no arithmetic on them. It is false
 * now, and the way it was found to be false is the reason this file is a corpus and not five
 * examples: five statements typed in by hand said three proved and two unsettled, and a hand-typed
 * set is one whoever typed it chose, which is the failure this repository has already named once.
 *
 * So the corpus is `third-party/minif2f/lean/src/test.lean`, frozen at the commit its notice names
 * and byte-identical to upstream, and nothing in it is selected by hand. All 244 declarations are
 * put to the whole tactic surface through [[Cost]], which is what "reach" means: not what one
 * procedure does, but what the system as assembled makes of a statement somebody else wrote.
 *
 * == The buckets, and the two that are not failures ==
 *
 * `Unreadable` and `Outside` are the ones a reader must not add to the failures. The first is a
 * statement whose *syntax* this reader does not take, and the second is one it read and the theory
 * has no constant for: a square root, a factorial, a sum over a `Finset`. Neither is a proof that
 * was attempted and missed, and merging either into `Unsettled` would turn "I could not ask" into
 * "I asked and could not", which is the one way this measurement could mislead. It is the same
 * discipline `Refutation` keeps seven answers for.
 *
 * `ForeignType` is the third of them and it is the interesting one, because it is the bucket that
 * should shrink. It did, on 2026-09-11: `Translate` gained a target type, so a statement whose
 * variables are naturals is read through `real_of_num` and put to the same procedures as any other.
 * What is left in the bucket is `ℤ`, `ℚ` and `ℂ`, which wait on ADR 0007, and the statements
 * whose binders name a type this reader has no term language for at all.
 *
 * == Which types are read, and why the default is to refuse ==
 *
 * [[Known]] is the whole list, and a binder naming anything else is `ForeignType`. That direction
 * is deliberate and it is a repair rather than a restatement: until 2026-09-11 the list was of
 * types to **reject** and everything not on it was read as a real, so `(x : nnreal)` and
 * `(x y n : ℕ+)` were put to the prover as statements about arbitrary reals. None of them was proved,
 * so nothing wrong was ever certified, and that was luck rather than design: the non-negativity in
 * the first and the positivity in the second are hypotheses the source states by choosing a type,
 * and dropping them makes a different claim. A list of what is understood cannot fail that way.
 *
 * == One target per statement, and the mixture refused ==
 *
 * A Lean statement's arithmetic is elaborated at a type, and this reader has no elaborator: what it
 * has is the binders. A statement whose variable binders are all `ℝ` is read at the reals and one
 * whose binders are all `ℕ` at the naturals; one with both is refused, because deciding which of
 * `x + n` the source meant is the elaboration this reader cannot do, and a guess would be the
 * silent semantic step `LeanSyntax` already refuses to take for `↑`.
 *
 * == What it deliberately does not do ==
 *
 * **It does not select.** Every declaration in the file is counted, including the ones this system
 * has no hope of, and the assertions below are about the shape of the answer rather than about a
 * score: that nothing lands in two buckets, that the buckets sum to the file, and that the
 * proved set is not empty, which is the claim the stale sentence denied.
 *
 * **It does not read a Lean proof.** miniF2F statements are followed by `begin … end` at column
 * zero, so `LeanCorpus.declarations` hands back a statement with an empty proof, and there is
 * nothing here to compare a tactic against. What is being measured is a statement, and the number
 * to compare against the literature is a pass rate on the same statements, not on the same proofs.
 */
final class ReachSpec extends AnyFlatSpec with Matchers {

  private val CorpusFile: String = "third-party/minif2f/lean/src/test.lean"
  private val NoticeFile: String = "third-party/minif2f/README.md"

  /**
   * What became of one statement.
   *
   * The five `Cost` outcomes are carried through unchanged rather than folded into "proved" and
   * "not", because a conditional theorem and a claim nothing is known about are the two things this
   * repository is most careful never to merge.
   */
  private enum Outcome:
    case Proved, Conditional, Holds, Fails, Unsettled, Unreadable, Outside, ForeignType

  /**
   * The types a variable binder can name that this reader has a term language for.
   *
   * An allowlist rather than a list of refusals, and the class comment argues the direction. The
   * value is what a variable of that type becomes: a real stays a real, a natural is embedded by
   * `real_of_num` and the statement that comes out is about its image.
   */
  private val Known: Map[String, Translate.Target] = Map(
    "ℝ" -> Translate.Target.Reals,
    "real" -> Translate.Target.Reals,
    "ℕ" -> Translate.Target.Naturals,
    "nat" -> Translate.Target.Naturals
  )

  private def read(relative: String): String =
    LeanCorpus.read(relative).getOrElse(fail(s"cannot find $relative"))

  /**
   * The whole chain, because a statement about the naturals has to be sayable before it is put.
   *
   * `Real.standard` was here until 2026-09-11 and it is a signature with no `num` in it: a term
   * carrying `real_of_num` could not be built against it, and a quantifier at `num` could not be
   * either. `Chain.widest` declares both types and everything the chain proved about them, which is
   * what `Prove.over` and `Cost.over` are for.
   */
  private val chain: Chain = Chain.standard
  private val reals: Signature = chain.widest
  private val cost: Cost = Cost.construct(chain).fold(error => fail(error.message), identity)
  private val realType: Type = TyApp(Real.TypeName, Nil)

  /**
   * The connectives over the theory that has `real`, which is not the ones the signature carries.
   *
   * `Real.standard` stays over `Logic.standard` on purpose, so that a development about the reals
   * is not asked to believe the choice operator; `Logic.standard` has never heard of the type
   * operator `real`, and building `!x:real. …` needs a universal quantifier **at that type**, which
   * a theory refuses to hand out for a type operator it does not have. `Divisibility` documents the
   * same refusal, in the same words, for the same reason.
   *
   * Measured rather than reasoned about: with the signature's own logic here, every statement with
   * a variable in it came back "no type operator named real in this theory" and the only three that
   * were proved were the three with no variables at all. A reader of that run would have concluded
   * the prover reaches closed arithmetic and nothing else, which is not what it does.
   *
   * It is the chain's own since 2026-09-11, for the second half of the same reason: closing a
   * statement about naturals over its free variables needs the universal at `num` too.
   */
  private val logic: Logic = chain.logic

  /**
   * The benchmark's problems, which are the `theorem` declarations and not everything in the file.
   *
   * The file also holds one `lemma`, `sum_pairs`, which its author wrote as a step towards one of
   * the problems rather than as a problem. Filtering by keyword is a rule stated in advance and
   * applied by machine, which is what keeps this from being a hand selection: the alternative,
   * naming `sum_pairs` and skipping it, is the shape that lets a later reader skip a second one.
   * The count that comes out is 244, which is the number the paper reports for this split.
   */
  private val corpus: Vector[LeanCorpus.Declaration] =
    LeanCorpus.declarations(read(CorpusFile)).filter(_.keyword == "theorem")

  /* ------------------------------------------------------- reading a declaration */

  private enum Binder:
    case Assumptions(relations: Vector[LeanSyntax.Relation])
    case Variables(names: Vector[String], typeName: String)
    case Unusable(text: String)
    case Ignored

  /**
   * Read one binder group.
   *
   * The one thing done here that the linear corpus does not do is split a conjunction: miniF2F
   * writes `(h₀ : 0 < b ∧ 0 < h ∧ 0 < v)` where Mathlib's own test file writes three groups, and a
   * conjunction in a *hypothesis* position is exactly what Lean's `h₀.1` and `h₀.2` take it apart
   * into. That is structural and not a reinterpretation: assuming `A ∧ B` and assuming `A` and `B`
   * are the same assumption. A conjunction in the **goal** is not split, because there it would be
   * a claim about what proving means rather than about what was assumed.
   */
  private def binder(group: String): Binder = {
    val body = group.substring(1, group.length - 1).trim

    if (group.startsWith("[")) Binder.Ignored
    else
      body.indexOf(':') match {
        case -1 => Binder.Ignored
        case at =>
          val names = body.substring(0, at).trim.split("\\s+").toVector.filter(_.nonEmpty)
          val rest = body.substring(at + 1).trim
          val conjuncts = rest.split("∧").toVector.map(_.trim).filter(_.nonEmpty)
          val read = conjuncts.map(LeanSyntax.relation)

          if (read.nonEmpty && read.forall(_.isRight))
            Binder.Assumptions(read.map(_.toOption.get))
          else if (rest.split("\\s+").length == 1) Binder.Variables(names, rest)
          else Binder.Unusable(rest)
      }
  }

  /**
   * A relation as a term of this theory, or the reason it cannot be one.
   *
   * The comparison is the reals' whichever target was asked for, and under
   * [[Translate.Target.Naturals]] both sides are images under `real_of_num`. That is faithful
   * because the embedding is an order embedding as well as a ring one: `m <= n` and
   * `real_of_num m <= real_of_num n` hold together, so the statement put to the procedures is the
   * statement the source wrote. `Peano` derives the ring half (`NUM_REAL_ADD`, `NUM_REAL_MUL`); the
   * order half is true of the definition and is not yet a theorem here, which is a gap in what can
   * be **proved about** the translation rather than in what it means.
   */
  private def term(relation: LeanSyntax.Relation, target: Translate.Target): Either[String, Term] = {
    val name = relation.comparison match {
      case LeanSyntax.Comparison.Less => Real.Order
      case LeanSyntax.Comparison.LessEqual => Real.NonStrictOrder
      case LeanSyntax.Comparison.Equal => ""
    }

    for {
      left <- Translate.toTerm(reals, relation.left, target).left.map(_.message)
      right <- Translate.toTerm(reals, relation.right, target).left.map(_.message)
      result <-
        if (name.isEmpty) Term.eq(left, right).left.map(_.message)
        else
          for {
            constant <- reals.theory
              .constant(name, Type.fun(realType, Type.fun(realType, Type.Bool)))
              .left
              .map(_.message)
            applied <- Term.appAll(constant, List(left, right)).left.map(_.message)
          } yield applied
    } yield result
  }

  /** The whole declaration as one proposition: the hypotheses conjoined, implying the goal. */
  private def proposition(
    hypotheses: Vector[LeanSyntax.Relation],
    goal: LeanSyntax.Relation,
    target: Translate.Target
  ): Either[String, Term] =
    for {
      conclusion <- term(goal, target)
      premises <- hypotheses.foldLeft(Right(Vector.empty): Either[String, Vector[Term]]) {
        (acc, relation) => for { done <- acc; next <- term(relation, target) } yield done :+ next
      }
      result <- premises.toList match {
        case Nil => Right(conclusion)
        case first :: rest =>
          for {
            antecedent <- rest.foldLeft(Right(first): Either[String, Term]) { (acc, next) =>
              acc.flatMap(logic.mkConj(_, next).left.map(_.message))
            }
            implication <- logic.mkImp(antecedent, conclusion).left.map(_.message)
          } yield implication
      }
    } yield result

  /**
   * The claim closed over its free variables, which is what a statement with binders means.
   *
   * miniF2F declares its variables and states an open formula; `Cost` is asked a closed one, so
   * every free variable left is bound here. Skipping this would put a universally quantified
   * statement to a prover as if it were about particular unknowns, which is a different claim.
   */
  private def closed(statement: Term): Either[String, Term] =
    Term.freeVariables(statement).toVector.sortBy(_.name).foldRight(Right(statement): Either[String, Term]) {
      (variable, acc) => acc.flatMap(inner => logic.mkForall(variable, inner).left.map(_.message))
    }

  /* ------------------------------------------------------------------ the measurement */

  private lazy val outcomes: Vector[(LeanCorpus.Declaration, Outcome, String)] =
    corpus.map { declaration =>
      val started = System.nanoTime()
      val result = LeanCorpus.split(declaration) match {
        case None => (Outcome.Unreadable, "no goal separator")

        case Some((groups, goalText)) =>
          val binders = groups.map(binder)
          val declared = binders.collect { case Binder.Variables(_, typeName) => typeName }.distinct
          val unknown = declared.filterNot(Known.contains)
          val targets = declared.flatMap(Known.get).distinct
          val unusable = binders.collect { case Binder.Unusable(text) => text }

          if (unknown.nonEmpty) (Outcome.ForeignType, unknown.mkString(", "))
          else if (targets.size > 1)
            (Outcome.ForeignType, s"${declared.mkString(" and ")} in one statement, which is a coercion")
          else if (unusable.nonEmpty) (Outcome.Unreadable, s"a hypothesis: ${unusable.head}")
          else
            LeanSyntax.relation(goalText.trim.stripSuffix(":=").trim) match {
              case Left(why) => (Outcome.Unreadable, why)

              case Right(goal) =>
                val target = targets.headOption.getOrElse(Translate.Target.Reals)
                val hypotheses = binders.collect { case Binder.Assumptions(relations) => relations }.flatten
                val sides =
                  (hypotheses :+ goal).flatMap(relation => Vector(relation.left, relation.right))
                // The refusal and not only the expression, because the refusals now group: a
                // dozen statements are outside for the one reason that the naturals' subtraction
                // is not the reals', and a histogram keyed on the expression would show a dozen
                // rows of one and hide that.
                val unsayable = sides.flatMap(side =>
                  Translate.toTerm(reals, side, target).left.toOption.map(why => s"${why.message} ($side)")
                )

                if (unsayable.nonEmpty) (Outcome.Outside, unsayable.distinct.take(2).mkString("; "))
                else
                  proposition(hypotheses, goal, target).flatMap(closed) match {
                    case Left(why) => (Outcome.Unreadable, why)
                    case Right(statement) =>
                      cost.of(statement) match {
                        case Left(error) => (Outcome.Unsettled, error.message)
                        case Right(report) =>
                          val outcome = report.outcome match {
                            case Cost.Outcome.Proved => Outcome.Proved
                            case Cost.Outcome.Conditional => Outcome.Conditional
                            case Cost.Outcome.Holds => Outcome.Holds
                            case Cost.Outcome.Fails => Outcome.Fails
                            case Cost.Outcome.Unsettled => Outcome.Unsettled
                          }
                          (outcome, reals.show(statement))
                      }
                  }
            }
      }

      elapsed = elapsed :+ ((name(declaration), result._1, (System.nanoTime() - started) / 1000000L))
      (declaration, result._1, result._2)
    }

  private var elapsed: Vector[(String, Outcome, Long)] = Vector.empty

  private def count(outcome: Outcome): Int = outcomes.count(_._2 == outcome)

  private def name(declaration: LeanCorpus.Declaration): String =
    declaration.statement.split("\\s+")(1)

  private def named(outcome: Outcome): Vector[String] =
    outcomes.collect { case (declaration, found, _) if found == outcome => name(declaration) }

  /* ------------------------------------------------------------------------- the tests */

  "The vendored corpus" should "be the file its notice describes" in {
    val hash = LeanCorpus.hashOf(CorpusFile).getOrElse(fail(s"cannot find $CorpusFile"))

    withClue(s"$CorpusFile now hashes to $hash; $NoticeFile does not say so\n") {
      read(NoticeFile) should include(hash)
    }
  }

  it should "be the whole benchmark and not a selection" in {
    val whole = LeanCorpus.declarations(read(CorpusFile))

    corpus.size shouldBe 244
    corpus.map(_.keyword).distinct shouldBe Vector("theorem")
    whole.size - corpus.size shouldBe 1 // `sum_pairs`, and the notice says so
  }

  "The reach into miniF2F" should "be counted, and every declaration land in exactly one bucket" taggedAs Corpus in {
    val buckets = Outcome.values.toVector.map(outcome => (outcome, count(outcome)))

    info(
      s"${corpus.size} statements: " +
        buckets.filter(_._2 > 0).map { case (outcome, howMany) => s"$outcome $howMany" }.mkString(", ")
    )

    buckets.map(_._2).sum shouldBe corpus.size
  }

  it should "say what stopped every statement it never attempted, which is the roadmap's denominator" taggedAs Corpus in {
    // Not decoration, and not only the unreadable ones. The card that asked for this measurement
    // asked for a histogram of **blocking features**: for each problem never attempted, what is
    // missing. That is what turns a list of opinions about what to build next into a list with a
    // denominator, and it is the half of this file that is worth more than the proof count.
    //
    // All three not-attempted buckets take part, because they name three different absences: a
    // syntax this reader does not take, a type the tactics have no signature for, and a function
    // the theory has no constant for. Merging them would say "244 minus what we proved" and answer
    // nothing.
    val reasons = outcomes
      .collect {
        case (_, Outcome.Unreadable, why) => s"syntax: ${why.takeWhile(_ != ':')}"
        case (_, Outcome.ForeignType, which) => s"type: $which"
        case (_, Outcome.Outside, what) => s"no constant for: ${what.takeWhile(_ != ',')}"
      }
      .groupBy(identity)
      .toVector
      .map { case (why, held) => (held.size, why) }
      .sortBy(-_._1)

    reasons.take(12).foreach { case (howMany, why) => info(s"$howMany  $why") }

    reasons.map(_._1).sum shouldBe
      count(Outcome.Unreadable) + count(Outcome.ForeignType) + count(Outcome.Outside)
  }

  it should "report what it decided false, which is a claim about somebody else's theorem" taggedAs Corpus in {
    outcomes.collect { case (declaration, Outcome.Fails, what) => info(s"${name(declaration)}  $what") }
    succeed
  }

  it should "report what it could not settle" taggedAs Corpus in {
    outcomes.collect { case (declaration, Outcome.Unsettled, what) => info(s"${name(declaration)}  $what") }
    succeed
  }

  it should "report what it spent the time on" taggedAs Corpus in {
    outcomes // force
    elapsed.sortBy(-_._3).take(10).foreach { case (what, outcome, ms) => info(s"$ms ms  $outcome  $what") }
    succeed
  }

  it should "prove something, which is what the document used to deny" taggedAs Corpus in {
    withClue(
      "docs/evaluation.md said a run would produce parse errors and not failed proofs. " +
        s"It produces both, and this is the set that is neither:\n  ${named(Outcome.Proved).mkString("\n  ")}\n"
    ) {
      count(Outcome.Proved) should be > 0
    }
  }

  it should "keep what could not be asked apart from what was asked and missed" taggedAs Corpus in {
    // The assertion that matters most here, and it is about the arithmetic rather than the prover:
    // a reader who adds `Unreadable` and `Outside` to `Unsettled` gets a failure count that
    // includes every statement this system never attempted. They are counted apart above and the
    // sum below is what a reader may call "attempted".
    val attempted =
      count(Outcome.Proved) + count(Outcome.Conditional) + count(Outcome.Holds) +
        count(Outcome.Fails) + count(Outcome.Unsettled)
    val notAttempted = count(Outcome.Unreadable) + count(Outcome.Outside) + count(Outcome.ForeignType)

    info(s"attempted $attempted, not attempted $notAttempted")
    attempted + notAttempted shouldBe corpus.size
    attempted should be > 0
  }

  it should "say which statements it proved, by name, so the claim can be checked one at a time" taggedAs Corpus in {
    named(Outcome.Proved).foreach(name => info(name))
    named(Outcome.Proved).distinct.size shouldBe named(Outcome.Proved).size
  }
}
