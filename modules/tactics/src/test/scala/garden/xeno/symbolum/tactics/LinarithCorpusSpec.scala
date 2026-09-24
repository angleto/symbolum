package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * How much of another prover's linear arithmetic corpus this one proves.
 *
 * Track L of `docs/evaluation.md`, and the same arrangement as track R one file over: the corpus is
 * `third-party/mathlib/MathlibTest/Tactic/Linarith/Basic.lean`, frozen at the commit its notice
 * names and byte-identical to upstream, and nothing in it is selected by hand. Every count below is
 * produced by the code here, and the last test asserts the document repeats them.
 *
 * == What is counted as a question put to LINARITH ==
 *
 * A declaration upstream closed with exactly `linarith` and nothing else. `nlinarith`, `polyrith`,
 * `linarith [h]` with extra terms, and `linarith` after a preprocessing step are different
 * questions: the first two are different tactics, and the others hand `linarith` a goal or a
 * context this system was never given.
 *
 * == The buckets, and which of them is a finding ==
 *
 *  - **unreadable**: the declaration does not reach a statement of this theory. A character
 *    [[LeanSyntax]] does not lex, `¬` and a decimal point among them; a hypothesis whose type is
 *    not a comparison it reads, such as `Set ℕ` or `Nat.prime 7`; a type ascription that could be a
 *    coercion. `⁻¹` was here until the reader learned it on 2026-09-09. It says nothing about the
 *    prover; it is the width of the reader, which is deliberately narrow. An unreadable hypothesis
 *    makes its whole declaration unreadable rather than being dropped, which is what keeps a limit
 *    of the reader from being counted as a failure of the prover.
 *  - **another theory's**: the declaration is about `ℕ` or `ℤ`. This is the bucket that matters
 *    most for honesty, and it is not a reader limitation. Over the integers `x < y` gives
 *    `x + 1 <= y`, which is false over the reals, so reading such a goal as a goal about the reals
 *    would be reading a different statement. The theory here has no naturals, so those declarations
 *    are not put to it at all.
 *  - **outside the fragment**: read, and refused by [[Translate]] by name: a fractional literal, an
 *    exponent it will not expand, or a function the theory has no constant for. Division was the
 *    whole of this bucket until 2026-09-09, when [[Translate]] learned that reading `x / y` asks
 *    for nothing and only cancelling it does; those goals are attempted now, and what refuses the
 *    ones that stay refused names the procedure rather than the reader.
 *  - **not linear**: read, said, attempted, refused, and containing an atom that is not a
 *    variable, such as a product of two unknowns. LINARITH decides the linear fragment and reaches
 *    past it only by multiplying its facts, in pairs and then those pairs by the facts again, so a
 *    refusal here is a shape it does not claim rather than a failure. Attempted rather than assumed
 *    since 2026-09-09, because those products decide some of what used to be in here by
 *    construction.
 *  - **proved**, and **linear and unproved**. The last must be empty, and it is the only assertion
 *    here. A member of it would be a goal this system can state, is linear, and cannot prove, while
 *    another prover's test suite says it is true: that is a finding about LINARITH.
 */
class LinarithCorpusSpec extends AnyFlatSpec with Matchers {

  private val CorpusFile: String =
    "third-party/mathlib/MathlibTest/Tactic/Linarith/Basic.lean"
  private val NoticeFile: String = "third-party/mathlib/README.md"

  private enum Outcome:
    case Proved, Unreadable, ForeignType, Outside, NotLinear, Unproved

  /** The types whose statements are not statements about an ordered field. */
  private val Discrete: Set[String] = Set("ℕ", "ℤ", "Nat", "Int")

  private def read(relative: String): String =
    LeanCorpus.read(relative).getOrElse(fail(s"cannot find $relative"))

  private val reals = Real.standard
  private val linarith = Linarith.standard
  private val realType: Type = TyApp(Real.TypeName, Nil)

  private val corpus: Vector[LeanCorpus.Declaration] =
    LeanCorpus.declarations(read(CorpusFile))

  private val goals: Vector[LeanCorpus.Declaration] =
    corpus.filter(declaration => LeanCorpus.tactic(declaration) == "linarith")

  /* ------------------------------------------------------- reading a declaration */

  /** What a binder group says: a hypothesis, some variables at a type, or nothing usable. */
  private enum Binder:
    case Assumption(relation: LeanSyntax.Relation)
    case Variables(names: Vector[String], typeName: String)
    case Unusable(text: String)
    case Ignored

  /**
   * Read one binder group.
   *
   * `[Field K]` and its kind are ignored: an instance says which structure the statement is about
   * and carries no premise about the values. `(h : 0 < x)` is a hypothesis. `(x y : ℚ)` declares
   * variables, and the type name is kept because it is what decides whether the declaration is
   * about this theory at all.
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

          LeanSyntax.relation(rest) match {
            case Right(relation) => Binder.Assumption(relation)
            case Left(_) =>
              // A type is one token in these files and a hypothesis is not, so a group whose type
              // does not read as a relation and is not one token is a hypothesis this reader
              // cannot read. Dropping it would make the declaration harder rather than easier and
              // would then be counted as something the prover failed at, which is the one way this
              // measurement could lie in its own favour by being unfair to itself.
              if (rest.split("\\s+").length == 1) Binder.Variables(names, rest)
              else Binder.Unusable(rest)
          }
      }
  }

  /** A relation as a term of this theory, or the reason it cannot be one. */
  private def term(relation: LeanSyntax.Relation): Either[String, Term] = {
    val name = relation.comparison match {
      case LeanSyntax.Comparison.Less => Real.Order
      case LeanSyntax.Comparison.LessEqual => Real.NonStrictOrder
      case LeanSyntax.Comparison.Equal => ""
    }

    for {
      left <- Translate.toTerm(reals, relation.left).left.map(_.message)
      right <- Translate.toTerm(reals, relation.right).left.map(_.message)
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
    goal: LeanSyntax.Relation
  ): Either[String, Term] =
    term(goal).flatMap(proposition(hypotheses, _))

  private def proposition(
    hypotheses: Vector[LeanSyntax.Relation],
    conclusion: Term
  ): Either[String, Term] =
    for {
      premises <- hypotheses.foldLeft(Right(Vector.empty): Either[String, Vector[Term]]) {
        (acc, relation) =>
          for {
            done <- acc
            next <- term(relation)
          } yield done :+ next
      }
      result <- premises.toList match {
        case Nil => Right(conclusion)
        case first :: rest =>
          for {
            antecedent <- rest.foldLeft(Right(first): Either[String, Term]) { (acc, next) =>
              acc.flatMap(reals.logic.mkConj(_, next).left.map(_.message))
            }
            implication <- reals.logic.mkImp(antecedent, conclusion).left.map(_.message)
          } yield implication
      }
    } yield result

  /**
   * Whether every atom the linear forms rest on is a variable.
   *
   * A product of two unknowns is one atom to the search, and no combination of hypotheses about
   * `x` and `y` reaches an atom `x * y`. Computed from the forms rather than read off a refusal,
   * which is what keeps the assertion below meaningful: otherwise every goal the procedure cannot
   * do would be excused as non-linear by the fact that it could not do it.
   *
   * It excuses a refusal and no longer decides whether to ask. LINARITH multiplies its hypotheses
   * in pairs when the linear search fails, so a non-variable atom no longer puts a goal outside the
   * procedure by construction, and a bucket that skipped those goals would have hidden every one it
   * had learned to prove.
   */
  private def linear(hypotheses: Vector[Term], conclusion: Term): Boolean = {
    def atoms(form: LinearForm): Set[Term] = form.atoms

    val fromHypotheses = hypotheses.flatMap { hypothesis =>
      LinearFact.of(reals, hypothesis).map(fact => atoms(fact.form)).getOrElse(Set.empty)
    }.toSet

    val fromGoal =
      LinearForm.goal(reals, conclusion).map { case (form, _) => atoms(form) }.getOrElse(Set.empty)

    (fromHypotheses ++ fromGoal).forall {
      case _: FVar => true
      case _ => false
    }
  }

  /* ------------------------------------------------------------------ the measurement */

  private lazy val outcomes: Vector[(LeanCorpus.Declaration, Outcome, String)] =
    goals.map { declaration =>
      val result = LeanCorpus.split(declaration) match {
        case None => (Outcome.Unreadable, "no goal separator")

        case Some((groups, goalText)) =>
          val binders = groups.map(binder)
          val foreign = binders.collect {
            case Binder.Variables(_, typeName) if Discrete.contains(typeName) => typeName
          }
          val unusable = binders.collect { case Binder.Unusable(text) => text }

          if (foreign.nonEmpty) (Outcome.ForeignType, foreign.distinct.mkString(", "))
          else if (unusable.nonEmpty) (Outcome.Unreadable, s"a hypothesis: ${unusable.head}")
          else
            // `False` as a goal is read, and it is not an exception to the syntax-only rule: it is
            // the same falsity the logic already has, and asking whether the premises imply it is
            // asking whether they can all hold, which is the half of the procedure that has
            // nothing to do with a goal. Several declarations in this file are written that way.
            if (goalText.trim == "False") {
              val hypotheses = binders.collect { case Binder.Assumption(relation) => relation }
              val sides = hypotheses.flatMap(relation => Vector(relation.left, relation.right))

              if (sides.exists(!Translate.isTranslatable(reals, _)))
                (Outcome.Outside, "a hypothesis cannot be said")
              else
                proposition(hypotheses, reals.logic.falsity) match {
                  case Left(why) => (Outcome.Unreadable, why)
                  case Right(statement) =>
                    val premises = hypotheses.flatMap(term(_).toOption)
                    if (!linear(premises, reals.logic.falsity))
                      (Outcome.NotLinear, "an atom is not a variable")
                    else
                      linarith.prove(statement) match {
                        case Right(_) => (Outcome.Proved, "")
                        case Left(error) => (Outcome.Unproved, error.message)
                      }
                }
            } else
            LeanSyntax.relation(goalText) match {
              case Left(why) => (Outcome.Unreadable, why)

              case Right(goal) =>
                val hypotheses = binders.collect { case Binder.Assumption(relation) => relation }
                val sides =
                  (hypotheses :+ goal).flatMap(relation => Vector(relation.left, relation.right))
                val unsayable = sides.filterNot(Translate.isTranslatable(reals, _))

                if (unsayable.nonEmpty)
                  (Outcome.Outside, unsayable.map(_.toString).distinct.mkString(", "))
                else
                  proposition(hypotheses, goal) match {
                    case Left(why) => (Outcome.Unreadable, why)

                    case Right(statement) =>
                      val premises = hypotheses.flatMap(term(_).toOption)
                      val conclusion = term(goal).toOption.getOrElse(statement)

                      // Asked first and excused afterwards, since 2026-09-09. Deciding that a
                      // goal is non-linear and not attempting it was right while a non-variable
                      // atom put it outside the procedure by construction; LINARITH multiplies its
                      // hypotheses now, so some of those goals are decided and skipping them would
                      // have hidden every one. `linear` still does the excusing, and it is computed
                      // from the forms rather than read off the refusal, so a goal the procedure
                      // merely could not do is not excused by its having failed.
                      linarith.prove(statement) match {
                        case Right(_) => (Outcome.Proved, "")
                        case Left(error) =>
                          if (!linear(premises, conclusion))
                            (Outcome.NotLinear, "an atom is not a variable")
                          else (Outcome.Unproved, error.message)
                      }
                  }
            }
      }

      (declaration, result._1, result._2)
    }

  private def count(outcome: Outcome): Int = outcomes.count(_._2 == outcome)

  /* ------------------------------------------------------------------------- the tests */

  "The vendored corpus" should "be the file its notice describes" in {
    val hash = LeanCorpus.hashOf(CorpusFile).getOrElse(fail(s"cannot find $CorpusFile"))

    withClue(s"$CorpusFile now hashes to $hash; $NoticeFile does not say so\n") {
      read(NoticeFile) should include(hash)
    }
  }

  "LINARITH against Mathlib's linarith corpus" should "leave nothing linear unproved" in {
    info(
      s"${corpus.size} declarations, ${goals.size} closed by exactly linarith: " +
        s"proved ${count(Outcome.Proved)}, another theory's ${count(Outcome.ForeignType)}, " +
        s"unreadable ${count(Outcome.Unreadable)}, outside the fragment ${count(Outcome.Outside)}, " +
        s"not linear ${count(Outcome.NotLinear)}, unproved ${count(Outcome.Unproved)}"
    )

    // Where the excluded ones went, by line, because the size of a bucket is a claim about this
    // corpus that a reader should be able to check against the file rather than take on trust.
    Outcome.values.filterNot(_ == Outcome.Proved).foreach { bucket =>
      val members = outcomes.collect { case (declaration, `bucket`, why) => s"${declaration.line} ($why)" }
      if (members.nonEmpty) info(s"$bucket: ${members.mkString(", ")}")
    }

    val unproved = outcomes.collect { case (declaration, Outcome.Unproved, why) => (declaration.line, why) }
    val unexplained = unproved.filterNot { case (line, _) => KnownUnproved.contains(line) }
    withClue(
      "stated, linear, and not proved, and not on the written exception list:\n" +
        unexplained.map { case (line, why) => s"line $line: $why" }.mkString("\n") + "\n"
    ) {
      unexplained shouldBe empty
    }

    val fixed = KnownUnproved -- unproved.map(_._1).toSet
    withClue(s"on the exception list and no longer failing, so remove them: $fixed\n") {
      fixed shouldBe empty
    }
  }

  /**
   * The written exception list, which is where a failing case goes when the prover is not fixed
   * instead, and it is empty.
   *
   * It is worth keeping empty rather than deleting, because what it records is not the entries but
   * the discipline: the suite fails on an entry that has stopped failing as well as on one that has
   * not, so a limit that goes away takes its own excuse with it.
   *
   * Both times this list emptied itself, on 2026-09-09. `ε/3 + ε/3 + ε/3 = ε` left when LINARITH's
   * linear form gained rational coefficients. Lines 97, 99, 101 and 105 arrived in the same change
   * and left an hour later: they were `0 < x/(-1)`, `0 < x/(-2)`, `0 < x/(-4/5)` and `0 < x/(2/3)`,
   * the search found every certificate, and what refused was the ring step, because RING read
   * `inv <numeral>` and nothing else as a denominator. `Coefficient.inverseOfUnit` is what changed:
   * a factor of one cannot be zero, so the side condition is discharged by the arithmetic rather
   * than by the order.
   *
   * The second of those is the one worth remembering. That limit of RING was invisible until this
   * reader got wide enough to hand it those goals, so the corpus found a defect in a tactic it was
   * not measuring.
   */
  private val KnownUnproved: Set[Int] = Set.empty

  it should "reach the corpus rather than bounce off it" in {
    // The bucket above is empty on a reader that reads nothing, which is how a must-be-empty
    // assertion goes quietly wrong. This is the guard, and it is a fixed floor rather than a
    // fraction of the corpus as in track R: most of this file is about the naturals or the
    // integers, so the share this theory can state is small and the fraction would say little.
    count(Outcome.Proved) should be >= 10
  }

  "The reader" should "refuse what it cannot read and turn round what it can" in {
    LeanSyntax.relation("a < b") should matchPattern {
      case Right(LeanSyntax.Relation(LeanSyntax.Comparison.Less, _, _)) =>
    }
    LeanSyntax.relation("b > a") should matchPattern {
      case Right(LeanSyntax.Relation(LeanSyntax.Comparison.Less, _, _)) =>
    }
    LeanSyntax.relation("a ≤ b") should matchPattern {
      case Right(LeanSyntax.Relation(LeanSyntax.Comparison.LessEqual, _, _)) =>
    }
    LeanSyntax.relation("a ≠ b").isLeft shouldBe true
    LeanSyntax.relation("a < b → c < d").isLeft shouldBe true
  }

  "The counts in the evaluation document" should "be the ones this suite measures" in {
    val evaluation = read("docs/evaluation.md")
    val claims = Vector(
      s"| declarations in the file | ${corpus.size} |",
      s"| closed by exactly `linarith` | ${goals.size} |",
      s"| about the naturals or the integers | ${count(Outcome.ForeignType)} |",
      s"| not read here | ${count(Outcome.Unreadable)} |",
      s"| refused as outside the fragment | ${count(Outcome.Outside)} |",
      s"| read, and not linear | ${count(Outcome.NotLinear)} |",
      s"| proved by LINARITH | ${count(Outcome.Proved)} |",
      s"| linear and unproved | ${count(Outcome.Unproved)} |"
    )

    val missing = claims.filterNot(evaluation.contains)
    withClue(s"docs/evaluation.md does not say:\n${missing.mkString("\n")}\n") {
      missing shouldBe empty
    }
  }
}
