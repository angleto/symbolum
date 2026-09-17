package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Derivations of a relation, and the one question a potential-function lemma has to survive.
 *
 * **What it cost.** One constant and no axiom, asserted against the theory it extends.
 *
 * **What it says.** Each fact against the text `Reaching.Statements` holds, read as a term.
 *
 * **Whether it can be used.** A relation on `num` that takes a number to its predecessor, with
 * every step counted, a derivation built with the introduction rules, and
 * [[Reaching.Potential]] applied to it. That is the whole loop the development exists for, and it
 * is the test that says the statements fit together rather than each being true alone.
 *
 * **Whether the second hypothesis is load-bearing, which is the test this file exists for.** It is,
 * and the card that asked for this development had it the wrong way round: it asked that no rule
 * **raise** the measure, where what the argument needs is that no uncounted rule **lower** it. A
 * theorem does not refuse, so the only form a negative control can take here is the one
 * `PrimesSpec` uses on `NUM_SQUARE_NOT_DOUBLE` — exhibit the instance that makes the weakened
 * statement false. The witness is one uncounted step from one to zero: nothing is counted, the
 * measure falls anyway, and the bound the lemma would give is `1 <= 0`.
 *
 * Without that test the second hypothesis could be dropped, or weakened to the condition the card
 * asked for, and every other assertion in this file would still pass.
 */
class ReachingSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), value => value)

  private def lift[T](result: Either[KernelError, T]): T = force(LogicError.lift(result))

  private val chain = Chain.standard
  private val reaching = chain.reaching
  private val logic = reaching.logic
  private val rules = logic.rules
  private val peano = chain.peano
  private val product = chain.product

  private def fact(name: String): Kernel.Thm = force(reaching.fact(name))

  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val steps: Type = TyApp(Product.TypeName, List(numbers, numbers))

  private def atNumbers(theorem: Kernel.Thm): Kernel.Thm =
    Kernel.instType(Map(Classical.TypeVariable -> numbers), theorem)

  private def term(text: String): Term = force(reaching.term(text))
  private def proposition(text: String): Term = force(reaching.proposition(text))

  /** The rules that do the arithmetic every statement here is stated around. */
  private lazy val projections: Vector[Rewrite.Rule] = Vector(
    force(Rewrite.Rule.of(logic, force(product.fact(Product.FirstOfPair)))),
    force(Rewrite.Rule.of(logic, force(product.fact(Product.SecondOfPair))))
  )

  /** Every constant name occurring in a term, the way `ConcatenationSpec` asks the same question. */
  private def constantsIn(term: Term): Set[String] = term match {
    case Const(name, _) => Set(name)
    case App(operator, argument) => constantsIn(operator) ++ constantsIn(argument)
    case Abs(_, body) => constantsIn(body)
    case _ => Set.empty
  }

  /**
   * What the definition of `REACH` is built from, and nothing else: the constant being defined,
   * equality, four connectives, the two projections of a pair and its constructor, and the two of
   * `num` that a counter needs. Twelve, and the one that carries the argument is `INDUCTIVE`.
   */
  private val DefinitionConstants: Set[String] =
    Set(
      Reaching.Name,
      Inductive.Name,
      "=",
      "\\/",
      "/\\",
      "~",
      "?",
      "PAIR",
      "FST",
      "SND",
      "SUC",
      "ZERO"
    )

  private def reduce(theorem: Kernel.Thm): Kernel.Thm = {
    val beta = force(Conv.betaNormalise(theorem.conclusion))
    val opened = lift(Kernel.eqMp(beta, theorem))
    force(Rewrite.inTheorem(projections, opened))
  }

  /* --------------------------------------------------------------- what it cost */

  "Reachability" should "be defined rather than assumed" in {
    val below = chain.inductive.theory

    reaching.theory.axioms shouldBe below.axioms
    (reaching.theory.constants.keySet -- below.constants.keySet) shouldBe Set(Reaching.Name)
  }

  it should "carry every fact without a hypothesis left standing" in {
    Reaching.Statements.foreach { case (name, _) =>
      withClue(s"$name: ")(fact(name).hypotheses shouldBe empty)
    }
  }

  it should "say what `Reaching.Statements` says, read as a term" in {
    Reaching.Statements.foreach { case (name, text) =>
      withClue(s"$name: ")(fact(name).conclusion shouldBe proposition(text))
    }
  }

  it should "need no recursion on `num`, which is what defining the closure bought" in {
    // Read off the definition rather than off the proof. A derivation is a finite sequence, and a
    // development that had to walk one would recurse on its length; this one quantifies over an
    // index instead, so the only thing it is built from is `INDUCTIVE`.
    //
    // The question is asked of the definition's CONSTANTS and not of its printed text, and the
    // second half of this test used to ask it of the text: it compared against
    // `Recursion.getClass.getSimpleName`, which is the Scala module's class name `Recursion$`, and
    // no term this printer produces carries a `$` — zero of the 462 statements in
    // `docs/lemmas.md` do. So it passed on every input, including a definition that walked a
    // derivation's length, which is the one thing it was named after refusing.
    //
    // Asserting against a name `Recursion` publishes is not the repair, because it publishes
    // none: `Recursion.define` mints the CALLER's constant, and the object itself declares no
    // constant that could appear in any term. What says the closure was defined rather than
    // iterated is the whole set the definition is built from, so a constant arriving here — one
    // minted by `Recursion.define`, or `Descent`'s — turns this red rather than passing unseen.
    val definition = force(reaching.definition(Reaching.Name))
    constantsIn(definition.conclusion) shouldBe DefinitionConstants
    DefinitionConstants should contain(Inductive.Name)

    // The control on the instrument, which is what the line this replaced never had: the same
    // helper, asked of a term carrying a constant `REACH` is not built from, finds it. An
    // assertion about an absence is worth what its instrument is worth when something IS there.
    constantsIn(term("NUM_ADD ZERO ZERO")) shouldBe Set("NUM_ADD", "ZERO")
    DefinitionConstants should not contain "NUM_ADD"
  }

  /* -------------------------------------------------- a relation, and the lemma applied to it */

  /** `\u v. u = SUC v` — a step goes to the predecessor, and every step is counted. */
  private val downwards: Term = term("\\u:num. \\v:num. u = SUC v")

  private val two: Term = term("SUC (SUC ZERO)")
  private val one: Term = term("SUC ZERO")
  private val zero: Term = term("ZERO")

  /** `\n. n` — the number is its own potential, so a step down is a drop of exactly one. */
  private val measure: Term = term("\\n:num. n")

  private def shapedBy(rewrites: Vector[Rewrite.Rule], target: Term, proof: Kernel.Thm): Kernel.Thm = {
    val beta = force(Conv.betaNormalise(target))
    val normal = force(Rewrite.rewrite(rewrites, force(rightOf(beta))))
    val whole = force(Conv.trans(beta, normal))
    lift(Kernel.eqMp(force(Conv.sym(whole)), proof))
  }

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def normalOf(rewrites: Vector[Rewrite.Rule], target: Term): Term = {
    val beta = force(Conv.betaNormalise(target))
    force(rightOf(force(Conv.trans(beta, force(Rewrite.rewrite(rewrites, force(rightOf(beta))))))))
  }

  "A relation whose every step is counted" should "carry the bound the lemma promises" in {
    // The whole loop this development exists for, end to end: build a derivation with the
    // introduction rules, discharge the lemma's two hypotheses at this relation, and read the
    // bound off. Each statement being true on its own says nothing about whether they fit.
    val start = force(
      rules.specAll(atNumbers(fact(Reaching.Start)), List(downwards, downwards, two))
    )

    val from = term("PAIR (SUC (SUC ZERO)) ZERO")
    val counted = force(
      rules.specAll(
        atNumbers(fact(Reaching.CountedStep)),
        List(downwards, downwards, two, from, one)
      )
    )
    val hypothesis = force(logic.destImp(counted.conclusion).toRight(NotOfForm("an implication", counted.conclusion)))._1

    // `REACH R A 2 (PAIR 2 0) /\ R (FST (PAIR 2 0)) 1 /\ A (FST (PAIR 2 0)) 1`. The first is the
    // empty derivation; the other two beta-reduce and project to `2 = SUC 1`, which is reflexivity.
    val (reached, tail) = force(logic.destConj(hypothesis).toRight(NotOfForm("a conjunction", hypothesis)))
    val (movedTerm, countedTerm) = force(logic.destConj(tail).toRight(NotOfForm("a conjunction", tail)))
    val moved = shapedBy(projections, movedTerm, Conv.refl(normalOfEquationLeft(movedTerm)))
    val isCounted = shapedBy(projections, countedTerm, Conv.refl(normalOfEquationLeft(countedTerm)))

    val supplied = force(rules.conjIntro(start, force(rules.conjIntro(moved, isCounted))))
    val derivation = force(rules.mp(counted, supplied))
    derivation.hypotheses shouldBe empty

    // The lemma at this relation, with both hypotheses discharged.
    val potential = force(
      rules.specAll(atNumbers(fact(Reaching.Potential)), List(downwards, downwards, measure, two))
    )
    val assumptions = force(logic.destImp(potential.conclusion).toRight(NotOfForm("an implication", potential.conclusion)))._1
    val (dropsOne, neverLowers) = force(logic.destConj(assumptions).toRight(NotOfForm("a conjunction", assumptions)))

    // `A u v ==> Phi u = SUC (Phi v)` is, at this relation and this measure, `u = SUC v` implying
    // itself: the measure IS the number, so a counted step drops it by exactly one definitionally.
    val dropsProof = shapedBy(Vector.empty, dropsOne, provingSelfImplication(dropsOne))

    // `R u v /\ ~(A u v)` is empty here, because `A` is `R`. So the second hypothesis holds for the
    // reason that makes it vacuous rather than for a reason about the measure, and the negative
    // control below is what stops that from being the only evidence about it.
    val neverProof = shapedBy(Vector.empty, neverLowers, provingFromContradiction(neverLowers))

    val applied = force(rules.mp(potential, force(rules.conjIntro(dropsProof, neverProof))))
    val bound = force(rules.spec(force(rightOfImplicationSubject(derivation)), applied).flatMap(rules.mp(_, derivation)))

    bound.hypotheses shouldBe empty
    reduce(bound).conclusion shouldBe normalOf(projections, proposition(
      "SUC (SUC ZERO) <= NUM_ADD (SUC ZERO) (SUC ZERO)"))
  }

  /** The left side of the equation a beta-and-project normalised proposition turns out to be. */
  private def normalOfEquationLeft(target: Term): Term = {
    val normal = normalOf(projections, target)
    force(Term.destEq(normal).map(_._1).toRight(NotOfForm("an equation", normal)))
  }

  /** `!u v. p ==> p`, where the two sides are the same proposition. */
  private def provingSelfImplication(target: Term): Kernel.Thm = {
    val normal = normalOf(Vector.empty, target)
    val (binders, body) = force(Logic.stripForall(normal))
    val (antecedent, _) = force(logic.destImp(body).toRight(NotOfForm("an implication", body)))
    val assumed = lift(Kernel.assume(antecedent))
    binders.reverse.foldLeft(force(rules.disch(antecedent, assumed)))((theorem, binder) =>
      force(rules.gen(binder, theorem))
    )
  }

  /** `!u v. p /\ ~p ==> q`, discharged by ex falso. */
  private def provingFromContradiction(target: Term): Kernel.Thm = {
    val normal = normalOf(Vector.empty, target)
    val (binders, body) = force(Logic.stripForall(normal))
    val (antecedent, consequent) = force(logic.destImp(body).toRight(NotOfForm("an implication", body)))
    val assumed = lift(Kernel.assume(antecedent))
    val positive = force(rules.conjElim1(assumed))
    val negative = force(rules.conjElim2(assumed))
    val absurd = force(rules.notElim(negative, positive))
    val anything = force(rules.falsityElim(consequent, absurd))
    binders.reverse.foldLeft(force(rules.disch(antecedent, anything)))((theorem, binder) =>
      force(rules.gen(binder, theorem))
    )
  }

  /** The step a derivation reached, which is what the lemma has to be specialised at. */
  private def rightOfImplicationSubject(derivation: Kernel.Thm): Either[LogicError, Term] =
    derivation.conclusion match {
      case App(_, step) => Right(step)
      case other => Left(NotOfForm("a membership", other))
    }

  /* ------------------------------------------------- the negative control, which is the point */

  "The hypothesis that no uncounted step lowers the measure" should "be one the lemma cannot drop" in {
    // The witness: one step from one to zero, and NOTHING counted. `A` is the empty relation, so
    // the first hypothesis holds vacuously and the second is exactly what fails -- the measure
    // falls across a step that contributed no count.
    //
    // This is what the card asking for this development got backwards. It asked that no rule
    // RAISE the measure; the argument needs that no uncounted rule LOWER it. Under the condition
    // the card asked for, this same instance is admissible and the conclusion is false.
    val relation = term("\\u:num. \\v:num. u = SUC v")
    val nothing = term("\\u:num. \\v:num. F")

    val start = force(
      rules.specAll(atNumbers(fact(Reaching.Start)), List(relation, nothing, one))
    )

    val plain = force(
      rules.specAll(
        atNumbers(fact(Reaching.PlainStep)),
        List(relation, nothing, one, term("PAIR (SUC ZERO) ZERO"), zero)
      )
    )

    // What the lemma would conclude at this instance, if its second hypothesis were not there:
    // `Phi 1 <= SND (PAIR 0 0) + Phi (FST (PAIR 0 0))`, which reduces to `1 <= 0`.
    val bound = proposition("(SUC ZERO) <= NUM_ADD ZERO ZERO")
    val reducedBound = force(Rewrite.rewrite(Vector(force(Rewrite.Rule.of(logic, force(peano.fact(Peano.ZeroPlus))))), bound))
    val atZero = force(Term.destEq(reducedBound.conclusion).map(_._2).toRight(NotOfForm("an equation", reducedBound.conclusion)))

    // And it is false: `n <= ZERO` forces `n = ZERO`, which `SUC ZERO` is not.
    val atMostZero = force(peano.fact(Peano.AtMostZero))
    val assumed = lift(Kernel.assume(atZero))
    val collapsed = force(rules.spec(one, atMostZero).flatMap(rules.mp(_, assumed)))
    val never = force(rules.spec(zero, force(chain.naturals.fact(Natural.SuccessorNotZero))))
    val refusal = force(rules.notElim(never, collapsed).flatMap(rules.notIntro(atZero, _)))

    refusal.hypotheses shouldBe empty
    refusal.conclusion shouldBe force(logic.mkNot(atZero))

    // The two derivations exist, so the instance really is reachable rather than merely stated.
    start.hypotheses shouldBe empty
    plain.hypotheses shouldBe empty
  }
}
