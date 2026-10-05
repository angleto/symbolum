package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The integers: a type operator of their own, and the first thing built through the quotient
 * builder.
 *
 * == The question this file exists to answer ==
 *
 * `QuotientSpec` validates the builder on a toy, and says in as many words that the one guard it
 * cannot carry is non-collapse: refuting it there means deriving `~(NUM_CONG 2 2 3)`, which nothing
 * in this repository can, so that file's evidence is structural. **Here it is not**, and that is
 * the reason for the first assertion below: `num` has a distinctness procedure, so
 * `~(INT_OF_PAIR (PAIR 0 0) = INT_OF_PAIR (PAIR 1 0))` is derivable, and a quotient that had
 * identified everything could not produce it. Zero and one are different integers, proved rather
 * than assumed, and every other assertion in this file would pass over a one-point type.
 *
 * The positive half is beside it and is the other half of the same question: two pairs the relation
 * relates really do give one integer. A type that separated everything would pass the paragraph
 * above and fail this one, so the pair is what says the quotient quotients.
 *
 * == What the divisibility assertions are for, and what they are not ==
 *
 * The card that asked for this development names `Divisibility` as what it could not use, because
 * over a field every non-zero element divides everything and the condition is discharged
 * vacuously. Three assertions here answer different parts of that, and a reader should keep them
 * apart: that the relation carries a divisor across a **linear combination**, which is the step a
 * lattice argument is made of; that it is not everywhere true, spent on `~(INT_DIVIDES INT_ZERO INT_ONE)`; and that it
 * fails at a divisor that is **not** zero, which is `Integer.TwoDoesNotDivide` and is the one that
 * separates this relation from the field's.
 *
 * The middle one is deliberately the weakest such statement there is, and it is kept rather than
 * replaced: it is true over a field too, so what it measures is that the reading can see a
 * refusal at all. **This paragraph said the third was missing and wanted the discreteness of the
 * order until 2026-09-19**, which is what `docs/adr/0033` predicted and not what it cost: the
 * statement is `Integer.DividesOfNatural` detached at two numerals, and `INT_LE` is not consulted
 * anywhere in its derivation.
 */
class IntegerSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def lift[T](result: Either[KernelError, T]): T = force(LogicError.lift(result))

  private val chain = Chain.standard
  private val integers = chain.integers
  private val peano = chain.peano
  private val product = chain.product
  private val rules = integers.logic.rules

  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  private def fact(name: String): Kernel.Thm = force(integers.fact(name))

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term
      .destEq(theorem.conclusion)
      .map(_._1)
      .toRight(NotOfForm("an equation", theorem.conclusion))

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term
      .destEq(theorem.conclusion)
      .map(_._2)
      .toRight(NotOfForm("an equation", theorem.conclusion))

  /* ------------------------------------------------------------------ the type exists */

  /**
   * An unknown **type** is a parse error, where an unknown constant is a free variable.
   *
   * That difference is the trap `Chain.peano`'s note records for `NUM_LE ZERO n` and `ChainSpec`
   * for `zork`, and it is what makes this assertion worth making in both directions: a claim about
   * `int` against the link below would not have been refused if `int` were a name rather than a
   * type operator, it would have been a claim about something else. So the reading is taken against
   * `product`, which is the link the construction of `int` extends, rather than against a development
   * chosen for being far away. That link was `forward` until phase 5, when the integers moved below
   * the reals: `chain.integers` still extends `forward`, but `int` was declared long before it, by
   * `chain.fractions.integers`, and `forward` types a claim about `int` because the type is its own.
   */
  "The chain" should "declare `int`, which the link under this one does not" in {
    integers.proposition("!a:int. a = a") should be(Symbol("right"))
    chain.fractions.integers.proposition("!a:int. a = a") should be(Symbol("right"))

    chain.product.proposition("!a:int. a = a") match {
      case Left(_) => succeed
      case Right(term) =>
        fail(s"the link below this one typed a claim about `int`: ${chain.product.show(term)}")
    }
  }

  it should "read `int` through the widest signature, which is where a caller asks" in {
    // `Chain.widest` is the one place the name of the last link is written, and a goal about `int`
    // reaching `Ask` or `Find` goes through it rather than through this development. A link whose
    // constants the widest signature could not name would be in the chain and unreachable from it,
    // which is the defect `ChainCoverageSpec` exists to fail on.
    chain.widest.proposition("!a:int. a = a") should be(Symbol("right"))
    chain.widest.term("INT_OF_NUM ZERO", Integer.Classes) should be(Symbol("right"))
  }

  /* ------------------------------------------------------------------ the statements */

  it should "prove each of its facts with nothing assumed" in {
    Integer.Statements.foreach { case (name, _) =>
      withClue(s"$name: ")(fact(name).hypotheses shouldBe empty)
    }
  }

  it should "say what `Integer.Statements` says, read as a term" in {
    Integer.Statements.foreach { case (name, text) =>
      withClue(s"$name: ")(fact(name).conclusion shouldBe force(integers.proposition(text)))
    }
  }

  /* ------------------------------------------------------------------ the two halves of collapse */

  /** `FST (PAIR x y) = x`, `SND (PAIR x y) = y`, and the two recurrences of addition. */
  private lazy val carrierRules: Vector[Rewrite.Rule] =
    force(
      Rewrite.Rule.all(
        integers.logic,
        Vector(
          force(product.fact(Product.FirstOfPair)),
          force(product.fact(Product.SecondOfPair)),
          force(peano.fact(Peano.AddAtZero)),
          force(peano.fact(Peano.AddAtSuccessor))
        )
      )
    )

  private def pair(left: String, right: String): Term =
    force(integers.term(s"PAIR ($left) ($right)", Integer.Pairs))

  /**
   * Two pairs the relation relates give one integer, at pairs where a reader can check the answer.
   *
   * `(1, 0)` and `(2, 1)` both stand for one, and the relation says so because `1 + 1 = 2 + 0`.
   * Both sides are brought to `SUC (SUC ZERO)` by the two recurrences of addition rather than by
   * the semiring, which would not close it: `SUC ZERO` and `SUC (SUC ZERO)` are two atoms to a
   * semiring normaliser, and nothing in a commutative semiring says one is the other's successor.
   */
  "Two pairs with the same difference" should "be one integer" in {
    val left = pair("SUC ZERO", "ZERO")
    val right = pair("SUC (SUC ZERO)", "SUC ZERO")

    val unfolded =
      force(Conv.unfold(force(integers.definition(Integer.SameName)), List(left, right)))
    val body = force(rightOf(unfolded))
    val (leftSum, rightSum) = Term.destEq(body).getOrElse(fail("the relation is not an equation"))

    val arithmetic = force(Rewrite.prove(carrierRules, leftSum, rightSum))
    val related = lift(Kernel.eqMp(force(Conv.sym(unfolded)), arithmetic))

    val central = force(rules.specAll(fact(Integer.Equal), List(left, right)))
    val equal = lift(Kernel.eqMp(force(Conv.sym(central)), related))

    equal.hypotheses shouldBe empty
    Term.destEq(equal.conclusion) shouldBe defined
    integers.show(equal.conclusion) should include(Integer.Projection)
  }

  /**
   * `|- ~(INT_OF_PAIR (PAIR 0 0) = INT_OF_PAIR (PAIR 1 0))`, the non-collapse guard.
   *
   * A quotient that had collapsed satisfies every other assertion in this file and in
   * `QuotientSpec`: the central fact holds, the lifts lift, the axiom count is unchanged. What
   * refutes it is a derived **non**-equality between two classes, and it needs the carrier to have
   * one. `num` does, since `Successor.distinct` settles two written numerals, so the argument runs
   * all the way down to `~(0 = 1)` with nothing assumed anywhere in it.
   *
   * **The numerals are written `1:num` and not `SUC ZERO`, and the difference is not cosmetic.**
   * `Successor.distinct` reads the bit encoding `Peano` declares and refuses a successor form by
   * name: measured here on 2026-09-18, `SUC ZERO` comes back as *expected a numeral of num*. The
   * test above wants the other spelling, because its two sides are brought together by the
   * recurrences of addition and those are stated at `SUC`. So this file uses both spellings on
   * purpose, and `NUM_ONE_SUC` is what joins them where one term has to be the other.
   */
  private lazy val separated: Kernel.Thm = {
    val zero = pair("ZERO", "ZERO")
    val one = pair("1:num", "ZERO")

    val unfolded =
      force(Conv.unfold(force(integers.definition(Integer.SameName)), List(zero, one)))
    val body = force(rightOf(unfolded))
    val (leftSum, rightSum) = Term.destEq(body).getOrElse(fail("the relation is not an equation"))

    // `0 + 0` and `1 + 0` reduced to `ZERO` and `NUM_ONE` by the two recurrences.
    val leftValue = force(Rewrite.rewrite(carrierRules, leftSum))
    val rightValue = force(Rewrite.rewrite(carrierRules, rightSum))

    val apart =
      force(chain.successor.distinct(force(rightOf(leftValue)), force(rightOf(rightValue))))

    // `~(0 + 0 = 1 + 0)` from `~(0 = 1)`, by congruence and **not** by rewriting.
    //
    // The rewriting route is what this test did first and it exhausted the heap in four and a half
    // minutes: the two value equations read backwards are the rules `ZERO -> NUM_ADD ZERO ZERO`
    // and its twin, whose right side contains two copies of the left, so every pass doubles the
    // term. `Rewrite.Rule.of` refuses the two shapes that do this **through a variable** and has
    // nothing to say about a ground rule that grows, which is worth knowing before reversing any
    // equation into a rule: the direction that contracts is a property of the equation and the
    // guard only covers half of it.
    val congruence = force(equalityCongruence(leftValue, rightValue))
    val unrelated = force(carryNegation(apart, force(Conv.sym(congruence))))
    val notRelated = force(carryNegation(unrelated, force(Conv.sym(unfolded))))
    val central = force(rules.specAll(fact(Integer.Equal), List(zero, one)))

    force(carryNegation(notRelated, force(Conv.sym(central))))
  }

  it should "separate zero from one, which is what says the type did not collapse" in {
    separated.hypotheses shouldBe empty
    integers.show(separated.conclusion) should include(Integer.Projection)
    Real.spent(separated) should not be empty
  }

  /**
   * `|- (s = t) = (s' = t')` from `|- s = s'` and `|- t = t'`.
   *
   * Two congruences, the head taken off an equation this builds rather than looked up: the equality
   * constant is polymorphic, so asking the theory for it means naming the type, and naming the type
   * is the one thing this can read off the terms it was handed.
   */
  private def equalityCongruence(
    left: Kernel.Thm,
    right: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      leftSide <- leftOf(left)
      rightSide <- leftOf(right)
      equation <- LogicError.lift(Term.eq(leftSide, rightSide))
      head <- equation match {
        case App(App(constant, _), _) => Right(constant)
        case other => Left(NotOfForm("an equation", other))
      }
      partial <- Conv.apTerm(head, left)
      combined <- LogicError.lift(Kernel.mkComb(partial, right))
    } yield combined

  /**
   * From `|- ~P` and `|- P = Q`, the theorem `|- ~Q`.
   *
   * Written here rather than reached for because the rewriter is the general instrument and this is
   * one congruence: `~` applied to both sides of the equation, then `eqMp`.
   */
  private def carryNegation(
    negated: Kernel.Thm,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = integers.logic
    for {
      left <- leftOf(equation)
      negatedLeft <- logic.mkNot(left)
      negation <- negatedLeft match {
        case App(constant, _) => Right(constant)
        case other => Left(NotOfForm("a negation", other))
      }
      step <- Conv.apTerm(negation, equation)
      result <- LogicError.lift(Kernel.eqMp(step, negated))
    } yield result
  }

  /* ------------------------------------------------------------------ the ring and the divisibility */

  private def constant(name: String): Term =
    lift(integers.theory.constant(name, Integer.Classes))

  /**
   * `|- ~(INT_ZERO = INT_ONE)`: [[separated]] read at the two names the ring is stated with.
   *
   * The join between the two spellings is the one step here that is not mechanical. `INT_ONE` is
   * the class of `(SUC ZERO, ZERO)`, because the semiring's unit lemma is stated at `SUC ZERO`;
   * the numeral `1:num` that `Successor.distinct` reads is `NUM_ONE`, a different term with the
   * same value. `NUM_ONE_SUC` joins them, and it is applied to the **component** and carried in by
   * congruence rather than rewritten into the whole statement, which is the discipline `Collatz`
   * records for the same lemma and for the same reason.
   */
  private lazy val zeroIsNotOne: Kernel.Thm = {
    val oneIsSuccessor = force(peano.fact(Peano.NumeralOneIsSuccessorOfZero))
    val pairing = lift(
      integers.theory.constant(
        Product.Pairing,
        Type.fun(numbers, Type.fun(numbers, Integer.Pairs))
      )
    )
    val projection = lift(
      integers.theory.constant(Integer.Projection, Type.fun(Integer.Pairs, Integer.Classes))
    )
    val zeroNumeral = force(integers.term("ZERO", numbers))

    // `INT_OF_PAIR (PAIR NUM_ONE ZERO) = INT_ONE`, built one application at a time.
    val components = force(Conv.apTerm(pairing, oneIsSuccessor))
    val pairs = force(Conv.apThm(components, zeroNumeral))
    val classes = force(Conv.apTerm(projection, pairs))
    val toOne =
      force(Conv.trans(classes, force(Conv.sym(force(integers.definition(Integer.One))))))

    // `INT_OF_PAIR (PAIR ZERO ZERO) = INT_ZERO`, which is the definition read backwards.
    val toZero = force(Conv.sym(force(integers.definition(Integer.Zero))))

    val naming = force(Rewrite.Rule.all(integers.logic, Vector(toZero, toOne)))
    force(Rewrite.inTheorem(naming, separated))
  }

  /* ------------------------------------------------------------------ cancelling a factor */

  "A factor that cannot be zero" should "come off both sides, which is what the rationals want" in {
    // `INT_MUL_CANCEL_NUM`, spent rather than read. The instance is at a multiplier that is
    // written as a successor and at two integers that are **not** given as pairs, which is the
    // shape a consumer has: `docs/adr/0036` reads the denominator of a rational `(a, d)` as
    // `INT_OF_NUM (SUC d)`, and the transitivity of the relation on those pairs is this lemma at
    // `d` the middle pair's index.
    val theorem = force(
      for {
        lemma <- integers.fact(Integer.CancelsPositive)
        left <- integers.term("INT_OF_NUM 3", Integer.Classes)
        right <- integers.term("INT_OF_NUM 5", Integer.Classes)
        index <- integers.term("SUC (SUC (0:num))", numbers)
        instance <- rules.specAll(lemma, List(left, right, index))
      } yield instance
    )

    theorem.hypotheses shouldBe empty
    integers.show(theorem.conclusion) shouldBe
      "INT_MUL (INT_OF_NUM 3) (INT_OF_NUM (SUC (SUC (SUC 0)))) = " +
        "INT_MUL (INT_OF_NUM 5) (INT_OF_NUM (SUC (SUC (SUC 0)))) ==> INT_OF_NUM 3 = INT_OF_NUM 5"
  }

  it should "be the restricted law and not the general one, which this development cannot state" in {
    // What the lemma is NOT, asserted because a reader who wants the general cancellation will
    // reach for this name and has to be told in one line rather than by reading the statement.
    // `~(c = INT_ZERO) ==> INT_MUL a c = INT_MUL b c ==> a = b` is the general law, it wants the
    // absence of zero divisors, and nothing here holds that. The multiplier of the fact that does
    // exist is a successor, so the hypothesis is discharged by the shape of the term rather than
    // by a fact about zero.
    val general = force(
      integers.proposition(
        "!a:int. !b:int. !c:int. ~(c = INT_ZERO) ==> INT_MUL a c = INT_MUL b c ==> a = b"))

    integers.facts.values.exists(_.conclusion == general) shouldBe false
  }

  "Divisibility over the integers" should "refuse to let zero divide one" in {
    // The half of `Divisibility.ZeroDivides` that survives the move, spent on a concrete pair. It
    // is the cheapest statement this development can make that divisibility is not everywhere
    // true, and it is deliberately the weakest one: what it does NOT say is that a non-zero divisor
    // fails to divide something. That is `Integer.TwoDoesNotDivide`, and the assertion two below
    // is where it is spent. This one is kept because the two are different measurements: this
    // holds over a field and that one does not.
    val one = constant(Integer.One)

    val onlyZero = force(rules.spec(one, fact(Integer.ZeroDividesOnly)))
    val premise = integers.logic
      .destImp(onlyZero.conclusion)
      .getOrElse(fail("the zero case is not an implication"))
      ._1

    val assumed = lift(Kernel.assume(premise))
    val equated = force(rules.mp(onlyZero, assumed))
    val flipped = force(Conv.sym(equated))
    val absurd = force(rules.notElim(zeroIsNotOne, flipped))
    val refused = force(rules.notIntro(premise, absurd))

    refused.hypotheses shouldBe empty
    integers.show(refused.conclusion) should include(Integer.Divides)
  }

  it should "carry a divisor across a linear combination, which is what a consumer reaches for" in {
    // The fact the card that asked for this development names: an invariant survives a step because
    // the new value is a combination of old ones, so this is the step of such an argument that is
    // about divisibility at all. Over the reals the same statement is true and empty, since every
    // non-zero quantity divides everything there.
    val two = force(integers.term("INT_OF_NUM (SUC (SUC ZERO))", Integer.Classes))
    val zero = constant(Integer.Zero)
    val one = constant(Integer.One)

    val reflexive = force(rules.spec(two, fact(Integer.DividesReflexive)))
    val atZero = force(rules.spec(two, fact(Integer.DividesZero)))
    val instance = force(rules.specAll(fact(Integer.DividesLinear), List(two, two, zero, one, one)))
    val once = force(rules.mp(instance, reflexive))
    val settled = force(rules.mp(once, atZero))

    settled.hypotheses shouldBe empty
    integers.show(settled.conclusion) should include(Integer.Divides)

    // And it rests on nothing of the reals, which is the whole point of building the ring rather
    // than borrowing one. All sixteen and not one of them: the guard at the foot of this file
    // says why the single-axiom reading was not enough.
    Real.spent(settled) should contain noElementsOf realAxioms
  }

  /**
   * The embedding answers the same question on both sides, and the two sides can disagree with a
   * third thing rather than only with each other.
   *
   * `INT_DIVIDES_OF_NUM` is an equation between propositions, so it is satisfied by two sides that
   * are both always false as readily as by a faithful embedding, and nothing above would notice.
   * What separates the two is detaching it at a pair where the answer is **yes** and at a pair
   * where it is **no**, which is what these two lines are: `2` divides `2` on both sides and
   * divides `1` on neither. The negative is `Integer.TwoDoesNotDivide` and is published, so what
   * is exercised here is that it detaches with nothing assumed.
   */
  it should "answer alike over `num` and over `int`, and answer both ways" in {
    val two = force(integers.term("2", numbers))

    val reflexive = force(chain.modular.fact(Modular.DividesRefl).flatMap(rules.spec(two, _)))
    val transferred = force(
      rules
        .specAll(fact(Integer.DividesOfNatural), List(two, two))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(force(Conv.sym(equation)), reflexive)))
    )

    transferred.hypotheses shouldBe empty
    integers.show(transferred.conclusion) shouldBe "INT_DIVIDES (INT_OF_NUM 2) (INT_OF_NUM 2)"

    fact(Integer.TwoDoesNotDivide).hypotheses shouldBe empty
    integers.show(fact(Integer.TwoDoesNotDivide).conclusion) shouldBe
      "~(INT_DIVIDES (INT_OF_NUM 2) (INT_OF_NUM 1))"
  }

  /**
   * The refusal at a non-zero divisor does not reach the order, which is where the prediction was.
   *
   * `docs/adr/0033` said `~(INT_DIVIDES 2 1)` wanted the discreteness of the order. It does not,
   * and this is the assertion that keeps the corrected record honest rather than leaving the claim
   * in prose: the derivation is walked and no fact of this development's order is in it. A route
   * that went back through `INT_LE` would still prove the theorem and would make that record wrong
   * again with nothing going red.
   */
  it should "refuse `2` dividing `1` without consulting the order" in {
    val refusal = fact(Integer.TwoDoesNotDivide)

    val order = Vector(
      Integer.AtMostPairs,
      Integer.AtMostReflexive,
      Integer.AtMostTransitive,
      Integer.AtMostAntisymmetric,
      Integer.AtMostTotal,
      Integer.AddMonotone,
      Integer.AtMostOfNatural
    ).map(name => fact(name).conclusion).toSet

    // The positive control, and it is not decoration: `restingOn` answers with a set, and a set is
    // empty both when nothing was used and when the walk read nothing. What is known present here
    // for a reason independent of the instrument is the equation the refusal is six steps over.
    val faithful = Set(fact(Integer.DividesOfNatural).conclusion)
    Derivation.restingOn(refusal, faithful) should not be empty

    Derivation.restingOn(refusal, order) shouldBe empty
  }

  /**
   * The order reaches a concrete pair of integers, through the embedding rather than through a
   * pair.
   *
   * `INT_LE_OF_NUM` is what makes that possible and it is the fact a consumer will reach for:
   * `NUM_LE` over the naturals is already decided at written numerals, so an order between two
   * embedded naturals costs nothing beyond the equation. The half worth asserting is that the
   * detachment goes through with **nothing assumed**, which is what says the published equation is
   * usable rather than merely true.
   */
  "The order" should "settle a comparison of two embedded naturals" in {
    val three = force(integers.term("SUC (SUC (SUC ZERO))", numbers))
    val zeroNumeral = force(integers.term("ZERO", numbers))

    val embedded = force(rules.specAll(fact(Integer.AtMostOfNatural), List(zeroNumeral, three)))
    val least = force(peano.fact(Peano.ZeroIsLeast).flatMap(rules.spec(three, _)))
    val ordered = lift(Kernel.eqMp(force(Conv.sym(embedded)), least))

    ordered.hypotheses shouldBe empty
    integers.show(ordered.conclusion) should include(Integer.AtMost)
    integers.show(ordered.conclusion) should include(Integer.OfNatural)
  }

  it should "be compatible with addition, which is what makes the ring an ordered one" in {
    // The detachment `INT_ADD_LE_MONOTONE` exists for, at the comparison above. What it asserts
    // beyond the statement is that the two are composable: a consumer holding an order between two
    // integers gets one between two sums without restating anything.
    val three = force(integers.term("SUC (SUC (SUC ZERO))", numbers))
    val zeroNumeral = force(integers.term("ZERO", numbers))
    val embedded = force(rules.specAll(fact(Integer.AtMostOfNatural), List(zeroNumeral, three)))
    val least = force(peano.fact(Peano.ZeroIsLeast).flatMap(rules.spec(three, _)))
    val ordered = lift(Kernel.eqMp(force(Conv.sym(embedded)), least))

    // The two integers read off the order that was just derived, rather than rebuilt: the monotone
    // fact has to be specialised at the very terms the premise is about, and spelling them again
    // here is the second place they would live.
    val lower = force(firstArgumentOf(ordered.conclusion))
    val upper = force(secondArgumentOf(ordered.conclusion))
    val one = constant(Integer.One)
    val instance = force(rules.specAll(fact(Integer.AddMonotone), List(lower, upper, one)))
    val settled = force(rules.mp(instance, ordered))

    settled.hypotheses shouldBe empty
    integers.show(settled.conclusion) should include(Integer.Addition)
  }

  private def firstArgumentOf(term: Term): Either[LogicError, Term] =
    term match {
      case App(App(_, left), _) => Right(left)
      case other => Left(NotOfForm("an application of two arguments", other))
    }

  private def secondArgumentOf(term: Term): Either[LogicError, Term] =
    term match {
      case App(_, right) => Right(right)
      case other => Left(NotOfForm("an application", other))
    }

  /* ------------------------------------------------------------------ what it cost */

  private lazy val eta: Term = force(chain.classical.axiom(Classical.Eta)).conclusion
  private lazy val choice: Term = force(chain.classical.axiom(Classical.Choice)).conclusion
  private lazy val infinity: Term = force(chain.naturals.axiom(Natural.Infinity)).conclusion

  /** The three the carrier costs, which is the whole of what anything here is allowed to spend. */
  private lazy val foundation: Set[Term] = Set(choice, eta, infinity)

  /** All sixteen of the reals, read off `Real.Laws` rather than named one at a time. */
  private lazy val realAxioms: Set[Term] =
    Real.Laws.map { case (name, _) => force(chain.reals.law(name)).conclusion }.toSet

  /**
   * The type costs what the carrier cost and not one axiom more, and so does everything over it.
   *
   * An equality at [[Integer.Equal]] rather than a ceiling, which is the form `CodingSpec` uses
   * and the one `docs/adr/0016` predicted the answer to: a fact here that quietly stopped spending
   * the naturals' two would be as much a defect as one that started spending a seventeenth.
   *
   * **The other forty were checked against one of the sixteen until 2026-09-19**, `ADD_SYM`, so a
   * statement resting on `COMPLETENESS` or on any of the other fourteen passed, and
   * `docs/adr/0033` described the check as asserting that no axiom of the reals is among them.
   * What replaced it is a **containment** and not a widened non-membership, because containment is
   * the stronger true statement: it refuses the sixteen, and it also refuses a seventeenth axiom
   * arriving from anywhere else, which is the failure nothing here was watching for.
   *
   * The blanket **equality** over every statement was the other candidate and is false, which is
   * worth writing down because it is what the card proposed and what reading would have missed:
   * `INT_SAME_REFL` is one of them and the last assertion in this file says it does not reach
   * choice. A guard that contradicts its neighbour is not the stronger form of it.
   *
   * The containment is only about the reals while the sixteen are outside the foundation, so that
   * is asserted rather than assumed: a `choice` that happened to be one of the sixteen would make
   * every line here pass and mean nothing.
   */
  "The integers" should "cost the carrier's axioms and no others" in {
    realAxioms should have size 16
    realAxioms should contain noElementsOf foundation

    Real.spent(fact(Integer.Equal)) shouldBe foundation

    Integer.Statements.foreach { case (name, _) =>
      withClue(s"$name: ")(Real.spent(fact(name)) should contain noElementsOf realAxioms)
      withClue(s"$name: ")(Real.spent(fact(name)).diff(foundation) shouldBe empty)
    }
  }

  /**
   * And the reading it replaced would have passed something this one refuses, shown rather than
   * argued.
   *
   * A loop that is green over every statement says nothing about whether the guard can go red,
   * and the claim that the new form is stronger is exactly the kind a reader cannot check by
   * looking. The subject is
   * an axiom of the reals that is not `ADD_SYM`, taken from the chain rather than constructed:
   * `axiomsOf` of it is itself, the old predicate accepts it, and both halves of the new one
   * refuse it. That is the defect the guard had, exhibited on a real theorem of this repository
   * and without perturbing anything.
   */
  it should "refuse what the single-axiom reading accepted" in {
    val completeness = force(chain.reals.law("COMPLETENESS"))
    val addSym = force(chain.reals.law("ADD_SYM")).conclusion

    Real.spent(completeness) shouldBe Set(completeness.conclusion)
    Real.spent(completeness) should not contain addSym

    Real.spent(completeness) should contain atLeastOneElementOf realAxioms
    Real.spent(completeness).diff(foundation) should not be empty
  }

  /**
   * And the relation's own three cost less than the type does, which says the reading can see a
   * difference at all.
   *
   * Without this the assertion above is one number with nothing to compare it against: a walk that
   * returned the same set for everything would pass it. Reflexivity and symmetry of the relation
   * are about equality and the arithmetic of `num`, so neither reaches choice; the type does,
   * through the representative the builder chooses.
   */
  it should "spend less on the relation than on the type built from it" in {
    Real.spent(fact(Integer.SameReflexive)) should not contain choice
    Real.spent(fact(Integer.SameSymmetric)) should not contain choice
    Real.spent(fact(Integer.Equal)) should contain(choice)
  }

  /* ------------------------------------------------------------------ what the graph costs */

  /**
   * What a fact of the first quotient carries, read two ways since `docs/adr/0047`.
   *
   * `docs/adr/0016` says an asserted axiom has `Derivation.size` 1 and that after the sixteen become
   * theorems every claim about a real carries the construction's shared graph. The first quotient
   * is the first real number to extrapolate from, and taking it late means taking it when it is
   * expensive to act on, so it is taken here, as an assertion rather than a probe for the reason
   * `docs/adr/0034` gives.
   *
   * == Two sizes since the boundary ==
   *
   * **What a checker replays** is the whole graph: the written proof holds every cited fact's proof
   * once, and counting its step records is that size. It is what 0016 extrapolated and it did not
   * move: `INT_EQUAL` replays 7696 nodes, the 7687 of 2026-09-20 plus its nine citations.
   *
   * **What a report reads** is `Derivation.size`, which stops at a cited fact. That is the one the
   * boundary was for. Measured on 2026-09-25 against 2026-09-20: the median fact of `Integer` from
   * 11107 to 1445, the bridge's nine from 12827–24362 to 3925–5975.
   *
   * == What is asserted, with the room each leaves ==
   *
   * **The carving is replayed and not read.** `INT_SAME_REFL` is about equality and the arithmetic
   * of `num` and `INT_EQUAL` carries the carving of the type: replayed they are 39 and 7696, a
   * factor of 197 against an assertion of 50, and `INT_EQUAL` read is 1443, a fifth of what it
   * replays against an assertion of a half. A boundary that stopped holding fails the second, and a
   * quotient whose facts stopped carrying the carving fails the first.
   *
   * **A fact of the bridge reads at most half of what it replays, cites something, and still reads
   * four figures.** The ratio ran from 0.22 to 0.31 over the nine. The citation count is the guard
   * against the ratio being empty: a fact with no citation in its proof reads what it replays, and
   * it is the census that says whether a boundary was crossed at all. The floor of a thousand, under
   * a least reading of 3925, is the guard on the other side: a size that stopped walking and
   * reported a constant would pass the ratio and not this.
   *
   * **The replayed size stays in the band the reals' construction sets**, five or six figures.
   * 0016's band was four or five figures, and it held while the sixteen were asserted: on
   * 2026-09-26, before `docs/adr/0053`, the nine replayed 12837 to 24386. Proving the sixteen from
   * the cuts is what 0016 said would move it, and it moved at that stage and not earlier: after,
   * the same nine replay 105911 to 127984, while what each **reads** is unchanged to the node, 3925
   * to 5975, which is the citation boundary holding across the change. Below the floor that record
   * wants rereading; above the ceiling the cost grew past the construction.
   *
   * Each of those was seen red on 2026-09-25 with one piece of the boundary taken away, which is
   * `tools/verify/perturb-cited-fact-boundary.sh` and `perturb-graph-cost-at-the-integers.sh`.
   *
   * == What it does not cover ==
   *
   * The wall clock, deliberately: a node count is a function of the proof and two machines agree
   * on it. And what a bridge fact still reads, four to six thousand nodes, is its own proof and the
   * procedures' lemmas that are not published facts; the boundary does not reach those, and the
   * record says how far that leaves it.
   */
  it should "carry the carving in every fact it replays, and read it in none" in {
    def replayed(theorem: Kernel.Thm): Int =
      Proof.write(theorem).linesIterator.count(_.startsWith("s "))
    def quartiles(found: Vector[Int]): String = {
      val ordered = found.sorted
      s"${ordered(ordered.size / 4)}/${ordered(ordered.size / 2)}/${ordered(3 * ordered.size / 4)}"
    }
    val read = Integer.Statements.map { case (name, _) => Derivation.size(fact(name)) }.toVector
    val whole = Integer.Statements.map { case (name, _) => replayed(fact(name)) }.toVector
    val bridge = Inclusion.Statements.map { case (name, _) =>
      val theorem = force(chain.inclusion.fact(name))
      (name, Derivation.size(theorem), replayed(theorem), Derivation.census(theorem))
    }

    info(s"${read.size} facts of the first quotient: read ${quartiles(read)}, replayed ${quartiles(whole)} by quartile")
    bridge.foreach { case (name, reads, replays, census) =>
      info(s"$name reads $reads, replays $replays, cites ${census.getOrElse("Citation", 0)}")
    }

    val equal = fact(Integer.Equal)
    replayed(equal) should be > 50 * replayed(fact(Integer.SameReflexive))
    2 * Derivation.size(equal) should be < replayed(equal)

    bridge.foreach { case (name, reads, replays, census) =>
      withClue(s"$name: ") {
        census.getOrElse("Citation", 0) should be > 0
        2 * reads should be < replays
        reads should be > 1000
        replays should be > 1000
        replays should be < 1000000
      }
    }
  }
}
