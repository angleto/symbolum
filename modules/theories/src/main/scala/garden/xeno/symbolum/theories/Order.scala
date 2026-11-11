package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The order facts that need more than the order axioms, and the order of the numerals.
 *
 * The five order axioms say how `<` behaves under addition and multiplication and that it is a
 * total order, and every one of them is conditional or relational: none of them asserts that any
 * particular number is below any other. So the theory can state `0 < 1` from the first day and
 * cannot prove it, and until it does there is no inequality between two numerals anywhere in the
 * development, which is what [[Linarith]] means when it refuses a goal for wanting a multiplier.
 *
 * That is the gap [[Positivity]] exists to close, and this file builds on it. `0 < 1` is the first
 * stone and [[Positivity.positive]] carries it up the binary encoding to `0 < n` for every numeral;
 * [[Order.less]], here, compares two arbitrary numerals by proving their difference positive, which
 * is the one step of that chain that wants the collecting ring normal form.
 *
 * == What else is here ==
 *
 * The order lemmas that need more than one axiom and are wanted in more than one place: moving an
 * inequality to and from the form `0 < e`, which is the form [[Linarith]] works in; cancelling a
 * positive factor, which is what makes a rational multiplier usable without ever writing one down;
 * multiplying both sides of an inequality by something positive; and the positivity of an inverse,
 * which is the only fact here that mentions `inv` and the one any ratio between two measured
 * quantities needs.
 *
 * Two more that the axioms leave out and that every bound wants: that a square is at least zero,
 * which is what an extremal argument reaches for and which `LT_MUL` does not give because it is
 * silent about a factor that is negative or zero; and that two inequalities can be added, which
 * `LT_ADD` does not give because it adds the same term to both sides of one of them.
 *
 * == Why the cost follows the digits ==
 *
 * `positive` recurses on the bits rather than counting up, because `BIT0 k` is `k + k` and `BIT1 k`
 * is `(k + k) + 1` by definition and a sum of positives is positive. So `0 < 1000000` costs twenty
 * steps and not a million, which is the same distinction the collecting ring normal form is built
 * on: the length of a numeral, not its value.
 *
 * == Why it sits above [[Ring]], and why three of its facts do not ==
 *
 * [[Order.less]] proves `m < n` by proving `n - m` positive and adding `m` back, and the identity
 * it hands the ring is between two arbitrary numerals: through the expanding normal form that
 * costs what the value of the numeral costs, not what its length costs. So this file wants the
 * collecting form and therefore sits above [[Ring]]. The chain is
 * `Real -> Arithmetic -> Positivity -> Polynomial -> Ring -> Order`, and [[Linarith]] is the
 * consumer this is for.
 *
 * The three facts about the sign of a numeral run the other way and are declared in [[Positivity]],
 * below the ring, because the ring normal form needs one of them: a rational coefficient is a
 * numeral over a numeral, and cancelling that denominator needs `~(n = 0)`. They are cited here,
 * not derived a second time.
 */
final class Order private (val ring: Ring, published: Map[String, Kernel.Thm]) {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  val reals: RealTheory = ring.reals

  private val rules = reals.logic.rules

  /** The fact named, as a theorem with no hypotheses. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** `|- 0 < 1` */
  def zeroLessOne: Either[LogicError, Kernel.Thm] = fact(Order.ZeroLessOne)

  /** `|- !x y. 0 < x ==> 0 < y ==> 0 < x + y` */
  def addPositive: Either[LogicError, Kernel.Thm] = fact(Order.AddPositive)

  /** `|- !x y. x < y ==> 0 < y - x` */
  def moveToZero: Either[LogicError, Kernel.Thm] = fact(Order.MoveToZero)

  /** `|- !x y. 0 < y - x ==> x < y` */
  def moveFromZero: Either[LogicError, Kernel.Thm] = fact(Order.MoveFromZero)

  /** `|- !x. 0 < x ==> ~(x = 0)` */
  def nonZero: Either[LogicError, Kernel.Thm] = fact(Order.NonZero)

  /** `|- !c x. 0 < c ==> 0 < c * x ==> 0 < x` */
  def cancelPositive: Either[LogicError, Kernel.Thm] = fact(Order.CancelPositive)

  /** `|- !c x y. 0 < c ==> x < y ==> x * c < y * c` */
  def multiplyBoth: Either[LogicError, Kernel.Thm] = fact(Order.MultiplyBoth)

  /** `|- !x. 0 < x ==> 0 < inv x` */
  def inversePositive: Either[LogicError, Kernel.Thm] = fact(Order.InversePositive)

  /** `|- !x y. x < y ==> x <= y` */
  def leOfLt: Either[LogicError, Kernel.Thm] = fact(Order.LeOfLt)

  /** `|- !x y. x = y ==> x <= y` */
  def leOfEq: Either[LogicError, Kernel.Thm] = fact(Order.LeOfEq)

  /** `|- !x y. x <= y ==> x < y \/ x = y` */
  def leCases: Either[LogicError, Kernel.Thm] = fact(Order.LeCases)

  /** `|- !x y. 0 <= x ==> 0 < y ==> 0 < x + y` */
  def addNonNegativePositive: Either[LogicError, Kernel.Thm] = fact(Order.AddNonNegativePositive)

  /** `|- !x y. 0 <= x ==> 0 <= y ==> 0 <= x + y` */
  def addNonNegatives: Either[LogicError, Kernel.Thm] = fact(Order.AddNonNegatives)

  /** `|- !c x. 0 < c ==> 0 <= x ==> 0 <= c * x` */
  def multiplyNonNegative: Either[LogicError, Kernel.Thm] = fact(Order.MultiplyNonNegative)

  /** `|- !c x. 0 <= c ==> 0 <= x ==> 0 <= c * x` */
  def multiplyNonNegatives: Either[LogicError, Kernel.Thm] = fact(Order.MultiplyNonNegatives)

  /** `|- !c x. 0 < c ==> 0 <= c * x ==> 0 <= x` */
  def cancelNonNegative: Either[LogicError, Kernel.Thm] = fact(Order.CancelNonNegative)

  /** `|- !x y. x <= y ==> 0 <= y - x` */
  def leToZero: Either[LogicError, Kernel.Thm] = fact(Order.LeToZero)

  /** `|- !x y. 0 <= y - x ==> x <= y` */
  def leFromZero: Either[LogicError, Kernel.Thm] = fact(Order.LeFromZero)

  /** `|- !x y. x <= y ==> y <= x ==> x = y` */
  def antisymmetric: Either[LogicError, Kernel.Thm] = fact(Order.Antisymmetric)

  /** `|- !x. 0 <= x * x` */
  def squareNonNegative: Either[LogicError, Kernel.Thm] = fact(Order.SquareNonNegative)

  /** `|- !x. x * x = 0 ==> x = 0` */
  def squareZero: Either[LogicError, Kernel.Thm] = fact(Order.SquareZero)

  /** `|- !x y z w. x <= y ==> z <= w ==> x + z <= y + w` */
  def addLe: Either[LogicError, Kernel.Thm] = fact(Order.AddLe)

  /** `|- !c x y. 0 <= c ==> x <= y ==> x * c <= y * c` */
  def multiplyLe: Either[LogicError, Kernel.Thm] = fact(Order.MultiplyLe)

  /** `|- !x y. 0 < x ==> x <= y ==> inv y <= inv x` */
  def inverseAntitone: Either[LogicError, Kernel.Thm] = fact(Order.InverseAntitone)

  /**
   * `|- 0 < n`, for a numeral above zero.
   *
   * Zero and below are refused rather than attempted: `0 < 0` is false, and there is no numeral
   * below zero to be handed one.
   */
  def positive(value: BigInt): Either[LogicError, Kernel.Thm] = ring.positivity.positive(value)

  /**
   * `|- m < n`, for numerals with `m` below `n`.
   *
   * The difference is worked out on the numerals before anything is proved, so what the ring step
   * sees is an identity between numerals rather than a cancellation: `0 < n - m` from [[positive]],
   * then `n - m` added to nothing and `m` added to both sides, which is the order axiom.
   */
  def less(left: BigInt, right: BigInt): Either[LogicError, Kernel.Thm] =
    if (left < 0)
      reals.term(left.toString).flatMap(found => Left(NotOfForm("a numeral", found)))
    else if (right <= left)
      reals
        .term(right.toString)
        .flatMap(found => Left(NotOfForm(s"a numeral above $left", found)))
    else
      for {
        gap <- positive(right - left)
        difference <- Numeral.of(reals, right - left)
        below <- Numeral.of(reals, left)
        zero <- reals.term("0")

        // `!x y z. x < y ==> x + z < y + z`, at `0`, the difference, and the smaller numeral.
        addition <- reals
          .law("LT_ADD")
          .flatMap(rules.spec(zero, _))
          .flatMap(rules.spec(difference, _))
          .flatMap(rules.spec(below, _))
        shifted <- rules.mp(addition, gap)

        absorbs <- ring.prove(s"0 + $left = $left")
        sums <- ring.prove(s"${right - left} + $left = $right")
        result <- Conv.rewriteSides(absorbs, sums, shifted)
      } yield result

}

object Order {

  /**
   * The strict order's vocabulary, which is declared where `<` is first reasoned about.
   *
   * Exported rather than redefined: [[Positivity]] sits below this file because the ring normal
   * form needs a numeral to be non-zero, and it takes `<` down with it. Callers keep writing
   * `Order.destLess`, which is where they look for it, and there is still one declaration.
   */
  export Positivity.{destLess, lessThanConstant}

  /** `|- 0 < 1` */
  val ZeroLessOne: String = Positivity.ZeroLessOne

  /** `|- !x y. 0 < x ==> 0 < y ==> 0 < x + y` */
  val AddPositive: String = Positivity.AddPositive

  /** `|- !x y. x < y ==> 0 < y - x` */
  val MoveToZero: String = "LT_TO_ZERO"

  /** `|- !x y. 0 < y - x ==> x < y` */
  val MoveFromZero: String = "LT_FROM_ZERO"

  /** `|- !x. 0 < x ==> ~(x = 0)` */
  val NonZero: String = Positivity.NonZero

  /** `|- !c x. 0 < c ==> 0 < c * x ==> 0 < x` */
  val CancelPositive: String = "CANCEL_POSITIVE"

  /** `|- !c x y. 0 < c ==> x < y ==> x * c < y * c` */
  val MultiplyBoth: String = "LT_MUL_BOTH"

  /** `|- !x. 0 < x ==> 0 < inv x` */
  val InversePositive: String = "INV_POSITIVE"

  /** `|- !x y. x < y ==> x <= y` */
  val LeOfLt: String = "LE_OF_LT"

  /** `|- !x y. x = y ==> x <= y` */
  val LeOfEq: String = "LE_OF_EQ"

  /** `|- !x y. x <= y ==> x < y \/ x = y` */
  val LeCases: String = "LE_CASES"

  /**
   * `|- !x y. ~(x < y) ==> y <= x`, and it costs nothing classical.
   *
   * The obvious reading is that turning a negation into a positive statement is where the excluded
   * middle is spent, and on this order it is not: `LT_TOTAL` is an axiom, so the three cases are in
   * hand before anything is negated and the negation only discards one of them. That is why this
   * pair sits here, with the order's own facts, rather than beside the classical ones. A type whose
   * order is not total would need the other route and would not get this lemma at all.
   */
  val LeOfNotLt: String = "LE_OF_NOT_LT"

  /** `|- !x y. ~(x <= y) ==> y < x`, the same argument at the other relation. */
  val LtOfNotLe: String = "LT_OF_NOT_LE"

  /** `|- !x y. 0 <= x ==> 0 < y ==> 0 < x + y` */
  val AddNonNegativePositive: String = "ADD_NONNEG_LT"

  /** `|- !x y. 0 <= x ==> 0 <= y ==> 0 <= x + y` */
  val AddNonNegatives: String = "ADD_NONNEG"

  /** `|- !c x. 0 < c ==> 0 <= x ==> 0 <= c * x` */
  val MultiplyNonNegative: String = "MUL_NONNEG"

  /**
   * `|- !c x. 0 <= c ==> 0 <= x ==> 0 <= c * x`.
   *
   * The name is `MUL_NONNEG_BOTH` and not `MUL_NONNEG` because the latter is taken by the mixed
   * lemma above. The addition pair names itself the other way round, `ADD_NONNEG_LT` for the mixed
   * one and `ADD_NONNEG` for this shape, so the two families disagree; swapping the multiplication
   * pair over would be the tidier scheme and would change what an existing name denotes, which is
   * a decision rather than a rename.
   */
  val MultiplyNonNegatives: String = "MUL_NONNEG_BOTH"

  /** `|- !c x. 0 < c ==> 0 <= c * x ==> 0 <= x` */
  val CancelNonNegative: String = "CANCEL_NONNEG"

  /** `|- !x y. x <= y ==> 0 <= y - x` */
  val LeToZero: String = "LE_TO_ZERO"

  /** `|- !x y. 0 <= y - x ==> x <= y` */
  val LeFromZero: String = "LE_FROM_ZERO"

  /** `|- !x y. x <= y ==> y <= x ==> x = y` */
  val Antisymmetric: String = "LE_ANTISYMMETRIC"

  /**
   * `|- !x. 0 <= x * x`.
   *
   * The fact every extremal argument reaches for, and the cheapest one on this list that the order
   * axioms do not hand over: `LT_MUL` gives a positive product from two positive factors and says
   * nothing about a factor that is negative or zero, so the sign of a square is a case analysis and
   * not an instance.
   *
   * It is non-strict and cannot be strict. `0 < x * x` is false at zero, and the statement that
   * holds for every real is this one; a caller who has `~(x = 0)` gets the strict form from
   * [[LeCases]] and this, and nothing here does it for them.
   */
  val SquareNonNegative: String = "SQUARE_NONNEG"

  /**
   * `|- !x. x * x = 0 ==> x = 0`.
   *
   * A real whose square vanishes is zero, which is what turns a power of a difference into the
   * difference: `Ideal` finds `(L - R) * (L - R)` in the ideal of a goal's equations where `L - R`
   * itself is not, and this is the step from the one to the other. It is the case of the
   * zero-product law a field needs least to state, and the only one asked for so far; the general
   * `x * y = 0 ==> x = 0 \/ y = 0` wants `MUL_INVERSE` and a case split on a proposition, which
   * the order does not supply.
   *
   * By the same three cases as [[SquareNonNegative]]: at `0 = x` it is the hypothesis turned round,
   * and on either side of zero the square is strictly positive, so the hypothesis makes `0 < 0`,
   * which `LT_IRREFLEXIVE` refuses.
   */
  val SquareZero: String = "SQUARE_ZERO"

  /**
   * `|- !x y z w. x <= y ==> z <= w ==> x + z <= y + w`.
   *
   * Addition is monotone in both arguments at once, which `LT_ADD` does not say: the axiom adds the
   * *same* term to both sides of one inequality, and adding two inequalities together is two of
   * those steps or one of these. It is what every bound built out of parts wants, `Magnitude`'s
   * triangle inequality being the first consumer here, and the name follows [[AddNonNegatives]]
   * rather than [[MultiplyBoth]]: `_BOTH` in this file means both sides of one inequality, and this
   * is both inequalities.
   */
  val AddLe: String = "ADD_LE"

  /**
   * `|- !c x y. 0 <= c ==> x <= y ==> x * c <= y * c`.
   *
   * [[MultiplyBoth]] at the other relation, and the pair is not symmetric in what it costs: the
   * strict one is `LT_MUL` with the difference moved to zero, and this one cannot be, because a
   * product of non-negatives is not a case of a product of positives. It goes through
   * [[MultiplyNonNegatives]] instead, which is the lemma that already paid for that case analysis.
   *
   * **It was missing rather than unwanted**, and `Limit`'s own docstring named the gap from the
   * consumer's side before this existed: an order fact about a quotient is what the geometric
   * series wants at a symbolic ratio, and the only fact about `inv` in this chain was
   * [[InversePositive]]. This is half of what that needs and [[InverseAntitone]] is the other half.
   */
  val MultiplyLe: String = "LE_MUL_BOTH"

  /**
   * `|- !x y. 0 < x ==> x <= y ==> inv y <= inv x`.
   *
   * Taking the reciprocal reverses the order, on the positives. The hypothesis is on the **smaller**
   * one, which is what makes it usable: a caller holding `x <= y` and the positivity of the smaller
   * gets the positivity of the larger for free inside, and asking for both would be asking for
   * something the caller has to derive first.
   *
   * The derivation is the textbook one and every step of it is an order fact this file already
   * holds: multiply `x <= y` by `inv x * inv y`, which is non-negative because both factors are
   * positive, and read each side back through `MUL_INVERSE`. What it costs beyond the order is that
   * one axiom, and `~(x = 0)` from [[NonZero]] to spend it.
   *
   * **It is stated with `inv` and not with `/`**, because `/` is a definitional abbreviation and a
   * lemma about it would be a lemma about `\x y. x * inv y` unfolded at one shape. A caller with a
   * quotient unfolds the definition, which is what every other consumer of `inv` here does.
   */
  val InverseAntitone: String = "INV_ANTITONE"

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val relation: Type = Type.fun(real, Type.fun(real, Type.Bool))
  private val binary: Type = Type.fun(real, Type.fun(real, real))

  /** Built once over the standard ring. */
  lazy val standard: Order =
    construct(Ring.standard).fold(
      error => throw new IllegalStateException(s"the order facts do not build: ${error.message}"),
      identity
    )

  /**
   * Every fact in one pass, each derivation taking the ones before it as arguments.
   *
   * They are passed in rather than fetched because that is what makes each derivation readable on
   * its own: the signature says what it rests on, and a lemma that grew a dependency cannot hide
   * it in a lookup.
   */
  def construct(ring: Ring): Either[LogicError, Order] = {
    val reals = ring.reals

    for {
      zeroLeft <- ring.arithmetic.lemma(Arithmetic.ZeroOnTheLeft)
      unit <- ring.positivity.zeroLessOne
      sum <- ring.positivity.addPositive
      toZero <- moveToZero(reals)
      fromZero <- moveFromZero(ring, zeroLeft)
      notZero <- ring.positivity.nonZero
      cancel <- cancelPositive(ring, sum)
      both <- multiplyBoth(ring, toZero, fromZero)
      inverse <- inversePositive(ring, unit, notZero, cancel)

      ofLt <- leOfLt(reals)
      ofEq <- leOfEq(reals)
      cases <- leCases(reals)
      weakFromNegated <- leOfNotLt(reals, ofLt, ofEq)
      strictFromNegated <- ltOfNotLe(reals, ofLt, ofEq)
      addWithPositive <- addNonNegativePositive(ring, cases, sum)
      addBoth <- addNonNegatives(ring, cases, ofLt, addWithPositive)
      timesNonNegative <- multiplyNonNegative(ring, cases, ofLt, ofEq)
      timesNonNegatives <- multiplyNonNegatives(ring, cases, ofEq, timesNonNegative)
      cancelWeak <- cancelNonNegative(ring, ofLt, ofEq, addWithPositive)
      weakToZero <- leToZero(ring, cases, ofLt, ofEq, toZero)
      weakFromZero <- leFromZero(ring, cases, ofLt, ofEq, fromZero)
      antisymmetry <- antisymmetric(reals, cases)
      square <- squareNonNegative(ring, ofLt, ofEq)
      squareVanishes <- squareZero(ring)
      sumOfBounds <- addLe(ring, weakToZero, weakFromZero, addBoth)
      timesLe <- multiplyLe(ring, weakToZero, weakFromZero, timesNonNegatives)
      inverseReverses <- inverseAntitone(ring, notZero, inverse, cases, ofLt, timesLe)
    } yield new Order(
      ring,
      Map(
        ZeroLessOne -> unit,
        AddPositive -> sum,
        MoveToZero -> toZero,
        MoveFromZero -> fromZero,
        NonZero -> notZero,
        CancelPositive -> cancel,
        MultiplyBoth -> both,
        InversePositive -> inverse,
        LeOfLt -> ofLt,
        LeOfEq -> ofEq,
        LeCases -> cases,
        LeOfNotLt -> weakFromNegated,
        LtOfNotLe -> strictFromNegated,
        AddNonNegativePositive -> addWithPositive,
        AddNonNegatives -> addBoth,
        MultiplyNonNegative -> timesNonNegative,
        MultiplyNonNegatives -> timesNonNegatives,
        CancelNonNegative -> cancelWeak,
        LeToZero -> weakToZero,
        LeFromZero -> weakFromZero,
        Antisymmetric -> antisymmetry,
        SquareNonNegative -> square,
        SquareZero -> squareVanishes,
        AddLe -> sumOfBounds,
        MultiplyLe -> timesLe,
        InverseAntitone -> inverseReverses
      )
    )
  }

  /* ------------------------------------------------------------------ lemmas */

  /**
   * `|- !x y. x < y ==> 0 < y - x`.
   *
   * Adding `-x` to both sides is the order axiom; what is left is to see that `x + -x` is zero and
   * that `y + -x` is what `y - x` abbreviates.
   */
  def moveToZero(reals: RealTheory): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      ltAdd <- reals.law("LT_ADD")
      inverse <- reals.law("ADD_INVERSE")
      subtraction <- reals.definition(Real.Subtraction)

      negated <- reals.term("-x:real")
      premise <- reals.proposition("x:real < y:real")
      assumed <- LogicError.lift(Kernel.assume(premise))

      instance <- rules.specAll(ltAdd, List(x, y, negated))
      applied <- rules.mp(instance, assumed)

      inverseAtX <- rules.spec(x, inverse)
      unfolded <- Conv.unfold(subtraction, List(y, x))
      folded <- Conv.sym(unfolded)

      rules0 <- Rewrite.Rule.all(reals.logic, Vector(inverseAtX, folded))
      moved <- Rewrite.inTheorem(rules0, applied)

      discharged <- rules.disch(premise, moved)
      general <- rules.genAll(discharged, List(x, y))
    } yield general
  }

  /**
   * `|- !x y. 0 < y - x ==> x < y`, the way back.
   *
   * The same axiom with `x` added to both sides, and then the ring tactic to see that
   * `(y - x) + x` is `y`.
   */
  def moveFromZero(ring: Ring, zeroLeft: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      ltAdd <- reals.law("LT_ADD")

      zero <- reals.term("0")
      difference <- reals.term("y:real - x:real")
      premise <- reals.proposition("0 < y:real - x:real")
      assumed <- LogicError.lift(Kernel.assume(premise))

      instance <- rules.specAll(ltAdd, List(zero, difference, x))
      applied <- rules.mp(instance, assumed)

      restored <- ring.prove("(y:real - x:real) + x = y")
      zeroAtX <- rules.spec(x, zeroLeft)

      rules0 <- Rewrite.Rule.all(reals.logic, Vector(zeroAtX, restored))
      moved <- Rewrite.inTheorem(rules0, applied)

      discharged <- rules.disch(premise, moved)
      general <- rules.genAll(discharged, List(x, y))
    } yield general
  }

  /**
   * `|- !c x. 0 < c ==> 0 < c * x ==> 0 < x`.
   *
   * Cancelling a positive factor, by cases on trichotomy at `0` and `x`:
   *
   *  - `0 < x` is the goal;
   *  - `0 = x` makes `c * x` zero, and `0 < 0` is refused by irreflexivity;
   *  - `x < 0` makes `-x` positive, so `c * -x` is positive too, and adding it to `c * x` gives
   *    `0 < 0` again.
   *
   * It is what lets a rational multiplier be used without one ever being written down. A
   * certificate cleared of its denominators proves the goal multiplied by a positive numeral, and
   * this takes the numeral back off, with no `inv` anywhere, which matters because the ring
   * normalisation refuses `inv` by construction.
   */
  def cancelPositive(ring: Ring, addPositive: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val c = Term.variable("c", real)
    val x = Term.variable("x", real)

    for {
      irreflexive <- reals.law("LT_IRREFLEXIVE")
      ltAdd <- reals.law("LT_ADD")
      ltMul <- reals.law("LT_MUL")
      trichotomy <- reals.law("LT_TOTAL")

      zero <- reals.term("0")
      goal <- reals.proposition("0 < x:real")
      product <- reals.term("c:real * x:real")
      never <- rules.spec(zero, irreflexive)

      positiveFactor <- reals.proposition("0 < c:real")
      factorAssumed <- LogicError.lift(Kernel.assume(positiveFactor))
      positiveProduct <- reals.proposition("0 < c:real * x:real")
      productAssumed <- LogicError.lift(Kernel.assume(positiveProduct))

      cases <- rules.specAll(trichotomy, List(zero, x))

      // The first branch is the goal.
      first <- LogicError.lift(Kernel.assume(goal))

      // The second makes the product zero.
      equated <- reals.proposition("0 = x:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      reversed <- Conv.sym(equatedAssumed)
      toZero <- Rewrite.Rule.all(reals.logic, Vector(reversed))
      atZero <- Rewrite.inTheorem(toZero, productAssumed)
      productIsZero <- ring.prove("c:real * 0 = 0")
      collapse <- Rewrite.Rule.all(reals.logic, Vector(productIsZero))
      absurdSecond <- Rewrite.inTheorem(collapse, atZero)
      contradictionSecond <- rules.notElim(never, absurdSecond)
      second <- rules.falsityElim(goal, contradictionSecond)

      // The third makes `-x` positive, and then the other product with it.
      belowZero <- reals.proposition("x:real < 0")
      belowAssumed <- LogicError.lift(Kernel.assume(belowZero))
      negated <- reals.term("-x:real")
      shifted <- rules.specAll(ltAdd, List(x, zero, negated))
        .flatMap(rules.mp(_, belowAssumed))
      cancels <- ring.prove("x:real + -x = 0")
      absorbs <- ring.prove("0 + -x:real = -x")
      positiveNegation <- Conv.rewriteSides(cancels, absorbs, shifted)

      otherProduct <- rules.specAll(ltMul, List(c, negated))
      bothPositive <- rules.conjIntro(factorAssumed, positiveNegation)
      negativePart <- rules.mp(otherProduct, bothPositive)
      otherSide <- destLess(reals, negativePart.conclusion).map(_._2)

      summed <- rules.specAll(addPositive, List(product, otherSide))
        .flatMap(rules.mp(_, productAssumed))
        .flatMap(rules.mp(_, negativePart))
      sumIsZero <- ring.prove("c:real * x + c * -x = 0")
      vanishes <- Rewrite.Rule.all(reals.logic, Vector(sumIsZero))
      absurdThird <- Rewrite.inTheorem(vanishes, summed)
      contradictionThird <- rules.notElim(never, absurdThird)
      third <- rules.falsityElim(goal, contradictionThird)

      tail <- reals
        .proposition("0 = x:real \\/ x:real < 0")
        .flatMap(term => LogicError.lift(Kernel.assume(term)))
      fromTail <- rules.disjElim(tail, second, third)
      result <- rules.disjElim(cases, first, fromTail)

      innerDischarged <- rules.disch(positiveProduct, result)
      outerDischarged <- rules.disch(positiveFactor, innerDischarged)
      general <- rules.genAll(outerDischarged, List(c, x))
    } yield general
  }

  /**
   * `|- !c x y. 0 < c ==> x < y ==> x * c < y * c`.
   *
   * Multiplying an inequality by something positive. The difference `y - x` is positive, the
   * product of two positives is positive by the axiom, and `(y - x) * c` is `y * c - x * c` by
   * ring reasoning, which is the difference of the goal.
   *
   * Curried rather than stated with a conjunction, so that a caller who has only the positivity
   * can instantiate it and keep the rest.
   */
  def multiplyBoth(
    ring: Ring,
    toZero: Kernel.Thm,
    fromZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val c = Term.variable("c", real)
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      ltMul <- reals.law("LT_MUL")

      positiveFactor <- reals.proposition("0 < c:real")
      factorAssumed <- LogicError.lift(Kernel.assume(positiveFactor))
      premise <- reals.proposition("x:real < y:real")
      assumed <- LogicError.lift(Kernel.assume(premise))

      difference <- rules.specAll(toZero, List(x, y)).flatMap(rules.mp(_, assumed))
      gap <- destLess(reals, difference.conclusion).map(_._2)

      product <- rules.specAll(ltMul, List(gap, c))
      bothPositive <- rules.conjIntro(difference, factorAssumed)
      scaled <- rules.mp(product, bothPositive)

      distributed <- ring.prove("(y:real - x:real) * c:real = y * c - x * c")
      spread <- Rewrite.Rule.all(reals.logic, Vector(distributed))
      onGoal <- Rewrite.inTheorem(spread, scaled)

      left <- reals.term("x:real * c:real")
      right <- reals.term("y:real * c:real")
      result <- rules.specAll(fromZero, List(left, right)).flatMap(rules.mp(_, onGoal))

      innerDischarged <- rules.disch(premise, result)
      outerDischarged <- rules.disch(positiveFactor, innerDischarged)
      general <- rules.genAll(outerDischarged, List(c, x, y))
    } yield general
  }

  /**
   * `|- !x. 0 < x ==> 0 < inv x`.
   *
   * The inverse of a positive is positive, and the derivation is three steps once the pieces are
   * there: a positive number is not zero, so `MUL_INVERSE` applies and `x * inv x` is `1`, so
   * `0 < x * inv x` because `0 < 1`, and the positive factor cancels.
   *
   * It is the fact any ratio between two measured quantities needs, and it is the only one here
   * that mentions `inv` at all. Neither [[Ring]] nor [[Linarith]] can produce it: the first
   * refuses `inv` because `MUL_INVERSE` carries a side condition, and the second treats `inv x` as
   * an atom it knows nothing about.
   */
  def inversePositive(
    ring: Ring,
    unit: Kernel.Thm,
    notZero: Kernel.Thm,
    cancel: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val x = Term.variable("x", real)

    for {
      mulInverse <- reals.law("MUL_INVERSE")

      premise <- reals.proposition("0 < x:real")
      assumed <- LogicError.lift(Kernel.assume(premise))

      distinct <- rules.spec(x, notZero).flatMap(rules.mp(_, assumed))
      inverts <- rules.spec(x, mulInverse).flatMap(rules.mp(_, distinct))

      backwards <- Conv.sym(inverts)
      toProduct <- Rewrite.Rule.all(reals.logic, Vector(backwards))
      positiveProduct <- Rewrite.inTheorem(toProduct, unit)

      inverse <- reals.term("inv (x:real)")
      result <- rules.specAll(cancel, List(x, inverse))
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.mp(_, positiveProduct))

      discharged <- rules.disch(premise, result)
      general <- rules.gen(x, discharged)
    } yield general
  }

  /* ------------------------------------------------- the non-strict order */

  /**
   * `|- x <= y = (x < y \/ x = y)`, at two given terms.
   *
   * The definition read forwards, and the only thing there is to read: `<=` carries no axiom, so
   * every fact below is this disjunction plus the strict order.
   */
  private def unfoldLe(
    reals: RealTheory,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] =
    reals.definition(Real.NonStrictOrder).flatMap(Conv.unfold(_, List(left, right)))

  /** `|- !x y. x < y ==> x <= y` */
  def leOfLt(reals: RealTheory): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      premise <- reals.proposition("x:real < y:real")
      assumed <- LogicError.lift(Kernel.assume(premise))
      equated <- reals.proposition("x:real = y:real")
      disjunction <- rules.disjIntro1(equated, assumed)

      unfolded <- unfoldLe(reals, x, y)
      backwards <- Conv.sym(unfolded)
      result <- LogicError.lift(Kernel.eqMp(backwards, disjunction))

      discharged <- rules.disch(premise, result)
      general <- rules.genAll(discharged, List(x, y))
    } yield general
  }

  /** `|- !x y. x = y ==> x <= y` */
  def leOfEq(reals: RealTheory): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      premise <- reals.proposition("x:real = y:real")
      assumed <- LogicError.lift(Kernel.assume(premise))
      strict <- reals.proposition("x:real < y:real")
      disjunction <- rules.disjIntro2(strict, assumed)

      unfolded <- unfoldLe(reals, x, y)
      backwards <- Conv.sym(unfolded)
      result <- LogicError.lift(Kernel.eqMp(backwards, disjunction))

      discharged <- rules.disch(premise, result)
      general <- rules.genAll(discharged, List(x, y))
    } yield general
  }

  /**
   * `|- !x y. x <= y ==> x < y \/ x = y`.
   *
   * The way into a case analysis on a non-strict hypothesis, and every lemma below starts with it.
   */
  def leCases(reals: RealTheory): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      premise <- reals.proposition("x:real <= y:real")
      assumed <- LogicError.lift(Kernel.assume(premise))
      unfolded <- unfoldLe(reals, x, y)
      result <- LogicError.lift(Kernel.eqMp(unfolded, assumed))

      discharged <- rules.disch(premise, result)
      general <- rules.genAll(discharged, List(x, y))
    } yield general
  }

  /**
   * `|- !x y. 0 <= x ==> 0 < y ==> 0 < x + y`.
   *
   * Something that may be zero added to something that is not. The branch where it is zero is a
   * rewrite rather than an argument: the sum is the second one there, and the second premise is
   * the goal.
   */
  def addNonNegativePositive(
    ring: Ring,
    cases: Kernel.Thm,
    addPositive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      zero <- reals.term("0")
      sum <- reals.term("x:real + y:real")

      first <- reals.proposition("0 <= x:real")
      firstAssumed <- LogicError.lift(Kernel.assume(first))
      second <- reals.proposition("0 < y:real")
      secondAssumed <- LogicError.lift(Kernel.assume(second))

      split <- rules.specAll(cases, List(zero, x)).flatMap(rules.mp(_, firstAssumed))

      strict <- reals.proposition("0 < x:real")
      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      whenPositive <- rules.specAll(addPositive, List(x, y))
        .flatMap(rules.mp(_, strictAssumed))
        .flatMap(rules.mp(_, secondAssumed))

      equated <- reals.proposition("0 = x:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      reversed <- Conv.sym(equatedAssumed)
      shifted <- rewriteTerm(reals, reversed, sum)
      collapses <- ring.prove("0 + y:real = y")
      isSecond <- Conv.trans(shifted, collapses)
      backwards <- Conv.sym(isSecond)
      whenZero <- Conv.rewriteRight(secondAssumed, backwards)

      result <- rules.disjElim(split, whenPositive, whenZero)

      innerDischarged <- rules.disch(second, result)
      outerDischarged <- rules.disch(first, innerDischarged)
      general <- rules.genAll(outerDischarged, List(x, y))
    } yield general
  }

  /**
   * `|- !x y. 0 <= x ==> 0 <= y ==> 0 <= x + y`.
   *
   * One case analysis rather than two, because the branch where the second is positive is the
   * lemma above with its arguments the other way round.
   */
  def addNonNegatives(
    ring: Ring,
    cases: Kernel.Thm,
    ofLt: Kernel.Thm,
    addNonNegative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      zero <- reals.term("0")
      sum <- reals.term("x:real + y:real")

      first <- reals.proposition("0 <= x:real")
      firstAssumed <- LogicError.lift(Kernel.assume(first))
      second <- reals.proposition("0 <= y:real")
      secondAssumed <- LogicError.lift(Kernel.assume(second))

      split <- rules.specAll(cases, List(zero, y)).flatMap(rules.mp(_, secondAssumed))

      strict <- reals.proposition("0 < y:real")
      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      positive <- rules.specAll(addNonNegative, List(x, y))
        .flatMap(rules.mp(_, firstAssumed))
        .flatMap(rules.mp(_, strictAssumed))
      whenPositive <- rules.specAll(ofLt, List(zero, sum)).flatMap(rules.mp(_, positive))

      equated <- reals.proposition("0 = y:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      reversed <- Conv.sym(equatedAssumed)
      shifted <- rewriteTerm(reals, reversed, sum)
      collapses <- ring.prove("x:real + 0 = x")
      isFirst <- Conv.trans(shifted, collapses)
      backwards <- Conv.sym(isFirst)
      whenZero <- Conv.rewriteRight(firstAssumed, backwards)

      result <- rules.disjElim(split, whenPositive, whenZero)

      innerDischarged <- rules.disch(second, result)
      outerDischarged <- rules.disch(first, innerDischarged)
      general <- rules.genAll(outerDischarged, List(x, y))
    } yield general
  }

  /** `|- !c x. 0 < c ==> 0 <= x ==> 0 <= c * x` */
  def multiplyNonNegative(
    ring: Ring,
    cases: Kernel.Thm,
    ofLt: Kernel.Thm,
    ofEq: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val c = Term.variable("c", real)
    val x = Term.variable("x", real)

    for {
      ltMul <- reals.law("LT_MUL")
      zero <- reals.term("0")
      product <- reals.term("c:real * x:real")

      factor <- reals.proposition("0 < c:real")
      factorAssumed <- LogicError.lift(Kernel.assume(factor))
      second <- reals.proposition("0 <= x:real")
      secondAssumed <- LogicError.lift(Kernel.assume(second))

      split <- rules.specAll(cases, List(zero, x)).flatMap(rules.mp(_, secondAssumed))

      strict <- reals.proposition("0 < x:real")
      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      positive <- rules.specAll(ltMul, List(c, x))
        .flatMap(instance => rules.conjIntro(factorAssumed, strictAssumed).flatMap(rules.mp(instance, _)))
      whenPositive <- rules.specAll(ofLt, List(zero, product)).flatMap(rules.mp(_, positive))

      equated <- reals.proposition("0 = x:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      reversed <- Conv.sym(equatedAssumed)
      shifted <- rewriteTerm(reals, reversed, product)
      collapses <- ring.prove("c:real * 0 = 0")
      isZero <- Conv.trans(shifted, collapses)
      backwards <- Conv.sym(isZero)
      whenZero <- rules.specAll(ofEq, List(zero, product)).flatMap(rules.mp(_, backwards))

      result <- rules.disjElim(split, whenPositive, whenZero)

      innerDischarged <- rules.disch(second, result)
      outerDischarged <- rules.disch(factor, innerDischarged)
      general <- rules.genAll(outerDischarged, List(c, x))
    } yield general
  }

  /**
   * `|- !c x. 0 <= c ==> 0 <= x ==> 0 <= c * x`.
   *
   * The one the order facts did not have. `Linarith` multiplies a strict fact by a non-strict one
   * and used to leave two non-strict ones alone, and that was this lemma missing rather than a move
   * missing: nothing else about the procedure had to change once it existed.
   *
   * It splits on the first hypothesis and not the second, which is what keeps it to one case
   * analysis. `0 < c` hands the goal to [[multiplyNonNegative]] as it stands, and `0 = c` makes the
   * product zero, where what is left is that zero is at least zero.
   */
  def multiplyNonNegatives(
    ring: Ring,
    cases: Kernel.Thm,
    ofEq: Kernel.Thm,
    timesNonNegative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val c = Term.variable("c", real)
    val x = Term.variable("x", real)

    for {
      zero <- reals.term("0")
      product <- reals.term("c:real * x:real")

      first <- reals.proposition("0 <= c:real")
      firstAssumed <- LogicError.lift(Kernel.assume(first))
      second <- reals.proposition("0 <= x:real")
      secondAssumed <- LogicError.lift(Kernel.assume(second))

      split <- rules.specAll(cases, List(zero, c)).flatMap(rules.mp(_, firstAssumed))

      strict <- reals.proposition("0 < c:real")
      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      whenPositive <- rules
        .specAll(timesNonNegative, List(c, x))
        .flatMap(rules.mp(_, strictAssumed))
        .flatMap(rules.mp(_, secondAssumed))

      equated <- reals.proposition("0 = c:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      reversed <- Conv.sym(equatedAssumed)
      shifted <- rewriteTerm(reals, reversed, product)
      collapses <- ring.prove("0 * x:real = 0")
      isZero <- Conv.trans(shifted, collapses)
      backwards <- Conv.sym(isZero)
      whenZero <- rules.specAll(ofEq, List(zero, product)).flatMap(rules.mp(_, backwards))

      result <- rules.disjElim(split, whenPositive, whenZero)

      innerDischarged <- rules.disch(second, result)
      outerDischarged <- rules.disch(first, innerDischarged)
      general <- rules.genAll(outerDischarged, List(c, x))
    } yield general
  }

  /**
   * `|- !c x. 0 < c ==> 0 <= c * x ==> 0 <= x`.
   *
   * The non-strict twin of [[cancelPositive]], and the reason a goal that is not strict can still
   * be proved from a certificate with denominators in it. Trichotomy again, and again only the
   * third case is an argument: `x < 0` makes `c * -x` positive, and adding that to something that
   * is at least zero gives `0 < 0`.
   */
  def cancelNonNegative(
    ring: Ring,
    ofLt: Kernel.Thm,
    ofEq: Kernel.Thm,
    addNonNegative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val c = Term.variable("c", real)
    val x = Term.variable("x", real)

    for {
      irreflexive <- reals.law("LT_IRREFLEXIVE")
      ltAdd <- reals.law("LT_ADD")
      ltMul <- reals.law("LT_MUL")
      trichotomy <- reals.law("LT_TOTAL")

      zero <- reals.term("0")
      product <- reals.term("c:real * x:real")
      goal <- reals.proposition("0 <= x:real")
      never <- rules.spec(zero, irreflexive)

      factor <- reals.proposition("0 < c:real")
      factorAssumed <- LogicError.lift(Kernel.assume(factor))
      second <- reals.proposition("0 <= c:real * x:real")
      secondAssumed <- LogicError.lift(Kernel.assume(second))

      cases <- rules.specAll(trichotomy, List(zero, x))

      strict <- reals.proposition("0 < x:real")
      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      first <- rules.specAll(ofLt, List(zero, x)).flatMap(rules.mp(_, strictAssumed))

      equated <- reals.proposition("0 = x:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      second0 <- rules.specAll(ofEq, List(zero, x)).flatMap(rules.mp(_, equatedAssumed))

      belowZero <- reals.proposition("x:real < 0")
      belowAssumed <- LogicError.lift(Kernel.assume(belowZero))
      negated <- reals.term("-x:real")
      shifted <- rules.specAll(ltAdd, List(x, zero, negated))
        .flatMap(rules.mp(_, belowAssumed))
      cancels <- ring.prove("x:real + -x = 0")
      absorbs <- ring.prove("0 + -x:real = -x")
      positiveNegation <- Conv.rewriteSides(cancels, absorbs, shifted)

      otherProduct <- rules.specAll(ltMul, List(c, negated))
      bothPositive <- rules.conjIntro(factorAssumed, positiveNegation)
      negativePart <- rules.mp(otherProduct, bothPositive)
      otherSide <- destLess(reals, negativePart.conclusion).map(_._2)

      summed <- rules.specAll(addNonNegative, List(product, otherSide))
        .flatMap(rules.mp(_, secondAssumed))
        .flatMap(rules.mp(_, negativePart))
      sumIsZero <- ring.prove("c:real * x + c * -x = 0")
      absurd <- Conv.rewriteRight(summed, sumIsZero)
      contradiction <- rules.notElim(never, absurd)
      third <- rules.falsityElim(goal, contradiction)

      tail <- reals
        .proposition("0 = x:real \\/ x:real < 0")
        .flatMap(term => LogicError.lift(Kernel.assume(term)))
      fromTail <- rules.disjElim(tail, second0, third)
      result <- rules.disjElim(cases, first, fromTail)

      innerDischarged <- rules.disch(second, result)
      outerDischarged <- rules.disch(factor, innerDischarged)
      general <- rules.genAll(outerDischarged, List(c, x))
    } yield general
  }

  /** `|- !x y. x <= y ==> 0 <= y - x` */
  def leToZero(
    ring: Ring,
    cases: Kernel.Thm,
    ofLt: Kernel.Thm,
    ofEq: Kernel.Thm,
    toZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      zero <- reals.term("0")
      difference <- reals.term("y:real - x:real")

      premise <- reals.proposition("x:real <= y:real")
      assumed <- LogicError.lift(Kernel.assume(premise))
      split <- rules.specAll(cases, List(x, y)).flatMap(rules.mp(_, assumed))

      strict <- reals.proposition("x:real < y:real")
      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      positive <- rules.specAll(toZero, List(x, y)).flatMap(rules.mp(_, strictAssumed))
      whenStrict <- rules.specAll(ofLt, List(zero, difference)).flatMap(rules.mp(_, positive))

      equated <- reals.proposition("x:real = y:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      shifted <- rewriteTerm(reals, equatedAssumed, difference)
      collapses <- ring.prove("y:real - y = 0")
      isZero <- Conv.trans(shifted, collapses)
      backwards <- Conv.sym(isZero)
      whenEqual <- rules.specAll(ofEq, List(zero, difference)).flatMap(rules.mp(_, backwards))

      result <- rules.disjElim(split, whenStrict, whenEqual)

      discharged <- rules.disch(premise, result)
      general <- rules.genAll(discharged, List(x, y))
    } yield general
  }

  /**
   * `|- !x y. 0 <= y - x ==> x <= y`, the way back.
   *
   * The branch where the difference is zero is the one worth reading: it adds `x` to both sides of
   * `0 = y - x` by congruence and lets the ring tactic see that the two sides are `x` and `y`.
   */
  def leFromZero(
    ring: Ring,
    cases: Kernel.Thm,
    ofLt: Kernel.Thm,
    ofEq: Kernel.Thm,
    fromZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      zero <- reals.term("0")
      difference <- reals.term("y:real - x:real")
      plus <- LogicError.lift(reals.theory.constant(Real.Addition, binary))

      premise <- reals.proposition("0 <= y:real - x:real")
      assumed <- LogicError.lift(Kernel.assume(premise))
      split <- rules.specAll(cases, List(zero, difference)).flatMap(rules.mp(_, assumed))

      strict <- reals.proposition("0 < y:real - x:real")
      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      lessThan <- rules.specAll(fromZero, List(x, y)).flatMap(rules.mp(_, strictAssumed))
      whenStrict <- rules.specAll(ofLt, List(x, y)).flatMap(rules.mp(_, lessThan))

      equated <- reals.proposition("0 = y:real - x:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      onLeft <- LogicError.lift(Kernel.mkComb(Conv.refl(plus), equatedAssumed))
      added <- LogicError.lift(Kernel.mkComb(onLeft, Conv.refl(x)))
      absorbs <- ring.prove("0 + x:real = x")
      restores <- ring.prove("(y:real - x:real) + x = y")
      backwards <- Conv.sym(absorbs)
      equal <- Conv.trans(backwards, added).flatMap(Conv.trans(_, restores))
      whenEqual <- rules.specAll(ofEq, List(x, y)).flatMap(rules.mp(_, equal))

      result <- rules.disjElim(split, whenStrict, whenEqual)

      discharged <- rules.disch(premise, result)
      general <- rules.genAll(discharged, List(x, y))
    } yield general
  }

  /**
   * `|- !x y. ~(x < y) ==> y <= x` and `|- !x y. ~(x <= y) ==> y < x`, from trichotomy.
   *
   * One function for the pair because the derivation is the same three-way split twice, with the
   * middle case going to a different lemma each time: `LE_OF_EQ` where the conclusion is weak,
   * and the equation refuting the negated hypothesis where it is strict. Writing them apart would
   * be two copies of the split and one place for it to drift.
   *
   * **No classical step anywhere**, which is the fact worth knowing before reaching for these: a
   * negated comparison becomes a positive one here because `LT_TOTAL` already put all three cases
   * on the table, so the negation does no work except discard one of them. `Order` sits over the
   * axiom-free logic deliberately, and these two do not disturb that.
   */
  def leOfNotLt(
    reals: RealTheory,
    ofLt: Kernel.Thm,
    ofEq: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    fromNegatedComparison(reals, ofLt, ofEq, strict = false)

  /** `|- !x y. ~(x <= y) ==> y < x`, the same split with the strict conclusion. */
  def ltOfNotLe(
    reals: RealTheory,
    ofLt: Kernel.Thm,
    ofEq: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    fromNegatedComparison(reals, ofLt, ofEq, strict = true)

  /**
   * The split both of the two above are, with the one case that differs decided by `strict`.
   *
   * `LT_TOTAL` gives `x < y \/ x = y \/ y < x`. Under the negated hypothesis the first case is
   * refuted, since `x < y` gives the very comparison assumed absent, directly where it is strict
   * and through `LE_OF_LT` where it is weak. The third case IS the conclusion where it is strict
   * and reaches it through `LE_OF_LT` where it is weak. Only the middle case differs in kind: an
   * equation gives the weak conclusion by `LE_OF_EQ`, and refutes the hypothesis where the
   * conclusion is strict.
   */
  private def fromNegatedComparison(
    reals: RealTheory,
    ofLt: Kernel.Thm,
    ofEq: Kernel.Thm,
    strict: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val logic = reals.logic
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      trichotomy <- reals.law("LT_TOTAL")

      absent <- reals.proposition(if (strict) "x:real <= y:real" else "x:real < y:real")
      goal <- reals.proposition(if (strict) "y:real < x:real" else "y:real <= x:real")
      negated <- logic.mkNot(absent)
      assumed <- LogicError.lift(Kernel.assume(negated))

      split <- rules.specAll(trichotomy, List(x, y))

      // `x < y`: the hypothesis says this cannot be, directly or through `LE_OF_LT`.
      below <- reals.proposition("x:real < y:real")
      fromBelow <- for {
        belowAssumed <- LogicError.lift(Kernel.assume(below))
        present <-
          if (strict) rules.specAll(ofLt, List(x, y)).flatMap(rules.mp(_, belowAssumed))
          else Right(belowAssumed)
        clash <- rules.notElim(assumed, present)
        anything <- rules.falsityElim(goal, clash)
      } yield anything

      // `x = y`: the weak conclusion follows, and the strict one refutes the hypothesis instead.
      equated <- reals.proposition("x:real = y:real")
      fromEquated <- for {
        equatedAssumed <- LogicError.lift(Kernel.assume(equated))
        result <-
          if (strict)
            rules
              .specAll(ofEq, List(x, y))
              .flatMap(rules.mp(_, equatedAssumed))
              .flatMap(rules.notElim(assumed, _))
              .flatMap(rules.falsityElim(goal, _))
          else
            Conv
              .sym(equatedAssumed)
              .flatMap(reversed => rules.specAll(ofEq, List(y, x)).flatMap(rules.mp(_, reversed)))
      } yield result

      // `y < x`: the strict conclusion is exactly this, and the weak one is one step from it.
      above <- reals.proposition("y:real < x:real")
      fromAbove <- for {
        aboveAssumed <- LogicError.lift(Kernel.assume(above))
        result <-
          if (strict) Right(aboveAssumed)
          else rules.specAll(ofLt, List(y, x)).flatMap(rules.mp(_, aboveAssumed))
      } yield result

      tail <- reals.proposition("x:real = y:real \\/ y:real < x:real")
      tailAssumed <- LogicError.lift(Kernel.assume(tail))
      fromTail <- rules.disjElim(tailAssumed, fromEquated, fromAbove)
      settled <- rules.disjElim(split, fromBelow, fromTail)
      result <- rules
        .disch(negated, settled)
        .flatMap(rules.gen(y, _))
        .flatMap(rules.gen(x, _))
    } yield result
  }

  /**
   * `|- !x y. x <= y ==> y <= x ==> x = y`.
   *
   * Antisymmetry, and the only way an equality is ever concluded from inequalities: it is what lets
   * a goal like `v0 + 5 + (v1 - 3) = 10` be proved by bounding it on both sides. Two case analyses,
   * where three of the four branches hand back an equality that is already there and the fourth,
   * `x < y` with `y < x`, closes by transitivity and irreflexivity.
   */
  def antisymmetric(
    reals: RealTheory,
    cases: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      irreflexive <- reals.law("LT_IRREFLEXIVE")
      transitive <- reals.law("LT_TRANSITIVE")

      goal <- reals.proposition("x:real = y:real")
      first <- reals.proposition("x:real <= y:real")
      firstAssumed <- LogicError.lift(Kernel.assume(first))
      second <- reals.proposition("y:real <= x:real")
      secondAssumed <- LogicError.lift(Kernel.assume(second))

      split <- rules.specAll(cases, List(x, y)).flatMap(rules.mp(_, firstAssumed))
      other <- rules.specAll(cases, List(y, x)).flatMap(rules.mp(_, secondAssumed))

      // `x = y` is the goal.
      equated <- LogicError.lift(Kernel.assume(goal))

      // `x < y`, and then the second premise decides it.
      below <- reals.proposition("x:real < y:real")
      belowAssumed <- LogicError.lift(Kernel.assume(below))

      above <- reals.proposition("y:real < x:real")
      aboveAssumed <- LogicError.lift(Kernel.assume(above))
      cycle <- rules.specAll(transitive, List(x, y, x))
      both <- rules.conjIntro(belowAssumed, aboveAssumed)
      absurd <- rules.mp(cycle, both)
      never <- rules.spec(x, irreflexive)
      contradiction <- rules.notElim(never, absurd)
      fromCycle <- rules.falsityElim(goal, contradiction)

      reversed <- reals.proposition("y:real = x:real")
      reversedAssumed <- LogicError.lift(Kernel.assume(reversed))
      fromReversed <- Conv.sym(reversedAssumed)

      whenBelow <- rules.disjElim(other, fromCycle, fromReversed)
      result <- rules.disjElim(split, whenBelow, equated)

      innerDischarged <- rules.disch(second, result)
      outerDischarged <- rules.disch(first, innerDischarged)
      general <- rules.genAll(outerDischarged, List(x, y))
    } yield general
  }

  /**
   * `|- !x y z w. x <= y ==> z <= w ==> x + z <= y + w`.
   *
   * Both inequalities are moved to the form `0 <= e`, where adding them is [[addNonNegatives]] and
   * nothing else, and the sum is moved back. The one step that is not bookkeeping is the ring
   * identity `(y - x) + (w - z) = (y + w) - (x + z)`, which is where "the difference of the sums is
   * the sum of the differences" is actually used; every other line is [[leToZero]] and
   * [[leFromZero]] carrying the statement in and out of that form.
   *
   * Four variables, so the printer's fourth name appears: it names binders `x, y, z, u, v, w` by
   * depth, and what prints is `!x. !y. !z. !u.`
   */
  def addLe(
    ring: Ring,
    weakToZero: Kernel.Thm,
    weakFromZero: Kernel.Thm,
    addNonNegatives: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)
    val z = Term.variable("z", real)
    val w = Term.variable("w", real)

    for {
      first <- reals.proposition("x:real <= y:real")
      firstAssumed <- LogicError.lift(Kernel.assume(first))
      second <- reals.proposition("z:real <= w:real")
      secondAssumed <- LogicError.lift(Kernel.assume(second))

      leftGap <- rules.specAll(weakToZero, List(x, y)).flatMap(rules.mp(_, firstAssumed))
      rightGap <- rules.specAll(weakToZero, List(z, w)).flatMap(rules.mp(_, secondAssumed))

      leftDifference <- reals.term("y:real - x:real")
      rightDifference <- reals.term("w:real - z:real")
      summed <- rules
        .specAll(addNonNegatives, List(leftDifference, rightDifference))
        .flatMap(rules.mp(_, leftGap))
        .flatMap(rules.mp(_, rightGap))

      rearranged <- ring.prove(
        "(y:real - x:real) + (w:real - z:real) = (y + w) - (x + z)"
      )
      onGoal <- Conv.rewriteRight(summed, rearranged)

      left <- reals.term("x:real + z:real")
      right <- reals.term("y:real + w:real")
      result <- rules.specAll(weakFromZero, List(left, right)).flatMap(rules.mp(_, onGoal))

      innerDischarged <- rules.disch(second, result)
      outerDischarged <- rules.disch(first, innerDischarged)
      general <- rules.genAll(outerDischarged, List(x, y, z, w))
    } yield general
  }

  /* --------------------------------------------------- multiplying an inequality */

  /**
   * `|- !c x y. 0 <= c ==> x <= y ==> x * c <= y * c`.
   *
   * The same three moves [[addLe]] makes and it is worth reading beside it: carry the inequality to
   * a statement about a difference, do the arithmetic there, and carry it back. What differs is the
   * middle step, which is [[multiplyNonNegatives]] rather than [[addNonNegatives]] and is the one
   * line that could not have been written before that lemma existed.
   *
   * The ring identity is `(y - x) * c = y * c - x * c`, which is distribution over a subtraction
   * and is inside what RING decides, so no case analysis appears here at all: the whole of the case
   * analysis this lemma needs was paid once, in the lemma it calls.
   */
  def multiplyLe(
    ring: Ring,
    weakToZero: Kernel.Thm,
    weakFromZero: Kernel.Thm,
    multiplyNonNegatives: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val c = Term.variable("c", real)
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      nonNegative <- reals.proposition("0 <= c:real")
      nonNegativeAssumed <- LogicError.lift(Kernel.assume(nonNegative))
      ordered <- reals.proposition("x:real <= y:real")
      orderedAssumed <- LogicError.lift(Kernel.assume(ordered))

      gap <- rules.specAll(weakToZero, List(x, y)).flatMap(rules.mp(_, orderedAssumed))
      difference <- reals.term("y:real - x:real")
      scaled <- rules
        .specAll(multiplyNonNegatives, List(difference, c))
        .flatMap(rules.mp(_, gap))
        .flatMap(rules.mp(_, nonNegativeAssumed))

      distributed <- ring.prove("(y:real - x:real) * c:real = y * c - x * c")
      onGoal <- Conv.rewriteRight(scaled, distributed)

      left <- reals.term("x:real * c:real")
      right <- reals.term("y:real * c:real")
      result <- rules.specAll(weakFromZero, List(left, right)).flatMap(rules.mp(_, onGoal))

      innerDischarged <- rules.disch(ordered, result)
      outerDischarged <- rules.disch(nonNegative, innerDischarged)
      general <- rules.genAll(outerDischarged, List(c, x, y))
    } yield general
  }

  /* --------------------------------------------------------- the reciprocal */

  /**
   * `|- !x y. 0 < x ==> x <= y ==> inv y <= inv x`.
   *
   * Multiply the hypothesis by `inv x * inv y` and read both sides back through `MUL_INVERSE`. The
   * factor is non-negative because both of its factors are positive, and the second of those is
   * where the work is: `0 < y` does not come with the hypothesis and has to be derived from
   * `0 < x` and `x <= y`.
   *
   * **That derivation is a case split and not a transitivity step**, which is the thing to know
   * before reading it. `LT_TRANSITIVE` is an axiom and takes two *strict* inequalities; what is in
   * hand is one strict and one weak, so [[leCases]] opens the weak one into "strictly below" or
   * "equal", the first branch is the axiom and the second rewrites `0 < x` with `x = y`. This
   * repository has no `LT_LE_TRANSITIVE`, and adding one would be the same three lines under a
   * name.
   *
   * The two reads back are ring identities in three atoms, `x`, `inv x` and `inv y`, with
   * `x * inv x` replaced by `1`. RING treats `inv x` as an atom, which is exactly what makes this
   * work: nothing here asks the normal form to know anything about inverses, and the one fact about
   * them that is used arrives as a rewrite from `MUL_INVERSE`.
   */
  def inverseAntitone(
    ring: Ring,
    notZero: Kernel.Thm,
    inversePositive: Kernel.Thm,
    cases: Kernel.Thm,
    ofLt: Kernel.Thm,
    multiplyLe: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val logic = reals.logic
    val rules = logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      positive <- reals.proposition("0 < x:real")
      positiveAssumed <- LogicError.lift(Kernel.assume(positive))
      ordered <- reals.proposition("x:real <= y:real")
      orderedAssumed <- LogicError.lift(Kernel.assume(ordered))

      // `0 < y`, by cases on the weak inequality: the axiom, or a rewrite.
      opened <- rules.specAll(cases, List(x, y)).flatMap(rules.mp(_, orderedAssumed))
      strictly <- reals.proposition("x:real < y:real")
      strictlyAssumed <- LogicError.lift(Kernel.assume(strictly))
      zero <- reals.term("0:real")
      transitive <- reals.law("LT_TRANSITIVE")
      fromStrict <- rules
        .conjIntro(positiveAssumed, strictlyAssumed)
        .flatMap(pair => rules.specAll(transitive, List(zero, x, y)).flatMap(rules.mp(_, pair)))
      equally <- reals.proposition("x:real = y:real")
      equallyAssumed <- LogicError.lift(Kernel.assume(equally))
      fromEqual <- Rewrite.Rule
        .all(logic, Vector(equallyAssumed))
        .flatMap(Rewrite.inTheorem(_, positiveAssumed))
      positiveRight <- rules.disjElim(opened, fromStrict, fromEqual)

      // The factor, and that it is at least zero.
      leftInverse <- reals.term("inv (x:real)")
      rightInverse <- reals.term("inv (y:real)")
      inverseLeft <- rules.spec(x, inversePositive).flatMap(rules.mp(_, positiveAssumed))
      inverseRight <- rules.spec(y, inversePositive).flatMap(rules.mp(_, positiveRight))
      product <- reals.term("inv (x:real) * inv (y:real)")
      strictFactor <- rules
        .conjIntro(inverseLeft, inverseRight)
        .flatMap(pair =>
          reals
            .law("LT_MUL")
            .flatMap(rules.specAll(_, List(leftInverse, rightInverse)))
            .flatMap(rules.mp(_, pair))
        )
      factor <- rules.specAll(ofLt, List(zero, product)).flatMap(rules.mp(_, strictFactor))

      // The hypothesis, scaled.
      scaled <- rules
        .specAll(multiplyLe, List(product, x, y))
        .flatMap(rules.mp(_, factor))
        .flatMap(rules.mp(_, orderedAssumed))

      // And each side read back, `x * inv x` and `y * inv y` both being one.
      inverseAxiom <- reals.law("MUL_INVERSE")
      leftNotZero <- rules.spec(x, notZero).flatMap(rules.mp(_, positiveAssumed))
      rightNotZero <- rules.spec(y, notZero).flatMap(rules.mp(_, positiveRight))
      leftIsOne <- rules.spec(x, inverseAxiom).flatMap(rules.mp(_, leftNotZero))
      rightIsOne <- rules.spec(y, inverseAxiom).flatMap(rules.mp(_, rightNotZero))

      leftShape <- ring.prove("x:real * (inv (x:real) * inv (y:real)) = (x * inv x) * inv y")
      rightShape <- ring.prove("y:real * (inv (x:real) * inv (y:real)) = (y * inv y) * inv x")
      reshaped <- Conv.rewriteSides(leftShape, rightShape, scaled)
      substituted <- Rewrite.Rule
        .all(logic, Vector(leftIsOne, rightIsOne))
        .flatMap(Rewrite.inTheorem(_, reshaped))
      absorbLeft <- ring.prove("1 * inv (y:real) = inv y")
      absorbRight <- ring.prove("1 * inv (x:real) = inv x")
      result <- Conv.rewriteSides(absorbLeft, absorbRight, substituted)

      innerDischarged <- rules.disch(ordered, result)
      outerDischarged <- rules.disch(positive, innerDischarged)
      general <- rules.genAll(outerDischarged, List(x, y))
    } yield general
  }

  /* ------------------------------------------------------------- the square */

  /**
   * `|- !x. 0 <= x * x`.
   *
   * Trichotomy at `0` and `x`, and this is the shape [[cancelPositive]] reads as the worked
   * example, with one difference: no branch is a contradiction, so all three of them prove the
   * goal rather than two of them refusing their own case.
   *
   *  - `0 < x` is `LT_MUL` at `x` and `x`, and the goal is the weaker of the two;
   *  - `0 = x` makes the product zero, and zero is at least zero;
   *  - `x < 0` makes `-x` positive, `LT_MUL` at `-x` and `-x` gives `0 < -x * -x`, and `-x * -x`
   *    is `x * x` by ring reasoning, so the *negative* case is where the product is strictly
   *    positive and the *zero* case is the only one that needs `<=` at all.
   *
   * The third branch is the one to read twice, because it is the step nothing below the order can
   * take: `LT_MUL` says a product of positives is positive and says nothing about a product of
   * negatives, and turning the second into the first is `LT_ADD` moving `x < 0` to `0 < -x` and
   * then one ring identity. That is the same move [[cancelPositive]] and [[cancelNonNegative]]
   * make, and it is the whole content of "the square of a negative is positive".
   */
  def squareNonNegative(
    ring: Ring,
    ofLt: Kernel.Thm,
    ofEq: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val x = Term.variable("x", real)

    for {
      ltAdd <- reals.law("LT_ADD")
      ltMul <- reals.law("LT_MUL")
      trichotomy <- reals.law("LT_TOTAL")

      zero <- reals.term("0")
      square <- reals.term("x:real * x")

      cases <- rules.specAll(trichotomy, List(zero, x))

      // `0 < x`: the axiom, at the same factor twice.
      strict <- reals.proposition("0 < x:real")
      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      positive <- rules
        .specAll(ltMul, List(x, x))
        .flatMap(instance =>
          rules.conjIntro(strictAssumed, strictAssumed).flatMap(rules.mp(instance, _))
        )
      first <- rules.specAll(ofLt, List(zero, square)).flatMap(rules.mp(_, positive))

      // `0 = x`: the product is zero, and the goal is an equality read as an inequality.
      equated <- reals.proposition("0 = x:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      reversed <- Conv.sym(equatedAssumed)
      shifted <- rewriteTerm(reals, reversed, square)
      collapses <- ring.prove("0 * 0 = 0")
      isZero <- Conv.trans(shifted, collapses)
      backwards <- Conv.sym(isZero)
      second <- rules.specAll(ofEq, List(zero, square)).flatMap(rules.mp(_, backwards))

      // `x < 0`: `-x` is positive, and its square is the same term.
      belowZero <- reals.proposition("x:real < 0")
      belowAssumed <- LogicError.lift(Kernel.assume(belowZero))
      negated <- reals.term("-x:real")
      moved <- rules.specAll(ltAdd, List(x, zero, negated)).flatMap(rules.mp(_, belowAssumed))
      cancels <- ring.prove("x:real + -x = 0")
      absorbs <- ring.prove("0 + -x:real = -x")
      positiveNegation <- Conv.rewriteSides(cancels, absorbs, moved)

      negatedSquare <- rules
        .specAll(ltMul, List(negated, negated))
        .flatMap(instance =>
          rules.conjIntro(positiveNegation, positiveNegation).flatMap(rules.mp(instance, _))
        )
      sameSquare <- ring.prove("-x:real * -x = x * x")
      onGoal <- Conv.rewriteRight(negatedSquare, sameSquare)
      third <- rules.specAll(ofLt, List(zero, square)).flatMap(rules.mp(_, onGoal))

      tail <- reals
        .proposition("0 = x:real \\/ x:real < 0")
        .flatMap(term => LogicError.lift(Kernel.assume(term)))
      fromTail <- rules.disjElim(tail, second, third)
      result <- rules.disjElim(cases, first, fromTail)

      general <- rules.gen(x, result)
    } yield general
  }

  /**
   * `|- !x. x * x = 0 ==> x = 0`, by the three cases of [[squareNonNegative]].
   *
   * The strictly positive square is built the same way in both outer cases, `LT_MUL` at `x` or at
   * `-x`, and each is then contradicted by the hypothesis in the same way, so the contradiction is
   * written once.
   */
  def squareZero(ring: Ring): Either[LogicError, Kernel.Thm] = {
    val reals = ring.reals
    val rules = reals.logic.rules
    val x = Term.variable("x", real)

    for {
      ltAdd <- reals.law("LT_ADD")
      ltMul <- reals.law("LT_MUL")
      trichotomy <- reals.law("LT_TOTAL")
      irreflexive <- reals.law("LT_IRREFLEXIVE")

      zero <- reals.term("0")
      vanishes <- reals.proposition("x:real * x = 0")
      vanishesAssumed <- LogicError.lift(Kernel.assume(vanishes))
      goal <- reals.proposition("x:real = 0")
      zeroNotBelowZero <- rules.spec(zero, irreflexive)

      // `0 < x * x` and the hypothesis say `0 < 0`.
      absurd = (positive: Kernel.Thm) =>
        for {
          collapsed <- Conv.rewriteRight(positive, vanishesAssumed)
          falsity <- rules.notElim(zeroNotBelowZero, collapsed)
          out <- rules.falsityElim(goal, falsity)
        } yield out

      cases <- rules.specAll(trichotomy, List(zero, x))

      // `0 < x`: the axiom at the same factor twice.
      strict <- reals.proposition("0 < x:real")
      strictAssumed <- LogicError.lift(Kernel.assume(strict))
      positive <- rules
        .specAll(ltMul, List(x, x))
        .flatMap(instance =>
          rules.conjIntro(strictAssumed, strictAssumed).flatMap(rules.mp(instance, _))
        )
      first <- absurd(positive)

      // `0 = x`: the goal turned round.
      equated <- reals.proposition("0 = x:real")
      equatedAssumed <- LogicError.lift(Kernel.assume(equated))
      second <- Conv.sym(equatedAssumed)

      // `x < 0`: `-x` is positive and its square is the same term.
      belowZero <- reals.proposition("x:real < 0")
      belowAssumed <- LogicError.lift(Kernel.assume(belowZero))
      negated <- reals.term("-x:real")
      moved <- rules.specAll(ltAdd, List(x, zero, negated)).flatMap(rules.mp(_, belowAssumed))
      cancels <- ring.prove("x:real + -x = 0")
      absorbs <- ring.prove("0 + -x:real = -x")
      positiveNegation <- Conv.rewriteSides(cancels, absorbs, moved)
      negatedSquare <- rules
        .specAll(ltMul, List(negated, negated))
        .flatMap(instance =>
          rules.conjIntro(positiveNegation, positiveNegation).flatMap(rules.mp(instance, _))
        )
      sameSquare <- ring.prove("-x:real * -x = x * x")
      onGoal <- Conv.rewriteRight(negatedSquare, sameSquare)
      third <- absurd(onGoal)

      tail <- reals
        .proposition("0 = x:real \\/ x:real < 0")
        .flatMap(term => LogicError.lift(Kernel.assume(term)))
      fromTail <- rules.disjElim(tail, second, third)
      result <- rules.disjElim(cases, first, fromTail)

      discharged <- rules.disch(vanishes, result)
      general <- rules.gen(x, discharged)
    } yield general
  }

  /* ----------------------------------------------------------------- helpers */

  /** The two sides of `a <= b`. */
  def destLessEqual(reals: Signature, term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(Const(Real.NonStrictOrder, _), left), right) => Right((left, right))
    case other => Left(NotOfForm("a non-strict inequality", other))
  }

  /** The two sides of an inequality of either kind, and whether it was the strict one. */
  def destOrder(reals: Signature, term: Term): Option[(Term, Term, Boolean)] = term match {
    case App(App(Const(Real.Order, _), left), right) => Some((left, right, true))
    case App(App(Const(Real.NonStrictOrder, _), left), right) => Some((left, right, false))
    case _ => None
  }

  /** The `<=` constant. */
  def lessEqualConstant(reals: Signature): Either[LogicError, Term] =
    LogicError.lift(reals.theory.constant(Real.NonStrictOrder, relation))

  /** `|- t = t'`, by one pass of rewriting with an equation. */
  private def rewriteTerm(
    reals: Signature,
    equation: Kernel.Thm,
    term: Term
  ): Either[LogicError, Kernel.Thm] =
    Rewrite.Rule
      .of(reals.logic, equation)
      .flatMap(rule => Rewrite.depthConv(Rewrite.rewriteConv(rule))(term))

}
