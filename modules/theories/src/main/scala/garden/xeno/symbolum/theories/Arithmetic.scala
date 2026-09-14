package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Arithmetic on numerals, digit by digit.
 *
 * Addition and multiplication both work the same way: a handful of lemmas say what the result is
 * one binary digit at a time, and rewriting with them bottom-up turns `m + n` or `m * n` into the
 * numeral for the answer. What that costs follows the number of digits and not the size of the
 * numbers: measured on 2026-09-05, about three passes per digit for a sum and six and a half for a
 * product, which is where [[Arithmetic.NumeralLimit]] comes from. Every lemma is proved from the
 * sixteen axioms; nothing here is assumed.
 *
 * == How the lemmas are proved ==
 *
 * Each unfolds, by the definitions of the two bits, into an identity of a commutative ring:
 * `BIT1 x * y = BIT0 (x * y) + y` becomes `((x + x) + 1) * y = (x * y + x * y) + y`. Distributing
 * the products over the sums and then sorting both sides brings them to the same term, and that is
 * the proof. [[ringNormalisation]] is that procedure.
 *
 * Two things it cannot do, and both are done by hand below because they are what it rests on.
 * Exchanging neighbours in a sum is what lets sorting happen at all, and neither axiom gives it
 * alone. And `x * 0 = 0` is not an axiom of a field and does not follow from rearranging: it needs
 * the additive inverse and a cancellation, which is the one derivation in this file that reads
 * like a proof on paper.
 */
final class Arithmetic private (
  val reals: RealTheory,
  val lemmas: Map[String, Kernel.Thm],
  /** The ring normal form, shared with the tactic that proves identities. */
  val normalisation: Rewrite.Conversion,
  private val additionRules: Vector[Rewrite.Rule],
  private val multiplicationRules: Vector[Rewrite.Rule]
) {

  /** The lemma named, as proved when this was built. */
  def lemma(name: String): Either[LogicError, Kernel.Thm] =
    lemmas.get(name).toRight(MissingDefinition(name))

  /** `|- m + n = m+n`, for numerals. */
  def add(
    left: BigInt,
    right: BigInt,
    limit: Int = Arithmetic.NumeralLimit
  ): Either[LogicError, Kernel.Thm] =
    compute(additionRules, "+", left, right, left + right, limit)

  /**
   * `|- m * n = m*n`, for numerals.
   *
   * The rules include the ones for addition, because multiplying by an odd digit leaves a sum
   * behind: `BIT1 x * y` is `BIT0 (x * y) + y`, and that `+ y` is reduced by the same lemmas that
   * do addition.
   */
  def multiply(
    left: BigInt,
    right: BigInt,
    limit: Int = Arithmetic.NumeralLimit
  ): Either[LogicError, Kernel.Thm] =
    compute(multiplicationRules, "*", left, right, left * right, limit)

  private def compute(
    rules: Vector[Rewrite.Rule],
    operator: String,
    left: BigInt,
    right: BigInt,
    expected: BigInt,
    limit: Int
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- reals.term(s"$left $operator $right")
      answer <- Numeral.of(reals, expected)
      theorem <- Rewrite.prove(rules, statement, answer, limit)
    } yield theorem
}

object Arithmetic {

  /**
   * Passes of rewriting the numeral procedure is allowed.
   *
   * What a product costs follows the digits of its operands rather than their size, and the rate
   * is measured rather than assumed. Found on 2026-09-05 by bisecting on the limit, which is what
   * the parameter on [[Arithmetic.add]] and [[Arithmetic.multiply]] is for: a product needs 6
   * passes at one digit, 14 at two, 40 at six and 80 at twelve, and a sum needs 4, 20 and 40 at
   * one, six and twelve. So it is about six and a half passes per digit for a product and three
   * for a sum, and not the one per digit this file claimed until that measurement was taken.
   *
   * Twelve digits is where `Oracle.NumeralBudget` puts what a caller with a deadline should hand
   * over, so 80 is what this has to reach; the bound is four hundred, which covers about sixty
   * digits and is a guard against a rule set that does not terminate rather than a budget anyone
   * approaches. `ArithmeticSpec` pins the six-digit figure, cheaply, and the method with it.
   *
   * It was one constant with [[NormalisationLimit]] until 2026-09-05, which made a change to
   * either of two unrelated procedures a change to both.
   */
  val NumeralLimit: Int = 400

  /**
   * Passes of rewriting the expanding normalisation is allowed.
   *
   * A different procedure with a different unit: a pass here rewrites everywhere it can at once,
   * and what it has to reach is a normal form rather than a digit. Measured the same way on
   * 2026-09-05: every lemma this form has to prove, its own eleven and the six structural ones of
   * the collecting form, normalises in 5 passes; a cubic identity takes 8 and `10 * x + 10 * x =
   * 20 * x` takes 11.
   *
   * What sets the bound is none of those. It is `12 * 12 = 144`, which takes 72, because this form
   * does arithmetic by unfolding the numerals and a product of two-digit numerals becomes a sum of
   * a hundred and forty-four terms. That is the form's whole character and is why `Ring.standard`
   * is the other one.
   */
  val NormalisationLimit: Int = 400

  /* ------------------------------------------------------------------- lemmas */

  /**
   * The addition table of the binary digits, proved by normalising both sides.
   *
   * The cases with `1` are there because `1` is a constant of the field rather than a bit applied
   * to something. Making it `BIT1 0` would make these disappear and would take the multiplicative
   * identity out of the axioms, where a reader has to recognise it.
   */
  val AdditionLemmas: Vector[(String, String)] = Vector(
    "ADD_BIT0_BIT0" -> "BIT0 x + BIT0 y = BIT0 (x + y)",
    "ADD_BIT0_BIT1" -> "BIT0 x + BIT1 y = BIT1 (x + y)",
    "ADD_BIT1_BIT0" -> "BIT1 x + BIT0 y = BIT1 (x + y)",
    "ADD_BIT1_BIT1" -> "BIT1 x + BIT1 y = BIT0 ((x + y) + 1)",

    "ADD_BIT0_ONE" -> "BIT0 x + 1 = BIT1 x",
    "ADD_BIT1_ONE" -> "BIT1 x + 1 = BIT0 (x + 1)",
    "ADD_ONE_BIT0" -> "1 + BIT0 y = BIT1 y",
    "ADD_ONE_BIT1" -> "1 + BIT1 y = BIT0 (y + 1)",
    "ADD_ONE_ONE" -> "1 + 1 = BIT0 1"
  )

  /**
   * Multiplication, recursing on the left factor only.
   *
   * Two lemmas cover every case that is a bit, and the base cases are `1` and `0`, which are
   * derived rather than normalised. Recursing on one side is enough and halves the table.
   */
  val MultiplicationLemmas: Vector[(String, String)] = Vector(
    "MUL_BIT0" -> "BIT0 x * y = BIT0 (x * y)",
    "MUL_BIT1" -> "BIT1 x * y = BIT0 (x * y) + y"
  )

  val ZeroOnTheRight: String = "ADD_ZERO_RIGHT"
  val ZeroOnTheLeft: String = "ADD_ZERO_LEFT"
  val DoubledZero: String = "BIT0_ZERO"
  val OneOnTheLeft: String = "MUL_ONE_LEFT"
  val OneOnTheRight: String = "MUL_ONE_RIGHT"
  val TimesZero: String = "MUL_ZERO_RIGHT"
  val ZeroTimes: String = "MUL_ZERO_LEFT"
  val Exchange: String = "ADD_EXCHANGE"
  val MulExchange: String = "MUL_EXCHANGE"
  val RightDistribute: String = "RIGHT_DISTRIBUTE"
  val InverseOnTheLeft: String = "ADD_INVERSE_LEFT"
  val CancelMiddle: String = "ADD_CANCEL"
  val UniqueInverse: String = "UNIQUE_INVERSE"
  val NegNeg: String = "NEG_NEG"
  val NegAdd: String = "NEG_ADD"
  val NegMulLeft: String = "NEG_MUL_LEFT"
  val NegMulRight: String = "NEG_MUL_RIGHT"
  val NegZero: String = "NEG_ZERO"

  /**
   * The order the addition rules are tried in.
   *
   * `BIT0_ZERO` last and present at all because multiplying by zero leaves a tower of doubled
   * zeros: `BIT0 (BIT0 0)` denotes zero and is not how zero is written.
   */
  private val AdditionOrder: Vector[String] =
    AdditionLemmas.map { case (name, _) => name } :+ ZeroOnTheLeft :+ ZeroOnTheRight :+ DoubledZero

  private val MultiplicationOrder: Vector[String] =
    MultiplicationLemmas.map { case (name, _) => name } :+ OneOnTheLeft :+ ZeroTimes

  /** Built once over the standard theory of the reals. */
  lazy val standard: Arithmetic =
    construct(Real.standard).fold(
      error => throw new IllegalStateException(s"the arithmetic does not build: ${error.message}"),
      identity
    )

  /** Prove everything, then assemble the two rule sets. */
  def construct(
    reals: RealTheory,
    limit: Int = NormalisationLimit
  ): Either[LogicError, Arithmetic] =
    for {
      // In three stages, because each needs the one before it. The facts that do not mention a
      // negation come first; the normalisation built from them is what proves that `-x + -y` is an
      // inverse of `x + y`; and only then can the negation lemmas join the normalisation.
      basic <- derivedFacts(reals)
      cancelling <- normalisationFrom(reals, basic, negation = false, limit)
      negations <- negationFacts(reals, cancelling)

      derived = basic ++ negations
      normalisation <- normalisationFrom(reals, derived, negation = true, limit)
      proved <- proveLemmas(reals, normalisation, AdditionLemmas ++ MultiplicationLemmas)

      all = derived ++ proved

      addition <- Rewrite.Rule.all(reals.logic, AdditionOrder.map(all))
      multiplication <- Rewrite.Rule.all(
        reals.logic,
        (MultiplicationOrder ++ AdditionOrder).map(all)
      )
    } yield new Arithmetic(reals, all, normalisation, addition, multiplication)

  /* ------------------------------------------------------- derivations by hand */

  /**
   * What the normalisation cannot prove, because it is what the normalisation is made of, or
   * because rearranging a sum never removes a term.
   */
  def derivedFacts(reals: RealTheory): Either[LogicError, Map[String, Kernel.Thm]] =
    for {
      addAssoc <- reals.axiom("ADD_ASSOC")
      addSym <- reals.axiom("ADD_SYM")
      mulAssoc <- reals.axiom("MUL_ASSOC")
      mulSym <- reals.axiom("MUL_SYM")
      addZero <- reals.axiom("ADD_ZERO")
      mulOne <- reals.axiom("MUL_ONE")
      distribute <- reals.axiom("DISTRIBUTE")

      addExchange <- exchange(reals, addAssoc, addSym)
      mulExchange <- exchange(reals, mulAssoc, mulSym)
      zeroLeft <- unitOnTheLeft(reals, addSym, addZero, "0")
      oneLeft <- unitOnTheLeft(reals, mulSym, mulOne, "1")
      rightDistribute <- rightDistribution(reals, mulSym, distribute)
      doubledZero <- doubledZeroIsZero(reals, addZero)
      timesZeroFact <- timesZero(reals, addZero, addSym, addAssoc, distribute)
      zeroTimes <- flip(reals, mulSym, timesZeroFact)
      inverseLeft <- inverseOnTheLeft(reals)
      cancel <- cancelMiddle(reals)
    } yield Map(
      InverseOnTheLeft -> inverseLeft,
      CancelMiddle -> cancel,
      ZeroOnTheRight -> addZero,
      ZeroOnTheLeft -> zeroLeft,
      OneOnTheRight -> mulOne,
      OneOnTheLeft -> oneLeft,
      Exchange -> addExchange,
      MulExchange -> mulExchange,
      RightDistribute -> rightDistribute,
      DoubledZero -> doubledZero,
      TimesZero -> timesZeroFact,
      ZeroTimes -> zeroTimes
    )

  /**
   * `|- !x. e op x = x`, from the axiom that says it for the other side.
   *
   * Rewriting is directional: a rule for `x + 0` does nothing to `0 + x`, so the mirror image has
   * to exist as its own theorem.
   */
  def unitOnTheLeft(
    reals: Signature,
    symmetry: Kernel.Thm,
    unitAxiom: Kernel.Thm,
    unitText: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)

    for {
      unit <- reals.term(unitText)
      symmetryAtUnit <- rules.spec(unit, symmetry)
      symmetryAtUnitAndX <- rules.spec(x, symmetryAtUnit)
      unitAtX <- rules.spec(x, unitAxiom)
      chained <- Conv.trans(symmetryAtUnitAndX, unitAtX)
      general <- rules.gen(x, chained)
    } yield general
  }

  /**
   * `|- !x y z. x op (y op z) = y op (x op z)`, which is what lets a sorted term be reached by
   * exchanging neighbours.
   *
   * Derived by hand because it is what the sorting needs and cannot come from the sorting:
   * commutativity alone cannot move a term past a parenthesis, and associativity alone cannot
   * exchange two terms.
   */
  def exchange(
    reals: Signature,
    associativity: Kernel.Thm,
    symmetry: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)
    val z = Term.variable("z", real)

    for {
      assocAtXYZ <- specialise(rules, associativity, List(x, y, z))
      assocAtYXZ <- specialise(rules, associativity, List(y, x, z))
      symAtXY <- specialise(rules, symmetry, List(x, y))

      regrouped <- Conv.sym(assocAtXYZ)
      regroupedRight <- rightOfConclusion(regrouped)
      exchanged <- rewriteWith(reals, symAtXY, regroupedRight)

      firstHalf <- Conv.trans(regrouped, exchanged)
      whole <- Conv.trans(firstHalf, assocAtYXZ)

      general <- generalise(reals, whole, List(x, y, z))
    } yield general
  }

  /** `|- !x y z. (x + y) * z = x * z + y * z`, from the left-handed axiom and commutativity. */
  def rightDistribution(
    reals: Signature,
    symmetry: Kernel.Thm,
    distribute: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)
    val z = Term.variable("z", real)

    for {
      sum <- reals.term("x:real + y:real")
      symAtSum <- specialise(rules, symmetry, List(sum, z))
      distributeAtZ <- specialise(rules, distribute, List(z, x, y))

      // (x + y) * z = z * (x + y) = z * x + z * y
      opened <- Conv.trans(symAtSum, distributeAtZ)
      openedRight <- rightOfConclusion(opened)

      symAtZX <- specialise(rules, symmetry, List(z, x))
      symAtZY <- specialise(rules, symmetry, List(z, y))
      firstSwapped <- rewriteWith(reals, symAtZX, openedRight)
      firstRight <- rightOfConclusion(firstSwapped)
      secondSwapped <- rewriteWith(reals, symAtZY, firstRight)

      whole <- chain(List(opened, firstSwapped, secondSwapped))
      general <- generalise(reals, whole, List(x, y, z))
    } yield general
  }

  /** `|- BIT0 0 = 0`, which multiplying by zero leaves behind. */
  def doubledZeroIsZero(reals: RealTheory, addZero: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      zero <- reals.term("0")
      definition <- reals.definition(Real.Bit0)
      unfolded <- Conv.unfold(definition, List(zero))
      zeroPlusZero <- reals.logic.rules.spec(zero, addZero)
      result <- Conv.trans(unfolded, zeroPlusZero)
    } yield result

  /**
   * `|- !x. x * 0 = 0`.
   *
   * Not an axiom of a field and not a consequence of rearranging, so this is the one derivation
   * here that reads like a proof on paper:
   *
   * {{{
   * x * 0 = x * (0 + 0)                 zero added to itself is zero
   *       = x * 0 + x * 0               distributing
   * so    x * 0 + -(x * 0) = (x * 0 + x * 0) + -(x * 0)
   * and the left side is 0 while the right side is x * 0, by the additive inverse
   * }}}
   *
   * It is the first use of the additive inverse axiom, and it is what makes multiplication by a
   * numeral terminate at zero rather than at a tower of doubled zeros.
   */
  def timesZero(
    reals: RealTheory,
    addZero: Kernel.Thm,
    addSym: Kernel.Thm,
    addAssoc: Kernel.Thm,
    distribute: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)

    for {
      inverseAxiom <- reals.axiom("ADD_INVERSE")
      zero <- reals.term("0")
      product <- reals.term("x:real * 0")
      negated <- reals.term("-(x:real * 0)")
      plus <- LogicError.lift(reals.theory.constant(Real.Addition, binary))

      // x * 0 = x * (0 + 0) = x * 0 + x * 0
      zeroSum <- rules.spec(zero, addZero)
      splitZero <- Conv.sym(zeroSum)
      expanded <- rewriteWith(reals, splitZero, product)
      distributed <- specialise(rules, distribute, List(x, zero, zero))
      doubled <- Conv.trans(expanded, distributed)

      // The same statement with the inverse added on the right of both sides.
      onFunction <- Conv.apTerm(plus, doubled)
      congruent <- LogicError.lift(Kernel.mkComb(onFunction, Conv.refl(negated)))

      inverse <- rules.spec(product, inverseAxiom)
      regrouped <- specialise(rules, addAssoc, List(product, product, negated))
      onProduct <- LogicError.lift(Term.app(plus, product))
      innerZero <- Conv.apTerm(onProduct, inverse)
      zeroOnTheRight <- rules.spec(product, addZero)

      backwards <- List(zeroOnTheRight, innerZero, regrouped, congruent).foldLeft(
        Right(Nil): Either[LogicError, List[Kernel.Thm]]
      ) { (acc, step) => acc.flatMap(steps => Conv.sym(step).map(_ :: steps)) }

      whole <- chain(backwards.reverse :+ inverse)
      general <- rules.gen(x, whole)
    } yield general
  }

  /** `|- !x y. y op x = z` from `|- !x y. x op y = z`, by commutativity. */
  def flip(
    reals: Signature,
    symmetry: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)

    for {
      atX <- rules.spec(x, theorem)
      sides <- Term.destEq(atX.conclusion).toRight(NotOfForm("an equation", atX.conclusion))
      operands <- destBinary(sides._1)
      swapped <- specialise(rules, symmetry, List(operands._2, operands._1))
      result <- Conv.trans(swapped, atX)
      general <- rules.gen(x, result)
    } yield general
  }

  /** `|- !x. -x + x = 0`, the inverse axiom from the other side. */
  def inverseOnTheLeft(reals: RealTheory): Either[LogicError, Kernel.Thm] =
    for {
      addSym <- reals.axiom("ADD_SYM")
      inverse <- reals.axiom("ADD_INVERSE")
      result <- flip(reals, addSym, inverse)
    } yield result

  /**
   * `|- !x z. x + (-x + z) = z`.
   *
   * The inverse axiom cancels a pair at the end of a sum. A sorted sum has the pair in the middle
   * with the rest behind it, and this is that case.
   */
  def cancelMiddle(reals: RealTheory): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val z = Term.variable("z", real)

    for {
      addAssoc <- reals.axiom("ADD_ASSOC")
      inverse <- reals.axiom("ADD_INVERSE")
      zeroLeft <- unitOnTheLeft(reals, force(reals.axiom("ADD_SYM")), force(reals.axiom("ADD_ZERO")), "0")

      negated <- reals.term("-x:real")
      associated <- specialise(rules, addAssoc, List(x, negated, z))
      regrouped <- Conv.sym(associated)
      regroupedRight <- rightOfConclusion(regrouped)

      inverseAtX <- rules.spec(x, inverse)
      collapsed <- rewriteWith(reals, inverseAtX, regroupedRight)

      zeroAtZ <- rules.spec(z, zeroLeft)
      whole <- chain(List(regrouped, collapsed, zeroAtZ))
      general <- generalise(reals, whole, List(x, z))
    } yield general
  }

  /**
   * `|- !x y. x + y = 0 ==> y = -x`.
   *
   * The inverse of a value is unique, and this is the only route from the axiom to any fact about
   * the negation of a compound term: `-(x + y)` is related to `-x + -y` by showing the second is
   * an inverse of `x + y`, and then by this.
   *
   * {{{
   * y = 0 + y = (-x + x) + y = -x + (x + y) = -x + 0 = -x
   * }}}
   */
  def uniqueInverse(reals: RealTheory): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      addAssoc <- reals.axiom("ADD_ASSOC")
      addZero <- reals.axiom("ADD_ZERO")
      addSym <- reals.axiom("ADD_SYM")
      zeroLeft <- unitOnTheLeft(reals, addSym, addZero, "0")
      inverseLeft <- inverseOnTheLeft(reals)

      negated <- reals.term("-x:real")
      plus <- constantOf(reals, Real.Addition, binary)
      premise <- reals.proposition("x:real + y:real = 0")
      assumed <- LogicError.lift(Kernel.assume(premise))

      zeroAtY <- rules.spec(y, zeroLeft)
      opened <- Conv.sym(zeroAtY)
      openedRight <- rightOfConclusion(opened)

      inverseAtX <- rules.spec(x, inverseLeft)
      splitZero <- Conv.sym(inverseAtX)
      expanded <- rewriteWith(reals, splitZero, openedRight)

      regrouped <- specialise(rules, addAssoc, List(negated, x, y))
      onNegated <- LogicError.lift(Term.app(plus, negated))
      folded <- Conv.apTerm(onNegated, assumed)
      zeroAtNegated <- rules.spec(negated, addZero)

      whole <- chain(List(opened, expanded, regrouped, folded, zeroAtNegated))
      discharged <- rules.disch(premise, whole)
      general <- generalise(reals, discharged, List(x, y))
    } yield general
  }

  /**
   * What the negation of a compound term is, each proved by showing a candidate is an inverse.
   *
   * `-(x + y) = -x + -y` because `(x + y) + (-x + -y)` is zero, which the cancelling normalisation
   * shows by sorting the four terms so that each meets its own negation. The two about products go
   * through distribution instead: `x * y + -x * y` is `(x + -x) * y`, which is `0 * y`.
   */
  def negationFacts(
    reals: RealTheory,
    cancelling: Rewrite.Conversion
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      unique <- uniqueInverse(reals)
      inverseLeft <- inverseOnTheLeft(reals)
      addZero <- reals.axiom("ADD_ZERO")
      mulSym <- reals.axiom("MUL_SYM")
      distribute <- reals.axiom("DISTRIBUTE")
      rightDistribute <- rightDistribution(reals, mulSym, distribute)

      negatedX <- reals.term("-x:real")
      inverseAtX <- rules.spec(x, inverseLeft)
      negNegImplication <- specialise(rules, unique, List(negatedX, x))
      negNegBackwards <- rules.mp(negNegImplication, inverseAtX)
      negNegAtX <- Conv.sym(negNegBackwards)
      negNeg <- rules.gen(x, negNegAtX)

      zero <- reals.term("0")
      zeroPlusZero <- rules.spec(zero, addZero)
      negZeroImplication <- specialise(rules, unique, List(zero, zero))
      negZeroBackwards <- rules.mp(negZeroImplication, zeroPlusZero)
      negZero <- Conv.sym(negZeroBackwards)

      sum <- reals.term("x:real + y:real")
      negatedSum <- reals.term("-x:real + -y:real")
      addStatement <- reals.proposition("(x:real + y:real) + (-x + -y) = 0")
      addSides <- Term.destEq(addStatement).toRight(NotOfForm("an equation", addStatement))
      addPremise <- Rewrite.proveWith(cancelling, addSides._1, addSides._2)
      negAddImplication <- specialise(rules, unique, List(sum, negatedSum))
      negAddBackwards <- rules.mp(negAddImplication, addPremise)
      negAddAtXY <- Conv.sym(negAddBackwards)
      negAdd <- generalise(reals, negAddAtXY, List(x, y))

      product <- reals.term("x:real * y:real")
      negatedProduct <- reals.term("-x:real * y:real")
      mulPremise <- negatedProductIsInverse(reals, rightDistribute, x, y)
      negMulImplication <- specialise(rules, unique, List(product, negatedProduct))
      negMulAtXY <- rules.mp(negMulImplication, mulPremise)
      negMulLeft <- generalise(reals, negMulAtXY, List(x, y))

      negMulRight <- mirrorNegatedProduct(reals, mulSym, negMulLeft)
    } yield Map(
      UniqueInverse -> unique,
      InverseOnTheLeft -> inverseLeft,
      NegNeg -> negNeg,
      NegZero -> negZero,
      NegAdd -> negAdd,
      NegMulLeft -> negMulLeft,
      NegMulRight -> negMulRight
    )
  }

  /** `|- x * y + -x * y = 0`: the factors add to zero, and zero times anything is zero. */
  private def negatedProductIsInverse(
    reals: RealTheory,
    rightDistribute: Kernel.Thm,
    x: FVar,
    y: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules

    for {
      inverse <- reals.axiom("ADD_INVERSE")
      mulSym <- reals.axiom("MUL_SYM")
      addZero <- reals.axiom("ADD_ZERO")
      addSym <- reals.axiom("ADD_SYM")
      addAssoc <- reals.axiom("ADD_ASSOC")
      distribute <- reals.axiom("DISTRIBUTE")

      negated <- reals.term("-x:real")
      timesZeroFact <- timesZero(reals, addZero, addSym, addAssoc, distribute)
      zeroTimesFact <- flip(reals, mulSym, timesZeroFact)

      distributed <- specialise(rules, rightDistribute, List(x, negated, y))
      gathered <- Conv.sym(distributed)
      gatheredRight <- rightOfConclusion(gathered)

      inverseAtX <- rules.spec(x, inverse)
      collapsed <- rewriteWith(reals, inverseAtX, gatheredRight)

      zeroTimesAtY <- rules.spec(y, zeroTimesFact)
      whole <- chain(List(gathered, collapsed, zeroTimesAtY))
    } yield whole
  }

  /** `|- !x y. x * -y = -(x * y)`, from the left-handed version and commutativity. */
  private def mirrorNegatedProduct(
    reals: Signature,
    mulSym: Kernel.Thm,
    negMulLeft: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = reals.logic.rules
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      negatedY <- reals.term("-y:real")
      negation <- constantOf(reals, Real.Negation, Type.fun(real, real))

      swapped <- specialise(rules, mulSym, List(x, negatedY))
      atYX <- specialise(rules, negMulLeft, List(y, x))
      productSwapped <- specialise(rules, mulSym, List(y, x))
      negationOfSwap <- Conv.apTerm(negation, productSwapped)

      whole <- chain(List(swapped, atYX, negationOfSwap))
      general <- generalise(reals, whole, List(x, y))
    } yield general
  }

  /* ---------------------------------------------------------- normalisation */

  /**
   * The order the sorting rules use: a term and its negation sort next to each other.
   *
   * Any total order makes the sorting terminate and canonical, so this one is chosen for what it
   * puts side by side. Cancellation is a rewrite between neighbours, and under the kernel's own
   * order every variable sorts before every application, so `x` and `-x` end up at opposite ends
   * of `x + (y + (-x + -y))` and never meet. Comparing by the term under the negations first, and
   * only then by how many there are, makes that sum `x + (-x + (y + -y))`, where both pairs are
   * adjacent and one rule removes them.
   *
   * == It does not transfer to another arithmetic, and the sentence above is what hides that ==
   *
   * "Any total order makes the sorting terminate and canonical" is true of the property it names and
   * is the reason the choice above is free. It is **not** true that any total order lets the rule
   * set reach a canonical form, and reading the first as the second cost a session on 2026-09-13.
   *
   * Associativity is an ordered rule: `(A + B) + C` becomes `A + (B + C)` only where that is
   * smaller. Under a structural comparison that reduces to whether `A + B` outranks `A`, and
   * `Term.ordering` settles it by **rank first** (a variable ranks below an application) and, at
   * equal rank, by the constant's **name**. So where `A` is a variable the sum outranks it and the
   * rule fires; where `A` is itself a product, both are applications and the answer comes from
   * comparing the two head constants by name. Here they are `*` and `+`, and `*` precedes `+` in
   * ASCII, so the sum wins and flattening works. Over `num` they are `NUM_ADD` and `NUM_MUL`, the
   * comparison comes out the other way, and associativity **stops flattening wherever the left
   * summand is a product**. What that produces is not a wrong theorem but two different normal
   * forms for two equal sums, and a refusal that reads as though the identity were false.
   *
   * `Semiring.order` is what `num` uses instead: size first, inside the recursion. This order is
   * for the reals, where there is cancellation to arrange; a development that copies it because it
   * is the one that exists will get the accident and not the reason.
   */
  val ringOrder: Ordering[Term] = new Ordering[Term] {

    def compare(left: Term, right: Term): Int = {
      val (leftBase, leftDepth) = strip(left, 0)
      val (rightBase, rightDepth) = strip(right, 0)

      val byBase = compareBase(leftBase, rightBase)
      if (byBase != 0) byBase else leftDepth.compare(rightDepth)
    }

    /**
     * Compare two terms that are not themselves negations.
     *
     * Recursive through applications rather than deferring to the kernel's order, and that is the
     * whole point: the first version stripped the negations only at the top and then compared the
     * rest with the kernel's order, so two sums were compared by comparing their first summands
     * with the wrong order, and `x + (y + (-x + -y))` came out sorted. Every level has to use the
     * same rule.
     */
    private def compareBase(left: Term, right: Term): Int = (left, right) match {
      case (App(leftFn, leftArgument), App(rightFn, rightArgument)) =>
        val byFunction = compare(leftFn, rightFn)
        if (byFunction != 0) byFunction else compare(leftArgument, rightArgument)

      case (Abs(leftType, leftBody), Abs(rightType, rightBody)) =>
        val byBinder = Type.ordering.compare(leftType, rightType)
        if (byBinder != 0) byBinder else compare(leftBody, rightBody)

      case _ => Term.ordering.compare(left, right)
    }

    @annotation.tailrec
    private def strip(term: Term, depth: Int): (Term, Int) = term match {
      case App(Const(Real.Negation, _), argument) => strip(argument, depth + 1)
      case other => (other, depth)
    }
  }

  /**
   * The conversion that puts a ring expression in canonical form.
   *
   * Subtraction is unfolded, negations are pushed down to the atoms, products are distributed over
   * sums, units and cancelling pairs are removed, and both operations are flattened and sorted.
   * Everything but the sorting applies unconditionally; the six associativity and commutativity
   * rules apply only when they make the term smaller, because commutativity applies to its own
   * output and would otherwise never stop.
   *
   * Termination of the two kinds together: the unconditional rules strictly reduce a measure of
   * how much structure is left to expand, and the ordered rules leave that measure alone while
   * strictly decreasing an order on terms of a fixed size. Lexicographically, every step goes
   * down.
   *
   * @param negation whether the lemmas about negating a compound term are available. They are not,
   *                 while they are themselves being proved.
   */
  def normalisationFrom(
    reals: RealTheory,
    facts: Map[String, Kernel.Thm],
    negation: Boolean,
    limit: Int = NormalisationLimit
  ): Either[LogicError, Rewrite.Conversion] = {
    val negationLemmas =
      if (negation) Vector(NegAdd, NegMulLeft, NegMulRight, NegNeg, NegZero) else Vector.empty

    for {
      addAssoc <- reals.axiom("ADD_ASSOC")
      addSym <- reals.axiom("ADD_SYM")
      mulAssoc <- reals.axiom("MUL_ASSOC")
      mulSym <- reals.axiom("MUL_SYM")
      distribute <- reals.axiom("DISTRIBUTE")
      inverse <- reals.axiom("ADD_INVERSE")
      bit0 <- reals.definition(Real.Bit0)
      bit1 <- reals.definition(Real.Bit1)
      subtraction <- reals.definition(Real.Subtraction)
      // `x / y` is an abbreviation for `x * inv y` and unfolding it asks for nothing: the
      // definition is an equation without hypotheses, and `inv y` is left as an opaque term. What
      // needs `~(y = 0)` is cancelling `y * inv y`, which nothing here does. Absent until
      // 2026-09-08, and the sentence that kept it out read "the axiom for `inv` holds only where
      // its argument is not zero", which is the reason for the cancellation and not for the
      // unfolding: it made two spellings of one quotient two terms.
      division <- reals.definition(Real.Division)

      expanding <- Rewrite.Rule.all(
        reals.logic,
        Vector(
          bit0, bit1, subtraction, division, distribute,
          facts(RightDistribute), facts(OneOnTheLeft), facts(OneOnTheRight),
          // Multiplication by zero, on both sides. Absent from this set until the oracle harness
          // ran the computer algebra system over random polynomials and asked for a proof of
          // `2 + y * 0 * x^2 = 2`: the product had to vanish before the sum could lose it, and
          // nothing here made it vanish. They shrink the term like the unit rules, so they are
          // unconditional and the termination argument is unchanged.
          facts(TimesZero), facts(ZeroTimes)
        ) ++ negationLemmas.map(facts)
      )
      cancelling <- Rewrite.Rule.all(
        reals.logic,
        Vector(inverse, facts(CancelMiddle), facts(ZeroOnTheLeft), facts(ZeroOnTheRight))
      )
      ordered <- Rewrite.Rule.all(
        reals.logic,
        Vector(addAssoc, addSym, facts(Exchange), mulAssoc, mulSym, facts(MulExchange))
      )
      // The assembly moved to `Rewrite.normaliser` on 2026-09-13, when `Semiring` needed the same
      // six lines over `num`. What is the reals' here is the rules and nothing else.
    } yield Rewrite.normaliser(expanding ++ cancelling, ordered, ringOrder, limit)
  }

  private def proveLemmas(
    reals: Signature,
    normalisation: Rewrite.Conversion,
    lemmas: Vector[(String, String)]
  ): Either[LogicError, Map[String, Kernel.Thm]] =
    lemmas.foldLeft(Right(Map.empty): Either[LogicError, Map[String, Kernel.Thm]]) {
      case (acc, (name, text)) =>
        for {
          proved <- acc
          theorem <- proveLemma(reals, normalisation, text)
        } yield proved.updated(name, theorem)
    }

  private def proveLemma(
    reals: Signature,
    normalisation: Rewrite.Conversion,
    text: String
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- reals.proposition(text)
      sides <- Term.destEq(statement).toRight(NotOfForm("an equation", statement))
      proved <- Rewrite.proveWith(normalisation, sides._1, sides._2)
      general <- generaliseAll(reals, proved)
    } yield general

  /* ----------------------------------------------------------------- helpers */

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val binary: Type = Type.fun(real, Type.fun(real, real))

  /** Rewrite `term` with one equation, wherever that equation's left side occurs. */
  private def rewriteWith(
    reals: Signature,
    equation: Kernel.Thm,
    term: Term
  ): Either[LogicError, Kernel.Thm] =
    Rewrite.Rule.of(reals.logic, equation).flatMap(rule =>
      Rewrite.depthConv(Rewrite.rewriteConv(rule))(term)
    )

  /** Chain equations end to end. */
  private def chain(steps: List[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    steps match {
      case Nil => Left(NotOfForm("at least one equation", Term.variable("nothing", real)))
      case first :: rest =>
        rest.foldLeft(Right(first): Either[LogicError, Kernel.Thm]) { (acc, step) =>
          acc.flatMap(Conv.trans(_, step))
        }
    }

  private def specialise(
    rules: Rules,
    theorem: Kernel.Thm,
    arguments: List[Term]
  ): Either[LogicError, Kernel.Thm] =
    arguments.foldLeft(Right(theorem): Either[LogicError, Kernel.Thm]) { (acc, argument) =>
      acc.flatMap(current => rules.spec(argument, current))
    }

  /** Close over the given variables, innermost last, so they read in the order written. */
  private def generalise(
    reals: Signature,
    theorem: Kernel.Thm,
    variables: List[FVar]
  ): Either[LogicError, Kernel.Thm] =
    variables.reverse.foldLeft(Right(theorem): Either[LogicError, Kernel.Thm]) { (acc, variable) =>
      acc.flatMap(current => reals.logic.rules.gen(variable, current))
    }

  /** Close over every variable free in the conclusion, in the order their names sort. */
  private def generaliseAll(
    reals: Signature,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    generalise(reals, theorem, Term.freeVariables(theorem.conclusion).toList.sortBy(_.name))

  private def destBinary(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(_, left), right) => Right((left, right))
    case other => Left(NotOfForm("an application of a binary operator", other))
  }

  private def constantOf(reals: Signature, name: String, ty: Type): Either[LogicError, Term] =
    LogicError.lift(reals.theory.constant(name, ty))

  private def rightOfConclusion(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  /**
   * Take the value of something that cannot fail here.
   *
   * Used only where the argument is an axiom of the theory being built, which is present by
   * construction. A failure means the theory was assembled wrongly, and there is nothing a caller
   * could do about it.
   */
  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => throw new IllegalStateException(error.message), identity)
}
