package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.{Add, Div, Expr, Mul, Neg, Num, Pow, SimplificationConfig, Sub}
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Real, RealTheory, Ring}

/**
 * The computer algebra system as an untrusted oracle, with the kernel checking its work.
 *
 * This is the arrangement `docs/adr/0003` describes and nothing until now exercised. The oracle is
 * fast and knows a great deal; it is also wrong in ways this repository has measured, and several
 * of its rewrites hold only under hypotheses it does not record. None of that matters here, because
 * nothing it says is believed. It proposes an answer, the answer is translated into the theory of
 * the reals, and [[Ring]] proves the two are equal or refuses.
 *
 * So the failure modes are: a theorem, or no theorem. There is no third outcome where the oracle
 * persuades anybody of something false.
 *
 * == What this is for ==
 *
 * Exploration. An algebraic development that runs for weeks rests on hundreds of simplifications,
 * and one of them being valid only for positive arguments is the kind of mistake that is found
 * months later, if at all. Certifying each step as it is taken costs a second and removes that
 * class of error entirely.
 *
 * == The fragment ==
 *
 * Polynomials with whole coefficients, in any number of variables: `+`, `*`, `-`, whole powers.
 * [[Translate]] says exactly what is in and what is out, and refuses the rest rather than trying.
 */
final class Oracle private (val reals: RealTheory, val ring: Ring) {

  /**
   * Ask the oracle to simplify, and prove that its answer equals what went in.
   *
   * Returns both the simplified expression and the theorem, because the expression is what the
   * caller wanted and the theorem is why they may believe it.
   */
  def certifySimplification(
    expression: Expr,
    config: SimplificationConfig = SimplificationConfig.Default
  ): Either[TacticError, Oracle.Certified] =
    certifyProposal(expression, expression.simplify(config), "simplification")

  /** The same for the oracle's expansion, which is where most of its work shows. */
  def certifyExpansion(
    expression: Expr,
    config: SimplificationConfig = SimplificationConfig.Default
  ): Either[TacticError, Oracle.Certified] =
    certifyProposal(expression, expression.expand(config), "expansion")

  /**
   * Prove that two expressions are equal, whoever proposed them.
   *
   * The identity does not have to come from the oracle: this is also how a conjecture found by
   * hand, or by pattern, or by numerical search, gets checked.
   */
  def certifyIdentity(left: Expr, right: Expr): Either[TacticError, Kernel.Thm] =
    for {
      leftTerm <- Translate.toTerm(reals, left)
      rightTerm <- Translate.toTerm(reals, right)
      equation <- TacticError.lift(LogicError.lift(Term.eq(leftTerm, rightTerm)))
      theorem <- ring.prove(equation).left.map(error => NotCertified(s"$left = $right", error))
    } yield theorem

  private def certifyProposal(
    expression: Expr,
    proposal: Expr,
    what: String
  ): Either[TacticError, Oracle.Certified] =
    certifyIdentity(expression, proposal).map(theorem =>
      Oracle.Certified(expression, proposal, theorem, what)
    )
}

object Oracle {

  /**
   * What the oracle proposed, and the theorem that says it was right.
   *
   * The theorem is the whole value of this type. Without it the proposal is a suggestion from a
   * program with known defects; with it, it is a fact.
   */
  final case class Certified(
    original: Expr,
    proposal: Expr,
    theorem: Kernel.Thm,
    operation: String
  ) {
    override def toString: String = s"$original --$operation--> $proposal, certified"
  }

  /**
   * The largest written numeral a caller with a deadline should hand to a certification.
   *
   * It was 100, and the wall it guarded is gone. That number came from the expanding ring normal
   * form, where certifying `k * x = k * x` cost 5.5 s at 50, 32 s at 200 and had not returned after
   * two hundred seconds at 500, because a coefficient of `k` became `k` copies of the term. `Ring`
   * has collected coefficients since 2026-09-04 and `1000 * x` now normalises in about 2 ms, so a
   * budget of 100 was refusing goals that cost nothing.
   *
   * The cost that is left is the numeral arithmetic, and it grows with the number of digits rather
   * than with the value. Measured warm on 2026-09-04 through the collecting form: a product of two
   * numerals costs 7 ms at three digits, 104 ms at six, 273 ms at nine and 688 ms at twelve, and
   * collecting a coefficient of twenty-four digits costs 331 ms. So the budget is set at twelve
   * digits, where a single numeral product is still under a second, and it is a bound on the risk
   * rather than on the time: the cost depends on the shape as well as the size.
   *
   * Read those times as orders of magnitude. The same measurements taken cold were four to fifty
   * times slower: `multiply(999, 999)` is 8 ms warm and was 459 ms on the first call.
   *
   * It is not enforced by [[Oracle.certifyIdentity]], deliberately. Refusing a goal the theory
   * cannot state is `Translate`'s job and belongs to the tactic; refusing a goal that would take
   * half an hour is a judgement about someone's afternoon, and it belongs to the caller who has
   * the afternoon. [[Discovery]] consults it because a loop that hangs has stopped being a loop.
   *
   * What it bounds is what was **written**. Expansion creates numerals nobody typed, which is how
   * `-3^2^2` reaches 81 with no literal above 3 in it, so this catches the thirteen-digit
   * coefficient somebody hands over and not the one exponentiation produces on the way.
   */
  val NumeralBudget: BigInt = BigInt(10).pow(12)

  /** The largest whole literal written anywhere in an expression. */
  def largestNumeral(expression: Expr): BigInt = expression match {
    case n: Num =>
      if (n.denominator == 1.0 && n.numerator == n.numerator.floor)
        BigInt(math.abs(n.numerator).toLong)
      else BigInt(0)
    case Add(parts) => parts.map(largestNumeral).foldLeft(BigInt(0))(_ max _)
    case Mul(parts) => parts.map(largestNumeral).foldLeft(BigInt(0))(_ max _)
    case Sub(parts) => parts.map(largestNumeral).foldLeft(BigInt(0))(_ max _)
    case Div(parts) => parts.map(largestNumeral).foldLeft(BigInt(0))(_ max _)
    case Neg(argument) => largestNumeral(argument)
    case Pow(base, exponent) => largestNumeral(base) max largestNumeral(exponent)
    case _ => BigInt(0)
  }

  /** Whether both sides are within [[NumeralBudget]], with the numeral that decided it. */
  def affordable(left: Expr, right: Expr): Either[BigInt, Unit] = {
    val largest = largestNumeral(left) max largestNumeral(right)
    if (largest > NumeralBudget) Left(largest) else Right(())
  }

  /** Built once over the standard theory. */
  lazy val standard: Oracle = new Oracle(Ring.standard.reals, Ring.standard)

  def apply(ring: Ring): Oracle = new Oracle(ring.reals, ring)
}
