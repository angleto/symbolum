package garden.xeno.symbolum.tactics

import scala.annotation.tailrec

import garden.xeno.symbolum.{Arbitrary, Relation}
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * The polynomial a sum of radicals satisfies, found by a numeric search and then proved.
 *
 * The first source on the conjecture card's list, and the one with the real track record: integer
 * relation detection is how the BBP formula for pi was found and how the Ramanujan-type series
 * were. `Relation` has been in this repository since 2026-09-11 and `RelationSpec` calibrates it,
 * and until now it was a **measuring instrument** and not a source: what it reports is a relation
 * among real numbers, and this theory has no way to say that pi is a sum of a series, so nothing
 * it found could be put to the kernel at all.
 *
 * {{{
 *   Algebraic.standard.of(Vector(Root(2, 2), Root(2, 3), Root(2, 5)))
 *   // Found(!x:real. !y:real. !z:real. x * x = 2 ==> y * y = 3 ==> z * z = 5 ==>
 *   //         Power (x + y + z) 8 - 40 * Power (x + y + z) 6 + 352 * Power (x + y + z) 4
 *   //           - 960 * Power (x + y + z) 2 + 576 = 0,
 *   //       1 0 -40 0 352 0 -960 0 576, confirmed to 33 digits)
 * }}}
 *
 * == What made it sayable, which is a change of subject and not a change of precision ==
 *
 * The card says the blocker is digits, and on 2026-09-11 the note under it said the rest: fifty
 * digits are not the hundreds PSLQ wants, **and** a relation between real constants is not
 * statable here. Both were true and the second is the one that mattered. `pi = 4 S1 - 2 S4 - S5 -
 * S6` needs a constant for pi and an infinite sum, and infinite sums need the completeness of the
 * reals, which `docs/adr/0007` puts after the construction: that source is not near.
 *
 * A relation among **algebraic** values needs none of it. `sqrt2 + sqrt3 + sqrt5` is not a constant
 * of this theory either, but it does not have to be: the claim is about any three reals whose
 * squares are 2, 3 and 5, which is an implication between polynomial equations and is exactly what
 * the theory can already write. Nothing new is defined, no axiom is added, and the statement quantifies
 * over **every** choice of sign, which is right: the four conjugates of `sqrt2 + sqrt3` are all roots
 * of the same polynomial, and that is why the statement is an ideal membership rather than a fact
 * about one number.
 *
 * == How the claim is proved, and why the untrusted half computes a certificate ==
 *
 * `Ring` decides equations that hold in every commutative ring. The claim is not one of those: it
 * is false in a ring where `x * x` is not 2. What **is** a ring identity is
 *
 * {{{
 *   p(x + y + z) = A(x,y,z) * (x*x - 2) + B(x,y,z) * (y*y - 3) + C(x,y,z) * (z*z - 5)
 * }}}
 *
 * so the untrusted side reduces `p` modulo the defining equations, keeping the quotient at each
 * step, and hands the cofactors over as a **certificate `Ring` can check**. Then the assumed
 * equations rewrite `x*x` to 2 in the right-hand side, every factor becomes `2 - 2`, and `Ring`
 * closes what is left. The certificate is not trusted for a moment: a wrong cofactor is a false
 * equation and `Ring` refuses it, which [[Algebraic.certifying]] exists to let a caller demonstrate.
 *
 * The alternative was to rewrite the goal into the ring's normal form and reduce there, which needs
 * the normal form to expose `x * x` as a subterm; it is not obliged to, and the cofactor identity
 * needs nothing of the normaliser but the decision it already makes. The largest case here, the
 * degree-eight polynomial over three roots, cost 111078 inferences end to end on 2026-09-24, which
 * `AlgebraicSpec` reports rather than asserts.
 *
 * == What the theorem says, and the three things it does not ==
 *
 * It says `p` annihilates every such sum. It does **not** say `p` is the minimal polynomial, that
 * `p` is irreducible, or that no polynomial of lower degree annihilates the sum. The search walks
 * the degrees upward and reports the first that carries a credible relation, so the degree is
 * evidence of minimality and not a proof of it, and a reader who needs minimality does not have it
 * here. Keeping that separate is the same discipline as everywhere else in this module: the numbers
 * screen, and only what the kernel says is certain.
 *
 * == The limit a reader met first, and what removed it ==
 *
 * Until 2026-09-13 the claim was written with the multiplication spelled out, so the degree-eight
 * polynomial over a three-term sum carried **twenty copies** of `(x + y + z)`. The theorem was
 * true and a reader could check it by counting copies; what it cost was the comparison with the
 * informal claim, which is the whole reason a statement is written down. `Ring` refused the
 * readable form because `Power x 2` is an atom to it and the only thing that could open it,
 * `POWER_SUC`, is stated over `SUC y` while a written exponent is bit-encoded.
 *
 * `Successor` is the conversion that closes the gap, and `derive` spends it: the claim is stated
 * with `Power`, that driver opens the written exponents, and `Ring` decides the cofactor identity
 * it always decided. The whole thing came out **cheaper**, 111048 inferences at the degree-eight
 * case against 111247 before, because the side being normalised is smaller.
 *
 * That driver refuses a written exponent above 32, and this is one place that line cannot bite: the
 * numeric half gives out long before it. The four roots `sqrt2 + sqrt3 + sqrt5 + sqrt7` want degree
 * sixteen and come back [[Algebraic.Outcome.NotCredible]] at [[Algebraic.Digits]] digits, confirmed
 * to six, which is the same wall the card that proposed this source named. The largest degree
 * certified here is nine.
 */
final class Algebraic private (val chain: Chain, val arithmetic: Arbitrary, val digits: Int) {

  import Algebraic.*

  private val signature: Signature = chain.widest
  private val logic: Logic = chain.logic
  private val rules: Rules = logic.rules
  private val real: Type = TyApp(Real.TypeName, Nil)

  /**
   * The polynomial the sum of these roots satisfies, found and then proved.
   *
   * The degree is searched upward rather than fixed at the product of the root degrees, which is
   * only an upper bound: `sqrt2 + sqrt8` is `3 sqrt2` and satisfies `x*x = 18`, and a search fixed
   * at four would report a multiple of that and call it the polynomial.
   */
  def of(roots: Vector[Root]): Outcome =
    values(roots) match {
      case Left(why) => Outcome.Unusable(why)
      case Right(alpha) =>
        search(alpha, 1, roots.map(_.degree).product) match {
          case Left(outcome) => outcome
          case Right((coefficients, confirmed)) =>
            certifying(roots, coefficients) match {
              case Outcome.Found(theorem, found, _, inferences) =>
                Outcome.Found(theorem, found, Some(confirmed), inferences)
              case other => other
            }
        }
    }

  /**
   * The kernel half alone, on a polynomial somebody else chose.
   *
   * Published so that a caller can point the certification at a polynomial whose answer is already
   * known and watch it refuse: `x*x = 2` and the coefficients of `x^2 - 3` come back
   * [[Algebraic.Outcome.NotInTheIdeal]], which is what says the guard is not reading its own
   * conclusion back. `of` uses it on what the search produced, and cannot tell the difference.
   */
  def certifying(roots: Vector[Root], coefficients: Vector[BigInt]): Outcome =
    if (roots.isEmpty) Outcome.Unusable("a sum of no roots is not a value")
    else if (coefficients.forall(_ == 0)) Outcome.Unusable("the zero polynomial annihilates everything")
    else {
      val names = Vector.tabulate(roots.length)(nameOf)
      val degrees = roots.map(_.degree)
      val radicands = roots.map(_.radicand)
      val sum = names.indices.foldLeft(Polynomial.zero)((acc, i) =>
        Polynomial.add(acc, Polynomial.variable(i, names.length))
      )
      val expanded = coefficients.zipWithIndex.foldLeft(Polynomial.zero) { case (acc, (c, k)) =>
        Polynomial.add(acc, Polynomial.scale(Polynomial.power(sum, k, names.length), c))
      }
      val (remainder, cofactors) = Polynomial.reduce(expanded, degrees, radicands)

      if (remainder.nonEmpty)
        Outcome.NotInTheIdeal(Polynomial.show(remainder, names), coefficients)
      else
        derive(names, degrees, radicands, coefficients, cofactors) match {
          case Right(theorem) =>
            Outcome.Found(theorem, coefficients, None, Derivation.size(theorem))
          case Left(error) => Outcome.NotCertified(error.message, coefficients)
        }
    }

  /* ----------------------------------------------------------------- the numeric half */

  /** The powers of the sum of the roots, to the precision this was built with. */
  private def values(roots: Vector[Root]): Either[String, BigDecimal] =
    if (roots.isEmpty) Left("a sum of no roots is not a value")
    else if (roots.exists(_.degree < 1)) Left("a root of degree below one is not a root")
    else if (roots.exists(_.radicand <= 0))
      Left("a root of a number that is not positive has no real value here")
    else {
      val computed = roots.map { root =>
        arithmetic
          .over(Vector(BigDecimal(1), BigDecimal(root.degree)))
          .flatMap(exponent => arithmetic.power(BigDecimal(root.radicand), exponent))
      }
      if (computed.exists(_.isEmpty)) Left("a root could not be computed to this precision")
      else Right(arithmetic.sum(computed.map(_.get)))
    }

  /**
   * The lowest degree at which the powers of `alpha` carry a relation the precision supports.
   *
   * A `Left` is the outcome to report: either nothing credible up to the bound, or a value whose
   * powers could not be computed. Walking upward is what makes the degree mean something, and the
   * first credible answer is taken rather than the shortest over the whole range, because a
   * relation at degree `d` reappears at every higher degree multiplied by anything.
   */
  @tailrec
  private def search(
    alpha: BigDecimal,
    degree: Int,
    bound: Int
  ): Either[Outcome, (Vector[BigInt], Int)] = {
    val powers = (0 to degree).toVector.map(k => arithmetic.power(alpha, BigDecimal(k)))
    if (powers.exists(_.isEmpty))
      Left(Outcome.Unusable(s"a power of the value could not be computed at degree $degree"))
    else
      Relation.among(powers.map(_.get), digits) match {
        case Relation.Found(coefficients, confirmed, _) =>
          Right((primitive(coefficients), confirmed))
        case _ if degree < bound => search(alpha, degree + 1, bound)
        case Relation.NotCredible(coefficients, confirmed) =>
          Left(Outcome.NotCredible(coefficients, confirmed, bound))
        case Relation.Unusable(why) => Left(Outcome.Unusable(why))
      }
  }

  /** The coefficients with their common factor taken out, so that the same relation has one form. */
  private def primitive(coefficients: Vector[BigInt]): Vector[BigInt] = {
    val divisor = coefficients.map(_.abs).filter(_ != 0).reduceOption(_.gcd(_)).getOrElse(BigInt(1))
    val reduced = coefficients.map(_ / divisor)
    if (reduced.reverse.find(_ != 0).exists(_ < 0)) reduced.map(-_) else reduced
  }

  /* ------------------------------------------------------------------ the kernel half */

  /**
   * The theorem, from the certificate the untrusted half produced.
   *
   * Four steps and each one is checked: `Ring` on the cofactor identity, the assumed equations
   * rewriting their own left sides away, `Ring` on what is left, and then the discharge that turns
   * the assumptions into the arrows a reader sees.
   */
  private def derive(
    names: Vector[String],
    degrees: Vector[Int],
    radicands: Vector[BigInt],
    coefficients: Vector[BigInt],
    cofactors: Vector[Polynomial.P]
  ): Either[LogicError, Kernel.Thm] = {
    val variables = names.map(name => Term.variable(name, real))
    // `written` and not `names` from here down: these strings are parsed, and a name in a parsed
    // text has to carry its type since `docs/adr/0018`. `names` stays bare for the variables above
    // and for `Polynomial.show` where it is read by a person rather than by the parser.
    val written = spelled(names)
    val claim = appliedText(coefficients, written)
    val certificate = names.indices
      .map { i =>
        val powered = Vector.fill(degrees(i))(written(i)).mkString(" * ")
        s"(${Polynomial.show(cofactors(i), written)}) * (($powered) - ${radicands(i)})"
      }
      .mkString(" + ")

    for {
      // `Successor` and not `Ring` directly, and the two halves are what they were: this opens the
      // written exponents of the left side and `Ring` decides what is left, which is the cofactor
      // identity it always decided. `Ring` is built four stages below `Series` in the chain and
      // cannot name `Power` at all, so the split is the layering rather than a preference.
      stated <- signature.proposition(s"$claim = $certificate")
      identity <- chain.successor.prove(stated)
      defining <- definitions(names, degrees, radicands)
      assumed <- defining.foldLeft(Right(Vector.empty): Either[LogicError, Vector[Kernel.Thm]]) {
        (acc, term) => acc.flatMap(seen => LogicError.lift(Kernel.assume(term)).map(seen :+ _))
      }
      ruleSet <- Rewrite.Rule.all(logic, assumed)
      right <- rightOf(identity)
      reduced <- Rewrite.rewrite(ruleSet, right)
      collapsed <- rightOf(reduced)
      zero <- signature.term("0", real)
      vanishing <- LogicError.lift(Term.eq(collapsed, zero))
      vanishes <- chain.ring.prove(vanishing)
      step <- LogicError.lift(Kernel.trans(identity, reduced))
      whole <- LogicError.lift(Kernel.trans(step, vanishes))
      discharged <- defining.foldRight(Right(whole): Either[LogicError, Kernel.Thm]) {
        (term, acc) => acc.flatMap(inner => rules.disch(term, inner))
      }
      closed <- rules.genAll(discharged, variables.toList)
    } yield closed
  }

  /** `x * x = 2` and its neighbours, in the order the roots were given. */
  private def definitions(
    names: Vector[String],
    degrees: Vector[Int],
    radicands: Vector[BigInt]
  ): Either[LogicError, Vector[Term]] =
    val written = spelled(names)
    names.indices
      .foldLeft(Right(Vector.empty): Either[LogicError, Vector[Term]]) { (acc, i) =>
        val powered = Vector.fill(degrees(i))(written(i)).mkString(" * ")
        acc.flatMap(seen => signature.proposition(s"$powered = ${radicands(i)}").map(seen :+ _))
      }

  /**
   * The polynomial written at the sum, which is the side of the claim a reader checks.
   *
   * Written with `Power` since 2026-09-13, and until then with the multiplication spelled out,
   * which put **twenty copies** of `(x + y + z)` in the degree-eight statement. The claim was true
   * and a reader could check it by counting copies; what it cost was the comparison with the
   * informal claim, which is the one thing a formal statement is for. `Successor` is what made the
   * readable form provable, and `derive` spends it.
   *
   * The first degree is written bare rather than as `Power p 1`, because `p` is what a reader of
   * `x^1` expects to see and the expansion of the two is the same.
   */
  private def appliedText(coefficients: Vector[BigInt], names: Vector[String]): String = {
    val sum = names.mkString("(", " + ", ")")
    Algebraic.signedSum(coefficients.zipWithIndex.reverse.filter(_._1 != 0).map { case (c, k) =>
      val power = if (k == 1) sum else s"Power $sum ($k:${Natural.TypeName})"
      val magnitude = c.abs.toString
      val body =
        if (k == 0) magnitude
        else if (c.abs == 1) power
        else s"$magnitude * ($power)"
      (c.signum, body)
    })
  }

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}

object Algebraic {

  /**
   * One of the radicals the target is built from: a real whose `degree`-th power is `radicand`.
   *
   * `Root(2, 3)` is a square root of three, and the claim it contributes is `y * y = 3`. It is
   * deliberately not "the positive square root". The theory has a name for that one since
   * 2026-09-24, `sqrt 3`, and it is still not what this means: the statement holds of both roots, and
   * a hypothesis that pinned the sign would be a hypothesis the proof never uses.
   */
  final case class Root(degree: Int, radicand: BigInt)

  /** How many digits the numeric search works to. */
  val Digits: Int = 60

  /**
   * What the source made of a request, kept apart because they say different things.
   *
   * [[Algebraic.Outcome.NotCredible]] is the one to read carefully: it says the search found
   * nothing the precision it was given can support, **not** that no polynomial annihilates the
   * value. A relation with larger coefficients, or one needing more digits, looks exactly like this
   * from here.
   */
  enum Outcome {

    /**
     * A polynomial that annihilates the sum, proved.
     *
     * `confirmed` is the digits the numeric search had left over once the size of the coefficients
     * was paid for, and it is `None` when the polynomial came from the caller through
     * [[Algebraic.certifying]] rather than from a search. Not zero: zero is a search that confirmed
     * nothing, which is a different thing from a search that never ran.
     */
    case Found(
      theorem: Kernel.Thm,
      coefficients: Vector[BigInt],
      confirmed: Option[Int],
      inferences: Int
    )

    /** Nothing the precision supports, up to the degree bound. Not "there is no relation". */
    case NotCredible(coefficients: Vector[BigInt], confirmed: Int, bound: Int)

    /**
     * The numeric candidate is not an algebraic identity over these roots.
     *
     * The reduction left something behind, so the polynomial does not lie in the ideal the defining
     * equations generate and no certificate exists to hand `Ring`. It is the answer a candidate
     * from too few digits deserves, and it is reached before the kernel is troubled.
     */
    case NotInTheIdeal(remainder: String, coefficients: Vector[BigInt])

    /** The certificate was built and the prover refused it, with what it said. */
    case NotCertified(why: String, coefficients: Vector[BigInt])

    /** The request could not be put: no roots, a degree below one, a radicand that is not positive. */
    case Unusable(why: String)
  }

  /** The variable a root is written with: `x`, `y`, `z`, then `x4` and upward. */
  def nameOf(index: Int): String =
    if (index < 3) Vector("x", "y", "z")(index) else s"x${index + 1}"

  /**
   * The same name as it goes into a TEXT, carrying the type it is a variable of.
   *
   * Bare until `docs/adr/0018`, and bare worked only because `+`, `*` and `<` belonged to the reals
   * alone: every text built here is real arithmetic over free variables, so once those symbols
   * stood for two constants nothing in `(x + y) * (x + y) - 2 = ...` said which, and the whole
   * certification refused.
   *
   * On every occurrence rather than the first, because these texts are assembled from pieces that
   * do not know what precedes them. And in the text rather than through `Signature.term`'s expected
   * type, which is the escape that record prefers and which does not reach this case: the texts are
   * **propositions**, so the type a caller could pass is `bool`, and `bool` says nothing about the
   * operands. A caller whose ambiguity is inside an equation has to annotate.
   */
  private def spelled(names: Vector[String]): Vector[String] =
    names.map(name => s"$name:${Real.TypeName}")

  /**
   * Signed terms as one expression, with subtraction rather than a negated summand.
   *
   * `x * x - 2` and `x * x + (neg 2)` are the same term to the prover and not to a reader, and a
   * reader who did not write the translation comparing it against `x^2 - 2` is the only check a
   * formal statement of an informal claim ever gets. The leading term keeps `neg`, since there is
   * nothing for it to be subtracted from.
   */
  def signedSum(terms: Vector[(Int, String)]): String =
    terms.zipWithIndex
      .map {
        case ((sign, body), 0) => if (sign < 0) s"(neg $body)" else body
        case ((sign, body), _) => if (sign < 0) s" - $body" else s" + $body"
      }
      .mkString match {
      case "" => "0"
      case written => written
    }

  /** Over the standard chain, at [[Digits]] digits. */
  lazy val standard: Algebraic = new Algebraic(Chain.standard, Arbitrary.to(Digits), Digits)

  /** Over a chain and a precision of one's own. */
  def apply(chain: Chain, digits: Int): Algebraic =
    new Algebraic(chain, Arbitrary.to(digits), digits)

  /**
   * Multivariate polynomials over the integers, for the certificate and for nothing else.
   *
   * Entirely untrusted, like everything that proposes here. What it computes is handed to `Ring` as
   * an equation, so an error in it is a refusal and never a theorem, which is why it is forty lines
   * of `Map` rather than a dependency: `modules/core` has `Canonical` over `Expr`, and going through
   * it would mean parsing back what this builds in order to build what the prover is given.
   */
  object Polynomial {

    /** Exponent vector to coefficient. An absent key is a zero coefficient, so `empty` is zero. */
    type P = Map[Vector[Int], BigInt]

    val zero: P = Map.empty

    def constant(value: BigInt, arity: Int): P =
      if (value == 0) zero else Map(Vector.fill(arity)(0) -> value)

    def variable(index: Int, arity: Int): P =
      Map(Vector.tabulate(arity)(i => if (i == index) 1 else 0) -> BigInt(1))

    def add(left: P, right: P): P =
      (left.keySet ++ right.keySet).flatMap { monomial =>
        val total = left.getOrElse(monomial, BigInt(0)) + right.getOrElse(monomial, BigInt(0))
        if (total == 0) None else Some(monomial -> total)
      }.toMap

    def scale(polynomial: P, factor: BigInt): P =
      if (factor == 0) zero else polynomial.map((monomial, c) => monomial -> c * factor)

    def multiply(left: P, right: P): P =
      left.foldLeft(zero) { case (acc, (monomial, c)) =>
        add(acc, right.map((other, d) => monomial.zip(other).map(_ + _) -> c * d))
      }

    def power(polynomial: P, exponent: Int, arity: Int): P =
      (0 until exponent).foldLeft(constant(1, arity))((acc, _) => multiply(acc, polynomial))

    /**
     * `p = sum_i cofactor_i * (x_i^{d_i} - a_i) + remainder`, every exponent in the remainder below
     * its degree.
     *
     * One step takes a monomial with `e_i >= d_i`, writes `c*m` as `c*a_i*m' + c*m'*(x_i^{d_i} -
     * a_i)` where `m'` is `m` with the exponent lowered, and moves `c*m'` into the cofactor. The
     * total degree of the offending monomial falls by `d_i >= 1` each time and no step raises any
     * other, so it stops.
     */
    def reduce(polynomial: P, degrees: Vector[Int], radicands: Vector[BigInt]): (P, Vector[P]) = {
      @tailrec
      def go(rest: P, cofactors: Vector[P]): (P, Vector[P]) =
        rest.collectFirst {
          case (monomial, c) if monomial.indices.exists(i => monomial(i) >= degrees(i)) =>
            (monomial, c, monomial.indices.filter(i => monomial(i) >= degrees(i)).min)
        } match {
          case None => (rest, cofactors)
          case Some((monomial, c, i)) =>
            val lowered = monomial.updated(i, monomial(i) - degrees(i))
            val quotient: P = Map(lowered -> c)
            val replaced = add(add(rest, Map(monomial -> -c)), scale(quotient, radicands(i)))
            go(replaced, cofactors.updated(i, add(cofactors(i), quotient)))
        }

      go(polynomial, Vector.fill(degrees.length)(zero))
    }

    /**
     * The polynomial in the theory's notation, with a fixed order so that two runs agree.
     *
     * Highest total degree first and the monomial spelling to break ties, which is arbitrary and is
     * the point: a `Map` has no order and a claim whose text depends on iteration order is a claim
     * that reads differently on different days.
     */
    def show(polynomial: P, names: Vector[String]): String =
      signedSum(
        polynomial.toVector
          .sortBy((monomial, _) => (-monomial.sum, monomial.mkString(",")))
          .map { (monomial, c) =>
            val factors = names.indices.flatMap(i => Vector.fill(monomial(i))(names(i)))
            val magnitude = c.abs.toString
            val body =
              if (factors.isEmpty) magnitude
              else if (c.abs == 1) factors.mkString(" * ")
              else (magnitude +: factors).mkString(" * ")
            (c.signum, body)
          }
      )
  }
}
