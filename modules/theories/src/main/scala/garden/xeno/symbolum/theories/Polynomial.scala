package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A ring normal form that keeps a coefficient as a number instead of expanding it into that many
 * copies of a term.
 *
 * The normalisation in [[Arithmetic]] puts `BIT0` and `BIT1` among its expanding rules, so `2`
 * becomes `1 + 1` and `k * x` becomes `k` copies of `x`. Measured on 2026-09-04 the normal form of
 * `k * x` has exactly `4k - 3` nodes and the normal form of `(x + 1)^k` has exactly `k * 2^(k+1) + 1`
 * nodes: 769 nodes and 13.8 seconds at degree six, and 98305 nodes at degree twelve, which is why
 * degree six is the ceiling and why `12 * 12` costs seconds where the numeral procedure costs
 * milliseconds. This is the other normal form, and it is a different procedure rather than a
 * different rule set.
 *
 * Here, measured the same day on the same machine, the normal form of `k * x` has `2 * bits(k) + 3`
 * nodes, which follows the size of the input rather than the value of the coefficient; `(x + 1)^k`
 * has `k + 1` monomials, so 133 nodes at degree six and 507 at degree twelve, the last in 143 ms;
 * `12 * 12` reaches the numeral `144` in 2 ms against 528 ms. `RingCostSpec` asserts both columns,
 * because the point of the change is the difference between them, and it asserts the sizes rather
 * than the times: the same measurements taken cold outside the suite were four to ten times slower
 * and identical to the node.
 *
 * == Why not another rule set ==
 *
 * The obvious repair is to drop the two bit definitions from the expanding rules and add a rule
 * that collects `a * x + b * x` into `(a + b) * x`. It does not work, for two reasons that were
 * measured rather than argued.
 *
 * Collection by rewriting is a rewrite between NEIGHBOURS, so two like monomials have to sort next
 * to each other, and under `Arithmetic.ringOrder` they do not always: a monomial is compared by its
 * leading factor, and where the atom is an application whose head constant sorts after `BIT0` the
 * coefficient leads. `{2 * inv x, 4 * inv y, 8 * inv x}` sorts in exactly that order, with
 * `4 * inv y` between the two terms that should have met. Linarith reaches Ring with such atoms,
 * and `div` is a second instance: no rule set unfolds it either.
 *
 * The witness has to be chosen with care and a first version of this paragraph got it wrong. It
 * used `{2 * inv x, 3 * y, 5 * inv x}`, which does not separate the pair: the ordered product rules
 * settle `3 * y` as `y * 3`, because a variable sorts below a numeral, and `y * 3` then sorts below
 * both of the others. The coefficient trails in any monomial made of variables, at every degree, so
 * the hazard needs an atom that outranks a numeral and not merely a second monomial.
 *
 * And sorting by exchanging neighbours costs a number of steps quadratic in the number of
 * monomials, which is `2^k` for `(x + 1)^k` before anything is collected. Collection removes the
 * coefficient wall and leaves the degree wall standing.
 *
 * == The procedure ==
 *
 * A recursion over the term that carries a polynomial in a canonical shape, with a theorem for
 * every step. `convert` turns a term into that shape; `addPoly`, `mulPoly` and `negPoly` combine
 * two terms already in it. Each is a merge over sorted lists, so the cost is linear in the size of
 * what it produces rather than quadratic in it, and a coefficient is a numeral throughout: the
 * arithmetic on it is [[Arithmetic.add]] and [[Arithmetic.multiply]], which work digit by digit in
 * binary and are already proved from the sixteen axioms.
 *
 * Nothing here is asserted. Every structural lemma is an identity over variables with no numeral in
 * it, which is exactly what the expanding normalisation is good at, so the lemmas are proved by it
 * once when this is built; every fact about a particular numeral comes from the numeral procedures.
 * The two halves meet and no third source of truth is introduced.
 *
 * == The internal shape ==
 *
 * While the recursion runs, every term is in one uniform shape, and the uniformity is what keeps
 * the case analysis small enough to read:
 *
 *   - a polynomial is `m1 + (m2 + (... + (mk + 0)))`, monomials strictly increasing, and `0` when
 *     there are none;
 *   - a monomial is `c * p`, where `c` is a coefficient in the sense of [[Coefficient]], never
 *     zero, and `p` is `a1 * (a2 * (... * (ad * 1)))` with the atoms in non-decreasing order and
 *     `1` when there are none. A coefficient is a rational number: a signed numeral, or a signed
 *     numeral times the inverse of one, in lowest terms.
 *
 * The trailing `0` and `1` are what remove the base cases: every polynomial is a sum and every
 * monomial's atoms are a product, so `addPoly` has three cases rather than nine. They are taken off
 * at the end by [[tidyPoly]], which walks the shape it built rather than rewriting at depth: a
 * depth pass would also reach inside an atom, and an atom is a term this procedure has decided not
 * to look at.
 *
 * == The order the monomials are kept in ==
 *
 * By degree first, then the atoms compared one by one with `Arithmetic.ringOrder`. Degree first is
 * not decoration: multiplying every monomial of a polynomial by one monomial has to preserve the
 * order, or a product would come out unsorted and would have to be sorted again. Graded orders have
 * that property and ungraded ones need not, so this one is graded.
 *
 * `ringOrder` is unchanged and is still what compares two atoms. What it is no longer asked to do
 * is put a term next to its own negation, because a negation is no longer a term here: it is the
 * sign of a coefficient, and two monomials cancel by their coefficients adding to zero.
 */
final class Polynomial private (
  val reals: RealTheory,
  private val arithmetic: Arithmetic,
  /**
   * Arithmetic on the coefficient, which is a rational number rather than a whole one.
   *
   * Split out rather than inlined because the two questions are different: this file decides which
   * monomials are alike and in what order they sit, and [[Coefficient]] decides what a coefficient
   * is and what two of them add to. A quotient by a numeral is a coefficient here, never an atom,
   * which is the whole of what made `x / 2 + x / 2 = x` unreachable.
   */
  private val coefficient: Coefficient,
  private val rules: Map[String, Rewrite.Rule],
  private val subtraction: Kernel.Thm,
  private val division: Kernel.Thm,
  private val syntax: Polynomial.Syntax,
  /**
   * How two atoms compare, which decides where an atom sits in a monomial.
   *
   * A parameter rather than `Arithmetic.ringOrder` read directly, because a caller that has
   * cancellation rules needs the two atoms a rule cancels to be neighbours: a rewrite between
   * neighbours cannot reach across a third atom, and nothing here reorders once the merge has
   * placed them. [[Field]] passes an order that puts `inv d` next to `d`; everyone else passes
   * `ringOrder` and nothing about their normal forms moves.
   */
  private val atomOrder: Ordering[Term]
) {

  import Polynomial.*

  /** `|- t = t'`, with `t'` the collected normal form of `t`. */
  val normalisation: Rewrite.Conversion = term =>
    for {
      converted <- convert(term)
      internal <- rightOf(converted)
      tidied <- tidyPoly(internal)
      result <- Conv.trans(converted, tidied)
    } yield result

  /* ------------------------------------------------------------- the recursion */

  /**
   * `|- t = P`, with `P` a polynomial in the internal shape.
   *
   * The order of the cases is the specification. A numeral is recognised before anything else,
   * because `2` is an application of `BIT0` and would otherwise be taken apart as one; a bit
   * applied to something that is not a numeral is unfolded, because `BIT0 x` is an ordinary ring
   * expression and the expanding normalisation could always handle it; and whatever is left is an
   * atom, which is how `inv x` and any other application this theory has no rule for gets through
   * without being mishandled.
   */
  private def convert(term: Term): Either[LogicError, Kernel.Thm] =
    Numeral.valueOf(reals, term) match {
      case Some(value) => constant(term, value)

      case None =>
        term match {
          case Add(left, right) => binaryCase(left, right, syntax.plus, addPoly)
          case Mul(left, right) => binaryCase(left, right, syntax.times, mulPoly)

          case Sub(left, right) =>
            for {
              unfolded <- Conv.unfold(subtraction, List(left, right))
              opened <- rightOf(unfolded)
              converted <- convert(opened)
              result <- Conv.trans(unfolded, converted)
            } yield result

          // Unfolded for the same reason subtraction is, and it took longer to see because the
          // wrong reason was written down. `x / y` abbreviates `x * inv y`; the definition is an
          // equation with no hypothesis, so replacing one by the other asks for nothing. What
          // asks for `~(y = 0)` is cancelling `y` against `inv y`, and this does not do that:
          // `inv y` goes on to be an atom, exactly as `inv y` written by hand already was.
          //
          // Without this case a quotient was opaque, and `interpretArguments` normalised what it
          // was applied to but could not see past it: `(z * x) / (2 * y)` and `z * (x / (2 * y))`
          // were two atoms rather than one monomial written twice. That is the shape a paper made
          // of rates is written in, so it was not an edge.
          case Div(left, right) =>
            for {
              unfolded <- Conv.unfold(division, List(left, right))
              opened <- rightOf(unfolded)
              converted <- convert(opened)
              result <- Conv.trans(unfolded, converted)
            } yield result

          case Neg(argument) =>
            for {
              inner <- convert(argument)
              lifted <- Conv.apTerm(syntax.negation, inner)
              form <- rightOf(lifted)
              negatedForm <- destNeg(form)
              combined <- negPoly(negatedForm)
              result <- Conv.trans(lifted, combined)
            } yield result

          case Bit(definition, argument) =>
            for {
              unfolded <- Conv.unfold(definition, List(argument))
              opened <- rightOf(unfolded)
              converted <- convert(opened)
              result <- Conv.trans(unfolded, converted)
            } yield result

          // A redex, contracted before anything else looks at it. The expanding normalisation has
          // `Rewrite.betaConv` in its vector, so `(\y. y + y) x` is an ordinary ring expression
          // there; without this case it would become an atom here and stop being provable.
          case redex @ App(Abs(_, _), _) =>
            for {
              contracted <- Conv.betaRoot(redex)
              opened <- rightOf(contracted)
              converted <- convert(opened)
              result <- Conv.trans(contracted, converted)
            } yield result

          case atom =>
            for {
              inside <- interpretArguments(atom)
              rebuilt <- rightOf(inside)
              polynomial <- denominatorOf(rebuilt) match {
                case Some((numerator, denominator)) => inversePolynomial(numerator, denominator)
                case None => atomPolynomial(rebuilt)
              }
              result <- Conv.trans(inside, polynomial)
            } yield result
        }
    }

  /**
   * Normalise what an opaque term is applied to, before deciding it is an atom.
   *
   * `inv` and `div` have no rule in either normal form, so `inv (2 * x)` is opaque both here and in
   * the expanding form. But the expanding form reaches inside it anyway, because `Rewrite.depthConv`
   * rewrites subterms whatever their parent is, and so `inv (2 * x)` and `inv (x + x)` are the same
   * term there and the identity between them is proved. A recursion that stopped at the atom would
   * make them two atoms and refuse it, which is the one failure this design can have: two terms of
   * equal value reaching two different terms.
   *
   * Found by a second reader of this file rather than by the property test beside it, which
   * generates `inv x` and never `inv` of anything compound. The property now generates both.
   */
  private def interpretArguments(term: Term): Either[LogicError, Kernel.Thm] = term match {
    case App(function, argument) =>
      for {
        head <- interpretArguments(function)
        inner <-
          if (Term.typeOf(argument) == Polynomial.real) normalisation(argument)
          else Right(Conv.refl(argument))
        result <- LogicError.lift(Kernel.mkComb(head, inner))
      } yield result

    case other => Right(Conv.refl(other))
  }

  /** Convert both sides, rebuild the application, and combine the two normal forms. */
  private def binaryCase(
    left: Term,
    right: Term,
    operator: Term,
    combine: (Term, Term) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      leftStep <- convert(left)
      rightStep <- convert(right)
      lifted <- onBoth(operator, leftStep, rightStep)
      form <- rightOf(lifted)
      sides <- destBinary(form)
      combined <- combine(sides._1, sides._2)
      result <- Conv.trans(lifted, combined)
    } yield result

  /** `|- n = n * 1 + 0`, and `|- 0 = 0`: a numeral is a polynomial of one constant monomial. */
  private def constant(term: Term, value: BigInt): Either[LogicError, Kernel.Thm] =
    if (value == 0) Right(Conv.refl(term))
    else constantPolynomial(term)

  /** `|- c = c * 1 + 0`, for a coefficient that is not zero. */
  private def constantPolynomial(scalar: Term): Either[LogicError, Kernel.Thm] =
    for {
      monomial <- product(scalar, syntax.one)
      asMonomial <- at(rules(MulOne), monomial).flatMap(Conv.sym)
      polynomial <- sum(monomial, syntax.zero)
      asPolynomial <- at(rules(AddZero), polynomial).flatMap(Conv.sym)
      result <- Conv.trans(asMonomial, asPolynomial)
    } yield result

  /**
   * `|- inv c = r * 1 + 0`, with `c` the coefficient `numerator` over `denominator` and `r` its
   * reciprocal: a numeral, a negated numeral or a ratio of numerals under an `inv` is a
   * coefficient here, not an atom.
   *
   * Reached after [[interpretArguments]] rather than before it, and the order is the point. That
   * pass normalises what an opaque term is applied to, so `inv (1 + 1)` arrives here as `inv 2`;
   * deciding earlier would make the two of them a coefficient and an atom, and two terms of equal
   * value reaching two different normal forms is the one way this procedure can be wrong.
   */
  private def inversePolynomial(
    numerator: BigInt,
    denominator: BigInt
  ): Either[LogicError, Kernel.Thm] =
    for {
      asCoefficient <- coefficient.ofInverse(numerator, denominator)
      form <- rightOf(asCoefficient)
      polynomial <- constantPolynomial(form)
      result <- Conv.trans(asCoefficient, polynomial)
    } yield result

  /** `|- t = 1 * (t * 1) + 0`, for a term this procedure does not take apart. */
  private def atomPolynomial(atom: Term): Either[LogicError, Kernel.Thm] =
    for {
      _ <- ofTypeReal(atom)
      atoms <- product(atom, syntax.one)
      withUnit <- at(rules(MulOne), atoms).flatMap(Conv.sym)
      monomial <- product(syntax.one, atoms)
      withCoefficient <- at(rules(MulOneLeft), monomial).flatMap(Conv.sym)
      polynomial <- sum(monomial, syntax.zero)
      withZero <- at(rules(AddZero), polynomial).flatMap(Conv.sym)
      first <- Conv.trans(withUnit, withCoefficient)
      result <- Conv.trans(first, withZero)
    } yield result

  /* ------------------------------------------------------------------ addition */

  /**
   * `|- A + B = C`, the merge of two polynomials.
   *
   * Three cases and no more, which is what the trailing zero buys: a polynomial is either `0` or a
   * sum, so the empty cases are two lemmas and the rest is one comparison.
   */
  private def addPoly(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    (destPoly(left), destPoly(right)) match {
      case (None, _) => sum(left, right).flatMap(at(rules(AddZeroLeft), _))
      case (_, None) => sum(left, right).flatMap(at(rules(AddZero), _))

      case (Some((leadLeft, restLeft)), Some((leadRight, restRight))) =>
        for {
          order <- compareMonomials(leadLeft, leadRight)
          whole <- sum(left, right)
          result <-
            if (order < 0)
              for {
                regrouped <- at(rules(AddAssoc), whole)
                merged <- addPoly(restLeft, right)
                lifted <- onSecond(syntax.plus, leadLeft, merged)
                joined <- Conv.trans(regrouped, lifted)
              } yield joined
            else if (order > 0)
              for {
                exchanged <- at(rules(AddExchange), whole)
                merged <- addPoly(left, restRight)
                lifted <- onSecond(syntax.plus, leadRight, merged)
                joined <- Conv.trans(exchanged, lifted)
              } yield joined
            else
              for {
                interchanged <- at(rules(AddInterchange), whole)
                heads <- addMonomials(leadLeft, leadRight)
                tails <- addPoly(restLeft, restRight)
                lifted <- onBoth(syntax.plus, heads, tails)
                joined <- Conv.trans(interchanged, lifted)
                dropped <- dropZeroHead(joined)
              } yield dropped
        } yield result
    }

  /**
   * When two monomials cancelled, the `0` they left has to go.
   *
   * A polynomial with a zero monomial in it is not in the shape, and leaving it there would make
   * two equal polynomials reach different terms, which is the one way this procedure can fail: it
   * would refuse an identity that holds.
   */
  private def dropZeroHead(step: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      form <- rightOf(step)
      result <- destPoly(form) match {
        case Some((lead, _)) if lead == syntax.zero =>
          at(rules(AddZeroLeft), form).flatMap(Conv.trans(step, _))
        case _ => Right(step)
      }
    } yield result

  /** `|- a + b = m`, for two monomials over the same atoms: the coefficients add. */
  private def addMonomials(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    for {
      leftParts <- destMonomial(left)
      rightParts <- destMonomial(right)
      whole <- sum(left, right)
      gathered <- at(rules(Gather), whole)
      coefficients <- coefficient.add(leftParts._1, rightParts._1)
      lifted <- onFirst(syntax.times, coefficients, leftParts._2)
      joined <- Conv.trans(gathered, lifted)
      result <- collapseZero(joined)
    } yield result

  /** A monomial whose coefficient became zero is zero, and stops being a monomial. */
  private def collapseZero(step: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      form <- rightOf(step)
      result <- destBinary(form) match {
        case Right((coefficient, _)) if coefficient == syntax.zero =>
          at(rules(MulZeroLeft), form).flatMap(Conv.trans(step, _))
        case _ => Right(step)
      }
    } yield result



  /* ------------------------------------------------------------ multiplication */

  /** `|- A * B = C`: every monomial of the left is scaled over the right, and the results merge. */
  private def mulPoly(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    destPoly(left) match {
      case None => product(left, right).flatMap(at(rules(MulZeroLeft), _))

      case Some((lead, rest)) =>
        for {
          whole <- product(left, right)
          distributed <- at(rules(RightDistribute), whole)
          scaled <- scalePoly(lead, right)
          others <- mulPoly(rest, right)
          lifted <- onBoth(syntax.plus, scaled, others)
          joined <- Conv.trans(distributed, lifted)
          form <- rightOf(joined)
          sides <- destBinary(form)
          merged <- addPoly(sides._1, sides._2)
          result <- Conv.trans(joined, merged)
        } yield result
    }

  /**
   * `|- m * B = C`, one monomial over a whole polynomial.
   *
   * The result needs no sorting, and that is what the graded order is for: multiplying by a fixed
   * monomial adds the same atoms to every monomial of `B`, which leaves their degrees in the same
   * relation and their atom sequences in the same relation. An ungraded order would not give that
   * and this would have to merge instead of build.
   */
  private def scalePoly(monomial: Term, right: Term): Either[LogicError, Kernel.Thm] =
    destPoly(right) match {
      case None => product(monomial, right).flatMap(at(rules(MulZeroRight), _))

      case Some((lead, rest)) =>
        for {
          whole <- product(monomial, right)
          distributed <- at(rules(Distribute), whole)
          head <- multiplyMonomials(monomial, lead)
          tail <- scalePoly(monomial, rest)
          lifted <- onBoth(syntax.plus, head, tail)
          result <- Conv.trans(distributed, lifted)
        } yield result
    }

  /** `|- (a * p) * (b * q) = (a * b) * (p * q)`, then both halves computed. */
  private def multiplyMonomials(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    for {
      leftParts <- destMonomial(left)
      rightParts <- destMonomial(right)
      whole <- product(left, right)
      interchanged <- at(rules(MulInterchange), whole)
      coefficients <- coefficient.multiply(leftParts._1, rightParts._1)
      atoms <- mergeAtoms(leftParts._2, rightParts._2)
      lifted <- onBoth(syntax.times, coefficients, atoms)
      result <- Conv.trans(interchanged, lifted)
    } yield result

  /** `|- p * q = r`, the merge of two sorted products of atoms. */
  private def mergeAtoms(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    (destAtoms(left), destAtoms(right)) match {
      case (None, _) => product(left, right).flatMap(at(rules(MulOneLeft), _))
      case (_, None) => product(left, right).flatMap(at(rules(MulOne), _))

      case (Some((leadLeft, restLeft)), Some((leadRight, restRight))) =>
        val whole = product(left, right)
        if (atomOrder.compare(leadLeft, leadRight) <= 0)
          for {
            term <- whole
            regrouped <- at(rules(MulAssoc), term)
            merged <- mergeAtoms(restLeft, right)
            lifted <- onSecond(syntax.times, leadLeft, merged)
            result <- Conv.trans(regrouped, lifted)
          } yield result
        else
          for {
            term <- whole
            exchanged <- at(rules(MulExchange), term)
            merged <- mergeAtoms(left, restRight)
            lifted <- onSecond(syntax.times, leadRight, merged)
            result <- Conv.trans(exchanged, lifted)
          } yield result
    }

  /* ---------------------------------------------------------------- negation */

  /** `|- -A = C`: every coefficient changes sign and the monomials stay where they are. */
  private def negPoly(term: Term): Either[LogicError, Kernel.Thm] =
    destPoly(term) match {
      case None => negate(term).flatMap(at(rules(NegZero), _))

      case Some((lead, rest)) =>
        for {
          whole <- negate(term)
          distributed <- at(rules(NegAdd), whole)
          head <- negMonomial(lead)
          tail <- negPoly(rest)
          lifted <- onBoth(syntax.plus, head, tail)
          result <- Conv.trans(distributed, lifted)
        } yield result
    }

  /** `|- -(c * p) = c' * p`, with `c'` the coefficient of the other sign. */
  private def negMonomial(term: Term): Either[LogicError, Kernel.Thm] =
    for {
      parts <- destMonomial(term)
      whole <- negate(term)
      gathered <- at(rules(NegMulGather), whole)
      negated <- coefficient.negate(parts._1)
      lifted <- onFirst(syntax.times, negated, parts._2)
      result <- Conv.trans(gathered, lifted)
    } yield result

  /* ------------------------------------------------------------------- tidying */

  /**
   * `|- P = P'`, taking off what the uniform shape carried and the answer does not need.
   *
   * Written as a walk over the shape rather than as a pass of the rewriter, and the difference
   * matters: `Rewrite.depthConv` would apply `x * 1 = x` inside an atom as well, and an atom is
   * precisely the part of the term this procedure decided not to interpret. Two callers who wrote
   * the same atom differently would then be told they had written the same thing.
   */
  private def tidyPoly(term: Term): Either[LogicError, Kernel.Thm] =
    destPoly(term) match {
      case None => Right(Conv.refl(term))

      case Some((lead, rest)) =>
        for {
          head <- tidyMonomial(lead)
          result <-
            if (rest == syntax.zero)
              for {
                dropped <- at(rules(AddZero), term)
                joined <- Conv.trans(dropped, head)
              } yield joined
            else
              for {
                tail <- tidyPoly(rest)
                joined <- onBoth(syntax.plus, head, tail)
              } yield joined
        } yield result
    }

  /** `|- c * p = m`: the trailing unit goes, and a coefficient of one or minus one is absorbed. */
  private def tidyMonomial(term: Term): Either[LogicError, Kernel.Thm] =
    for {
      parts <- destMonomial(term)
      value <- coefficient.valueOf(parts._1).toRight(NotOfForm("a coefficient", parts._1))
      scalar <- tidyCoefficient(parts._1, value)
      result <-
        if (parts._2 == syntax.one)
          at(rules(MulOne), term).flatMap(Conv.trans(_, scalar))
        else
          for {
            atoms <- tidyAtoms(parts._2)
            lifted <- onBoth(syntax.times, scalar, atoms)
            form <- rightOf(lifted)
            absorbed <-
              if (value == (BigInt(1), BigInt(1)))
                at(rules(MulOneLeft), form).flatMap(Conv.trans(lifted, _))
              else if (value == (BigInt(-1), BigInt(1)))
                at(rules(NegOneTimes), form).flatMap(Conv.trans(lifted, _))
              else Right(lifted)
          } yield absorbed
    } yield result

  /**
   * `|- c = c'`, dropping the numerator a fraction does not need to show.
   *
   * `1 * inv 2` is the shape every fraction is held in while the recursion runs, because a uniform
   * shape is what keeps the case analysis readable; `inv 2` is the shape a reader expects. The two
   * are the same number and the difference is cosmetic, which is why it happens here, once, at the
   * end, and not in the arithmetic.
   */
  private def tidyCoefficient(
    scalar: Term,
    value: (BigInt, BigInt)
  ): Either[LogicError, Kernel.Thm] =
    if (value._2 == 1) Right(Conv.refl(scalar))
    else if (value._1 == 1) at(rules(MulOneLeft), scalar)
    else if (value._1 == -1) at(rules(NegOneTimes), scalar)
    else Right(Conv.refl(scalar))

  /** `|- a1 * (... * (ad * 1)) = a1 * (... * ad)`. */
  private def tidyAtoms(term: Term): Either[LogicError, Kernel.Thm] =
    destAtoms(term) match {
      case None => Right(Conv.refl(term))

      case Some((lead, rest)) =>
        if (rest == syntax.one) at(rules(MulOne), term)
        else
          for {
            tail <- tidyAtoms(rest)
            result <- onSecond(syntax.times, lead, tail)
          } yield result
    }

  /* ------------------------------------------------------- reading the shape */

  /** The leading monomial and the rest, or nothing when the polynomial is empty. */
  private def destPoly(term: Term): Option[(Term, Term)] =
    if (term == syntax.zero) None
    else term match {
      case Add(lead, rest) => Some((lead, rest))
      case _ => None
    }

  /** The leading atom and the rest, or nothing when the product is empty. */
  private def destAtoms(term: Term): Option[(Term, Term)] =
    if (term == syntax.one) None
    else term match {
      case Mul(lead, rest) => Some((lead, rest))
      case _ => None
    }

  /** The coefficient and the atoms of a monomial. */
  private def destMonomial(term: Term): Either[LogicError, (Term, Term)] = term match {
    case Mul(coefficient, atoms) => Right((coefficient, atoms))
    case other => Left(NotOfForm("a monomial", other))
  }

  /**
   * The coefficient a term is the inverse of, when it is the inverse of one that is not zero.
   *
   * A numeral until 2026-09-09, and any coefficient now, which is what `interpretArguments` running
   * first makes safe: the argument of an opaque term is already in normal form when this looks at
   * it, so `inv (2 / 3)` arrives as `inv (2 * inv 3)` and is read, while `inv (1 + 1)` arrives as
   * `inv 2`. Deciding earlier would make two terms of equal value reach two different normal forms.
   *
   * Zero is not a coefficient to invert, so `inv 0` stays an atom. That is not a gap: nothing this
   * normal form holds says what `inv 0` is, and giving it one here would be inventing it. The chain
   * proves `inv 0 = 0` since the reals were constructed, through `CUT_INV_ZERO`, a fact published
   * under no name of the reals, and until one is, a refusal over the atom is not a decision.
   */
  private def denominatorOf(term: Term): Option[(BigInt, BigInt)] = term match {
    case Inv(argument) => coefficient.valueOf(argument).filter { case (top, _) => top != 0 }
    case _ => None
  }

  /**
   * Compare two monomials: by degree, then by their atoms one at a time.
   *
   * The coefficient takes no part, which is the whole difference from the order the expanding
   * normalisation sorts by. Two monomials that compare equal are the two this procedure adds.
   */
  private def compareMonomials(left: Term, right: Term): Either[LogicError, Int] =
    for {
      leftParts <- destMonomial(left)
      rightParts <- destMonomial(right)
    } yield {
      val leftAtoms = atomsOf(leftParts._2)
      val rightAtoms = atomsOf(rightParts._2)
      val byDegree = leftAtoms.length.compare(rightAtoms.length)
      if (byDegree != 0) byDegree
      else
        leftAtoms
          .zip(rightAtoms)
          .map { case (one, other) => atomOrder.compare(one, other) }
          .find(_ != 0)
          .getOrElse(0)
    }

  private def atomsOf(term: Term): Vector[Term] = {
    @annotation.tailrec
    def go(current: Term, collected: Vector[Term]): Vector[Term] =
      destAtoms(current) match {
        case None => collected
        case Some((lead, rest)) => go(rest, collected :+ lead)
      }

    go(term, Vector.empty)
  }

  /* ------------------------------------------------------------------ plumbing */

  /** Instantiate a lemma at the root of a term, refusing when it does not apply. */
  private def at(rule: Rewrite.Rule, term: Term): Either[LogicError, Kernel.Thm] =
    Matching.matchTerm(rule.variables, rule.lhs, term) match {
      case None => Left(NotOfForm(s"a term ${reals.show(rule.lhs)} matches", term))
      case Some(found) => LogicError.lift(found.instance(rule.theorem))
    }

  private def sum(left: Term, right: Term): Either[LogicError, Term] =
    apply2(syntax.plus, left, right)

  private def product(left: Term, right: Term): Either[LogicError, Term] =
    apply2(syntax.times, left, right)

  private def negate(term: Term): Either[LogicError, Term] =
    LogicError.lift(Term.app(syntax.negation, term))

  private def apply2(operator: Term, left: Term, right: Term): Either[LogicError, Term] =
    for {
      partial <- LogicError.lift(Term.app(operator, left))
      whole <- LogicError.lift(Term.app(partial, right))
    } yield whole

  /** `G |- l = r` gives `G |- f a l = f a r`. */
  private def onSecond(
    operator: Term,
    first: Term,
    step: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- LogicError.lift(Term.app(operator, first))
      result <- Conv.apTerm(partial, step)
    } yield result

  /** `G |- l = r` gives `G |- f l a = f r a`. */
  private def onFirst(
    operator: Term,
    step: Kernel.Thm,
    second: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      applied <- Conv.apTerm(operator, step)
      result <- Conv.apThm(applied, second)
    } yield result

  /** Two equations under one binary operator. */
  private def onBoth(
    operator: Term,
    left: Kernel.Thm,
    right: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      applied <- Conv.apTerm(operator, left)
      result <- LogicError.lift(Kernel.mkComb(applied, right))
    } yield result

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def destBinary(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(_, left), right) => Right((left, right))
    case other => Left(NotOfForm("an application of a binary operator", other))
  }

  private def destNeg(term: Term): Either[LogicError, Term] = term match {
    case Neg(argument) => Right(argument)
    case other => Left(NotOfForm("a negation", other))
  }

  private def ofTypeReal(term: Term): Either[LogicError, Unit] =
    if (Term.typeOf(term) == Polynomial.real) Right(())
    else Left(NotOfForm("a term of type real", term))

  /* --------------------------------------------------------------- extractors */

  private object Add {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(Real.Addition, _), left), right) => Some((left, right))
      case _ => None
    }
  }

  private object Mul {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(Real.Multiplication, _), left), right) => Some((left, right))
      case _ => None
    }
  }

  private object Sub {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(Real.Subtraction, _), left), right) => Some((left, right))
      case _ => None
    }
  }

  private object Div {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(Real.Division, _), left), right) => Some((left, right))
      case _ => None
    }
  }

  private object Neg {
    def unapply(term: Term): Option[Term] = term match {
      case App(Const(Real.Negation, _), argument) => Some(argument)
      case _ => None
    }
  }

  private object Inv {
    def unapply(term: Term): Option[Term] = term match {
      case App(Const(Real.Inverse, _), argument) => Some(argument)
      case _ => None
    }
  }

  /** A bit applied to something that is not a numeral, with the definition that unfolds it. */
  private object Bit {
    def unapply(term: Term): Option[(Kernel.Thm, Term)] = term match {
      case App(Const(Real.Bit0, _), argument) =>
        reals.definition(Real.Bit0).toOption.map((_, argument))
      case App(Const(Real.Bit1, _), argument) =>
        reals.definition(Real.Bit1).toOption.map((_, argument))
      case _ => None
    }
  }
}

object Polynomial {

  /** The terms this procedure builds with, read once rather than at every step. */
  private[theories] final case class Syntax(
    plus: Term,
    times: Term,
    negation: Term,
    zero: Term,
    one: Term
  )

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val binary: Type = Type.fun(real, Type.fun(real, real))
  private val unary: Type = Type.fun(real, real)

  /* The lemmas, by the name they are looked up under. Those with a statement here are the ones
   * this procedure adds; the rest are axioms or are already proved in `Arithmetic`. */

  val AddAssoc: String = "ADD_ASSOC"
  val AddZero: String = "ADD_ZERO"
  val MulAssoc: String = "MUL_ASSOC"
  val MulOne: String = "MUL_ONE"
  val Distribute: String = "DISTRIBUTE"

  val AddZeroLeft: String = Arithmetic.ZeroOnTheLeft
  val MulOneLeft: String = Arithmetic.OneOnTheLeft
  val MulZeroLeft: String = Arithmetic.ZeroTimes
  val MulZeroRight: String = Arithmetic.TimesZero
  val AddExchange: String = Arithmetic.Exchange
  val MulExchange: String = Arithmetic.MulExchange
  val RightDistribute: String = Arithmetic.RightDistribute
  val NegAdd: String = Arithmetic.NegAdd
  val NegZero: String = Arithmetic.NegZero
  val NegMulLeft: String = Arithmetic.NegMulLeft

  val AddInterchange: String = "ADD_INTERCHANGE"
  val MulInterchange: String = "MUL_INTERCHANGE"
  val NegOneTimes: String = "NEG_ONE_TIMES"

  /** The reversed forms, which a rewriter needs as their own theorems because it is directional. */
  val Gather: String = "MUL_GATHER"
  val NegMulGather: String = "NEG_MUL_GATHER"

  /**
   * What this procedure adds to what `Arithmetic` already proved.
   *
   * Every one is an identity of a commutative ring over variables, with no numeral in it beyond the
   * multiplicative unit, so the expanding normalisation settles each in a few passes and none of
   * them costs what a numeral would cost there. That is why the two normal forms coexist rather
   * than one replacing the other: the expanding one is what proves the lemmas the collecting one
   * runs on.
   */
  val Lemmas: Vector[(String, String)] = Vector(
    // Two sums merge by taking a monomial from each and merging what is left.
    AddInterchange -> "(w:real + x:real) + (y:real + z:real) = (w + y) + (x + z)",
    // Two monomials multiply by multiplying the coefficients and merging the atoms.
    MulInterchange -> "(w:real * x:real) * (y:real * z:real) = (w * y) * (x * z)",
    // A coefficient of minus one is not written down, and putting it back is this read backwards.
    NegOneTimes -> "-1 * x:real = -x"
  )

  /** Built once over the standard arithmetic. */
  lazy val standard: Polynomial =
    construct(Coefficient.standard).fold(
      error =>
        throw new IllegalStateException(s"the collecting normal form does not build: ${error.message}"),
      identity
    )

  /**
   * Prove what this needs, then keep it as rules ready to instantiate.
   *
   * A rule rather than a theorem because every step here is "this lemma, at the root of this
   * term", and matching is what turns the one into the other. Instantiating by hand through `spec`
   * would name the variables at every call site and would say the same thing four times.
   */
  def construct(coefficient: Coefficient): Either[LogicError, Polynomial] =
    construct(coefficient, Arithmetic.ringOrder)

  /** The same, with the order two atoms are compared by. See the field of that name. */
  def construct(
    coefficient: Coefficient,
    atomOrder: Ordering[Term]
  ): Either[LogicError, Polynomial] = {
    val arithmetic = coefficient.arithmetic
    val reals = arithmetic.reals
    val logic = reals.logic

    def named(name: String): Either[LogicError, Kernel.Thm] =
      reals.law(name).orElse(arithmetic.lemma(name))

    for {
      syntax <- readSyntax(reals)

      inherited <- collect(
        Vector(AddAssoc, AddZero, MulAssoc, MulOne, Distribute,
          AddZeroLeft, MulOneLeft, MulZeroLeft, MulZeroRight, AddExchange, MulExchange,
          RightDistribute, NegAdd, NegZero, NegMulLeft).map(name =>
          named(name).map(name -> _)
        )
      )

      proved <- collect(
        Lemmas.map { case (name, text) => prove(reals, arithmetic, text).map(name -> _) }
      )

      gathered <- collect(
        Vector(
          reverse(logic, inherited(RightDistribute)).map(Gather -> _),
          reverse(logic, inherited(NegMulLeft)).map(NegMulGather -> _)
        )
      )

      theorems = inherited ++ proved ++ gathered
      rules <- collect(theorems.toVector.map { case (name, theorem) =>
        Rewrite.Rule.of(logic, theorem).map(name -> _)
      })

      subtraction <- reals.definition(Real.Subtraction)
      division <- reals.definition(Real.Division)
    } yield new Polynomial(
      reals,
      arithmetic,
      coefficient,
      rules,
      subtraction,
      division,
      syntax,
      atomOrder
    )
  }

  /** `|- l = r` from an identity written in the theory's notation, through the expanding form. */
  private def prove(
    reals: Signature,
    arithmetic: Arithmetic,
    text: String
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- reals.proposition(text)
      proved <- Rewrite.proveEquation(reals.logic, arithmetic.normalisation, statement)
      general <- generaliseAll(reals, proved)
    } yield general

  /** `|- !x. r = l` from `|- !x. l = r`: a rewriter reads an equation in one direction only. */
  private def reverse(logic: Logic, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Rewrite.specialiseAll(logic, theorem)
      flipped <- Conv.sym(stripped._2)
      general <- stripped._1.reverse.foldLeft(Right(flipped): Either[LogicError, Kernel.Thm]) {
        (acc, variable) => acc.flatMap(logic.rules.gen(variable, _))
      }
    } yield general

  private def generaliseAll(
    reals: Signature,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Term
      .freeVariables(theorem.conclusion)
      .toList
      .sortBy(_.name)
      .reverse
      .foldLeft(Right(theorem): Either[LogicError, Kernel.Thm]) { (acc, variable) =>
        acc.flatMap(reals.logic.rules.gen(variable, _))
      }

  private def readSyntax(reals: Signature): Either[LogicError, Syntax] =
    for {
      plus <- LogicError.lift(reals.theory.constant(Real.Addition, binary))
      times <- LogicError.lift(reals.theory.constant(Real.Multiplication, binary))
      negation <- LogicError.lift(reals.theory.constant(Real.Negation, unary))
      zero <- reals.term("0")
      one <- reals.term("1")
    } yield Syntax(plus, times, negation, zero, one)

  private def collect[T](
    steps: Vector[Either[LogicError, (String, T)]]
  ): Either[LogicError, Map[String, T]] =
    steps.foldLeft(Right(Map.empty[String, T]): Either[LogicError, Map[String, T]]) {
      (acc, step) =>
        for {
          collected <- acc
          entry <- step
        } yield collected.updated(entry._1, entry._2)
    }
}
