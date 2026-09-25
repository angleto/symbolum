package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A polynomial in the index times a geometric term: the series is decided in both directions, and
 * what decides it is the ratio test at degree one and a comparison from each degree to the next.
 *
 * The derivations are here and the names, statements and docstrings are in `Limit`, for the reason
 * `Criteria` gives about itself; this file is a second one because what it needs beyond `Criteria`'s
 * kit is the embedding of `num` in the reals and the order on `num`, and nothing in `Criteria` does.
 *
 * == The route, which needs no root and no division by a symbol ==
 *
 *  - **Degree one** is the ratio test, and it is that theorem's first consumer. `i s^i` has ratio
 *    `(i + 1) s / i`, which is at most `r = (1 + s) / 2` once `i` is past `2 s / (1 - s)`, and the
 *    index past that is `NUM_CEIL` of it. So the `N` the test asks for is a term, built here once for
 *    every `s`, rather than a numeral a procedure would compute per call.
 *  - **From degree `k` to `k + 1`** is a comparison, and the trick is the half-way point
 *    `s' = (1 + s) / 2` taken twice: `s <= s' * s'` because the difference is `(1 - s)^2 / 4`, so
 *    `i^(k+1) s^i <= (i s'^i) (i^k s'^i)`. The first factor is the term of a convergent series,
 *    so it vanishes and is bounded, `CONVERGES_BOUNDED`; the second is the previous degree at `s'`.
 *    Writing `s = s' t` with a second ratio would ask for `t = s / s'`, a quotient by a symbol,
 *    which LINARITH cannot reason about and `Field` only cancels.
 *  - **A signed ratio** goes through absolute convergence, and **the divergent side** is the term
 *    test: at `1 <= abs q` every term from index one on has magnitude at least one.
 *
 * == Three instruments that were measured and are worth knowing ==
 *
 * `Field` cancels an **atom**: asked `(1 - s) * (2 s / (1 - s)) = 2 s` it distributes the product
 * first and the reciprocal never meets its denominator, so the cancellation is proved at a variable
 * `g` and specialised. LINARITH decides every non-linear step here once the products are named as
 * the atoms they are, which is why each such step states its goal over the products it compares.
 * And `Induct.proveBy` inducts on the **last** leading quantifier, so the degree induction, whose
 * claim quantifies over `s` inside, is `NUM_INDUCTION` at a predicate instead.
 */
private[theories] object Degrees {
  import Criteria.Kit

  /**
   * What these derivations take beyond `Criteria.Kit`: the embedding of `num` in the reals, the
   * order on `num`, and the facts about powers and magnitudes the kit's derivations never needed.
   * The last five are `Limit`'s own, derived in `Criteria` just before these.
   */
  final case class Pieces(
    field: Field,
    total: Kernel.Thm,
    realLe: Kernel.Thm,
    realNonNeg: Kernel.Thm,
    realSuc: Kernel.Thm,
    realZero: Kernel.Thm,
    ceilLe: Kernel.Thm,
    sumNonNeg: Kernel.Thm,
    sumGrows: Kernel.Thm,
    sucAdd: Kernel.Thm,
    induction: Kernel.Thm,
    powerOfProduct: Kernel.Thm,
    powerMonotone: Kernel.Thm,
    powerOne: Kernel.Thm,
    productNonNeg: Kernel.Thm,
    square: Kernel.Thm,
    inversePositive: Kernel.Thm,
    triangle: Kernel.Thm,
    termsVanish: Kernel.Thm,
    scaleConverges: Kernel.Thm,
    ratioTest: Kernel.Thm,
    termTest: Kernel.Thm,
    geometric: Kernel.Thm
  )

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val sequences: Type = Type.fun(numbers, values)

  private def at(kit: Kit, template: String, arguments: Term*): Either[LogicError, Term] =
    for {
      lambda <- Parser.term(kit.theory, kit.notation, template)
      applied <- LogicError.lift(Term.appAll(lambda, arguments.toList))
      reduced <- Conv.betaNormalise(applied)
      right <- Limit.rightOf(reduced)
    } yield right

  /** `fact` specialised at `args` and detached from `premises` in order. */
  private def apply(kit: Kit, fact: Kernel.Thm, args: List[Term], premises: Kernel.Thm*): Either[LogicError, Kernel.Thm] =
    premises.foldLeft(kit.rules.specAll(fact, args).flatMap(Limit.normalised))((acc, p) => acc.flatMap(kit.rules.mp(_, p)))

  private def linear(kit: Kit, statement: String, args: List[Term], premises: Kernel.Thm*): Either[LogicError, Kernel.Thm] =
    kit.linarith.prove(statement).flatMap(apply(kit, _, args, premises*))

  /** `abs t = t` for a non-negativity `0 <= t`. */
  private def sizeOf(kit: Kit, nonNeg: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    nonNeg.conclusion match {
      case App(App(_, _), t) => kit.rules.spec(t, kit.absOfNonNegative).flatMap(kit.rules.mp(_, nonNeg))
      case other => Left(NotOfForm("a non-negativity", other))
    }

  /** `|- !s l. converges s l ==> ?B. !n. abs (s n) <= B` */
  private def bounded(kit: Kit, pieces: Pieces): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val s = Term.variable("s", sequences)
    val l = Term.variable("l", values)
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)
    val bound = Term.variable("N", numbers)
    val d = Term.variable("d", numbers)
    for {
      assumedS <- kit.assume("converges (s:num -> real) (l:real)")
      (premise, isS) = assumedS
      unfolded <- Conv.unfold(kit.convergesDefinition, List(s, l)).flatMap(Limit.normaliseRight)
      body <- LogicError.lift(Kernel.eqMp(unfolded, isS))
      one <- kit.term("1:real", values)
      onePositive <- kit.linarith.prove("0 < (1:real)")
      near <- rules.spec(one, body).flatMap(rules.mp(_, onePositive))
      assumedInside <- kit.assume("!n:num. NUM_LE (N:num) n ==> abs ((s:num -> real) n - (l:real)) < 1")
      (_, inside) = assumedInside

      sizes <- kit.term("\\i:num. abs ((s:num -> real) i)", sequences)
      termAt <- kit.term("(s:num -> real) (i:num)", values)
      sizesNonNeg <- rules.spec(termAt, kit.absNonNegative).flatMap(rules.gen(i, _))
      sucN <- kit.term("SUC (N:num)", numbers)
      sucn <- kit.term("SUC (n:num)", numbers)
      head <- kit.term("Sum (\\i:num. abs ((s:num -> real) i)) (SUC (N:num))", values)
      everyPartialNonNeg <- apply(kit, pieces.sumNonNeg, List(sizes), sizesNonNeg)
      headNonNeg <- rules.spec(sucN, everyPartialNonNeg)
      grows <- apply(kit, pieces.sumGrows, List(sizes), sizesNonNeg)
      limitSize <- kit.term("abs (l:real)", values)
      limitNonNeg <- rules.spec(l, kit.absNonNegative)
      witness <- kit.term("abs (l:real) + 1 + Sum (\\i:num. abs ((s:num -> real) i)) (SUC (N:num))", values)
      size <- kit.term("abs ((s:num -> real) (n:num))", values)

      // past N the term is within one of the limit
      assumedPast <- kit.assume("NUM_LE (N:num) (n:num)")
      (_, isPast) = assumedPast
      close <- rules.spec(n, inside).flatMap(rules.mp(_, isPast))
      diff <- kit.term("(s:num -> real) (n:num) - (l:real)", values)
      diffSize <- kit.term("abs ((s:num -> real) (n:num) - (l:real))", values)
      split <- rules.specAll(pieces.triangle, List(diff, l))
      rejoin <- kit.proposition("(s:num -> real) (n:num) - (l:real) + l = s n").flatMap(kit.ring.prove)
      tri <- Limit.rewriteInProposition(rejoin, split)
      farCase <- linear(kit,
        "!a:real. !b:real. !c:real. !t:real. a <= b + c ==> b < 1 ==> 0 <= t ==> a <= c + 1 + t",
        List(size, diffSize, limitSize, head), tri, close, headNonNeg)

      // up to N the term is under the partial sum that ends just after it
      assumedBefore <- kit.assume("NUM_LE (n:num) (N:num)")
      (_, isBefore) = assumedBefore
      orderDef <- Conv.unfold(kit.orderDefinition, List(n, bound)).flatMap(Limit.normaliseRight)
      gap <- LogicError.lift(Kernel.eqMp(orderDef, isBefore))
      assumedGap <- kit.assume("NUM_ADD (n:num) (d:num) = N:num")
      (_, isGap) = assumedGap
      shifted <- rules.specAll(pieces.sucAdd, List(n, d))
      successor <- kit.term("\\m:num. SUC m", Type.fun(numbers, numbers))
      sucGap <- Conv.apTerm(successor, isGap).flatMap(Conv.betaSides)
      landed <- Conv.trans(shifted, sucGap)
      packed <- kit.exists("?d:num. NUM_ADD (SUC (n:num)) d = SUC (N:num)", d, landed)
      leUnfolded <- Conv.unfold(kit.orderDefinition, List(sucn, sucN)).flatMap(Limit.normaliseRight)
      sucLe <- rules.existsElim(gap, d, packed)
        .flatMap(t => Conv.sym(leUnfolded).flatMap(e => LogicError.lift(Kernel.eqMp(e, t))))
      chained <- rules.specAll(grows, List(sucn, sucN)).flatMap(rules.mp(_, sucLe))
      peeled <- rules.specAll(kit.sumAtSuccessor, List(sizes, n)).flatMap(Limit.normalised)
      partial <- kit.term("Sum (\\i:num. abs ((s:num -> real) i)) (n:num)", values)
      partialNonNeg <- rules.spec(n, everyPartialNonNeg)
      atSuc <- kit.term("Sum (\\i:num. abs ((s:num -> real) i)) (SUC (n:num))", values)
      nearCase <- linear(kit,
        "!a:real. !p:real. !q:real. !h:real. !m:real. q = p + a ==> 0 <= p ==> q <= h ==> 0 <= m ==> a <= m + 1 + h",
        List(size, partial, atSuc, head, limitSize), peeled, partialNonNeg, chained, limitNonNeg)

      cases <- rules.specAll(pieces.total, List(bound, n))
      everywhere <- rules.disjElim(cases, farCase, nearCase).flatMap(rules.gen(n, _))
      claim <- kit.exists("?B:real. !n:num. abs ((s:num -> real) n) <= B", witness, everywhere)
      result <- rules.existsElim(near, bound, claim).flatMap(rules.disch(premise, _)).flatMap(rules.genAll(_, List(s, l)))
    } yield result
  }

  /** `|- !x. 0 <= x ==> !n. 0 <= Power x n` */
  private def powerNonNeg(kit: Kit, pieces: Pieces): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val x = Term.variable("x", values)
    for {
      assumed <- kit.assume("0 <= x:real")
      (premise, isNonNeg) = assumed
      statement <- kit.proposition("!n:num. 0 <= Power (x:real) n")
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            zeroPower <- rules.spec(x, kit.powerAtZero)
            power <- Limit.destructEquation(zeroPower).map(_._1)
            result <- linear(kit, "!p:real. p = 1 ==> 0 <= p", List(power), zeroPower).flatMap(kit.landsOn(_, base))
          } yield result,
        step =>
          for {
            next <- rules.specAll(kit.powerAtSuccessor, List(x, step.variable))
            current <- at(kit, "\\k:num. Power (x:real) k", step.variable)
            product <- apply(kit, pieces.productNonNeg, List(x, current), isNonNeg, step.hypothesis)
            result <- Conv.sym(next).flatMap(Limit.rewriteInProposition(_, product)).flatMap(kit.landsOn(_, step.goal))
          } yield result
      )
      result <- rules.disch(premise, proved).flatMap(rules.gen(x, _))
    } yield result
  }

  /** `|- !s. 0 <= s ==> s < 1 ==> ?l. converges (Sum (\i. real_of_num i * Power s i)) l`, by the ratio test. */
  private def indexNonNeg(kit: Kit, pieces: Pieces): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val s = Term.variable("s", values)
    val n = Term.variable("n", numbers)
    for {
      a1 <- kit.assume("0 <= s:real")
      (p1, sNonNeg) = a1
      a2 <- kit.assume("s:real < 1")
      (p2, sBelow) = a2
      zero <- kit.term("0:real", values)
      terms <- kit.term("\\i:num. real_of_num i * Power (s:real) i", sequences)
      r <- kit.term("(1 + (s:real)) / 2", values)
      rNonNeg <- linear(kit, "!s:real. 0 <= s ==> 0 <= (1 + s) / 2", List(s), sNonNeg)
      rBelow <- linear(kit, "!s:real. s < 1 ==> (1 + s) / 2 < 1", List(s), sBelow)
      gap <- kit.term("1 - (s:real)", values)
      gapPos <- linear(kit, "!s:real. s < 1 ==> 0 < 1 - s", List(s), sBelow)
      gapNonNeg <- apply(kit, kit.leOfLt, List(zero, gap), gapPos)
      gapNonZero <- apply(kit, kit.positiveNotZero, List(gap), gapPos)

      // x = 2 s / (1 - s) is not negative, and (1 - s) x = 2 s
      x <- kit.term("2 * (s:real) / (1 - s)", values)
      twice <- kit.term("2 * (s:real)", values)
      reciprocal <- kit.term("inv (1 - (s:real))", values)
      twiceNonNeg <- linear(kit, "!s:real. 0 <= s ==> 0 <= 2 * s", List(s), sNonNeg)
      recipNonNeg <- apply(kit, pieces.inversePositive, List(gap), gapPos).flatMap(p => apply(kit, kit.leOfLt, List(zero, reciprocal), p))
      productNonNeg <- apply(kit, pieces.productNonNeg, List(twice, reciprocal), twiceNonNeg, recipNonNeg)
      asQuotient <- kit.proposition("2 * (s:real) * inv (1 - s) = 2 * s / (1 - s)").flatMap(kit.ring.prove)
      xNonNeg <- Limit.rewriteInProposition(asQuotient, productNonNeg)
      // `Field` cancels an ATOM: at `1 - s` it distributes the product first and the reciprocal
      // never meets its denominator, so the cancellation is proved at a variable and specialised.
      g = Term.variable("g", values)
      t = Term.variable("t", values)
      cancelledAtAtom <- kit.proposition("(g:real) * ((t:real) / g) = t").flatMap(pieces.field.prove)
      condition <- kit.proposition("~((g:real) = 0)")
      general <- rules.disch(condition, cancelledAtAtom).flatMap(rules.genAll(_, List(g, t)))
      cancel <- apply(kit, general, List(gap, twice), gapNonZero)
      bound <- kit.term("NUM_CEIL (2 * (s:real) / (1 - s))", numbers)
      ceiling <- apply(kit, pieces.ceilLe, List(x), xNonNeg)

      // past the bound the ratio of consecutive terms is at most r
      assumedGuard <- kit.assume("NUM_LE (NUM_CEIL (2 * (s:real) / (1 - s))) (n:num)")
      (guard, isPast) = assumedGuard
      m <- kit.term("real_of_num (n:num)", values)
      ceilReal <- kit.term("real_of_num (NUM_CEIL (2 * (s:real) / (1 - s)))", values)
      embedded <- apply(kit, pieces.realLe, List(bound, n), isPast)
      xUnderM <- linear(kit, "!a:real. !b:real. !c:real. a <= b ==> b <= c ==> a <= c", List(x, ceilReal, m), ceiling, embedded)
      scaledUp <- apply(kit, kit.multiplyLe, List(gap, x, m), gapNonNeg, xUnderM)
      key <- linear(kit,
        "!s:real. !x:real. !m:real. x * (1 - s) <= m * (1 - s) ==> (1 - s) * x = 2 * s ==> (m + 1) * s <= (1 + s) / 2 * m",
        List(s, x, m), scaledUp, cancel)
      power <- kit.term("abs (Power (s:real) (n:num))", values)
      powerAt <- kit.term("Power (s:real) (n:num)", values)
      powerNonNeg <- rules.spec(powerAt, kit.absNonNegative)
      leftFactor <- kit.term("(real_of_num (n:num) + 1) * (s:real)", values)
      rightFactor <- kit.term("(1 + (s:real)) / 2 * real_of_num (n:num)", values)
      weighted <- apply(kit, kit.multiplyLe, List(power, leftFactor, rightFactor), powerNonNeg, key)

      // the two sides, spelled as the ratio test asks
      sucReal <- kit.term("real_of_num (SUC (n:num))", values)
      sucPower <- kit.term("Power (s:real) (SUC (n:num))", values)
      productAbs <- rules.specAll(kit.absMultiplicative, List(sucReal, sucPower))
      sucN <- kit.term("SUC (n:num)", numbers)
      sucRealNonNeg <- rules.spec(sucN, pieces.realNonNeg)
      sucRealSize <- sizeOf(kit, sucRealNonNeg)
      sucRealValue <- rules.spec(n, pieces.realSuc)
      sucRealAbs <- Conv.trans(sucRealSize, sucRealValue)
      step1 <- Limit.rewriteInProposition(sucRealAbs, productAbs)
      powerStep <- rules.specAll(kit.powerAtSuccessor, List(s, n))
      absTemplate <- kit.term("\\y:real. abs y", Type.fun(values, values))
      powerAbs <- Conv.apTerm(absTemplate, powerStep).flatMap(Conv.betaSides)
      splitAbs <- rules.specAll(kit.absMultiplicative, List(s, powerAt))
      sSize <- sizeOf(kit, sNonNeg)
      splitPlain <- Limit.rewriteInProposition(sSize, splitAbs)
      sucPowerAbs <- Conv.trans(powerAbs, splitPlain)
      step2 <- Limit.rewriteInProposition(sucPowerAbs, step1)
      regroup <- kit
        .proposition("(real_of_num (n:num) + 1) * ((s:real) * abs (Power s n)) = ((real_of_num n + 1) * s) * abs (Power s n)")
        .flatMap(kit.ring.prove)
      leftSide <- Conv.trans(step2, regroup)
      nAbs <- rules.specAll(kit.absMultiplicative, List(m, powerAt))
      mNonNeg <- rules.spec(n, pieces.realNonNeg)
      mSize <- sizeOf(kit, mNonNeg)
      nAbsPlain <- Limit.rewriteInProposition(mSize, nAbs)
      regroupRight <- kit
        .proposition("((1 + (s:real)) / 2 * real_of_num (n:num)) * abs (Power s n) = (1 + s) / 2 * (real_of_num n * abs (Power s n))")
        .flatMap(kit.ring.prove)
      rightDone <- Conv.sym(nAbsPlain).flatMap(Limit.rewriteInProposition(_, regroupRight))
      leftDone <- Conv.sym(leftSide).flatMap(Limit.rewriteInProposition(_, weighted))
      ratio <- Limit.rewriteInProposition(rightDone, leftDone)
      target <- kit.proposition(
        "abs (real_of_num (SUC (n:num)) * Power (s:real) (SUC n)) <= (1 + s) / 2 * abs (real_of_num n * Power s n)")
      landed <- kit.landsOn(ratio, target)
      everyStep <- rules.disch(guard, landed).flatMap(rules.gen(n, _))

      converging <- apply(kit, pieces.ratioTest, List(terms, r, bound), rNonNeg, rBelow, everyStep)
      result <- rules.disch(p2, converging).flatMap(rules.disch(p1, _)).flatMap(rules.gen(s, _))
    } yield result
  }


  /** `|- !k s. 0 <= s ==> s < 1 ==> ?l. converges (Sum (\i. Power (real_of_num i) k * Power s i)) l` */
  private def polyNonNeg(kit: Kit, pieces: Pieces, index: Kernel.Thm, boundedFact: Kernel.Thm, powerNonNegFact: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val s = Term.variable("s", values)
    val k = Term.variable("k", numbers)
    val i = Term.variable("i", numbers)
    val c = Term.variable("C", values)
    val l1 = Term.variable("L1", values)
    val l2 = Term.variable("L2", values)
    val claimText = "!s:real. 0 <= s ==> s < 1 ==> ?l:real. converges (Sum (\\i:num. Power (real_of_num i) (k:num) * Power s i)) l"

    def nonNegPower(base: Term, baseNonNeg: Kernel.Thm, exponent: Term): Either[LogicError, Kernel.Thm] =
      rules.spec(base, powerNonNegFact).flatMap(rules.mp(_, baseNonNeg)).flatMap(rules.spec(exponent, _))

    for {
      zero <- kit.term("0:real", values)
      predicate <- kit.term("\\k:num. " + claimText, Type.fun(numbers, Type.Bool))
      induction <- apply(kit, pieces.induction, List(predicate))

      /* ---- base: the geometric series, with a factor of one in front ---- */
      base <- for {
        a1 <- kit.assume("0 <= s:real"); (p1, sNonNeg) = a1
        a2 <- kit.assume("s:real < 1"); (p2, sBelow) = a2
        sSize <- sizeOf(kit, sNonNeg)
        absS <- kit.term("abs (s:real)", values)
        small <- linear(kit, "!a:real. !b:real. a = b ==> b < 1 ==> a < 1", List(absS, s), sSize, sBelow)
        geometric <- rules.spec(s, pieces.geometric).flatMap(rules.mp(_, small))
        parts <- Limit.convergenceOf(geometric)
        powers <- kit.term("\\i:num. Power (s:real) i", sequences)
        weighted <- kit.term("\\i:num. Power (real_of_num i) 0 * Power (s:real) i", sequences)
        atI <- kit.term("real_of_num (i:num)", values)
        unit <- rules.spec(atI, kit.powerAtZero)
        oneTimes <- kit.proposition("1 * Power (s:real) (i:num) = Power s i").flatMap(kit.ring.prove)
        pointwise <- Conv.sym(unit).flatMap(Limit.rewriteInProposition(_, oneTimes)).flatMap(Conv.sym).flatMap(rules.gen(i, _))
        sums <- apply(kit, kit.congruence, List(powers, weighted), pointwise)
        n = Term.variable("n", numbers)
        guard <- kit.proposition("NUM_LE ZERO (n:num)")
        agree <- rules.spec(n, sums).flatMap(rules.disch(guard, _)).flatMap(rules.gen(n, _))
        series <- kit.term("Sum (\\i:num. Power (real_of_num i) 0 * Power (s:real) i)", sequences)
        indexZero <- kit.term("ZERO", numbers)
        carried <- apply(kit, kit.eventually, List(parts._1, series, parts._2, indexZero), agree, geometric)
        packed <- kit.exists("?l:real. converges (Sum (\\i:num. Power (real_of_num i) 0 * Power (s:real) i)) l", parts._2, carried)
        result <- rules.disch(p2, packed).flatMap(rules.disch(p1, _)).flatMap(rules.gen(s, _))
      } yield result

      /* ---- step: one more factor of the index costs a bounded sequence ---- */
      step <- for {
        ih <- Parser.proposition(kit.theory, kit.notation, claimText).flatMap(p => LogicError.lift(Kernel.assume(p)))
        a1 <- kit.assume("0 <= s:real"); (p1, sNonNeg) = a1
        a2 <- kit.assume("s:real < 1"); (p2, sBelow) = a2
        half <- kit.term("(1 + (s:real)) / 2", values)
        halfNonNeg <- linear(kit, "!s:real. 0 <= s ==> 0 <= (1 + s) / 2", List(s), sNonNeg)
        halfBelow <- linear(kit, "!s:real. s < 1 ==> (1 + s) / 2 < 1", List(s), sBelow)
        gap <- kit.term("1 - (s:real)", values)
        square <- rules.spec(gap, pieces.square)
        underSquare <- linear(kit, "!s:real. 0 <= (1 - s) * (1 - s) ==> s <= (1 + s) / 2 * ((1 + s) / 2)", List(s), square)
        sSize <- sizeOf(kit, sNonNeg)
        absS <- kit.term("abs (s:real)", values)
        halfSquared <- kit.term("(1 + (s:real)) / 2 * ((1 + s) / 2)", values)
        absUnder <- linear(kit, "!a:real. !b:real. !c:real. a = b ==> b <= c ==> a <= c", List(absS, s, halfSquared), sSize, underSquare)

        // the index times the powers of the half-way point is bounded
        degreeOne <- apply(kit, index, List(half), halfNonNeg, halfBelow)
        firstTerms <- kit.term("\\i:num. real_of_num i * Power ((1 + (s:real)) / 2) i", sequences)
        a3 <- kit.assume("converges (Sum (\\i:num. real_of_num i * Power ((1 + (s:real)) / 2) i)) (L1:real)")
        (_, atL1) = a3
        vanishing <- apply(kit, pieces.termsVanish, List(firstTerms, l1), atL1)
        boundedTerms <- apply(kit, boundedFact, List(firstTerms, zero), vanishing)
        a4 <- kit.assume("!n:num. abs (real_of_num n * Power ((1 + (s:real)) / 2) n) <= C:real")
        (_, underC) = a4

        // the previous degree at the half-way point, scaled by C
        previous <- rules.spec(half, ih).flatMap(rules.mp(_, halfNonNeg)).flatMap(rules.mp(_, halfBelow))
        a5 <- kit.assume("converges (Sum (\\i:num. Power (real_of_num i) (k:num) * Power ((1 + (s:real)) / 2) i)) (L2:real)")
        (_, atL2) = a5
        inner <- kit.term("\\i:num. Power (real_of_num i) (k:num) * Power ((1 + (s:real)) / 2) i", sequences)
        scaled <- apply(kit, pieces.scaleConverges, List(inner, c, l2), atL2)
        scaledParts <- Limit.convergenceOf(scaled)
        dominatingSeries <- scaledParts._1 match { case App(_, g) => Right(g); case o => Left(NotOfForm("a series", o)) }

        // non-negativities at a symbolic index
        a <- kit.term("real_of_num (i:num)", values)
        aNonNeg <- rules.spec(i, pieces.realNonNeg)
        kPower <- kit.term("Power (real_of_num (i:num)) (k:num)", values)
        kNonNeg <- nonNegPower(a, aNonNeg, k)
        sucK <- kit.term("SUC (k:num)", numbers)
        sucKNonNeg <- nonNegPower(a, aNonNeg, sucK)
        q <- kit.term("Power ((1 + (s:real)) / 2) (i:num)", values)
        qNonNeg <- nonNegPower(half, halfNonNeg, i)
        sPower <- kit.term("Power (s:real) (i:num)", values)
        sPowerNonNeg <- nonNegPower(s, sNonNeg, i)
        kq <- kit.term("Power (real_of_num (i:num)) (k:num) * Power ((1 + (s:real)) / 2) i", values)
        kqNonNeg <- apply(kit, pieces.productNonNeg, List(kPower, q), kNonNeg, qNonNeg)
        atZeroTerm <- kit.term("abs (real_of_num ZERO * Power ((1 + (s:real)) / 2) ZERO)", values)
        indexZero <- kit.term("ZERO", numbers)
        cAtZero <- rules.spec(indexZero, underC)
        firstTerm <- kit.term("real_of_num ZERO * Power ((1 + (s:real)) / 2) ZERO", values)
        absAtZero <- rules.spec(firstTerm, kit.absNonNegative)
        cNonNeg <- linear(kit, "!a:real. !c:real. 0 <= a ==> a <= c ==> 0 <= c", List(atZeroTerm, c), absAtZero, cAtZero)
        gNonNeg <- apply(kit, pieces.productNonNeg, List(c, kq), cNonNeg, kqNonNeg).flatMap(rules.gen(i, _))
        sucKPower <- kit.term("Power (real_of_num (i:num)) (SUC (k:num))", values)
        fNonNeg <- apply(kit, pieces.productNonNeg, List(sucKPower, sPower), sucKNonNeg, sPowerNonNeg).flatMap(rules.gen(i, _))

        // the dominating partial sums are under C * L2
        underLimit <- apply(kit, kit.belowLimit, List(dominatingSeries, scaledParts._2), gNonNeg, scaled)
        boundedSums <- kit.exists("?b:real. !n:num. Sum (\\i:num. (C:real) * (Power (real_of_num i) (k:num) * Power ((1 + (s:real)) / 2) i)) n <= b", scaledParts._2, underLimit)

        // termwise: s^i <= q^2 and i q^i <= C
        powerBound <- apply(kit, kit.powerOfAMagnitude, List(s, halfSquared, i), absUnder)
        above <- rules.spec(sPower, kit.absAbove)
        absSPower <- kit.term("abs (Power (s:real) (i:num))", values)
        squaredPower <- kit.term("Power ((1 + (s:real)) / 2 * ((1 + s) / 2)) (i:num)", values)
        sUnder <- linear(kit, "!a:real. !b:real. !c:real. a <= b ==> b <= c ==> a <= c", List(sPower, absSPower, squaredPower), above, powerBound)
        splitSquare <- rules.specAll(pieces.powerOfProduct, List(half, half, i))
        sUnderQQ <- Limit.rewriteInProposition(splitSquare, sUnder)
        ak <- kit.term("real_of_num (i:num) * Power (real_of_num i) (k:num)", values)
        akNonNeg <- apply(kit, pieces.productNonNeg, List(a, kPower), aNonNeg, kNonNeg)
        qq <- kit.term("Power ((1 + (s:real)) / 2) (i:num) * Power ((1 + s) / 2) i", values)
        h2 <- apply(kit, kit.multiplyLe, List(ak, sPower, qq), akNonNeg, sUnderQQ)
        cAtI <- rules.spec(i, underC)
        aq <- kit.term("real_of_num (i:num) * Power ((1 + (s:real)) / 2) i", values)
        aqNonNeg <- apply(kit, pieces.productNonNeg, List(a, q), aNonNeg, qNonNeg)
        aqSize <- sizeOf(kit, aqNonNeg)
        absAq <- kit.term("abs (real_of_num (i:num) * Power ((1 + (s:real)) / 2) i)", values)
        aqUnderC <- linear(kit, "!a:real. !b:real. !c:real. a = b ==> a <= c ==> b <= c", List(absAq, aq, c), aqSize, cAtI)
        h4 <- apply(kit, kit.multiplyLe, List(kq, aq, c), kqNonNeg, aqUnderC)
        goalText = "(real_of_num (i:num) * Power (real_of_num i) (k:num)) * Power (s:real) i <= (C:real) * (Power (real_of_num i) k * Power ((1 + s) / 2) i)"
        goal <- kit.proposition(goalText)
        implication <- kit.logic.mkImp(h4.conclusion, goal).flatMap(kit.logic.mkImp(h2.conclusion, _))
        combined <- kit.linarith.prove(implication).flatMap(rules.mp(_, h2)).flatMap(rules.mp(_, h4))
        powerStep <- rules.specAll(kit.powerAtSuccessor, List(a, k)).flatMap(Conv.sym)
        dominatedAt <- Limit.rewriteInProposition(powerStep, combined)
        dominated <- rules.gen(i, dominatedAt)

        terms <- kit.term("\\i:num. Power (real_of_num i) (SUC (k:num)) * Power (s:real) i", sequences)
        converging <- apply(kit, kit.comparison, List(terms, dominatingSeries), fNonNeg, dominated, boundedSums)
        overL2 <- rules.existsElim(previous, l2, converging)
        overC <- rules.existsElim(boundedTerms, c, overL2)
        overL1 <- rules.existsElim(degreeOne, l1, overC)
        atSuc <- rules.disch(p2, overL1).flatMap(rules.disch(p1, _)).flatMap(rules.gen(s, _))
        result <- rules.disch(ih.conclusion, atSuc).flatMap(rules.gen(k, _))
      } yield result

      both <- rules.conjIntro(base, step)
      everyK <- rules.mp(induction, both)
    } yield everyK
  }


  /**
   * From `!s. 0 <= s ==> s < 1 ==> ?l. converges (Sum (\i. F i * Power s i)) l` with `F i >= 0`,
   * `!q. abs q < 1 ==> ?l. converges (Sum (\i. F i * Power q i)) l`, by absolute convergence.
   * `factor` is `F` as a lambda over the index; `factorNonNeg` proves `0 <= F i` at a symbolic `i`.
   */
  private def absolutely(kit: Kit, pieces: Pieces, nonNeg: Kernel.Thm, factor: String => String,
                 factorNonNeg: Term => Either[LogicError, Kernel.Thm],
                 powerNonNegFact: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val q = Term.variable("q", values)
    val i = Term.variable("i", numbers)
    val big = Term.variable("L", values)
    val m = Term.variable("m", values)
    for {
      a1 <- kit.assume("abs (q:real) < 1"); (p1, small) = a1
      size <- kit.term("abs (q:real)", values)
      sizeNonNeg <- rules.spec(q, kit.absNonNegative)
      majorant <- apply(kit, nonNeg, List(size), sizeNonNeg, small)
      majorantTerms <- kit.term(s"\\i:num. ${factor("i")} * Power (abs (q:real)) i", sequences)
      a2 <- LogicError.lift(Term.app(majorantTerms, i)).flatMap(_ =>
        kit.assume(s"converges (Sum (\\i:num. ${factor("i")} * Power (abs (q:real)) i)) (L:real)"))
      (_, atL) = a2
      fi <- kit.term(factor("i:num"), values)
      fNonNeg <- factorNonNeg(i)
      absPower <- kit.term("Power (abs (q:real)) (i:num)", values)
      absPowerNonNeg <- rules.spec(size, powerNonNegFact).flatMap(rules.mp(_, sizeNonNeg)).flatMap(rules.spec(i, _))
      majorantNonNeg <- apply(kit, pieces.productNonNeg, List(fi, absPower), fNonNeg, absPowerNonNeg).flatMap(rules.gen(i, _))
      underL <- apply(kit, kit.belowLimit, List(majorantTerms, big), majorantNonNeg, atL)
      bounded <- kit.exists(s"?b:real. !n:num. Sum (\\i:num. ${factor("i")} * Power (abs (q:real)) i) n <= b", big, underL)

      // |F i q^i| = F i |q^i| <= F i |q|^i
      qPower <- kit.term("Power (q:real) (i:num)", values)
      split <- rules.specAll(kit.absMultiplicative, List(fi, qPower))
      fSize <- sizeOf(kit, fNonNeg)
      splitPlain <- Limit.rewriteInProposition(fSize, split)
      sizeLeSize <- linear(kit, "!a:real. a <= a", List(size))
      powerLe <- apply(kit, kit.powerOfAMagnitude, List(q, size, i), sizeLeSize)
      absQPower <- kit.term("abs (Power (q:real) (i:num))", values)
      scaled <- apply(kit, kit.multiplyLe, List(fi, absQPower, absPower), fNonNeg, powerLe)
      product <- at(kit, "\\a:real. \\b:real. a * b", fi, qPower)
      term <- at(kit, "\\a:real. \\b:real. abs (a * b)", fi, qPower)
      bound <- at(kit, "\\a:real. \\b:real. a * b", fi, absPower)
      goal <- at(kit, "\\x:real. \\y:real. x <= y", term, bound)
      implication <- kit.logic.mkImp(scaled.conclusion, goal).flatMap(kit.logic.mkImp(splitPlain.conclusion, _))
      dominatedAt <- kit.linarith.prove(implication).flatMap(rules.mp(_, splitPlain)).flatMap(rules.mp(_, scaled))
      dominated <- rules.gen(i, dominatedAt)
      absTerms <- kit.term(s"\\i:num. abs (${factor("i")} * Power (q:real) i)", sequences)
      absTermNonNeg <- rules.spec(product, kit.absNonNegative).flatMap(rules.gen(i, _))
      absolute <- apply(kit, kit.comparison, List(absTerms, majorantTerms), absTermNonNeg, dominated, bounded)
      a3 <- kit.assume(s"converges (Sum (\\i:num. abs (${factor("i")} * Power (q:real) i))) (m:real)")
      (_, atM) = a3
      plainTerms <- kit.term(s"\\i:num. ${factor("i")} * Power (q:real) i", sequences)
      converging <- apply(kit, kit.absolute, List(plainTerms, m), atM)
      overM <- rules.existsElim(absolute, m, converging)
      overL <- rules.existsElim(majorant, big, overM)
      result <- rules.disch(p1, overL).flatMap(rules.gen(q, _))
    } yield result
  }

  /**
   * `!q. 1 <= abs q ==> diverges (Sum (\i. F i * Power q i))` where `1 <= F n` from `n = 1` on,
   * by the term test; `atLeastOne` proves `1 <= F n` under `NUM_LE (SUC 0) n` at a symbolic `n`.
   */
  private def diverging(kit: Kit, pieces: Pieces, factor: String => String, atLeastOne: Term => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val q = Term.variable("q", values)
    val n = Term.variable("n", numbers)
    for {
      a1 <- kit.assume("1 <= abs (q:real)"); (p1, large) = a1
      statement <- kit.proposition("!n:num. 1 <= abs (Power (q:real) n)")
      absTemplate <- kit.term("\\y:real. abs y", Type.fun(values, values))
      powers <- kit.induct.proveBy(
        statement,
        base =>
          for {
            zeroPower <- rules.spec(q, kit.powerAtZero)
            absZero <- Conv.apTerm(absTemplate, zeroPower).flatMap(Conv.betaSides)
            oneNonNeg <- kit.linarith.prove("0 <= (1:real)")
            absOne <- sizeOf(kit, oneNonNeg)
            value <- Conv.trans(absZero, absOne)
            left <- Limit.destructEquation(value).map(_._1)
            result <- linear(kit, "!x:real. x = 1 ==> 1 <= x", List(left), value).flatMap(kit.landsOn(_, base))
          } yield result,
        step =>
          for {
            next <- rules.specAll(kit.powerAtSuccessor, List(q, step.variable))
            absNext <- Conv.apTerm(absTemplate, next).flatMap(Conv.betaSides)
            current <- at(kit, "\\k:num. Power (q:real) k", step.variable)
            split <- rules.specAll(kit.absMultiplicative, List(q, current))
            value <- Conv.trans(absNext, split)
            currentSize <- at(kit, "\\k:num. abs (Power (q:real) k)", step.variable)
            currentNonNeg <- rules.spec(current, kit.absNonNegative)
            one <- kit.term("1:real", values)
            size <- kit.term("abs (q:real)", values)
            scaled <- apply(kit, kit.multiplyLe, List(currentSize, one, size), currentNonNeg, large)
            left <- Limit.destructEquation(value).map(_._1)
            product <- Limit.destructEquation(value).map(_._2)
            result <- linear(kit, "!x:real. !p:real. !c:real. x = p ==> 1 * c <= p ==> 1 <= c ==> 1 <= x",
              List(left, product, currentSize), value, scaled, step.hypothesis).flatMap(kit.landsOn(_, step.goal))
          } yield result
      )
      // at an index from one on, both factors are at least one
      a2 <- kit.assume("NUM_LE (SUC 0) (n:num)"); (guard, isPast) = a2
      fn <- kit.term(factor("n:num"), values)
      fAtLeast <- atLeastOne(n).flatMap(f => f.hypotheses match {
        case Nil => Right(f)
        case List(h) if h == guard => Right(f)
        case other => Left(NotOfForm("a lower bound owing at most the guard", f.conclusion))
      })
      qPower <- kit.term("Power (q:real) (n:num)", values)
      powerAtLeast <- rules.spec(n, powers)
      absQPower <- kit.term("abs (Power (q:real) (n:num))", values)
      qPowerNonNeg <- rules.spec(qPower, kit.absNonNegative)
      fNonNeg <- linear(kit, "!x:real. 1 <= x ==> 0 <= x", List(fn), fAtLeast)
      split <- rules.specAll(kit.absMultiplicative, List(fn, qPower))
      fSize <- sizeOf(kit, fNonNeg)
      splitPlain <- Limit.rewriteInProposition(fSize, split)
      one <- kit.term("1:real", values)
      scaled <- apply(kit, kit.multiplyLe, List(absQPower, one, fn), qPowerNonNeg, fAtLeast)
      whole <- Limit.destructEquation(splitPlain)
      atN <- linear(kit, "!w:real. !p:real. !a:real. w = p ==> 1 * a <= p ==> 1 <= a ==> 1 <= w",
        List(whole._1, whole._2, absQPower), splitPlain, scaled, powerAtLeast)
      bound <- rules.disch(guard, atN).flatMap(rules.gen(n, _))
      terms <- kit.term(s"\\i:num. ${factor("i")} * Power (q:real) i", sequences)
      sucZero <- kit.term("SUC 0", numbers)
      onePositive <- kit.linarith.prove("0 < (1:real)")
      diverging <- apply(kit, pieces.termTest, List(terms, one, sucZero), onePositive, bound)
      result <- rules.disch(p1, diverging).flatMap(rules.gen(q, _))
    } yield result
  }

  /** `1 <= real_of_num n` under `NUM_LE (SUC 0) n`. */
  private def indexAtLeastOne(kit: Kit, pieces: Pieces, n: Term): Either[LogicError, Kernel.Thm] =
    for {
      guard <- at(kit, "\\n:num. NUM_LE (SUC 0) n", n)
      assumed <- LogicError.lift(Kernel.assume(guard))
      sucZero <- kit.term("SUC 0", numbers)
      zeroN <- kit.term("0", numbers)
      embedded <- apply(kit, pieces.realLe, List(sucZero, n), assumed)
      one <- apply(kit, pieces.realSuc, List(zeroN))
      zero = pieces.realZero
      m <- at(kit, "\\n:num. real_of_num n", n)
      r1 <- kit.term("real_of_num (SUC 0)", values)
      r0 <- kit.term("real_of_num 0", values)
      result <- linear(kit, "!a:real. !b:real. !m:real. a <= m ==> a = b + 1 ==> b = 0 ==> 1 <= m", List(r1, r0, m), embedded, one, zero)
    } yield result

  /** `1 <= Power (real_of_num n) k` under `NUM_LE (SUC 0) n`, for the `k` free in the kit's reading. */
  private def polyAtLeastOne(kit: Kit, pieces: Pieces, n: Term): Either[LogicError, Kernel.Thm] =
    for {
      mAtLeast <- indexAtLeastOne(kit, pieces, n)
      m <- at(kit, "\\n:num. real_of_num n", n)
      one <- kit.term("1:real", values)
      onePositive <- kit.linarith.prove("0 < (1:real)")
      k <- kit.term("k:num", numbers)
      monotone <- apply(kit, pieces.powerMonotone, List(one, m), onePositive, mAtLeast).flatMap(kit.rules.spec(k, _))
      unit <- kit.rules.spec(k, pieces.powerOne)
      result <- Limit.rewriteInProposition(unit, monotone)
    } yield result

  /**
   * The six facts `Limit` publishes from this file, under the names it gives them.
   *
   * `CONVERGES_BOUNDED` and `POWER_NONNEG` are published because they are general and each has a
   * second consumer here; the non-negative-ratio forms of the degree-one and degree-`k` lemmas are
   * not, because every caller has a signed ratio and the published forms take one.
   */
  def derive(kit: Kit, pieces: Pieces): Either[LogicError, Map[String, Kernel.Thm]] = {
    val k = Term.variable("k", numbers)
    def realNonNegAt(i: Term): Either[LogicError, Kernel.Thm] = kit.rules.spec(i, pieces.realNonNeg)
    for {
      boundedFact <- bounded(kit, pieces)
      powers <- powerNonNeg(kit, pieces)
      index <- indexNonNeg(kit, pieces)
      poly <- polyNonNeg(kit, pieces, index, boundedFact, powers)
      indexConverges <- absolutely(kit, pieces, index, i => s"real_of_num ($i)", realNonNegAt, powers)
      polyAtK <- kit.rules.spec(k, poly)
      polyConverges <- absolutely(
        kit,
        pieces,
        polyAtK,
        i => s"Power (real_of_num ($i)) (k:num)",
        i =>
          for {
            embedded <- at(kit, "\\i:num. real_of_num i", i)
            nonNeg <- realNonNegAt(i)
            atK <- kit.rules.spec(embedded, powers).flatMap(kit.rules.mp(_, nonNeg)).flatMap(kit.rules.spec(k, _))
          } yield atK,
        powers
      ).flatMap(kit.rules.gen(k, _))
      indexDiverges <- diverging(kit, pieces, i => s"real_of_num ($i)", n => indexAtLeastOne(kit, pieces, n))
      polyDiverges <- diverging(kit, pieces, i => s"Power (real_of_num ($i)) (k:num)", n => polyAtLeastOne(kit, pieces, n))
        .flatMap(kit.rules.gen(k, _))
    } yield Map(
      Limit.Bounded -> boundedFact,
      Limit.PowerNonNegative -> powers,
      Limit.IndexGeometricConverges -> indexConverges,
      Limit.IndexGeometricDiverges -> indexDiverges,
      Limit.PolyGeometricConverges -> polyConverges,
      Limit.PolyGeometricDiverges -> polyDiverges
    )
  }
}
