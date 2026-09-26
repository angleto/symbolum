package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The p-adic valuation on `num`: the exponent of the largest power of `p` dividing `n`, and the
 * laws that make it a register.
 *
 * Not a development: it declares nothing, and what it derives `Primes` publishes under names it
 * declares, the arrangement `Freshman` and `Euler` have. `NUM_VALUATION` is `Modular`'s, beside
 * `NUM_TOTIENT`, because `Primes` extends nothing.
 *
 * == Why the definition is a choice over the characterisation ==
 *
 * `NUM_VALUATION p n` is the `k` with `p^k | n` and not `p^(k+1) | n`. The alternative was a
 * count through the factorisation, `NUM_FACTORISATION`'s sorted family and the number of its
 * entries equal to `p`, which is what the card that asked for this suggested ("from the uniqueness
 * of the factorisation"). It was not taken because nothing a caller asks of a valuation reads a
 * family: the register machine tests `p^k | n`, and the law for a product is proved by cancelling a
 * power, so a count would have had to be converted back into the divisibility statement at every
 * use. What the uniqueness of factorisation supplies to that proof is Euclid's lemma, and
 * `NUM_EUCLID` is already that.
 *
 * == The order the facts are proved in ==
 *
 * `NUM_LT_POW` (`n < p^n` for `1 < p`) bounds the powers dividing a positive `n`, which is the
 * hypothesis `NUM_GREATEST` needs; the greatest such exponent is the valuation, and that is
 * existence. `NUM_POW_DIVIDES_POW` is the monotonicity every other argument uses: a smaller power
 * divides a larger one. Uniqueness is then a trichotomy with no hypothesis on `p` or `n`, which is
 * why `NUM_VALUATION_UNIQUE` is the fact the others are proved through: each of them exhibits a
 * `k` and shows it passes the test.
 *
 * `NUM_VALUATION_MUL` is the textbook argument. Write `a = p^i a'` and `b = p^j b'`; then
 * `p^(i+j)` divides `ab`, and if `p^(i+j+1)` did, cancelling `p^(i+j)` would put `p` under
 * `a' b'`, so under `a'` or `b'` by Euclid, and then `p^(i+1)` would divide `a` or `p^(j+1)`
 * would divide `b`. Both hypotheses of positivity are needed and neither is decoration: at `a = 0`
 * the left side is a valuation of zero, which is the unnamed value the definition leaves there.
 *
 * == Divisibility, and one FRACTRAN fraction, on the registers ==
 *
 * `NUM_DIVIDES_VALUATION` is the fact the register reading rests on: between positive numbers,
 * `b | c` exactly when no register of `b` exceeds `c`'s. Three facts follow for one fraction `a/b`
 * at a state `n`, which is the unit a FRACTRAN step is made of: whether it applies, what it does to
 * each register, and that the registers determine the state it lands on. The step relation itself
 * is not defined here, so the simulation of a whole program is stated where it is.
 */
private[theories] object Valuation {
  import Steps.*

  /**
   * The definitions the derivations unfold: the two orders of `num`, the valuation itself, and the
   * choice axiom that names its witness.
   */
  final case class Definitions(
    strictOrder: Kernel.Thm,
    nonStrictOrder: Kernel.Thm,
    valuation: Kernel.Thm,
    choice: Kernel.Thm
  )

  private def unfoldedBy(definition: Kernel.Thm, arguments: List[Term], thm: Kernel.Thm): R[Kernel.Thm] =
    Conv.unfold(definition, arguments).flatMap(e => LogicError.lift(Kernel.eqMp(e, thm)))

  private def normal(thm: Kernel.Thm): R[Kernel.Thm] =
    Conv.betaNormalise(thm.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, thm)))

  private def numbersTo(kit: Kit, result: Type): Type = Type.fun(kit.numbers, result)

  private def pow(kit: Kit, base: Term, exponent: Term): R[Term] =
    kit.term("NUM_POW", numbersTo(kit, numbersTo(kit, kit.numbers))).flatMap(app(_, base, exponent))

  private def plus(kit: Kit, x: Term, y: Term): R[Term] =
    kit.term("NUM_ADD", numbersTo(kit, numbersTo(kit, kit.numbers))).flatMap(app(_, x, y))

  /** `NUM_VALUATION p n = select (\k. ...)`, and the predicate chosen from. */
  private def chosen(definitions: Definitions, p: Term, n: Term): R[(Kernel.Thm, Term)] =
    for {
      equation <- Conv.unfold(definitions.valuation, List(p, n))
      right <- Limit.rightOf(equation)
      predicate <- right match {
        case App(_, predicate) => Right(predicate)
        case other => Left(NotOfForm("a choice", other))
      }
    } yield (equation, predicate)

  /** `0 < p` from `1 < p`. */
  private def positiveOfAbove(kit: Kit, p: Term, above: Kernel.Thm): R[Kernel.Thm] =
    for {
      z <- zero(kit)
      o <- one(kit)
      zeroBelowOne <- kit.use("NUM_ZERO_LT_SUC", List(z))
      both <- kit.rules.conjIntro(zeroBelowOne, above)
      r <- kit.use("NUM_LT_TRANS", List(z, o, p), both)
    } yield r

  /** `NUM_DIVIDES (NUM_POW p 0) n`: the zeroth power is one, and one divides everything. */
  private def zerothDivides(kit: Kit, p: Term, n: Term): R[Kernel.Thm] =
    for {
      z <- zero(kit)
      byOne <- kit.use("NUM_ONE_DIVIDES", List(n))
      powZero <- kit.use("NUM_POW_ZERO", List(p)).flatMap(Conv.sym)
      lambda <- kit.at("\\n:num. \\x:num. NUM_DIVIDES x n", n)
      r <- transport(lambda, powZero, byOne)
    } yield r

  /* ---------------------------------------------------------------- powers */

  /** `|- !p n. NUM_LT (SUC 0) p ==> NUM_LT n (NUM_POW p n)` */
  def ltPow(kit: Kit, definitions: Definitions): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val n = Term.variable("n", kit.numbers)
    val rules = kit.rules
    for {
      assumedAbove <- kit.assume("NUM_LT (SUC 0) (p:num)")
      (above, isAbove) = assumedAbove
      o <- one(kit)
      z <- zero(kit)
      pPositive <- positiveOfAbove(kit, p, isAbove)
      statement <- kit.proposition("!n:num. NUM_LT n (NUM_POW (p:num) n)")
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            zeroBelowOne <- kit.use("NUM_ZERO_LT_SUC", List(z))
            powZero <- kit.use("NUM_POW_ZERO", List(p)).flatMap(Conv.sym)
            lambda <- kit.at("\\x:num. NUM_LT 0 x")
            moved <- transport(lambda, powZero, zeroBelowOne)
            r <- kit.landsOn(moved, base)
          } yield r,
        step => {
          val m = step.variable
          for {
            pm <- pow(kit, p, m)
            sm <- succ(kit, m)
            pmp <- mul(kit, pm, p)
            // SUC m <= p^m, which is what m < p^m is by definition
            atMost <- unfoldedBy(definitions.strictOrder, List(m, pm), step.hypothesis)
            pmPositive <- kit.use("NUM_POW_POSITIVE", List(p, m), pPositive)
            grown <- kit.use("NUM_MUL_LT_MONOTONE", List(pm, o, p), pmPositive, isAbove)
            unit <- kit.use("NUM_MUL_ONE", List(pm))
            lambda1 <- kit.at("\\y:num. \\x:num. NUM_LT x y", pmp)
            below <- transport(lambda1, unit, grown)
            both <- rules.conjIntro(atMost, below)
            chained <- kit.use("NUM_LE_LT_TRANS", List(sm, pm, pmp), both)
            powSuc <- kit.use("NUM_POW_SUC", List(p, m)).flatMap(Conv.sym)
            lambda2 <- kit.at("\\s:num. \\x:num. NUM_LT s x", sm)
            moved <- transport(lambda2, powSuc, chained)
            r <- kit.landsOn(moved, step.goal)
          } yield r
        }
      )
      result <- rules.spec(n, proved).flatMap(rules.disch(above, _)).flatMap(rules.genAll(_, List(p, n)))
    } yield result
  }

  /** `|- !p j k. NUM_LE j k ==> NUM_DIVIDES (NUM_POW p j) (NUM_POW p k)` */
  def powDividesPow(kit: Kit, definitions: Definitions): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val j = Term.variable("j", kit.numbers)
    val k = Term.variable("k", kit.numbers)
    val d = Term.variable("d", kit.numbers)
    val rules = kit.rules
    for {
      assumedAtMost <- kit.assume("NUM_LE (j:num) (k:num)")
      (atMost, isAtMost) = assumedAtMost
      exists <- unfoldedBy(definitions.nonStrictOrder, List(j, k), isAtMost)
      predicate <- kit.logic.destExistsPredicate(exists.conclusion).toRight(NotOfForm("an existential", exists.conclusion))
      instance <- instantiate(predicate, d)
      sum <- assume(instance)
      powAdd <- kit.use("NUM_POW_ADD", List(p, j, d))
      lambda <- kit.at("\\x:num. NUM_POW (p:num) x = NUM_POW p (j:num) * NUM_POW p (d:num)")
      split <- transport(lambda, sum, powAdd)
      pj <- pow(kit, p, j)
      pk <- pow(kit, p, k)
      pd <- pow(kit, p, d)
      divides <- kit.use("NUM_DIVIDES_INTRO", List(pj, pk, pd), split)
      found <- rules.existsElim(exists, d, divides)
      result <- rules.disch(atMost, found).flatMap(rules.genAll(_, List(p, j, k)))
    } yield result
  }

  /* ---------------------------------------------------------------- the characterisation */

  /**
   * `|- !p n j k. NUM_DIVIDES (NUM_POW p j) n ==> ~(NUM_DIVIDES (NUM_POW p (SUC j)) n) ==>
   *     NUM_DIVIDES (NUM_POW p k) n ==> ~(NUM_DIVIDES (NUM_POW p (SUC k)) n) ==> j = k`
   *
   * Two exponents that both pass the test are equal: were one below the other, the power one past
   * the smaller would divide the larger power and so `n`, which the smaller one's refusal denies.
   */
  private def exponentUnique(kit: Kit, definitions: Definitions, powers: Kernel.Thm): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val n = Term.variable("n", kit.numbers)
    val j = Term.variable("j", kit.numbers)
    val k = Term.variable("k", kit.numbers)
    val rules = kit.rules

    // False, from `a < b`, `p^b | n` and `~(p^(SUC a) | n)`.
    def refuted(a: Term, b: Term, below: Kernel.Thm, divides: Kernel.Thm, refusal: Kernel.Thm): R[Kernel.Thm] =
      for {
        sa <- succ(kit, a)
        psa <- pow(kit, p, sa)
        pb <- pow(kit, p, b)
        atMost <- unfoldedBy(definitions.strictOrder, List(a, b), below)
        under <- kit.applyTo(powers, List(p, sa, b), atMost)
        chained <- kit.use("NUM_DIVIDES_TRANS", List(psa, pb, n), under, divides)
        absurd <- rules.notElim(refusal, chained)
      } yield absurd

    for {
      hj1 <- kit.assume("NUM_DIVIDES (NUM_POW (p:num) (j:num)) (n:num)")
      hj2 <- kit.assume("~(NUM_DIVIDES (NUM_POW (p:num) (SUC (j:num))) (n:num))")
      hk1 <- kit.assume("NUM_DIVIDES (NUM_POW (p:num) (k:num)) (n:num)")
      hk2 <- kit.assume("~(NUM_DIVIDES (NUM_POW (p:num) (SUC (k:num))) (n:num))")
      same <- eqTerm(j, k)
      total <- kit.use("NUM_LT_TOTAL", List(j, k))
      outer <- disj(kit, total.conclusion)
      (jBelow, rest) = outer
      inner <- disj(kit, rest)
      (equal, kBelow) = inner
      c1 <- assume(jBelow).flatMap(h => refuted(j, k, h, hk1._2, hj2._2)).flatMap(rules.falsityElim(same, _))
      c2 <- assume(equal)
      c3 <- assume(kBelow).flatMap(h => refuted(k, j, h, hj1._2, hk2._2)).flatMap(rules.falsityElim(same, _))
      assumedRest <- assume(rest)
      restCase <- rules.disjElim(assumedRest, c2, c3)
      both <- rules.disjElim(total, c1, restCase)
      result <- dischAll(kit, List(hj1._1, hj2._1, hk1._1, hk2._1), both)
        .flatMap(rules.genAll(_, List(p, n, j, k)))
    } yield result
  }

  /**
   * `|- !p n k. NUM_DIVIDES (NUM_POW p k) n ==> ~(NUM_DIVIDES (NUM_POW p (SUC k)) n) ==>
   *     NUM_VALUATION p n = k`
   */
  def unique(kit: Kit, definitions: Definitions, powers: Kernel.Thm): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val n = Term.variable("n", kit.numbers)
    val k = Term.variable("k", kit.numbers)
    val rules = kit.rules
    for {
      exponents <- exponentUnique(kit, definitions, powers)
      h1 <- kit.assume("NUM_DIVIDES (NUM_POW (p:num) (k:num)) (n:num)")
      h2 <- kit.assume("~(NUM_DIVIDES (NUM_POW (p:num) (SUC (k:num))) (n:num))")
      both <- rules.conjIntro(h1._2, h2._2)
      picked <- chosen(definitions, p, n)
      (named, predicate) = picked
      exists <- rules.existsIntro(predicate, k, both)
      witnessed <- Classical.witnessFrom(kit.logic, definitions.choice, exists).flatMap(normal)
      w1 <- rules.conjElim1(witnessed)
      w2 <- rules.conjElim2(witnessed)
      choice <- Limit.rightOf(named)
      equal <- kit.applyTo(exponents, List(p, n, choice, k), w1, w2, h1._2, h2._2)
      valued <- Conv.trans(named, equal)
      result <- dischAll(kit, List(h1._1, h2._1), valued).flatMap(rules.genAll(_, List(p, n, k)))
    } yield result
  }

  /**
   * `|- !p n. NUM_LT (SUC 0) p ==> NUM_LT 0 n ==>
   *     NUM_DIVIDES (NUM_POW p (NUM_VALUATION p n)) n /\ ~(NUM_DIVIDES (NUM_POW p (SUC (NUM_VALUATION p n))) n)`
   *
   * Existence, and the only fact here that needs `1 < p` and `0 < n`: the exponents whose power
   * divides `n` are non-empty, since the zeroth does, and bounded by `n`, since `k < p^k <= n`;
   * the greatest of them is one whose successor fails.
   */
  def spec(kit: Kit, definitions: Definitions, below: Kernel.Thm): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val n = Term.variable("n", kit.numbers)
    val m = Term.variable("m", kit.numbers)
    val zVar = Term.variable("z", kit.numbers)
    val rules = kit.rules
    for {
      assumedAbove <- kit.assume("NUM_LT (SUC 0) (p:num)")
      (above, isAbove) = assumedAbove
      assumedPositive <- kit.assume("NUM_LT 0 (n:num)")
      (positive, isPositive) = assumedPositive
      z <- zero(kit)
      dividing <- kit.at("\\p:num. \\n:num. \\k:num. NUM_DIVIDES (NUM_POW p k) n", p, n)
      greatest <- kit.use("NUM_GREATEST", List(dividing))
      antecedent <- imp(kit, greatest.conclusion)
      (conditions, _) = antecedent

      // non-empty: the zeroth power divides n
      atZero <- zerothDivides(kit, p, n)
      nonEmpty <- rules.existsIntro(dividing, z, atZero)

      // bounded by n: a power dividing a positive n is at most n, and its exponent is below it
      pz <- pow(kit, p, zVar)
      assumedDivides <- instantiate(dividing, zVar)
      hz <- assume(assumedDivides)
      sizes <- kit.use("NUM_DIVIDES_LE", List(pz, n), hz)
      exponentBelow <- kit.applyTo(below, List(p, zVar), isAbove)
      sizeCases <- disj(kit, sizes.conclusion)
      (atMostCase, zeroCase) = sizeCases
      zAtMost <- kit.term("NUM_LE (z:num) (n:num)", Type.Bool)
      first <- for {
        h <- assume(atMostCase)
        both <- rules.conjIntro(exponentBelow, h)
        lt <- kit.use("NUM_LT_LE_TRANS", List(zVar, pz, n), both)
        le <- kit.use("NUM_LE_OF_LT", List(zVar, n), lt)
      } yield le
      second <- for {
        h <- assume(zeroCase)
        lambda <- kit.at("\\x:num. NUM_LT 0 x")
        atZero <- transport(lambda, h, isPositive)
        irreflexive <- kit.use("NUM_LT_IRREFL", List(z))
        absurd <- rules.notElim(irreflexive, atZero)
        r <- rules.falsityElim(zAtMost, absurd)
      } yield r
      zBounded <- rules.disjElim(sizes, first, second)
      allBounded <- rules.disch(assumedDivides, zBounded).flatMap(rules.gen(zVar, _))
      bounding <- kit.at("\\p:num. \\n:num. \\y:num. !z:num. NUM_DIVIDES (NUM_POW p z) n ==> NUM_LE z y", p, n)
      bounded <- rules.existsIntro(bounding, n, allBounded)
      ante <- rules.conjIntro(nonEmpty, bounded)
      _ <- kit.landsOn(ante, conditions)
      greatestOne <- rules.mp(greatest, ante)

      // the greatest m: p^m divides n, and p^(SUC m) would be a larger exponent
      greatestPredicate <- kit.logic.destExistsPredicate(greatestOne.conclusion)
        .toRight(NotOfForm("an existential", greatestOne.conclusion))
      instance <- instantiate(greatestPredicate, m)
      hm <- assume(instance)
      atM <- rules.conjElim1(hm)
      maximal <- rules.conjElim2(hm)
      sm <- succ(kit, m)
      atSucTerm <- instantiate(dividing, sm)
      atSuc <- assume(atSucTerm)
      tooLarge <- rules.spec(sm, maximal).flatMap(rules.mp(_, atSuc))
      mBelow <- ltSuc(kit, m)
      notAtMost <- kit.use("NUM_LT_NOT_LE", List(m, sm), mBelow)
      absurd <- rules.notElim(notAtMost, tooLarge)
      refused <- rules.notIntro(atSucTerm, absurd)
      passes <- rules.conjIntro(atM, refused)
      picked <- chosen(definitions, p, n)
      (named, predicate) = picked
      exists <- rules.existsIntro(predicate, m, passes)
      found <- rules.existsElim(greatestOne, m, exists)

      witnessed <- Classical.witnessFrom(kit.logic, definitions.choice, found).flatMap(normal)
      back <- Conv.sym(named)
      renamed <- transport(predicate, back, witnessed)
      result <- dischAll(kit, List(above, positive), renamed).flatMap(rules.genAll(_, List(p, n)))
    } yield result
  }

  /**
   * `|- !p n k. NUM_LT (SUC 0) p ==> NUM_LT 0 n ==>
   *     (NUM_DIVIDES (NUM_POW p k) n = NUM_LE k (NUM_VALUATION p n))`
   *
   * The register reading: `p^k` divides `n` exactly when the valuation is at least `k`, which is
   * the test a FRACTRAN denominator makes on each of its primes.
   */
  def divides(kit: Kit, definitions: Definitions, powers: Kernel.Thm, specified: Kernel.Thm): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val n = Term.variable("n", kit.numbers)
    val k = Term.variable("k", kit.numbers)
    val rules = kit.rules
    for {
      assumedAbove <- kit.assume("NUM_LT (SUC 0) (p:num)")
      (above, isAbove) = assumedAbove
      assumedPositive <- kit.assume("NUM_LT 0 (n:num)")
      (positive, isPositive) = assumedPositive
      v <- kit.term("NUM_VALUATION (p:num) (n:num)", kit.numbers)
      pk <- pow(kit, p, k)
      pv <- pow(kit, p, v)
      sv <- succ(kit, v)
      psv <- pow(kit, p, sv)
      spec <- kit.applyTo(specified, List(p, n), isAbove, isPositive)
      s1 <- rules.conjElim1(spec)
      s2 <- rules.conjElim2(spec)

      atMost <- kit.assume("NUM_LE (k:num) (NUM_VALUATION (p:num) (n:num))")
      under <- kit.applyTo(powers, List(p, k, v), atMost._2)
      backward <- kit.use("NUM_DIVIDES_TRANS", List(pk, pv, n), under, s1)

      dividesK <- kit.assume("NUM_DIVIDES (NUM_POW (p:num) (k:num)) (n:num)")
      vBelow <- kit.term("NUM_LT (NUM_VALUATION (p:num) (n:num)) (k:num)", Type.Bool)
      forward <- split(kit, vBelow)(
        h =>
          for {
            le <- unfoldedBy(definitions.strictOrder, List(v, k), h)
            u <- kit.applyTo(powers, List(p, sv, k), le)
            chained <- kit.use("NUM_DIVIDES_TRANS", List(psv, pk, n), u, dividesK._2)
            absurd <- rules.notElim(s2, chained)
            r <- rules.falsityElim(atMost._1, absurd)
          } yield r,
        h => kit.use("NUM_LE_OF_NOT_LT", List(v, k), h)
      )
      equal = Kernel.deductAntisym(backward, forward)
      result <- dischAll(kit, List(above, positive), equal).flatMap(rules.genAll(_, List(p, n, k)))
    } yield result
  }

  /* ---------------------------------------------------------------- the laws */

  /** `|- !p n. ~(NUM_DIVIDES p n) ==> NUM_VALUATION p n = 0` */
  def zeroWhenCoprime(kit: Kit, uniqueness: Kernel.Thm): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val n = Term.variable("n", kit.numbers)
    val rules = kit.rules
    for {
      h <- kit.assume("~(NUM_DIVIDES (p:num) (n:num))")
      z <- zero(kit)
      o <- one(kit)
      atZero <- zerothDivides(kit, p, n)
      p1 <- pow(kit, p, o)
      powSuc <- kit.use("NUM_POW_SUC", List(p, z))
      powZero <- kit.use("NUM_POW_ZERO", List(p))
      first <- equate(kit, p1, p, Vector(powSuc, powZero), Vector.empty)
      back <- Conv.sym(first)
      lambda <- kit.at("\\n:num. \\x:num. ~(NUM_DIVIDES x n)", n)
      refused <- transport(lambda, back, h._2)
      valued <- kit.applyTo(uniqueness, List(p, n, z), atZero, refused)
      result <- rules.disch(h._1, valued).flatMap(rules.genAll(_, List(p, n)))
    } yield result
  }

  /** `|- !p k. NUM_PRIME p ==> NUM_VALUATION p (NUM_POW p k) = k` */
  def ofPower(kit: Kit, uniqueness: Kernel.Thm): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val k = Term.variable("k", kit.numbers)
    val c = Term.variable("c", kit.numbers)
    val rules = kit.rules
    for {
      prime <- kit.assume("NUM_PRIME (p:num)")
      above <- kit.use("NUM_PRIME_ABOVE_ONE", List(p), prime._2)
      pPositive <- positiveOfAbove(kit, p, above)
      o <- one(kit)
      pk <- pow(kit, p, k)
      pkp <- mul(kit, pk, p)
      pc <- mul(kit, p, c)
      pkPositive <- kit.use("NUM_POW_POSITIVE", List(p, k), pPositive)
      itself <- kit.use("NUM_DIVIDES_REFL", List(pk))

      largerTerm <- kit.term("NUM_DIVIDES (NUM_POW (p:num) (SUC (k:num))) (NUM_POW p k)", Type.Bool)
      larger <- assume(largerTerm)
      powSuc <- kit.use("NUM_POW_SUC", List(p, k))
      lambda <- kit.at("\\y:num. \\x:num. NUM_DIVIDES x y", pk)
      opened <- transport(lambda, powSuc, larger)
      exists <- kit.use("NUM_DIVIDES_ELIM", List(pkp, pk), opened)
      predicate <- kit.logic.destExistsPredicate(exists.conclusion).toRight(NotOfForm("an existential", exists.conclusion))
      instance <- instantiate(predicate, c)
      hc <- assume(instance)
      unit <- kit.use("NUM_MUL_ONE", List(pk))
      assoc <- kit.use("NUM_MUL_ASSOC", List(pk, p, c))
      chain <- transAll(unit, hc, assoc)
      cancelled <- kit.use("NUM_MUL_CANCEL_LEFT", List(pk, o, pc), pkPositive, chain)
      dividesOne <- kit.use("NUM_DIVIDES_INTRO", List(p, o, c), cancelled)
      isOne <- kit.use("NUM_DIVIDES_ONE", List(p), dividesOne)
      aboveLambda <- kit.at("\\x:num. NUM_LT (SUC 0) x")
      oneAboveOne <- transport(aboveLambda, isOne, above)
      irreflexive <- kit.use("NUM_LT_IRREFL", List(o))
      absurd <- rules.notElim(irreflexive, oneAboveOne)
      found <- rules.existsElim(exists, c, absurd)
      refused <- rules.notIntro(largerTerm, found)

      valued <- kit.applyTo(uniqueness, List(p, pk, k), itself, refused)
      result <- rules.disch(prime._1, valued).flatMap(rules.genAll(_, List(p, k)))
    } yield result
  }

  /**
   * `|- !p a b. NUM_PRIME p ==> NUM_LT 0 a ==> NUM_LT 0 b ==>
   *     NUM_VALUATION p (a * b) = NUM_VALUATION p a + NUM_VALUATION p b`
   */
  def multiplicative(kit: Kit, uniqueness: Kernel.Thm, specified: Kernel.Thm): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val a = Term.variable("a", kit.numbers)
    val b = Term.variable("b", kit.numbers)
    val a1 = Term.variable("a1", kit.numbers)
    val b1 = Term.variable("b1", kit.numbers)
    val c = Term.variable("c", kit.numbers)
    val d = Term.variable("d", kit.numbers)
    val rules = kit.rules

    // False, from `x = p^e * x1`, `p | x1` and `~(p^(SUC e) | x)`.
    def tooMany(x: Term, e: Term, x1: Term, split: Kernel.Thm, refusal: Kernel.Thm, pDivides: Kernel.Thm): R[Kernel.Thm] =
      for {
        pe <- pow(kit, p, e)
        se <- succ(kit, e)
        pse <- pow(kit, p, se)
        exists <- kit.use("NUM_DIVIDES_ELIM", List(p, x1), pDivides)
        predicate <- kit.logic.destExistsPredicate(exists.conclusion).toRight(NotOfForm("an existential", exists.conclusion))
        instance <- instantiate(predicate, d)
        hd <- assume(instance)
        inner <- kit.at("\\u:num. \\x:num. u * x", pe)
        step1 <- cong(inner, hd)
        assoc <- kit.use("NUM_MUL_ASSOC", List(pe, p, d)).flatMap(Conv.sym)
        powSuc <- kit.use("NUM_POW_SUC", List(p, e)).flatMap(Conv.sym)
        outer <- kit.at("\\u:num. \\x:num. x * u", d)
        step2 <- cong(outer, powSuc)
        eq <- transAll(split, step1, assoc, step2)
        more <- kit.use("NUM_DIVIDES_INTRO", List(pse, x, d), eq)
        absurd <- rules.notElim(refusal, more)
        r <- rules.existsElim(exists, d, absurd)
      } yield r

    for {
      prime <- kit.assume("NUM_PRIME (p:num)")
      aPositive <- kit.assume("NUM_LT 0 (a:num)")
      bPositive <- kit.assume("NUM_LT 0 (b:num)")
      above <- kit.use("NUM_PRIME_ABOVE_ONE", List(p), prime._2)
      pPositive <- positiveOfAbove(kit, p, above)
      i <- kit.term("NUM_VALUATION (p:num) (a:num)", kit.numbers)
      j <- kit.term("NUM_VALUATION (p:num) (b:num)", kit.numbers)
      ij <- plus(kit, i, j)
      pi <- pow(kit, p, i)
      pj <- pow(kit, p, j)
      pij <- pow(kit, p, ij)
      ab <- mul(kit, a, b)
      a1b1 <- mul(kit, a1, b1)
      pc <- mul(kit, p, c)
      specA <- kit.applyTo(specified, List(p, a), above, aPositive._2)
      specB <- kit.applyTo(specified, List(p, b), above, bPositive._2)
      sa1 <- rules.conjElim1(specA)
      sa2 <- rules.conjElim2(specA)
      sb1 <- rules.conjElim1(specB)
      sb2 <- rules.conjElim2(specB)
      existsA <- kit.use("NUM_DIVIDES_ELIM", List(pi, a), sa1)
      existsB <- kit.use("NUM_DIVIDES_ELIM", List(pj, b), sb1)
      predicateA <- kit.logic.destExistsPredicate(existsA.conclusion).toRight(NotOfForm("an existential", existsA.conclusion))
      predicateB <- kit.logic.destExistsPredicate(existsB.conclusion).toRight(NotOfForm("an existential", existsB.conclusion))
      instanceA <- instantiate(predicateA, a1)
      instanceB <- instantiate(predicateB, b1)
      ha <- assume(instanceA)
      hb <- assume(instanceB)

      // ab = p^(i+j) * (a1 b1)
      leftFactor <- kit.at("\\y:num. \\x:num. x * y", b)
      e1 <- cong(leftFactor, ha)
      pia1 <- mul(kit, pi, a1)
      rightFactor <- kit.at("\\u:num. \\y:num. u * y", pia1)
      e2 <- cong(rightFactor, hb)
      powAdd <- kit.use("NUM_POW_ADD", List(p, i, j))
      pjb1 <- mul(kit, pj, b1)
      spread <- mul(kit, pia1, pjb1)
      pijA1b1 <- mul(kit, pij, a1b1)
      e3 <- equate(kit, spread, pijA1b1, Vector.empty, Vector(powAdd))
      factored <- transAll(e1, e2, e3)
      atSum <- kit.use("NUM_DIVIDES_INTRO", List(pij, ab, a1b1), factored)

      // and p^(SUC (i+j)) does not divide it
      sij <- succ(kit, ij)
      psij <- pow(kit, p, sij)
      largerTerm <- kit.at("\\x:num. \\y:num. NUM_DIVIDES x y", psij, ab)
      larger <- assume(largerTerm)
      powSuc <- kit.use("NUM_POW_SUC", List(p, ij))
      openLambda <- kit.at("\\y:num. \\x:num. NUM_DIVIDES x y", ab)
      opened <- transport(openLambda, powSuc, larger)
      pijp <- mul(kit, pij, p)
      existsC <- kit.use("NUM_DIVIDES_ELIM", List(pijp, ab), opened)
      predicateC <- kit.logic.destExistsPredicate(existsC.conclusion).toRight(NotOfForm("an existential", existsC.conclusion))
      instanceC <- instantiate(predicateC, c)
      hc <- assume(instanceC)
      back <- Conv.sym(factored)
      assoc <- kit.use("NUM_MUL_ASSOC", List(pij, p, c))
      both <- transAll(back, hc, assoc)
      pijPositive <- kit.use("NUM_POW_POSITIVE", List(p, ij), pPositive)
      cancelled <- kit.use("NUM_MUL_CANCEL_LEFT", List(pij, a1b1, pc), pijPositive, both)
      pUnder <- kit.use("NUM_DIVIDES_INTRO", List(p, a1b1, c), cancelled)
      euclid <- kit.use("NUM_EUCLID", List(p, a1, b1), prime._2, pUnder)
      cases <- disj(kit, euclid.conclusion)
      (underA, underB) = cases
      caseA <- assume(underA).flatMap(tooMany(a, i, a1, ha, sa2, _))
      caseB <- assume(underB).flatMap(tooMany(b, j, b1, hb, sb2, _))
      absurd <- rules.disjElim(euclid, caseA, caseB)
      absurdC <- rules.existsElim(existsC, c, absurd)
      refused <- rules.notIntro(largerTerm, absurdC)

      valued <- kit.applyTo(uniqueness, List(p, ab, ij), atSum, refused)
      droppedB <- rules.existsElim(existsB, b1, valued)
      droppedA <- rules.existsElim(existsA, a1, droppedB)
      result <- dischAll(kit, List(prime._1, aPositive._1, bPositive._1), droppedA)
        .flatMap(rules.genAll(_, List(p, a, b)))
    } yield result
  }

  /** `|- !p q. NUM_PRIME p ==> NUM_PRIME q ==> ~(q = p) ==> NUM_VALUATION p q = 0` */
  def otherPrime(kit: Kit, coprime: Kernel.Thm): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val q = Term.variable("q", kit.numbers)
    val rules = kit.rules
    for {
      primeP <- kit.assume("NUM_PRIME (p:num)")
      primeQ <- kit.assume("NUM_PRIME (q:num)")
      distinct <- kit.assume("~((q:num) = (p:num))")
      above <- kit.use("NUM_PRIME_ABOVE_ONE", List(p), primeP._2)
      o <- one(kit)
      dividesTerm <- kit.term("NUM_DIVIDES (p:num) (q:num)", Type.Bool)
      divides <- assume(dividesTerm)
      divisors <- kit.use("NUM_PRIME_DIVISOR", List(q, p), primeQ._2, divides)
      cases <- disj(kit, divisors.conclusion)
      (isOne, isQ) = cases
      first <- for {
        h <- assume(isOne)
        lambda <- kit.at("\\x:num. NUM_LT (SUC 0) x")
        atOne <- transport(lambda, h, above)
        irreflexive <- kit.use("NUM_LT_IRREFL", List(o))
        absurd <- rules.notElim(irreflexive, atOne)
      } yield absurd
      second <- for {
        h <- assume(isQ)
        back <- Conv.sym(h)
        absurd <- rules.notElim(distinct._2, back)
      } yield absurd
      absurd <- rules.disjElim(divisors, first, second)
      refused <- rules.notIntro(dividesTerm, absurd)
      valued <- kit.applyTo(coprime, List(p, q), refused)
      result <- dischAll(kit, List(primeP._1, primeQ._1, distinct._1), valued)
        .flatMap(rules.genAll(_, List(p, q)))
    } yield result
  }

  /* ---------------------------------------------------------------- divisibility is registerwise */

  /** `0 < x` from `y = m * x` and `0 < y`: were `x` nought, so would `y` be. */
  private def positiveFactor(kit: Kit, m: Term, x: Term, split: Kernel.Thm, yPositive: Kernel.Thm): R[Kernel.Thm] =
    for {
      z <- zero(kit)
      isZero <- eqTerm(x, z)
      h <- assume(isZero)
      times <- kit.at("\\m:num. \\x:num. m * x", m)
      moved <- cong(times, h)
      atZero <- kit.use("NUM_MUL_ZERO", List(m))
      yZero <- transAll(split, moved, atZero)
      zeroLambda <- kit.at("\\x:num. NUM_LT 0 x")
      atNought <- transport(zeroLambda, yZero, yPositive)
      irreflexive <- kit.use("NUM_LT_IRREFL", List(z))
      absurd <- kit.rules.notElim(irreflexive, atNought)
      nonZero <- kit.rules.notIntro(isZero, absurd)
      r <- positive(kit, x, nonZero)
    } yield r

  /** `?z. y = x * z` from `NUM_DIVIDES x y`, and its instance at `witness`, assumed. */
  private def opened(kit: Kit, x: Term, y: Term, divides: Kernel.Thm, witness: FVar): R[(Kernel.Thm, Kernel.Thm)] =
    for {
      exists <- kit.use("NUM_DIVIDES_ELIM", List(x, y), divides)
      predicate <- kit.logic.destExistsPredicate(exists.conclusion).toRight(NotOfForm("an existential", exists.conclusion))
      instance <- instantiate(predicate, witness)
      h <- assume(instance)
    } yield (exists, h)

  /** `NUM_POW p (SUC 0) = p`. */
  private def firstPower(kit: Kit, p: Term): R[Kernel.Thm] =
    for {
      z <- zero(kit)
      o <- one(kit)
      p1 <- pow(kit, p, o)
      powSuc <- kit.use("NUM_POW_SUC", List(p, z))
      powZero <- kit.use("NUM_POW_ZERO", List(p))
      eq <- equate(kit, p1, p, Vector(powSuc, powZero), Vector.empty)
    } yield eq

  private def valuation(kit: Kit, p: Term, x: Term): R[Term] =
    kit.term("NUM_VALUATION", numbersTo(kit, numbersTo(kit, kit.numbers))).flatMap(app(_, p, x))

  /**
   * `NUM_DIVIDES b c ==> (!r. NUM_PRIME r ==> NUM_LE (NUM_VALUATION r b) (NUM_VALUATION r c))`, under
   * `0 < b` and `0 < c`, all three assumed: `c = b k` adds `k`'s registers to `b`'s.
   */
  private def dominatesOfDivides(kit: Kit, product: Kernel.Thm, b: Term, c: Term, bPositive: Kernel.Thm, cPositive: Kernel.Thm, divides: Kernel.Thm): R[Kernel.Thm] = {
    val k = Term.variable("k", kit.numbers)
    val r = Term.variable("r", kit.numbers)
    val rules = kit.rules
    for {
      pair <- opened(kit, b, c, divides, k)
      (exists, hk) = pair
      kPositive <- positiveFactor(kit, b, k, hk, cPositive)
      prime <- kit.assume("NUM_PRIME (r:num)")
      added <- kit.applyTo(product, List(r, b, k), prime._2, bPositive, kPositive)
      vLambda <- kit.at("\\r:num. \\x:num. NUM_VALUATION r x", r)
      renamed <- cong(vLambda, hk)                                   // v c = v (b k)
      atC <- Conv.trans(renamed, added)                              // v c = v b + v k
      vb <- valuation(kit, r, b)
      vk <- valuation(kit, r, k)
      grows <- kit.use("NUM_LE_ADD", List(vb, vk))
      leLambda <- kit.at("\\y:num. \\x:num. NUM_LE y x", vb)
      backC <- Conv.sym(atC)
      dominated <- transport(leLambda, backC, grows)
      each <- rules.disch(prime._1, dominated).flatMap(rules.gen(r, _))
      found <- rules.existsElim(exists, k, each)
    } yield found
  }

  /**
   * `|- !b c. NUM_LT 0 b ==> NUM_LT 0 c ==>
   *     (NUM_DIVIDES b c = (!p. NUM_PRIME p ==> NUM_LE (NUM_VALUATION p b) (NUM_VALUATION p c)))`
   *
   * Divisibility between positive numbers is a comparison of registers, one prime at a time. The
   * forward half is the product law: `c = b k` adds `k`'s registers to `b`'s. The backward half is a
   * strong induction on `b`: at one there is nothing to show; above one a prime `q` divides `b`, so
   * its register in `b` is positive, so it is in `c`, so `q` divides `c`; and cancelling `q` from
   * both leaves a smaller `b` whose registers are still dominated, because the product law adds
   * `q`'s registers to both sides alike.
   */
  def dividesByRegisters(kit: Kit, definitions: Definitions, product: Kernel.Thm, register: Kernel.Thm): R[Kernel.Thm] = {
    val b = Term.variable("b", kit.numbers)
    val c = Term.variable("c", kit.numbers)
    val r = Term.variable("r", kit.numbers)
    val q = Term.variable("q", kit.numbers)
    val b1 = Term.variable("b1", kit.numbers)
    val c1 = Term.variable("c1", kit.numbers)
    val e = Term.variable("e", kit.numbers)
    val rules = kit.rules

    // Above one: the case of the induction step that has a prime to cancel.
    def aboveOne(ih: Kernel.Thm, bPositive: Kernel.Thm, cPositive: Kernel.Thm, dominated: Kernel.Thm, above: Kernel.Thm): R[Kernel.Thm] =
      for {
        o <- one(kit)
        primeFactor <- kit.use("NUM_PRIME_FACTOR", List(b), above)
        qPredicate <- kit.logic.destExistsPredicate(primeFactor.conclusion)
          .toRight(NotOfForm("an existential", primeFactor.conclusion))
        qInstance <- instantiate(qPredicate, q)
        hq <- assume(qInstance)
        qPrime <- rules.conjElim1(hq)
        qDividesB <- rules.conjElim2(hq)
        qAbove <- kit.use("NUM_PRIME_ABOVE_ONE", List(q), qPrime)
        qPositive <- positiveOfAbove(kit, q, qAbove)

        // q divides c, through q's register: 1 <= v_q b <= v_q c
        qOne <- firstPower(kit, q)
        qOneBack <- Conv.sym(qOne)
        onB <- kit.at("\\b:num. \\x:num. NUM_DIVIDES x b", b)
        powDividesB <- transport(onB, qOneBack, qDividesB)
        readB <- kit.applyTo(register, List(q, b, o), qAbove, bPositive)
        oneAtMostB <- LogicError.lift(Kernel.eqMp(readB, powDividesB))
        bAtMostC <- kit.applyTo(dominated, List(q), qPrime)
        vqb <- valuation(kit, q, b)
        vqc <- valuation(kit, q, c)
        chain <- rules.conjIntro(oneAtMostB, bAtMostC)
        oneAtMostC <- kit.use("NUM_LE_TRANS", List(o, vqb, vqc), chain)
        readC <- kit.applyTo(register, List(q, c, o), qAbove, cPositive)
        powDividesC <- Conv.sym(readC).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, oneAtMostC)))
        onC <- kit.at("\\c:num. \\x:num. NUM_DIVIDES x c", c)
        qDividesC <- transport(onC, qOne, powDividesC)

        pairB <- opened(kit, q, b, qDividesB, b1)
        (existsB, hb) = pairB
        pairC <- opened(kit, q, c, qDividesC, c1)
        (existsC, hc) = pairC
        b1Positive <- positiveFactor(kit, q, b1, hb, bPositive)
        c1Positive <- positiveFactor(kit, q, c1, hc, cPositive)

        // b1 < b, since b = q b1 and 1 < q
        grown <- kit.use("NUM_MUL_LT_MONOTONE", List(b1, o, q), b1Positive, qAbove)
        b1q <- mul(kit, b1, q)
        b1o <- mul(kit, b1, o)
        toB1 <- equate(kit, b1o, b1, Vector.empty, Vector.empty)
        toB <- equate(kit, b1q, b, Vector.empty, Vector(hb))
        lt1 <- kit.at("\\y:num. \\x:num. NUM_LT x y", b1q)
        step1 <- transport(lt1, toB1, grown)
        lt2 <- kit.at("\\y:num. \\x:num. NUM_LT y x", b1)
        smaller <- transport(lt2, toB, step1)

        // every register of b1 is at most c1's: q's registers are added to both sides alike
        primeR <- kit.assume("NUM_PRIME (r:num)")
        rb <- kit.applyTo(dominated, List(r), primeR._2)
        vLambda <- kit.at("\\r:num. \\x:num. NUM_VALUATION r x", r)
        onB1 <- cong(vLambda, hb)
        onC1 <- cong(vLambda, hc)
        splitB <- kit.applyTo(product, List(r, q, b1), primeR._2, qPositive, b1Positive)
        splitC <- kit.applyTo(product, List(r, q, c1), primeR._2, qPositive, c1Positive)
        eqB <- Conv.trans(onB1, splitB)
        eqC <- Conv.trans(onC1, splitC)
        vrc <- valuation(kit, r, c)
        vrq <- valuation(kit, r, q)
        vrb1 <- valuation(kit, r, b1)
        vrc1 <- valuation(kit, r, c1)
        sumB <- plus(kit, vrq, vrb1)
        leftLambda <- kit.at("\\y:num. \\x:num. NUM_LE x y", vrc)
        leftMoved <- transport(leftLambda, eqB, rb)
        rightLambda <- kit.at("\\y:num. \\x:num. NUM_LE y x", sumB)
        rightMoved <- transport(rightLambda, eqC, leftMoved)
        cancelled <- kit.use("NUM_ADD_LE_CANCEL", List(vrq, vrb1, vrc1), rightMoved)
        dominatedBelow <- rules.disch(primeR._1, cancelled).flatMap(rules.gen(r, _))

        atB1 <- kit.applyTo(ih, List(b1), smaller)
        b1DividesC1 <- kit.applyTo(atB1, List(c1), b1Positive, c1Positive, dominatedBelow)

        // b = q b1 divides q c1 = c
        pairE <- opened(kit, b1, c1, b1DividesC1, e)
        (existsE, he) = pairE
        be <- mul(kit, b, e)
        factored <- equate(kit, c, be, Vector(hc, he), Vector(hb))
        divides <- kit.use("NUM_DIVIDES_INTRO", List(b, c, e), factored)
        dropE <- rules.existsElim(existsE, e, divides)
        dropC <- rules.existsElim(existsC, c1, dropE)
        dropB <- rules.existsElim(existsB, b1, dropC)
        dropQ <- rules.existsElim(primeFactor, q, dropB)
      } yield dropQ

    // !b c. 0 < b ==> 0 < c ==> (!r. prime r ==> v r b <= v r c) ==> b | c, by strong induction on b
    val backward: R[Kernel.Thm] =
      for {
        claim <- kit.at(
          "\\b:num. !c:num. NUM_LT 0 b ==> NUM_LT 0 c ==> " +
            "(!r:num. NUM_PRIME r ==> NUM_LE (NUM_VALUATION r b) (NUM_VALUATION r c)) ==> NUM_DIVIDES b c")
        strong <- kit.use("NUM_STRONG_INDUCTION", List(claim))
        hypothesis <- imp(kit, strong.conclusion)
        (stepTerm, _) = hypothesis
        stepBody <- open(kit, stepTerm, b)
        ihParts <- imp(kit, stepBody)
        (ihTerm, goalB) = ihParts
        ih <- assume(ihTerm)
        goalC <- open(kit, goalB, c)
        g1 <- imp(kit, goalC)
        (bPositiveTerm, g2) = g1
        g2Parts <- imp(kit, g2)
        (cPositiveTerm, g3) = g2Parts
        g3Parts <- imp(kit, g3)
        (dominatedTerm, target) = g3Parts
        bPositive <- assume(bPositiveTerm)
        cPositive <- assume(cPositiveTerm)
        dominated <- assume(dominatedTerm)
        o <- one(kit)
        z <- zero(kit)
        isOne <- eqTerm(b, o)
        divides <- split(kit, isOne)(
          h =>
            for {
              byOne <- kit.use("NUM_ONE_DIVIDES", List(c))
              back <- Conv.sym(h)
              lambda <- kit.at("\\c:num. \\x:num. NUM_DIVIDES x c", c)
              atOne <- transport(lambda, back, byOne)
            } yield atOne,
          notOne =>
            for {
              // 1 < b: 0 < b is SUC 0 <= b, and b is not one
              atLeast <- unfoldedBy(definitions.strictOrder, List(z, b), bPositive)
              cases <- kit.use("NUM_LE_CASES", List(o, b), atLeast)
              pair <- disj(kit, cases.conclusion)
              (strictly, same) = pair
              h1 <- assume(strictly)
              h2 <- assume(same)
              back <- Conv.sym(h2)
              absurd <- rules.notElim(notOne, back)
              viaSame <- rules.falsityElim(strictly, absurd)
              above <- rules.disjElim(cases, h1, viaSame)
              reached <- aboveOne(ih, bPositive, cPositive, dominated, above)
            } yield reached
        )
        _ <- kit.landsOn(divides, target)
        closed <- dischAll(kit, List(bPositiveTerm, cPositiveTerm, dominatedTerm), divides)
        generalC <- rules.gen(c, closed)
        stepDone <- rules.disch(ihTerm, generalC).flatMap(rules.gen(b, _))
        all <- rules.mp(strong, stepDone)
      } yield all

    for {
      back <- backward
      bPositive <- kit.assume("NUM_LT 0 (b:num)")
      cPositive <- kit.assume("NUM_LT 0 (c:num)")
      divides <- kit.assume("NUM_DIVIDES (b:num) (c:num)")
      dominance <- dominatesOfDivides(kit, product, b, c, bPositive._2, cPositive._2, divides._2)
      dominated <- assume(dominance.conclusion)
      atB <- rules.spec(b, back).flatMap(Limit.normalised).flatMap(rules.spec(c, _)).flatMap(Limit.normalised)
      reached <- kit.applyTo(atB, List(), bPositive._2, cPositive._2, dominated)
      equal = Kernel.deductAntisym(reached, dominance)
      result <- dischAll(kit, List(bPositive._1, cPositive._1), equal).flatMap(rules.genAll(_, List(b, c)))
    } yield result
  }

  /**
   * `|- !m n. NUM_LT 0 m ==> NUM_LT 0 n ==>
   *     (!p. NUM_PRIME p ==> NUM_VALUATION p m = NUM_VALUATION p n) ==> m = n`
   *
   * A positive number is its registers: two that agree at every prime are one number. Each divides
   * the other by [[dividesByRegisters]], and divisibility is antisymmetric. This is the uniqueness
   * of the factorisation in the form a register machine reads it.
   */
  def registersDetermine(kit: Kit, registers: Kernel.Thm): R[Kernel.Thm] = {
    val m = Term.variable("m", kit.numbers)
    val n = Term.variable("n", kit.numbers)
    val r = Term.variable("r", kit.numbers)
    val rules = kit.rules

    // !r. prime r ==> v r x <= v r y, from the agreement read in one direction
    def dominated(agree: Kernel.Thm, x: Term, y: Term, forwards: Boolean): R[Kernel.Thm] =
      for {
        prime <- kit.assume("NUM_PRIME (r:num)")
        same <- kit.applyTo(agree, List(r), prime._2)
        oriented <- if (forwards) Right(same) else Conv.sym(same)
        vx <- valuation(kit, r, x)
        itself <- kit.use("NUM_LE_REFL", List(vx))
        lambda <- kit.at("\\v:num. \\u:num. NUM_LE v u", vx)
        moved <- transport(lambda, oriented, itself)
        result <- rules.disch(prime._1, moved).flatMap(rules.gen(r, _))
      } yield result

    for {
      mPositive <- kit.assume("NUM_LT 0 (m:num)")
      nPositive <- kit.assume("NUM_LT 0 (n:num)")
      agree <- kit.assume("!r:num. NUM_PRIME r ==> NUM_VALUATION r (m:num) = NUM_VALUATION r (n:num)")
      mn <- dominated(agree._2, m, n, forwards = true)
      nm <- dominated(agree._2, n, m, forwards = false)
      readMN <- kit.applyTo(registers, List(m, n), mPositive._2, nPositive._2)
      readNM <- kit.applyTo(registers, List(n, m), nPositive._2, mPositive._2)
      mDividesN <- Conv.sym(readMN).flatMap(e => LogicError.lift(Kernel.eqMp(e, mn)))
      nDividesM <- Conv.sym(readNM).flatMap(e => LogicError.lift(Kernel.eqMp(e, nm)))
      both <- rules.conjIntro(mDividesN, nDividesM)
      equal <- kit.use("NUM_DIVIDES_ANTISYM", List(m, n), both)
      result <- dischAll(kit, List(mPositive._1, nPositive._1, agree._1), equal).flatMap(rules.genAll(_, List(m, n)))
    } yield result
  }

  /* ---------------------------------------------------------------- one fraction, on the registers */

  /**
   * `|- !n a b. NUM_LT 0 n ==> NUM_LT 0 a ==> NUM_LT 0 b ==>
   *     (NUM_DIVIDES b (n * a) = (!p. NUM_PRIME p ==> NUM_LE (NUM_VALUATION p b) (NUM_VALUATION p n + NUM_VALUATION p a)))`
   *
   * FRACTRAN's test for a fraction `a/b` at the state `n`, read on the registers: every register
   * of the denominator is covered by the state's and the numerator's together.
   */
  def fractionApplies(kit: Kit, product: Kernel.Thm, registers: Kernel.Thm): R[Kernel.Thm] = {
    val n = Term.variable("n", kit.numbers)
    val a = Term.variable("a", kit.numbers)
    val b = Term.variable("b", kit.numbers)
    val r = Term.variable("r", kit.numbers)
    val rules = kit.rules
    for {
      nPositive <- kit.assume("NUM_LT 0 (n:num)")
      aPositive <- kit.assume("NUM_LT 0 (a:num)")
      bPositive <- kit.assume("NUM_LT 0 (b:num)")
      na <- mul(kit, n, a)
      naPositive <- kit.use("NUM_MUL_POSITIVE", List(n, a), nPositive._2, aPositive._2)
      read <- kit.applyTo(registers, List(b, na), bPositive._2, naPositive)
      byProduct <- Limit.rightOf(read)
      bySum <- kit.proposition(
        "!r:num. NUM_PRIME r ==> NUM_LE (NUM_VALUATION r (b:num)) (NUM_VALUATION r (n:num) + NUM_VALUATION r (a:num))")
      vb <- valuation(kit, r, b)
      prime <- kit.assume("NUM_PRIME (r:num)")
      split <- kit.applyTo(product, List(r, n, a), prime._2, nPositive._2, aPositive._2)
      bound <- kit.at("\\y:num. \\x:num. NUM_LE y x", vb)
      toSum <- for {
        h <- assume(byProduct)
        atR <- kit.applyTo(h, List(r), prime._2)
        moved <- transport(bound, split, atR)
        general <- rules.disch(prime._1, moved).flatMap(rules.gen(r, _))
      } yield general
      toProduct <- for {
        h <- assume(bySum)
        atR <- kit.applyTo(h, List(r), prime._2)
        back <- Conv.sym(split)
        moved <- transport(bound, back, atR)
        general <- rules.disch(prime._1, moved).flatMap(rules.gen(r, _))
      } yield general
      same = Kernel.deductAntisym(toProduct, toSum)
      equal <- Conv.trans(read, same)
      result <- dischAll(kit, List(nPositive._1, aPositive._1, bPositive._1), equal)
        .flatMap(rules.genAll(_, List(n, a, b)))
    } yield result
  }

  /**
   * `|- !p n a b. NUM_PRIME p ==> NUM_LT 0 n ==> NUM_LT 0 a ==> NUM_LT 0 b ==> NUM_DIVIDES b (n * a) ==>
   *     NUM_VALUATION p (NUM_DIV (n * a) b) + NUM_VALUATION p b = NUM_VALUATION p n + NUM_VALUATION p a`
   *
   * What applying `a/b` does to each register: it adds the numerator's and takes the denominator's
   * away. Written with the subtraction moved to the other side, because `num`'s is truncated and the
   * sum form needs no side condition to be read.
   */
  def fractionEffect(kit: Kit, product: Kernel.Thm): R[Kernel.Thm] = {
    val p = Term.variable("p", kit.numbers)
    val n = Term.variable("n", kit.numbers)
    val a = Term.variable("a", kit.numbers)
    val b = Term.variable("b", kit.numbers)
    val k = Term.variable("k", kit.numbers)
    val rules = kit.rules
    for {
      prime <- kit.assume("NUM_PRIME (p:num)")
      nPositive <- kit.assume("NUM_LT 0 (n:num)")
      aPositive <- kit.assume("NUM_LT 0 (a:num)")
      bPositive <- kit.assume("NUM_LT 0 (b:num)")
      divides <- kit.assume("NUM_DIVIDES (b:num) ((n:num) * (a:num))")
      z <- zero(kit)
      na <- mul(kit, n, a)
      naPositive <- kit.use("NUM_MUL_POSITIVE", List(n, a), nPositive._2, aPositive._2)
      pair <- opened(kit, b, na, divides._2, k)
      (exists, hk) = pair                                            // n a = b k
      kPositive <- positiveFactor(kit, b, k, hk, naPositive)
      bk <- mul(kit, b, k)
      padded <- kit.use("NUM_ADD_ZERO", List(bk)).flatMap(Conv.sym)  // b k = b k + 0
      division <- Conv.trans(hk, padded)
      premises <- rules.conjIntro(division, bPositive._2)
      quotient <- kit.use("NUM_DIV_MOD_UNIQUE", List(na, b, k, z), premises)
      isQuotient <- rules.conjElim1(quotient)                        // k = NUM_DIV (n a) b
      splitNA <- kit.applyTo(product, List(p, n, a), prime._2, nPositive._2, aPositive._2)
      splitBK <- kit.applyTo(product, List(p, b, k), prime._2, bPositive._2, kPositive)
      vLambda <- kit.at("\\p:num. \\x:num. NUM_VALUATION p x", p)
      renamed <- cong(vLambda, hk)                                   // v (n a) = v (b k)
      back <- Conv.sym(splitNA)
      balance <- transAll(back, renamed, splitBK)                   // v n + v a = v b + v k
      vk <- valuation(kit, p, k)
      vb <- valuation(kit, p, b)
      vn <- valuation(kit, p, n)
      va <- valuation(kit, p, a)
      left <- plus(kit, vk, vb)
      right <- plus(kit, vn, va)
      atK <- equate(kit, left, right, Vector.empty, Vector(balance))
      shape <- kit.at("\\p:num. \\b:num. \\r:num. \\x:num. NUM_VALUATION p x + NUM_VALUATION p b = r", p, b, right)
      atQuotient <- transport(shape, isQuotient, atK)
      found <- rules.existsElim(exists, k, atQuotient)
      result <- dischAll(kit, List(prime._1, nPositive._1, aPositive._1, bPositive._1, divides._1), found)
        .flatMap(rules.genAll(_, List(p, n, a, b)))
    } yield result
  }

  /**
   * `|- !n a q m. NUM_LT 0 n ==> NUM_LT 0 a ==> NUM_LT 0 q ==> NUM_DIVIDES q (n * a) ==>
   *     ((m = NUM_DIV (n * a) q) = (NUM_LT 0 m /\
   *       (!p. NUM_PRIME p ==> NUM_VALUATION p m + NUM_VALUATION p q = NUM_VALUATION p n + NUM_VALUATION p a)))`
   *
   * Where a fraction that applies sends the state, said on the registers and in both directions:
   * the quotient is the one positive number whose registers are the state's plus the numerator's
   * less the denominator's. Forwards is [[fractionEffect]]; backwards is [[registersDetermine]],
   * after cancelling the denominator's register from both sides.
   */
  def fractionLands(kit: Kit, product: Kernel.Thm, effect: Kernel.Thm, determined: Kernel.Thm): R[Kernel.Thm] = {
    val n = Term.variable("n", kit.numbers)
    val a = Term.variable("a", kit.numbers)
    val q = Term.variable("q", kit.numbers)
    val m = Term.variable("m", kit.numbers)
    val k = Term.variable("k", kit.numbers)
    val r = Term.variable("r", kit.numbers)
    val rules = kit.rules
    for {
      nPositive <- kit.assume("NUM_LT 0 (n:num)")
      aPositive <- kit.assume("NUM_LT 0 (a:num)")
      qPositive <- kit.assume("NUM_LT 0 (q:num)")
      divides <- kit.assume("NUM_DIVIDES (q:num) ((n:num) * (a:num))")
      z <- zero(kit)
      na <- mul(kit, n, a)
      quotientTerm <- kit.term("NUM_DIV ((n:num) * (a:num)) (q:num)", kit.numbers)
      naPositive <- kit.use("NUM_MUL_POSITIVE", List(n, a), nPositive._2, aPositive._2)

      // the quotient is positive: n a = q k, k is the quotient, and k is not nought
      pair <- opened(kit, q, na, divides._2, k)
      (exists, hk) = pair
      kPositive <- positiveFactor(kit, q, k, hk, naPositive)
      qk <- mul(kit, q, k)
      padded <- kit.use("NUM_ADD_ZERO", List(qk)).flatMap(Conv.sym)
      division <- Conv.trans(hk, padded)
      premises <- rules.conjIntro(division, qPositive._2)
      unique <- kit.use("NUM_DIV_MOD_UNIQUE", List(na, q, k, z), premises)
      isQuotient <- rules.conjElim1(unique)
      positiveLambda <- kit.at("\\x:num. NUM_LT 0 x")
      atQuotient <- transport(positiveLambda, isQuotient, kPositive)
      quotientPositive <- rules.existsElim(exists, k, atQuotient)

      // the quotient's registers, at an arbitrary prime r
      prime <- kit.assume("NUM_PRIME (r:num)")
      itsRegisters <- kit.applyTo(effect, List(r, n, a, q), prime._2, nPositive._2, aPositive._2, qPositive._2, divides._2)

      landsTerm <- kit.term("(m:num) = NUM_DIV ((n:num) * (a:num)) (q:num)", Type.Bool)
      registersTerm <- kit.term(
        "NUM_LT 0 (m:num) /\\ (!r:num. NUM_PRIME r ==> NUM_VALUATION r m + NUM_VALUATION r (q:num) = " +
          "NUM_VALUATION r (n:num) + NUM_VALUATION r (a:num))", Type.Bool)

      registersRight <- Limit.rightOf(itsRegisters)
      forwards <- for {
        h <- assume(landsTerm)
        back <- Conv.sym(h)
        positiveM <- transport(positiveLambda, back, quotientPositive)
        shape <- kit.at("\\q:num. \\r:num. \\y:num. \\x:num. NUM_VALUATION r x + NUM_VALUATION r q = y", q, r,
          registersRight)
        atM <- transport(shape, back, itsRegisters)
        each <- rules.disch(prime._1, atM).flatMap(rules.gen(r, _))
        both <- rules.conjIntro(positiveM, each)
      } yield both

      backwards <- for {
        h <- assume(registersTerm)
        positiveM <- rules.conjElim1(h)
        registers <- rules.conjElim2(h)
        atR <- kit.applyTo(registers, List(r), prime._2)
        balanced <- Conv.sym(itsRegisters).flatMap(Conv.trans(atR, _))    // v m + v q = v D + v q
        vm <- valuation(kit, r, m)
        vq <- valuation(kit, r, q)
        vd <- valuation(kit, r, quotientTerm)
        left <- plus(kit, vq, vm)
        right <- plus(kit, vq, vd)
        mq <- plus(kit, vm, vq)
        dq <- plus(kit, vd, vq)
        swapLeft <- equate(kit, left, mq, Vector.empty, Vector.empty)
        swapRight <- equate(kit, dq, right, Vector.empty, Vector.empty)
        moved <- transAll(swapLeft, balanced, swapRight)
        same <- kit.use("NUM_ADD_CANCEL_LEFT", List(vm, vd, vq), moved)
        agree <- rules.disch(prime._1, same).flatMap(rules.gen(r, _))
        equal <- kit.applyTo(determined, List(m, quotientTerm), positiveM, quotientPositive, agree)
      } yield equal

      both = Kernel.deductAntisym(backwards, forwards)
      result <- dischAll(kit, List(nPositive._1, aPositive._1, qPositive._1, divides._1), both)
        .flatMap(rules.genAll(_, List(n, a, q, m)))
    } yield result
  }

  /** The facts `Primes` publishes from this file, under the names it gives them. */
  def derive(kit: Kit, definitions: Definitions): R[Map[String, Kernel.Thm]] =
    for {
      below <- ltPow(kit, definitions)
      powers <- powDividesPow(kit, definitions)
      uniqueness <- unique(kit, definitions, powers)
      specified <- spec(kit, definitions, below)
      register <- divides(kit, definitions, powers, specified)
      coprime <- zeroWhenCoprime(kit, uniqueness)
      power <- ofPower(kit, uniqueness)
      product <- multiplicative(kit, uniqueness, specified)
      other <- otherPrime(kit, coprime)
      registers <- dividesByRegisters(kit, definitions, product, register)
      determined <- registersDetermine(kit, registers)
      applies <- fractionApplies(kit, product, registers)
      effect <- fractionEffect(kit, product)
      lands <- fractionLands(kit, product, effect, determined)
    } yield Map(
      Primes.BelowPower -> below,
      Primes.PowerDividesPower -> powers,
      Primes.ValuationUnique -> uniqueness,
      Primes.ValuationSpec -> specified,
      Primes.ValuationDivides -> register,
      Primes.ValuationNotDivides -> coprime,
      Primes.ValuationPower -> power,
      Primes.ValuationMul -> product,
      Primes.ValuationOtherPrime -> other,
      Primes.DividesByValuations -> registers,
      Primes.ValuationDetermines -> determined,
      Primes.FractionApplies -> applies,
      Primes.FractionEffect -> effect,
      Primes.FractionLands -> lands
    )
}
