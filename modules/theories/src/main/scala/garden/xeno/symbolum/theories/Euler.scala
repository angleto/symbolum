package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Euler's theorem on `num`, and the invariance of a finite product under a permutation of its
 * indices, which is what the theorem was waiting on.
 *
 * Not a development: it declares nothing, and what it derives `Primes` publishes under names it
 * declares, the arrangement `Freshman` has for Fermat. `NUM_TOTIENT` is the one constant the
 * statement needs and it is `Modular`'s, beside `NUM_GCD` and `NUM_CONG`, because `Primes` extends
 * nothing.
 *
 * == The permutation, and why its statement asks for surjectivity ==
 *
 * `NUM_PROD_PERMUTE` says a product over `[0, n)` does not change when a map `s` of `[0, n)` into
 * itself that is injective and onto reindexes it. On a finite set an injection is onto, and the
 * statement asks for both anyway: the induction needs the index `k` with `s k = n`, and deriving
 * that from injectivity is a pigeonhole this library does not have. A caller holding an inverse,
 * which is the case for every permutation this file builds, pays nothing for it.
 *
 * The induction cannot be `Induct.proveBy`, which fixes every argument but the last: the step needs
 * the claim at a **different** map, `s' i = COND (i = k) (s n) (s i)`, which sends the one index
 * that went to `n` where `n` went and leaves the rest alone. So it runs `NUM_INDUCTION` over a
 * predicate quantifying `s` inside, as `Language`'s injectivity of numerals does, and the three
 * properties of `s'` are each a case split on whether an index is `k`. `NUM_PROD_POINT`, that two
 * products differing at one index trade that factor, is what stitches the two products back together
 * when `k < n`.
 *
 * == Euler, by the permutation that fixes the non-coprime residues ==
 *
 * The textbook multiplies the reduced residues by `a` and observes they are permuted. Here the
 * product runs over all of `[0, n)`, with `r k = COND (coprime k) k 1`, and the map is
 * `s k = COND (coprime k) (NUM_MOD (a * k) n) k`: multiplication by `a` on the coprime residues and
 * the identity on the others. That choice is what keeps the derivation to one direction of a fact
 * about coprimality, `NUM_GCD_MOD` after `NUM_GCD_MUL`, that `a k mod n` is coprime when `k` is; a
 * map moving every residue would need the converse as well, to keep a non-coprime one from landing
 * on a coprime one.
 *
 * Surjectivity is the inverse of `a`, `NUM_INVERSE`, from Bezout: in one of its two cases the
 * witness is Bezout's own coefficient, and in the other `n z = a u + 1` and the witness is
 * `u (n - 1)`, written as `u w` with `n = SUC w` so that no subtraction appears. `NUM_UNIT_COPRIME`
 * is what says the inverse is itself coprime, which the preimage of a coprime residue needs.
 *
 * Then `r (s k) == COND (coprime k) a 1 * r k` termwise, `NUM_PROD_CONG_MOD` carries that to the
 * products, `NUM_PROD_MUL` splits the right one, and `NUM_PROD_COND_POW` names the product of the
 * `a`s as `a` to the count of coprime residues, which is `NUM_TOTIENT n` unfolded. The product of the
 * `r k` is coprime to `n` by `NUM_GCD_PROD`, so it has an inverse, and cancelling it is the theorem.
 */
private[theories] object Euler {
  import Steps.*

  /* ---------------------------------------------------------------- the single-point change */

  /**
   * `|- !f g k n. k < n ==> (!i. i < n ==> ~(i = k) ==> f i = g i) ==>
   *     NUM_PROD f n * g k = NUM_PROD g n * f k`
   */
  def point(kit: Kit): R[Kernel.Thm] = {
    val fn = Type.fun(kit.numbers, kit.numbers)
    val f = Term.variable("f", fn)
    val g = Term.variable("g", fn)
    val k = Term.variable("k", kit.numbers)
    for {
      statement <- kit.proposition(
        "!n:num. NUM_LT (k:num) n ==> (!i:num. NUM_LT i n ==> ~(i = k) ==> (f:num->num) i = (g:num->num) i) ==> " +
          "NUM_PROD f n * g k = NUM_PROD g n * f k")
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            p_a1 <- imp(kit, base)
            (a1, rest) = p_a1
            h <- assume(a1)
            not <- kit.use("NUM_NOT_LT_ZERO", List(k))
            absurd <- kit.rules.notElim(not, h)
            out <- kit.rules.falsityElim(rest, absurd)
            r <- kit.rules.disch(a1, out)
          } yield r,
        step => pointStep(kit, step, f, g, k)
      )
      general <- kit.rules.genAll(proved, List(f, g, k))
    } yield general
  }

  private def pointStep(kit: Kit, step: Induct.Step, f: Term, g: Term, k: Term): R[Kernel.Thm] = {
    val n = step.variable
    val rules = kit.rules
    for {
      p_a1 <- imp(kit, step.goal)
      (a1, r1) = p_a1
      p_a2 <- imp(kit, r1)
      (a2, goalEq) = p_a2
      p_lhs <- sides(goalEq)
      (lhs, rhs) = p_lhs
      h1 <- assume(a1)
      h2 <- assume(a2)
      sn <- succ(kit, n)
      cases <- kit.use("NUM_LT_SUC_CASES", List(n, k), h1)
      p_caseLt <- disj(kit, cases.conclusion)
      (caseLt, caseEq) = p_caseLt
      fSuc <- kit.use("NUM_PROD_SUC", List(f, n))
      gSuc <- kit.use("NUM_PROD_SUC", List(g, n))

      // k < n: the hypothesis restricted to n, then the IH, then one factor moved.
      b <- assume(caseLt)
      i = fresh("i", kit.numbers, h1, h2, b, step.hypothesis)
      iLtT <- kit.term("NUM_LT", Type.fun(kit.numbers, Type.fun(kit.numbers, Type.Bool))).flatMap(app(_, i, n))
      iNeT <- eqTerm(i, k).flatMap(kit.logic.mkNot)
      p1 <- assume(iLtT)
      p2 <- assume(iNeT)
      iSuc <- belowSuc(kit, i, n, p1)
      fi <- kit.applyTo(h2, List(i), iSuc, p2)
      hypN <- dischAll(kit, List(iLtT, iNeT), fi).flatMap(rules.gen(i, _))
      ih <- rules.mp(step.hypothesis, b).flatMap(rules.mp(_, hypN))
      nNeK <- neqOfLt(kit, k, n, b)
      nSuc <- ltSuc(kit, n)
      fnEq <- kit.applyTo(h2, List(n), nSuc, nNeK)
      mid1 <- kit.at("\\m:num. (NUM_PROD (f:num->num) m * (g:num->num) (k:num)) * f m", n)
      mid2 <- kit.at("\\m:num. (NUM_PROD (g:num->num) m * (f:num->num) (k:num)) * f m", n)
      e1 <- equate(kit, lhs, mid1, Vector(fSuc), Vector.empty)
      times <- kit.at("\\m:num. \\x:num. x * (f:num->num) m", n)
      e2 <- cong(times, ih)
      e3 <- equate(kit, mid2, rhs, Vector(fnEq), Vector(gSuc))
      branchLt <- transAll(e1, e2, e3)

      // k = n: the products below n agree, and the factor at n is the one that moved.
      c <- assume(caseEq)
      u = fresh("u", kit.numbers, h1, h2, c)
      uLtT <- kit.term("NUM_LT", Type.fun(kit.numbers, Type.fun(kit.numbers, Type.Bool))).flatMap(app(_, u, n))
      q <- assume(uLtT)
      uEqK <- eqTerm(u, k)
      ue <- assume(uEqK)
      un <- Conv.trans(ue, c)
      nn <- Limit.rewriteInProposition(un, q)
      irr <- kit.use("NUM_LT_IRREFL", List(n))
      absurd <- rules.notElim(irr, nn)
      uNeK <- rules.notIntro(uEqK, absurd)
      uSuc <- belowSuc(kit, u, n, q)
      fu <- kit.applyTo(h2, List(u), uSuc, uNeK)
      agree <- rules.disch(uLtT, fu).flatMap(rules.gen(u, _))
      prodEq <- kit.use("NUM_PROD_CONG", List(f, g, n), agree)
      branchEq <- equate(kit, lhs, rhs, Vector(fSuc, c, prodEq), Vector(gSuc, c))

      joined <- rules.disjElim(cases, branchLt, branchEq)
      result <- dischAll(kit, List(a1, a2), joined)
    } yield result
  }

  /* ---------------------------------------------------------------- the permutation */

  private val PermutePredicate =
    "\\n:num. !s:num->num. (!i:num. NUM_LT i n ==> NUM_LT (s i) n) ==> " +
      "(!i:num. !j:num. NUM_LT i n ==> NUM_LT j n ==> s i = s j ==> i = j) ==> " +
      "(!j:num. NUM_LT j n ==> ?i:num. NUM_LT i n /\\ s i = j) ==> " +
      "NUM_PROD (\\i:num. (f:num->num) (s i)) n = NUM_PROD f n"

  def productOf(t: Term): R[(Term, Term)] = t match {
    case App(App(Const("NUM_PROD", _), function), bound) => Right((function, bound))
    case other => Left(NotOfForm("a finite product", other))
  }

  /**
   * `|- !f n s. (!i. i < n ==> s i < n) ==> (!i j. i < n ==> j < n ==> s i = s j ==> i = j) ==>
   *     (!j. j < n ==> ?i. i < n /\ s i = j) ==> NUM_PROD (\i. f (s i)) n = NUM_PROD f n`
   */
  def permute(kit: Kit, point: Kernel.Thm): R[Kernel.Thm] = {
    val fn = Type.fun(kit.numbers, kit.numbers)
    val f = Term.variable("f", fn)
    val rules = kit.rules
    for {
      predicate <- Parser.term(kit.theory, kit.notation, PermutePredicate)
      induction <- kit.use("NUM_INDUCTION", List(predicate))
      p_prem <- imp(kit, induction.conclusion)
      (premise, _) = p_prem
      p_base <- conj(kit, premise)
      (baseT, stepT) = p_base

      // Zero: both products are one.
      s0 = fresh("s", fn, induction)
      body0 <- open(kit, baseT, s0)
      p_r0 <- imp(kit, body0)
      (r0, rest0) = p_r0
      p_i0 <- imp(kit, rest0)
      (i0, rest1) = p_i0
      p_o0 <- imp(kit, rest1)
      (o0, eq0) = p_o0
      p_s0 <- sides(eq0)
      (lhs0, rhs0) = p_s0
      p_l0 <- productOf(lhs0)
      (fs0, _) = p_l0
      z1 <- kit.use("NUM_PROD_ZERO", List(fs0))
      z2 <- kit.use("NUM_PROD_ZERO", List(f))
      zero <- Conv.sym(z2).flatMap(Conv.trans(z1, _))
      baseThm <- dischAll(kit, List(r0, i0, o0), zero).flatMap(rules.gen(s0, _))

      // The step, at a fresh n with the claim at n for every s.
      n = fresh("n", kit.numbers, induction)
      stepBody <- open(kit, stepT, n)
      p_step <- imp(kit, stepBody)
      (atN, atSucN) = p_step
      ih <- assume(atN)
      s = fresh("s", fn, induction, ih)
      goalBody <- open(kit, atSucN, s)
      p_g1 <- imp(kit, goalBody)
      (rT, g1) = p_g1
      p_g2 <- imp(kit, g1)
      (iT, g2) = p_g2
      p_g3 <- imp(kit, g2)
      (oT, goalEq) = p_g3
      proved <- permuteStep(kit, point, f, n, s, ih, rT, iT, oT, goalEq)
      stepThm <- dischAll(kit, List(rT, iT, oT), proved)
        .flatMap(rules.gen(s, _))
        .flatMap(rules.disch(atN, _))
        .flatMap(rules.gen(n, _))

      both <- rules.conjIntro(baseThm, stepThm)
      all <- rules.mp(induction, both)
      general <- rules.gen(f, all)
    } yield general
  }

  private def permuteStep(
    kit: Kit, point: Kernel.Thm, f: Term, n: Term, s: Term,
    ih: Kernel.Thm, rT: Term, iT: Term, oT: Term, goalEq: Term
  ): R[Kernel.Thm] = {
    val rules = kit.rules
    val num = kit.numbers
    def lt(x: Term, y: Term): R[Term] =
      kit.term("NUM_LT", Type.fun(num, Type.fun(num, Type.Bool))).flatMap(app(_, x, y))
    def sAt(x: Term): R[Term] = app(s, x)
    for {
      hR <- assume(rT)
      hI <- assume(iT)
      hO <- assume(oT)
      sn <- succ(kit, n)
      nSuc <- ltSuc(kit, n)
      kEx <- kit.applyTo(hO, List(n), nSuc)
      kPred <- kit.logic.destExistsPredicate(kEx.conclusion).toRight(NotOfForm("an existential", kEx.conclusion))
      k = fresh("k", num, hR, hI, hO, ih, kEx)
      kBodyT <- instantiate(kPred, k)
      kb <- assume(kBodyT)
      kLt <- rules.conjElim1(kb)
      sk <- rules.conjElim2(kb)
      skBack <- Conv.sym(sk)
      sN <- sAt(n)

      // Whether s x is n decides whether x is k.
      inj = (x: Term, y: Term, xs: Kernel.Thm, ys: Kernel.Thm, e: Kernel.Thm) => kit.applyTo(hI, List(x, y), xs, ys, e)
      notOnN = (x: Term, xs: Kernel.Thm, notK: Term => R[Kernel.Thm]) =>
        for {
          sx <- sAt(x)
          e <- eqTerm(sx, n)
          he <- assume(e)
          toK <- Conv.trans(he, skBack)
          xk <- inj(x, k, xs, kLt, toK)
          absurd <- notK(x).flatMap(rules.notElim(_, xk))
          r <- rules.notIntro(e, absurd)
        } yield r

      sPrime <- kit.at("\\n:num. \\k:num. \\s:num->num. \\i:num. COND (i = k) (s n) (s i)", n, k, s)
      condAt = (x: Term) => kit.at("\\n:num. \\k:num. \\s:num->num. \\x:num. COND (x = k) (s n) (s x)", n, k, s, x)
      ihAt <- rules.spec(sPrime, ih).flatMap(Limit.normalised)
      p_h1 <- imp(kit, ihAt.conclusion)
      (rP, h1rest) = p_h1
      p_h2 <- imp(kit, h1rest)
      (iP, h2rest) = p_h2
      p_h3 <- imp(kit, h2rest)
      (oP, _) = p_h3

      // s' maps [0, n) into itself.
      i = fresh("i", num, hR, hI, hO, ih, kb)
      iLtT <- lt(i, n)
      hi <- assume(iLtT)
      iSuc <- belowSuc(kit, i, n, hi)
      snLtSuc <- kit.applyTo(hR, List(n), nSuc)
      rangeInner <- {
        val cT = eqTerm(i, k)
        cT.flatMap(c =>
          split(kit, c)(
            e =>
              for {
                condT <- condAt(i)
                si <- sAt(i)
                condEq <- condTrue(kit, c, sN, si, e)
                // s n = n would give n = k = i, and i < n.
                snNe <- {
                  for {
                    e2 <- eqTerm(sN, n)
                    he2 <- assume(e2)
                    toK <- Conv.trans(he2, skBack)
                    nk <- inj(n, k, nSuc, kLt, toK)
                    kn <- Conv.sym(nk)
                    in_ <- Conv.trans(e, kn)
                    nn <- Limit.rewriteInProposition(in_, hi)
                    irr <- kit.use("NUM_LT_IRREFL", List(n))
                    absurd <- rules.notElim(irr, nn)
                    r <- rules.notIntro(e2, absurd)
                  } yield r
                }
                below <- belowOfNeq(kit, sN, n, snLtSuc, snNe)
                back <- Conv.sym(condEq)
                r <- Limit.rewriteInProposition(back, below)
              } yield r,
            ne =>
              for {
                si <- sAt(i)
                condEq <- condFalse(kit, c, sN, si, ne)
                siLtSuc <- kit.applyTo(hR, List(i), iSuc)
                siNe <- notOnN(i, iSuc, _ => Right(ne))
                below <- belowOfNeq(kit, si, n, siLtSuc, siNe)
                back <- Conv.sym(condEq)
                r <- Limit.rewriteInProposition(back, below)
              } yield r
          )
        )
      }
      range <- rules.disch(iLtT, rangeInner).flatMap(rules.gen(i, _))
      _ <- if (range.conclusion == rP) Right(()) else Left(NotOfForm("the range condition the hypothesis asks for", range.conclusion))

      // s' is injective on [0, n).
      i2 = fresh("i", num, hR, hI, hO, ih, kb)
      j2 = fresh("j", num, hR, hI, hO, ih, kb, Conv.refl(i2))
      i2Lt <- lt(i2, n)
      j2Lt <- lt(j2, n)
      hi2 <- assume(i2Lt)
      hj2 <- assume(j2Lt)
      ci2 <- condAt(i2)
      cj2 <- condAt(j2)
      heT <- eqTerm(ci2, cj2)
      he <- assume(heT)
      i2Suc <- belowSuc(kit, i2, n, hi2)
      j2Suc <- belowSuc(kit, j2, n, hj2)
      si2 <- sAt(i2)
      sj2 <- sAt(j2)
      ik <- eqTerm(i2, k)
      jk <- eqTerm(j2, k)
      target <- eqTerm(i2, j2)
      // `x = n` with `x < n` is absurd.
      absurdAt = (x: Term, xLt: Kernel.Thm, xn: Kernel.Thm) =>
        for {
          nn <- Limit.rewriteInProposition(xn, xLt)
          irr <- kit.use("NUM_LT_IRREFL", List(n))
          r <- rules.notElim(irr, nn)
        } yield r
      injInner <- split(kit, ik)(
        ei =>
          for {
            ci <- condTrue(kit, ik, sN, si2, ei)
            r <- split(kit, jk)(
              ej => Conv.sym(ej).flatMap(Conv.trans(ei, _)),
              nj =>
                for {
                  cj <- condFalse(kit, jk, sN, sj2, nj)
                  e1 <- Conv.sym(ci)
                  e2 <- Conv.trans(he, cj)
                  snsj <- Conv.trans(e1, e2)
                  nj_ <- inj(n, j2, nSuc, j2Suc, snsj)
                  jn <- Conv.sym(nj_)
                  f_ <- absurdAt(j2, hj2, jn)
                  r <- rules.falsityElim(target, f_)
                } yield r
            )
          } yield r,
        ni =>
          for {
            ci <- condFalse(kit, ik, sN, si2, ni)
            r <- split(kit, jk)(
              ej =>
                for {
                  cj <- condTrue(kit, jk, sN, sj2, ej)
                  e1 <- Conv.sym(ci)
                  e2 <- Conv.trans(he, cj)
                  sisn <- Conv.trans(e1, e2)
                  in_ <- inj(i2, n, i2Suc, nSuc, sisn)
                  f_ <- absurdAt(i2, hi2, in_)
                  r <- rules.falsityElim(target, f_)
                } yield r,
              nj =>
                for {
                  cj <- condFalse(kit, jk, sN, sj2, nj)
                  e1 <- Conv.sym(ci)
                  e2 <- Conv.trans(he, cj)
                  sisj <- Conv.trans(e1, e2)
                  r <- inj(i2, j2, i2Suc, j2Suc, sisj)
                } yield r
            )
          } yield r
      )
      injective <- dischAll(kit, List(i2Lt, j2Lt, heT), injInner).flatMap(rules.gen(j2, _)).flatMap(rules.gen(i2, _))
      _ <- if (injective.conclusion == iP) Right(()) else Left(NotOfForm("the injectivity the hypothesis asks for", injective.conclusion))

      // s' is onto [0, n).
      j3 = fresh("j", num, hR, hI, hO, ih, kb)
      j3Lt <- lt(j3, n)
      hj3 <- assume(j3Lt)
      ontoBody <- open(kit, oP, j3)
      p_ob <- imp(kit, ontoBody)
      (_, wanted) = p_ob
      wantedPred <- kit.logic.destExistsPredicate(wanted).toRight(NotOfForm("an existential", wanted))
      j3Suc <- belowSuc(kit, j3, n, hj3)
      jEx <- kit.applyTo(hO, List(j3), j3Suc)
      jPred <- kit.logic.destExistsPredicate(jEx.conclusion).toRight(NotOfForm("an existential", jEx.conclusion))
      m = fresh("m", num, hR, hI, hO, ih, kb, hj3)
      mBodyT <- instantiate(jPred, m)
      mb <- assume(mBodyT)
      mLt <- rules.conjElim1(mb)
      sm <- rules.conjElim2(mb)
      mCases <- kit.use("NUM_LT_SUC_CASES", List(n, m), mLt)
      p_mc <- disj(kit, mCases.conclusion)
      (mBelow, mSame) = p_mc
      sM <- sAt(m)
      mk <- eqTerm(m, k)
      kn <- eqTerm(k, n)
      fromBelow <- for {
        mb2 <- assume(mBelow)
        mkNot <- for {
          he2 <- assume(mk)
          skm <- Limit.rewriteInProposition(he2, sm) // s k = j
          jBack <- Conv.sym(skm)
          jn <- Conv.trans(jBack, sk) // j = n
          f_ <- absurdAt(j3, hj3, jn)
          r <- rules.notIntro(mk, f_)
        } yield r
        cm <- condFalse(kit, mk, sN, sM, mkNot)
        cmj <- Conv.trans(cm, sm)
        both <- rules.conjIntro(mb2, cmj)
        r <- rules.existsIntro(wantedPred, m, both)
      } yield r
      fromSame <- for {
        ms <- assume(mSame)
        snj <- Limit.rewriteInProposition(ms, sm) // s n = j
        knNot <- for {
          he3 <- assume(kn)
          snn <- Limit.rewriteInProposition(he3, sk) // s n = n
          jBack <- Conv.sym(snj)
          jn <- Conv.trans(jBack, snn)
          f_ <- absurdAt(j3, hj3, jn)
          r <- rules.notIntro(kn, f_)
        } yield r
        kBelow <- belowOfNeq(kit, k, n, kLt, knNot)
        kkT <- eqTerm(k, k)
        sK <- sAt(k)
        ck <- condTrue(kit, kkT, sN, sK, Conv.refl(k))
        ckj <- Conv.trans(ck, snj)
        both <- rules.conjIntro(kBelow, ckj)
        r <- rules.existsIntro(wantedPred, k, both)
      } yield r
      ontoCase <- rules.disjElim(mCases, fromBelow, fromSame)
      ontoOne <- rules.existsElim(jEx, m, ontoCase)
      onto <- rules.disch(j3Lt, ontoOne).flatMap(rules.gen(j3, _))
      _ <- if (onto.conclusion == oP) Right(()) else Left(NotOfForm("the surjectivity the hypothesis asks for", onto.conclusion))

      // The claim at n for s', and the product at SUC n stitched onto it.
      ihEq <- rules.mp(ihAt, range).flatMap(rules.mp(_, injective)).flatMap(rules.mp(_, onto))
      p_goal <- sides(goalEq)
      (goalL, goalR) = p_goal
      p_fl <- productOf(goalL)
      (bigF, _) = p_fl
      p_gl <- sides(ihEq.conclusion)
      (ihL, _) = p_gl
      p_gg <- productOf(ihL)
      (bigG, _) = p_gg
      eqA <- kit.use("NUM_PROD_SUC", List(bigF, n))
      fSuc <- kit.use("NUM_PROD_SUC", List(f, n))
      fSucBack <- Conv.sym(fSuc)
      fn_ <- app(f, n)
      fsn <- sAt(n).flatMap(app(f, _))
      kCases <- kit.use("NUM_LT_SUC_CASES", List(n, k), kLt)
      p_kc <- disj(kit, kCases.conclusion)
      (kBelowT, kSameT) = p_kc
      byPoint <- for {
        kb2 <- assume(kBelowT)
        u = fresh("u", num, hR, hI, hO, ih, kb)
        uLt <- lt(u, n)
        hu <- assume(uLt)
        uk <- eqTerm(u, k).flatMap(kit.logic.mkNot)
        hne <- assume(uk)
        su <- sAt(u)
        uEq <- eqTerm(u, k)
        cu <- condFalse(kit, uEq, sN, su, hne)
        fcu <- cong(f, cu)
        agree <- dischAll(kit, List(uLt, uk), fcu).flatMap(rules.gen(u, _))
        pt <- kit.applyTo(point, List(bigG, bigF, k, n), kb2, agree)
        kkT <- eqTerm(k, k)
        sK <- sAt(k)
        ckk <- condTrue(kit, kkT, sN, sK, Conv.refl(k))
        pt1 <- Limit.rewriteInProposition(ckk, pt)
        pt2 <- Limit.rewriteInProposition(sk, pt1)
        back <- Conv.sym(pt2)
        times <- kit.at("\\y:num. \\x:num. x * y", fn_)
        moved <- cong(times, ihEq)
        r <- transAll(eqA, back, moved, fSucBack)
      } yield r
      byCong <- for {
        ks <- assume(kSameT)
        snn <- Limit.rewriteInProposition(ks, sk)
        u = fresh("u", num, hR, hI, hO, ih, kb)
        uLt <- lt(u, n)
        hu <- assume(uLt)
        uEq <- eqTerm(u, k)
        hue <- assume(uEq)
        un <- Conv.trans(hue, ks)
        f_ <- absurdAt(u, hu, un)
        uNe <- rules.notIntro(uEq, f_)
        su <- sAt(u)
        cu <- condFalse(kit, uEq, sN, su, uNe)
        fcu <- cong(f, cu)
        agree <- rules.disch(uLt, fcu).flatMap(rules.gen(u, _))
        gf <- kit.use("NUM_PROD_CONG", List(bigG, bigF, n), agree)
        fg <- Conv.sym(gf)
        ff <- Conv.trans(fg, ihEq)
        times <- kit.at("\\y:num. \\x:num. x * y", fsn)
        moved <- cong(times, ff)
        last <- kit.at("\\m:num. \\x:num. NUM_PROD (f:num->num) m * f x", n)
        movedLast <- cong(last, snn)
        r <- transAll(eqA, moved, movedLast, fSucBack)
      } yield r
      joined <- rules.disjElim(kCases, byPoint, byCong)
      result <- rules.existsElim(kEx, k, joined)
    } yield result
  }




  private def num(kit: Kit) = kit.numbers

  /* ---------------------------------------------------------------- congruence helpers */

  def congParts(t: Term): R[(Term, Term, Term)] = t match {
    case App(App(App(Const("NUM_CONG", _), m), x), y) => Right((m, x, y))
    case other => Left(NotOfForm("a congruence", other))
  }

  def congRefl(kit: Kit, m: Term, x: Term): R[Kernel.Thm] = kit.use("NUM_CONG_REFL", List(m, x))

  /** `NUM_CONG m x y` from `x = y`. */
  def congOfEq(kit: Kit, m: Term, eq: Kernel.Thm): R[Kernel.Thm] =
    for {
      p <- sides(eq.conclusion)
      (x, _) = p
      lam <- kit.at("\\m:num. \\x:num. \\t:num. NUM_CONG m x t", m, x)
      moved <- cong(lam, eq)
      refl <- congRefl(kit, m, x)
      r <- LogicError.lift(Kernel.eqMp(moved, refl))
    } yield r

  def congSym(kit: Kit, c: Kernel.Thm): R[Kernel.Thm] =
    congParts(c.conclusion).flatMap { case (m, x, y) => kit.use("NUM_CONG_SYM", List(m, x, y), c) }

  def congTrans(kit: Kit, a: Kernel.Thm, b: Kernel.Thm): R[Kernel.Thm] =
    for {
      pa <- congParts(a.conclusion)
      pb <- congParts(b.conclusion)
      r <- kit.use("NUM_CONG_TRANS", List(pa._1, pa._2, pa._3, pb._3), a, b)
    } yield r

  def congChain(kit: Kit, steps: Kernel.Thm*): R[Kernel.Thm] =
    steps.tail.foldLeft[R[Kernel.Thm]](Right(steps.head))((acc, s) => acc.flatMap(congTrans(kit, _, s)))

  def congMul(kit: Kit, a: Kernel.Thm, b: Kernel.Thm): R[Kernel.Thm] =
    for {
      pa <- congParts(a.conclusion)
      pb <- congParts(b.conclusion)
      r <- kit.use("NUM_CONG_MUL", List(pa._1, pa._2, pa._3, pb._2, pb._3), a, b)
    } yield r

  /** `NUM_CONG m x y` for two terms SEMIRING proves equal. */
  def congBy(kit: Kit, m: Term, x: Term, y: Term, eqs: Vector[Kernel.Thm] = Vector.empty): R[Kernel.Thm] =
    equate(kit, x, y, eqs, Vector.empty).flatMap(congOfEq(kit, m, _))

  def nonZero(kit: Kit, n: Term, hn: Kernel.Thm): R[Kernel.Thm] =
    zero(kit).flatMap(z => neqOfLt(kit, z, n, hn))

  /** `NUM_CONG n x (NUM_MOD x n)`. */
  def modCong(kit: Kit, n: Term, x: Term): R[Kernel.Thm] =
    for {
      z <- zero(kit)
      md <- kit.at("\\x:num. \\n:num. NUM_MOD x n", x, n)
      dv <- kit.at("\\x:num. \\n:num. NUM_DIV x n", x, n)
      left <- kit.at("\\x:num. \\n:num. x + n * 0", x, n)
      right <- kit.at("\\x:num. \\n:num. NUM_MOD x n + n * NUM_DIV x n", x, n)
      mid <- kit.at("\\x:num. \\n:num. n * NUM_DIV x n + NUM_MOD x n", x, n)
      dm <- kit.use("NUM_DIV_MOD", List(x, n))
      e1 <- equate(kit, left, x, Vector.empty, Vector.empty)
      e2 <- Conv.sym(dm)
      e3 <- equate(kit, mid, right, Vector.empty, Vector.empty)
      eq <- transAll(e1, e2, e3)
      r <- kit.use("NUM_CONG_INTRO", List(n, x, md, z, dv), eq)
    } yield r

  /* ---------------------------------------------------------------- gcd lemmas */

  /** `|- !n x. 0 < n ==> NUM_GCD x n = SUC 0 ==> NUM_GCD (NUM_MOD x n) n = SUC 0` */
  def gcdMod(kit: Kit): R[Kernel.Thm] = {
    val n = Term.variable("n", num(kit))
    val x = Term.variable("x", num(kit))
    val rules = kit.rules
    for {
      hnT <- kit.proposition("NUM_LT 0 (n:num)")
      hxT <- kit.proposition("NUM_GCD (x:num) (n:num) = SUC 0")
      hn <- assume(hnT)
      hx <- assume(hxT)
      nz <- nonZero(kit, n, hn)
      md <- kit.at("\\x:num. \\n:num. NUM_MOD x n", x, n)
      dv <- kit.at("\\x:num. \\n:num. NUM_DIV x n", x, n)
      d <- kit.at("\\x:num. \\n:num. NUM_GCD (NUM_MOD x n) n", x, n)
      mdZero <- zero(kit).flatMap(eqTerm(md, _)).flatMap(kit.logic.mkNot)
      xZero <- zero(kit).flatMap(eqTerm(x, _)).flatMap(kit.logic.mkNot)
      cond1 <- rules.disjIntro2(mdZero, nz)
      cond2 <- rules.disjIntro2(xZero, nz)
      dl <- kit.use("NUM_GCD_DIVIDES_LEFT", List(md, n), cond1)
      dr <- kit.use("NUM_GCD_DIVIDES_RIGHT", List(md, n), cond1)
      ndv <- mul(kit, n, dv)
      dnq <- kit.use("NUM_DIVIDES_MUL", List(d, n, dv), dr)
      both <- rules.conjIntro(dnq, dl)
      dsum <- kit.use("NUM_DIVIDES_ADD", List(d, ndv, md), both)
      dm <- kit.use("NUM_DIV_MOD", List(x, n))
      dx <- Limit.rewriteInProposition(dm, dsum)
      both2 <- rules.conjIntro(dx, dr)
      dg <- kit.use("NUM_GCD_DIVIDES", List(x, n, d), cond2, both2)
      d1 <- Limit.rewriteInProposition(hx, dg)
      r <- kit.use("NUM_DIVIDES_ONE", List(d), d1)
      out <- dischAll(kit, List(hnT, hxT), r)
      general <- rules.genAll(out, List(n, x))
    } yield general
  }

  /** `|- !n x y. 0 < n ==> NUM_CONG n (x * y) (SUC 0) ==> NUM_GCD y n = SUC 0` */
  def unitCoprime(kit: Kit): R[Kernel.Thm] = {
    val n = Term.variable("n", num(kit))
    val x = Term.variable("x", num(kit))
    val y = Term.variable("y", num(kit))
    val rules = kit.rules
    for {
      hnT <- kit.proposition("NUM_LT 0 (n:num)")
      hcT <- kit.proposition("NUM_CONG (n:num) ((x:num) * (y:num)) (SUC 0)")
      hn <- assume(hnT)
      hc <- assume(hcT)
      nz <- nonZero(kit, n, hn)
      d <- kit.at("\\y:num. \\n:num. NUM_GCD y n", y, n)
      yZero <- zero(kit).flatMap(eqTerm(y, _)).flatMap(kit.logic.mkNot)
      cond <- rules.disjIntro2(yZero, nz)
      dy <- kit.use("NUM_GCD_DIVIDES_LEFT", List(y, n), cond)
      dn <- kit.use("NUM_GCD_DIVIDES_RIGHT", List(y, n), cond)
      dyx <- kit.use("NUM_DIVIDES_MUL", List(d, y, x), dy)
      sym <- kit.use("NUM_MUL_SYM", List(y, x))
      dxy <- Limit.rewriteInProposition(sym, dyx)
      xy <- mul(kit, x, y)
      o <- one(kit)
      elim <- kit.use("NUM_CONG_ELIM", List(n, xy, o), hc)
      uPred <- kit.logic.destExistsPredicate(elim.conclusion).toRight(NotOfForm("an existential", elim.conclusion))
      u = fresh("u", num(kit), hc, hn)
      uBodyT <- instantiate(uPred, u)
      uBody <- assume(uBodyT)
      vPred <- kit.logic.destExistsPredicate(uBodyT).toRight(NotOfForm("an existential", uBodyT))
      v = fresh("v", num(kit), hc, hn, uBody)
      vBodyT <- instantiate(vPred, v)
      he <- assume(vBodyT)
      dnu <- kit.use("NUM_DIVIDES_MUL", List(d, n, u), dn)
      nu <- mul(kit, n, u)
      both <- rules.conjIntro(dxy, dnu)
      dsum <- kit.use("NUM_DIVIDES_ADD", List(d, xy, nu), both)
      dOnePlus <- Limit.rewriteInProposition(he, dsum)
      p_s <- sides(vBodyT)
      (_, onePlus) = p_s
      nv <- mul(kit, n, v)
      swapped <- kit.at("\\p:num. \\q:num. p + q", nv, o)
      swap <- equate(kit, onePlus, swapped, Vector.empty, Vector.empty)
      dSwapped <- Limit.rewriteInProposition(swap, dOnePlus)
      dnv <- kit.use("NUM_DIVIDES_MUL", List(d, n, v), dn)
      dOne <- kit.use("NUM_DIVIDES_SUMMAND", List(d, nv, o), dnv, dSwapped)
      r <- kit.use("NUM_DIVIDES_ONE", List(d), dOne)
      rv <- rules.existsElim(uBody, v, r)
      ru <- rules.existsElim(elim, u, rv)
      out <- dischAll(kit, List(hnT, hcT), ru)
      general <- rules.genAll(out, List(n, x, y))
    } yield general
  }

  /** `|- !n a. 0 < n ==> NUM_GCD a n = SUC 0 ==> ?b. NUM_CONG n (a * b) (SUC 0)` */
  def inverse(kit: Kit): R[Kernel.Thm] = {
    val n = Term.variable("n", num(kit))
    val a = Term.variable("a", num(kit))
    val rules = kit.rules
    for {
      hnT <- kit.proposition("NUM_LT 0 (n:num)")
      haT <- kit.proposition("NUM_GCD (a:num) (n:num) = SUC 0")
      goal <- kit.proposition("?b:num. NUM_CONG (n:num) ((a:num) * b) (SUC 0)")
      goalPred <- kit.logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
      hn <- assume(hnT)
      ha <- assume(haT)
      nz <- nonZero(kit, n, hn)
      aZero <- zero(kit).flatMap(eqTerm(a, _)).flatMap(kit.logic.mkNot)
      cond <- rules.disjIntro2(aZero, nz)
      bez <- kit.use("NUM_BEZOUT", List(a, n), cond)
      zPred <- kit.logic.destExistsPredicate(bez.conclusion).toRight(NotOfForm("an existential", bez.conclusion))
      z = fresh("z", num(kit), hn, ha)
      zBodyT <- instantiate(zPred, z)
      zBody <- assume(zBodyT)
      uPred <- kit.logic.destExistsPredicate(zBodyT).toRight(NotOfForm("an existential", zBodyT))
      u = fresh("u", num(kit), hn, ha, zBody)
      uBodyT <- instantiate(uPred, u)
      d0 <- assume(uBodyT)
      d <- Limit.rewriteInProposition(ha, d0)
      p_d <- disj(kit, d.conclusion)
      (caseA, caseB) = p_d
      o <- one(kit)
      zr <- zero(kit)
      az <- mul(kit, a, z)

      // a z = n u + 1: z is the inverse.
      fromA <- for {
        hA <- assume(caseA)
        left <- kit.at("\\a:num. \\z:num. \\n:num. a * z + n * 0", a, z, n)
        right <- kit.at("\\n:num. \\u:num. SUC 0 + n * u", n, u)
        eq <- equate(kit, left, right, Vector(hA), Vector.empty)
        c <- kit.use("NUM_CONG_INTRO", List(n, az, o, zr, u), eq)
        r <- rules.existsIntro(goalPred, z, c)
      } yield r

      // n z = a u + 1: with n = w + 1, u w is the inverse.
      fromB <- for {
        hB <- assume(caseB)
        cases <- kit.use("NUM_CASES", List(n))
        p_c <- disj(kit, cases.conclusion)
        (isZero, isSuc) = p_c
        zeroCase <- for {
          h0 <- assume(isZero)
          f_ <- rules.notElim(nz, h0)
          r <- rules.falsityElim(goal, f_)
        } yield r
        wPred <- kit.logic.destExistsPredicate(isSuc).toRight(NotOfForm("an existential", isSuc))
        w = fresh("w", num(kit), hn, ha, zBody, d)
        wBodyT <- instantiate(wPred, w)
        hw <- assume(wBodyT)
        addSuc <- kit.use("NUM_ADD_SUC", List(w, zr))
        addZero <- kit.use(Peano.AddAtZero, List(w))
        sucLam <- kit.term("SUC", Type.fun(num(kit), num(kit)))
        sucW <- cong(sucLam, addZero) // SUC (w + 0) = SUC w
        wPlus <- Conv.sym(sucW).flatMap(s1 => Conv.sym(addSuc).map(s2 => (s1, s2)))
        nw <- Conv.trans(hw, wPlus._1).flatMap(Conv.trans(_, wPlus._2)) // n = w + SUC 0
        timesW <- kit.at("\\w:num. \\x:num. x * w", w)
        e <- cong(timesW, hB) // (n z) w = (a u + 1) w
        uw <- mul(kit, u, w)
        zw <- mul(kit, z, w)
        auw <- mul(kit, a, uw)
        lhs <- kit.at("\\a:num. \\u:num. \\w:num. \\n:num. a * (u * w) + n * SUC 0", a, u, w, n)
        rhs <- kit.at("\\n:num. \\z:num. \\w:num. SUC 0 + n * (z * w)", n, z, w)
        midT <- kit.at("\\a:num. \\u:num. \\w:num. SUC 0 + (a * u + SUC 0) * w", a, u, w)
        e1 <- equate(kit, lhs, midT, Vector(nw), Vector.empty)
        plusOne <- Parser.term(kit.theory, kit.notation, "\\x:num. SUC 0 + x")
        eBack <- Conv.sym(e)
        e2 <- cong(plusOne, eBack)
        p_e2 <- sides(e2.conclusion)
        (_, afterE2) = p_e2
        e3 <- equate(kit, afterE2, rhs, Vector.empty, Vector.empty)
        eq <- transAll(e1, e2, e3)
        c <- kit.use("NUM_CONG_INTRO", List(n, auw, o, o, zw), eq)
        found <- rules.existsIntro(goalPred, uw, c)
        hs <- assume(isSuc)
        sucCase <- rules.existsElim(hs, w, found)
        r <- rules.disjElim(cases, zeroCase, sucCase)
      } yield r

      joined <- rules.disjElim(d, fromA, fromB)
      ru <- rules.existsElim(zBody, u, joined)
      rz <- rules.existsElim(bez, z, ru)
      out <- dischAll(kit, List(hnT, haT), rz)
      general <- rules.genAll(out, List(n, a))
    } yield general
  }

  /* ---------------------------------------------------------------- products */

  /** `|- !m f g n. (!i. i < n ==> NUM_CONG m (f i) (g i)) ==> NUM_CONG m (NUM_PROD f n) (NUM_PROD g n)` */
  def prodCongMod(kit: Kit): R[Kernel.Thm] = {
    val fn = Type.fun(num(kit), num(kit))
    val m = Term.variable("m", num(kit))
    val f = Term.variable("f", fn)
    val g = Term.variable("g", fn)
    val rules = kit.rules
    for {
      statement <- kit.proposition(
        "!n:num. (!i:num. NUM_LT i n ==> NUM_CONG (m:num) ((f:num->num) i) ((g:num->num) i)) ==> " +
          "NUM_CONG m (NUM_PROD f n) (NUM_PROD g n)")
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            p <- imp(kit, base)
            (h, _) = p
            z1 <- kit.use("NUM_PROD_ZERO", List(f))
            z2 <- kit.use("NUM_PROD_ZERO", List(g))
            eq <- Conv.sym(z2).flatMap(Conv.trans(z1, _))
            c <- congOfEq(kit, m, eq)
            r <- rules.disch(h, c)
          } yield r,
        step => {
          val n = step.variable
          for {
            p <- imp(kit, step.goal)
            (hT, _) = p
            h <- assume(hT)
            i = fresh("i", num(kit), h, step.hypothesis)
            iLt <- kit.term("NUM_LT", Type.fun(num(kit), Type.fun(num(kit), Type.Bool))).flatMap(app(_, i, n))
            hi <- assume(iLt)
            iSuc <- belowSuc(kit, i, n, hi)
            ci <- kit.applyTo(h, List(i), iSuc)
            below <- rules.disch(iLt, ci).flatMap(rules.gen(i, _))
            ih <- rules.mp(step.hypothesis, below)
            nSuc <- ltSuc(kit, n)
            cn <- kit.applyTo(h, List(n), nSuc)
            prod <- congMul(kit, ih, cn)
            fSuc <- kit.use("NUM_PROD_SUC", List(f, n)).flatMap(Conv.sym)
            gSuc <- kit.use("NUM_PROD_SUC", List(g, n)).flatMap(Conv.sym)
            r1 <- Limit.rewriteInProposition(fSuc, prod)
            r2 <- Limit.rewriteInProposition(gSuc, r1)
            r <- rules.disch(hT, r2)
          } yield r
        }
      )
      general <- rules.genAll(proved, List(m, f, g))
    } yield general
  }

  /** `|- !f g n. NUM_PROD (\i. f i * g i) n = NUM_PROD f n * NUM_PROD g n` */
  def prodMul(kit: Kit): R[Kernel.Thm] = {
    val fn = Type.fun(num(kit), num(kit))
    val f = Term.variable("f", fn)
    val g = Term.variable("g", fn)
    for {
      statement <- kit.proposition(
        "!n:num. NUM_PROD (\\i:num. (f:num->num) i * (g:num->num) i) n = NUM_PROD f n * NUM_PROD g n")
      both <- Parser.term(kit.theory, kit.notation, "\\i:num. (f:num->num) i * (g:num->num) i")
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            s <- sides(base)
            z1 <- kit.use("NUM_PROD_ZERO", List(both))
            z2 <- kit.use("NUM_PROD_ZERO", List(f))
            z3 <- kit.use("NUM_PROD_ZERO", List(g))
            r <- equate(kit, s._1, s._2, Vector(z1), Vector(z2, z3))
          } yield r,
        step => {
          val n = step.variable
          for {
            s <- sides(step.goal)
            p1 <- kit.use("NUM_PROD_SUC", List(both, n))
            p2 <- kit.use("NUM_PROD_SUC", List(f, n))
            p3 <- kit.use("NUM_PROD_SUC", List(g, n))
            r <- equate(kit, s._1, s._2, Vector(p1, step.hypothesis), Vector(p2, p3))
          } yield r
        }
      )
      general <- kit.rules.genAll(proved, List(f, g))
    } yield general
  }

  /**
   * `|- !p a n. NUM_PROD (\i. COND (p i) a (SUC 0)) n = NUM_POW a (NUM_SUM (\i. COND (p i) (SUC 0) 0) n)`
   */
  def prodCondPow(kit: Kit): R[Kernel.Thm] = {
    val p = Term.variable("p", Type.fun(num(kit), Type.Bool))
    val a = Term.variable("a", num(kit))
    for {
      statement <- kit.proposition(
        "!n:num. NUM_PROD (\\i:num. COND ((p:num->bool) i) (a:num) (SUC 0)) n = " +
          "NUM_POW a (NUM_SUM (\\i:num. COND (p i) (SUC 0) 0) n)")
      factor <- Parser.term(kit.theory, kit.notation, "\\i:num. COND ((p:num->bool) i) (a:num) (SUC 0)")
      count <- Parser.term(kit.theory, kit.notation, "\\i:num. COND ((p:num->bool) i) (SUC 0) 0")
      powAdd <- kit.fact("NUM_POW_ADD")
      powSuc <- kit.fact("NUM_POW_SUC")
      powZero <- kit.fact("NUM_POW_ZERO")
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            s <- sides(base)
            z1 <- kit.use("NUM_PROD_ZERO", List(factor))
            z2 <- kit.use("NUM_SUM_ZERO", List(count))
            r <- equate(kit, s._1, s._2, Vector(z1), Vector(z2, powZero))
          } yield r,
        step => {
          val n = step.variable
          for {
            s <- sides(step.goal)
            p1 <- kit.use("NUM_PROD_SUC", List(factor, n))
            p2 <- kit.use("NUM_SUM_SUC", List(count, n))
            pn <- app(p, n)
            o <- one(kit)
            z <- zero(kit)
            r <- split(kit, pn)(
              holds =>
                for {
                  c1 <- condTrue(kit, pn, a, o, holds)
                  c2 <- condTrue(kit, pn, o, z, holds)
                  r <- equate(kit, s._1, s._2, Vector(p1, step.hypothesis, c1), Vector(p2, c2, powAdd, powSuc, powZero))
                } yield r,
              fails =>
                for {
                  c1 <- condFalse(kit, pn, a, o, fails)
                  c2 <- condFalse(kit, pn, o, z, fails)
                  r <- equate(kit, s._1, s._2, Vector(p1, step.hypothesis, c1), Vector(p2, c2, powAdd, powZero))
                } yield r
            )
          } yield r
        }
      )
      general <- kit.rules.genAll(proved, List(p, a))
    } yield general
  }


  /* ---------------------------------------------------------------- Euler */

  final case class Lemmas(
    permute: Kernel.Thm, inverse: Kernel.Thm, gcdMod: Kernel.Thm, unitCoprime: Kernel.Thm,
    prodCongMod: Kernel.Thm, prodMul: Kernel.Thm, prodCondPow: Kernel.Thm
  )

  /**
   * `|- !n a. 0 < n ==> NUM_GCD a n = SUC 0 ==> NUM_CONG n (NUM_POW a (NUM_TOTIENT n)) (SUC 0)`
   */
  def euler(kit: Kit, l: Lemmas, totient: Kernel.Thm): R[Kernel.Thm] = {
    val nm = num(kit)
    val n = Term.variable("n", nm)
    val a = Term.variable("a", nm)
    val rules = kit.rules
    def lt(x: Term, y: Term): R[Term] =
      kit.term("NUM_LT", Type.fun(nm, Type.fun(nm, Type.Bool))).flatMap(app(_, x, y))
    for {
      hnT <- kit.proposition("NUM_LT 0 (n:num)")
      haT <- kit.proposition("NUM_GCD (a:num) (n:num) = SUC 0")
      hn <- assume(hnT)
      ha <- assume(haT)
      o <- one(kit)
      zr <- zero(kit)

      invEx <- kit.applyTo(l.inverse, List(n, a), hn, ha)
      bPred <- kit.logic.destExistsPredicate(invEx.conclusion).toRight(NotOfForm("an existential", invEx.conclusion))
      b = fresh("b", nm, hn, ha)
      hbT <- instantiate(bPred, b)
      hb <- assume(hbT)
      bCop <- kit.applyTo(l.unitCoprime, List(n, a, b), hn, hb)

      coprimeAt = (x: Term) => kit.at("\\n:num. \\x:num. NUM_GCD x n = SUC 0", n, x)
      rLam <- kit.at("\\n:num. \\k:num. COND (NUM_GCD k n = SUC 0) k (SUC 0)", n)
      sLam <- kit.at("\\n:num. \\a:num. \\k:num. COND (NUM_GCD k n = SUC 0) (NUM_MOD (a * k) n) k", n, a)
      sAt = (x: Term) => instantiate(sLam, x)
      modAt = (x: Term) => kit.at("\\n:num. \\a:num. \\x:num. NUM_MOD (a * x) n", n, a, x)
      // p x gives p (NUM_MOD (a * x) n).
      keeps = (x: Term, px: Kernel.Thm) =>
        for {
          ax <- mul(kit, a, x)
          g <- kit.use("NUM_GCD_MUL", List(a, x, n), hn, ha, px)
          r <- kit.applyTo(l.gcdMod, List(n, ax), hn, g)
        } yield r

      permAt <- rules.specAll(l.permute, List(rLam, n, sLam)).flatMap(Limit.normalised)
      p_1 <- imp(kit, permAt.conclusion)
      (rangeT, rest1) = p_1
      p_2 <- imp(kit, rest1)
      (injT, rest2) = p_2
      p_3 <- imp(kit, rest2)
      (ontoT, _) = p_3

      // Range.
      i = fresh("i", nm, hn, ha, hb)
      rangeBody <- open(kit, rangeT, i)
      p_rb <- imp(kit, rangeBody)
      (iLtT, _) = p_rb
      hi <- assume(iLtT)
      pi <- coprimeAt(i)
      si <- sAt(i)
      mi <- modAt(i)
      rangeInner <- split(kit, pi)(
        yes =>
          for {
            c <- condTrue(kit, pi, mi, i, yes)
            ai <- mul(kit, a, i)
            below <- kit.use("NUM_MOD_LT", List(ai, n), hn)
            back <- Conv.sym(c)
            ltLam <- kit.at("\\n:num. \\x:num. NUM_LT x n", n)
            r <- transport(ltLam, back, below)
          } yield r,
        no =>
          for {
            c <- condFalse(kit, pi, mi, i, no)
            back <- Conv.sym(c)
            ltLam <- kit.at("\\n:num. \\x:num. NUM_LT x n", n)
            r <- transport(ltLam, back, hi)
          } yield r
      )
      range <- rules.disch(iLtT, rangeInner).flatMap(rules.gen(i, _))
      _ <- if (range.conclusion == rangeT) Right(()) else Left(NotOfForm("the range", range.conclusion))

      // Cancelling a: a x == a y gives x == y.
      cancel = (x: Term, y: Term, c: Kernel.Thm) =>
        for {
          ab <- mul(kit, a, b)
          rx <- congRefl(kit, n, x)
          ry <- congRefl(kit, n, y)
          rb <- congRefl(kit, n, b)
          c1x <- congMul(kit, rx, hb)
          c1y <- congMul(kit, ry, hb)
          cA <- congMul(kit, c, rb)
          x1 <- mul(kit, x, o)
          y1 <- mul(kit, y, o)
          xab <- mul(kit, x, ab)
          yab <- mul(kit, y, ab)
          axb <- mul(kit, a, x).flatMap(mul(kit, _, b))
          ayb <- mul(kit, a, y).flatMap(mul(kit, _, b))
          e1 <- congBy(kit, n, x, x1)
          e2 <- congSym(kit, c1x)
          e3 <- congBy(kit, n, xab, axb)
          e5 <- congBy(kit, n, ayb, yab)
          e7 <- congBy(kit, n, y1, y)
          r <- congChain(kit, e1, e2, e3, cA, e5, c1y, e7)
        } yield r
      // x == y with both below n gives x = y.
      equalBelow = (x: Term, y: Term, c: Kernel.Thm, xLt: Kernel.Thm, yLt: Kernel.Thm) =>
        for {
          m1 <- kit.use("NUM_MOD_OF_CONG", List(n, x, y), c, yLt)
          rx <- congRefl(kit, n, x)
          m2 <- kit.use("NUM_MOD_OF_CONG", List(n, x, x), rx, xLt)
          r <- Conv.sym(m2).flatMap(Conv.trans(_, m1))
        } yield r

      // Injectivity.
      i2 = fresh("i", nm, hn, ha, hb)
      j2 = fresh("j", nm, hn, ha, hb, Conv.refl(i2))
      injBody <- open(kit, injT, i2).flatMap(t => kit.logic.destForallPredicate(t).toRight(NotOfForm("a universal", t)).flatMap(instantiate(_, j2)))
      p_ib <- imp(kit, injBody)
      (i2LtT, ib1) = p_ib
      p_ib2 <- imp(kit, ib1)
      (j2LtT, ib2) = p_ib2
      p_ib3 <- imp(kit, ib2)
      (heT, targetT) = p_ib3
      hi2 <- assume(i2LtT)
      hj2 <- assume(j2LtT)
      he <- assume(heT)
      pi2 <- coprimeAt(i2)
      pj2 <- coprimeAt(j2)
      mi2 <- modAt(i2)
      mj2 <- modAt(j2)
      gcdLam <- kit.at("\\n:num. \\x:num. NUM_GCD x n = SUC 0", n)
      injInner <- split(kit, pi2)(
        yi =>
          for {
            ci <- condTrue(kit, pi2, mi2, i2, yi)
            r <- split(kit, pj2)(
              yj =>
                for {
                  cj <- condTrue(kit, pj2, mj2, j2, yj)
                  mm <- Conv.sym(ci).flatMap(Conv.trans(_, he)).flatMap(Conv.trans(_, cj))
                  ai <- mul(kit, a, i2)
                  aj <- mul(kit, a, j2)
                  k1 <- modCong(kit, n, ai)
                  k2 <- congOfEq(kit, n, mm)
                  k3 <- modCong(kit, n, aj).flatMap(congSym(kit, _))
                  aij <- congChain(kit, k1, k2, k3)
                  ij <- cancel(i2, j2, aij)
                  r <- equalBelow(i2, j2, ij, hi2, hj2)
                } yield r,
              nj =>
                for {
                  cj <- condFalse(kit, pj2, mj2, j2, nj)
                  e <- Conv.sym(ci).flatMap(Conv.trans(_, he)).flatMap(Conv.trans(_, cj))
                  kept <- keeps(i2, yi)
                  pj <- transport(gcdLam, e, kept)
                  f_ <- rules.notElim(nj, pj)
                  r <- rules.falsityElim(targetT, f_)
                } yield r
            )
          } yield r,
        ni =>
          for {
            ci <- condFalse(kit, pi2, mi2, i2, ni)
            r <- split(kit, pj2)(
              yj =>
                for {
                  cj <- condTrue(kit, pj2, mj2, j2, yj)
                  back <- Conv.sym(he)
                  e <- Conv.sym(cj).flatMap(Conv.trans(_, back)).flatMap(Conv.trans(_, ci))
                  kept <- keeps(j2, yj)
                  pi_ <- transport(gcdLam, e, kept)
                  f_ <- rules.notElim(ni, pi_)
                  r <- rules.falsityElim(targetT, f_)
                } yield r,
              nj =>
                for {
                  cj <- condFalse(kit, pj2, mj2, j2, nj)
                  r <- Conv.sym(ci).flatMap(Conv.trans(_, he)).flatMap(Conv.trans(_, cj))
                } yield r
            )
          } yield r
      )
      injective <- dischAll(kit, List(i2LtT, j2LtT, heT), injInner).flatMap(rules.gen(j2, _)).flatMap(rules.gen(i2, _))
      _ <- if (injective.conclusion == injT) Right(()) else Left(NotOfForm("the injectivity", injective.conclusion))

      // Surjectivity.
      j3 = fresh("j", nm, hn, ha, hb)
      ontoBody <- open(kit, ontoT, j3)
      p_ob <- imp(kit, ontoBody)
      (j3LtT, wanted) = p_ob
      wantedPred <- kit.logic.destExistsPredicate(wanted).toRight(NotOfForm("an existential", wanted))
      hj3 <- assume(j3LtT)
      pj3 <- coprimeAt(j3)
      ontoInner <- split(kit, pj3)(
        yj =>
          for {
            bj <- mul(kit, b, j3)
            w <- kit.at("\\n:num. \\x:num. NUM_MOD x n", n, bj)
            wLt <- kit.use("NUM_MOD_LT", List(bj, n), hn)
            gbj <- kit.use("NUM_GCD_MUL", List(b, j3, n), hn, bCop, yj)
            wCop <- kit.applyTo(l.gcdMod, List(n, bj), hn, gbj)
            pw <- coprimeAt(w)
            mw <- modAt(w)
            cw <- condTrue(kit, pw, mw, w, wCop)
            aw <- mul(kit, a, w)
            ra <- congRefl(kit, n, a)
            k1 <- modCong(kit, n, bj).flatMap(congSym(kit, _))
            c1 <- congMul(kit, ra, k1) // a * w == a * (b * j)
            abj <- mul(kit, a, bj)
            abJ <- mul(kit, a, b).flatMap(mul(kit, _, j3))
            c2 <- congBy(kit, n, abj, abJ)
            rj <- congRefl(kit, n, j3)
            c3 <- congMul(kit, hb, rj) // (a b) j == 1 * j
            oj <- mul(kit, o, j3)
            c4 <- congBy(kit, n, oj, j3)
            awj <- congChain(kit, c1, c2, c3, c4)
            mwj <- kit.use("NUM_MOD_OF_CONG", List(n, aw, j3), awj, hj3)
            sw <- Conv.trans(cw, mwj)
            both <- rules.conjIntro(wLt, sw)
            r <- rules.existsIntro(wantedPred, w, both)
          } yield r,
        nj =>
          for {
            mj <- modAt(j3)
            cj <- condFalse(kit, pj3, mj, j3, nj)
            both <- rules.conjIntro(hj3, cj)
            r <- rules.existsIntro(wantedPred, j3, both)
          } yield r
      )
      onto <- rules.disch(j3LtT, ontoInner).flatMap(rules.gen(j3, _))
      _ <- if (onto.conclusion == ontoT) Right(()) else Left(NotOfForm("the surjectivity", onto.conclusion))

      permEq <- rules.mp(permAt, range).flatMap(rules.mp(_, injective)).flatMap(rules.mp(_, onto))
      p_pe <- sides(permEq.conclusion)
      (permL, bigP) = p_pe
      p_pl <- productOf(permL)
      (rsLam, _) = p_pl

      // Termwise: r (s k) == c k * r k.
      cLam <- kit.at("\\n:num. \\a:num. \\k:num. COND (NUM_GCD k n = SUC 0) a (SUC 0)", n, a)
      gLam <- kit.at("\\n:num. \\a:num. \\k:num. COND (NUM_GCD k n = SUC 0) a (SUC 0) * COND (NUM_GCD k n = SUC 0) k (SUC 0)", n, a)
      congAt <- rules.specAll(l.prodCongMod, List(n, rsLam, gLam, n)).flatMap(Limit.normalised)
      p_ca <- imp(kit, congAt.conclusion)
      (termwiseT, _) = p_ca
      k = fresh("k", nm, hn, ha, hb)
      twBody <- open(kit, termwiseT, k)
      p_tw <- imp(kit, twBody)
      (kLtT, twTarget) = p_tw
      twParts <- congParts(twTarget)
      (_, rsk, gk) = twParts
      pk <- coprimeAt(k)
      sk <- sAt(k)
      mk <- modAt(k)
      twInner <- split(kit, pk)(
        yk =>
          for {
            cs <- condTrue(kit, pk, mk, k, yk) // s k = MOD (a k) n
            moved <- cong(rLam, cs)
            kept <- keeps(k, yk)
            cm <- condTrue(kit, kept.conclusion, mk, o, kept)
            rsEq <- Conv.trans(moved, cm) // r (s k) = MOD (a k) n
            ca <- condTrue(kit, pk, a, o, yk)
            ck <- condTrue(kit, pk, k, o, yk)
            ak <- mul(kit, a, k)
            gEq <- equate(kit, gk, ak, Vector(ca, ck), Vector.empty)
            t1 <- congOfEq(kit, n, rsEq)
            t2 <- modCong(kit, n, ak).flatMap(congSym(kit, _))
            t3 <- Conv.sym(gEq).flatMap(congOfEq(kit, n, _))
            r <- congChain(kit, t1, t2, t3)
          } yield r,
        nk =>
          for {
            cs <- condFalse(kit, pk, mk, k, nk) // s k = k
            moved <- cong(rLam, cs)
            cr <- condFalse(kit, pk, k, o, nk)
            rsEq <- Conv.trans(moved, cr) // r (s k) = 1
            ca <- condFalse(kit, pk, a, o, nk)
            ck <- condFalse(kit, pk, k, o, nk)
            gEq <- equate(kit, gk, o, Vector(ca, ck), Vector.empty)
            eq <- Conv.sym(gEq).flatMap(Conv.trans(rsEq, _))
            r <- congOfEq(kit, n, eq)
          } yield r
      )
      termwise <- rules.disch(kLtT, twInner).flatMap(rules.gen(k, _))
      _ <- if (termwise.conclusion == termwiseT) Right(()) else Left(NotOfForm("the termwise congruence", termwise.conclusion))
      c0 <- rules.mp(congAt, termwise) // prod rs == prod g

      splitProd <- kit.applyTo(l.prodMul, List(cLam, rLam, n))
      pLam <- kit.at("\\n:num. \\k:num. NUM_GCD k n = SUC 0", n)
      power <- kit.applyTo(l.prodCondPow, List(pLam, a, n))
      p_pw <- sides(power.conclusion)
      (_, aT) = p_pw
      timesP <- kit.at("\\p:num. \\x:num. x * p", bigP)
      movedPow <- cong(timesP, power)
      gEqPow <- Conv.trans(splitProd, movedPow) // prod g = a^T * P
      m1 <- Conv.sym(permEq).flatMap(congOfEq(kit, n, _))
      m3 <- congOfEq(kit, n, gEqPow)
      main <- congChain(kit, m1, c0, m3) // P == a^T * P

      // P is a unit.
      u = fresh("u", nm, hn, ha, hb)
      uLtT <- lt(u, n)
      hu <- assume(uLtT)
      pu <- coprimeAt(u)
      ru <- instantiate(rLam, u)
      copInner <- split(kit, pu)(
        yu =>
          for {
            c <- condTrue(kit, pu, u, o, yu)
            back <- Conv.sym(c)
            r <- transport(gcdLam, back, yu)
          } yield r,
        nu =>
          for {
            c <- condFalse(kit, pu, u, o, nu)
            back <- Conv.sym(c)
            nz <- nonZero(kit, n, hn)
            oneZero <- eqTerm(o, zr).flatMap(kit.logic.mkNot)
            cond <- rules.disjIntro2(oneZero, nz)
            dl <- kit.use("NUM_GCD_DIVIDES_LEFT", List(o, n), cond)
            g1 <- kit.at("\\n:num. NUM_GCD (SUC 0) n", n)
            oneG <- kit.use("NUM_DIVIDES_ONE", List(g1), dl)
            r <- transport(gcdLam, back, oneG)
          } yield r
      )
      allCop <- rules.disch(uLtT, copInner).flatMap(rules.gen(u, _))
      pCop <- kit.use("NUM_GCD_PROD", List(rLam, n, n), hn, allCop)
      qEx <- kit.applyTo(l.inverse, List(n, bigP), hn, pCop)
      qPred <- kit.logic.destExistsPredicate(qEx.conclusion).toRight(NotOfForm("an existential", qEx.conclusion))
      q = fresh("q", nm, hn, ha, hb, main)
      hqT <- instantiate(qPred, q)
      hq <- assume(hqT)

      // a^T == a^T * (P q) == (a^T P) q == P q == 1.
      aT1 <- mul(kit, aT, o)
      pq <- mul(kit, bigP, q)
      aTpq <- mul(kit, aT, pq)
      aTPq <- mul(kit, aT, bigP).flatMap(mul(kit, _, q))
      f1 <- congBy(kit, n, aT, aT1)
      raT <- congRefl(kit, n, aT)
      f2 <- congSym(kit, hq).flatMap(congMul(kit, raT, _))
      f3 <- congBy(kit, n, aTpq, aTPq)
      rq <- congRefl(kit, n, q)
      f4 <- congSym(kit, main).flatMap(congMul(kit, _, rq))
      done <- congChain(kit, f1, f2, f3, f4, hq)

      rq_ <- rules.existsElim(qEx, q, done)
      rb <- rules.existsElim(invEx, b, rq_)
      unfolded <- Conv.unfold(totient, List(n))
      folded <- Conv.sym(unfolded)
      named <- Limit.rewriteInProposition(folded, rb)
      out <- dischAll(kit, List(hnT, haT), named)
      general <- rules.genAll(out, List(n, a))
    } yield general
  }



  /** The nine facts this derives, under the names `Primes` publishes them by. */
  def derive(kit: Kit, totient: Kernel.Thm): R[Map[String, Kernel.Thm]] =
    for {
      pt <- point(kit)
      perm <- permute(kit, pt)
      inv <- inverse(kit)
      gm <- gcdMod(kit)
      uc <- unitCoprime(kit)
      cm <- prodCongMod(kit)
      pm <- prodMul(kit)
      cp <- prodCondPow(kit)
      e <- euler(kit, Lemmas(perm, inv, gm, uc, cm, pm, cp), totient)
    } yield Map(
      Primes.ProdPoint -> pt,
      Primes.ProdPermute -> perm,
      Primes.Inverse -> inv,
      Primes.GcdMod -> gm,
      Primes.UnitCoprime -> uc,
      Primes.ProdCongMod -> cm,
      Primes.ProdMul -> pm,
      Primes.ProdCondPow -> cp,
      Primes.Euler -> e
    )
}
