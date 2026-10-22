package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The inversion of the finite Fourier transform over the roots of unity, and its reading in cosines
 * and sines: what `Complex` publishes as `COMPLEX_DFT_INVERSION` and `REAL_DFT_INVERSION`.
 *
 * Not a development: it declares nothing, and stands to `Complex` as `Fundamental` does.
 * `docs/adr/0062` is the decision, and the statement is the textbook's with the modulus written out:
 *
 * {{{
 *   COMPLEX_DFT_INVERSION
 *     !f m n. 0 < m ==> f (n mod m) = (1/m) sum[h < m] (sum[r < m] f r * cnj(w)^(h r)) * w^(h n),
 *     w = cis (2 pi / m)
 * }}}
 *
 * `f` is read at `NUM_MOD n m` rather than assumed periodic, so the theorem holds of every `f` and
 * says that only its values below `m` matter; a periodic `f` is the case where `f n` is that value.
 * `0 < m` is needed rather than cautious: at `m = 0` the right side is `inv 0` times an empty sum,
 * which is zero, and `ComplexSpec` shows the left side need not be.
 *
 * == The route ==
 *
 * At `m = SUC p` the conjugate of the root is its `p`-th power, because both are its inverse
 * (`CNJ_ROOT`), so `cnj(w)^(h r) * w^(h n)` is `w^((n + p r) h)` and the whole of the right side is
 * one double sum of powers of `w`. Exchanging the two sums, which the complex sums get here with
 * their linearity, leaves for each `r` the sum over `h` that `ROOTS_OF_UNITY_SUM_DIVIDES` and
 * `ROOTS_OF_UNITY_SUM_NOT_DIVIDES` evaluate: `m` when `m` divides `n + p r` and zero else. Below
 * `m`, it divides exactly when `r` is the residue of `n`, by the uniqueness of quotient and
 * remainder and nothing else, so the outer sum keeps one term, `m * f (n mod m)`.
 *
 * The real reading is the real part of the complex one at `complex_of_real o f`: the analysis
 * coefficient splits into the sum against the cosine and minus the sum against the sine, and the
 * synthesis multiplies them back with the cosine and the sine of `2 pi s n / m`. That is form (C)
 * of `collatz@8b991e5` `documents/02-closed-form-formula.md` section 2.3, with the coefficients
 * the transforms they are said there to be.
 *
 * == What it spends ==
 *
 * Choice, eta and infinity, which is what the complex numbers rest on. The sums over the complex
 * numbers are proved here by induction, part by part through the driver; the ones over the reals
 * are `Series`'s.
 */
private[theories] object FiniteFourier {

  type R[A] = Either[LogicError, A]

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private def Complexes: Type = Complex.Complexes
  private def Terms: Type = Type.fun(Numbers, Complexes)

  /** What `Complex` publishes from here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    "COMPLEX_DFT_INVERSION" ->
      ("!f:num->complex. !m:num. !n:num. 0 < m ==> f (NUM_MOD n m) = complex_of_real (inv (real_of_num m)) * " +
        "complex_sum (\\h:num. complex_sum (\\r:num. f r * complex_pow (cnj (cis (2 * pi / real_of_num m))) (h * r)) m * " +
        "complex_pow (cis (2 * pi / real_of_num m)) (h * n)) m"),
    "REAL_DFT_INVERSION" ->
      ("!f:num->real. !m:num. !n:num. 0 < m ==> f (NUM_MOD n m) = " +
        s"Sum (\\s:num. Sum (\\r:num. f r * cos (${angle("s * r", "m")})) m / real_of_num m * cos (${angle("s * n", "m")}) + " +
        s"Sum (\\r:num. f r * sin (${angle("s * r", "m")})) m / real_of_num m * sin (${angle("s * n", "m")})) m")
  )

  private lazy val StatementsMap: Map[String, String] = Statements.toMap

  private val Order: Vector[(String, Proofs => R[Kernel.Thm])] = Vector(
    "CSUM_RMUL" -> (_.sumRmul),
    "CSUM_LMUL" -> (_.sumLmul),
    "CSUM_ADD" -> (_.sumAdd),
    "CSUM_SWAP" -> (_.sumSwap),
    "CSUM_CONG_BELOW" -> (_.sumCongBelow),
    "CSUM_DELTA_COND" -> (_.sumDeltaCond),
    "CSUM_DELTA" -> (_.sumDelta),
    "CNJ_ROOT" -> (_.cnjRoot),
    "ROOT_EXPONENT" -> (_.rootExponent),
    "DIVIDES_AT_RESIDUE" -> (_.dividesAtResidue),
    "RESIDUE_OF_DIVIDES" -> (_.residueOfDivides),
    "ORTHOGONAL_AT" -> (_.orthogonalAt),
    "INVERSION_AT_SUCCESSOR" -> (_.inversionAtSuccessor),
    "COMPLEX_DFT_INVERSION" -> (_.complexInversion),
    "CNJ_POW" -> (_.cnjPow),
    "RE_SCALE" -> (_.reScale),
    "RE_ROTATE" -> (_.reRotate),
    "RE_CONJ_TERM" -> (_.conjTerm("Re", "a * cos")),
    "IM_CONJ_TERM" -> (_.conjTerm("Im", "(0 - 1) * (a * sin")),
    "REAL_DFT_INVERSION" -> (_.realInversion)
  )

  /** The angle of the `k`-th power of the root of order `m`, as the source writes it. */
  private def angle(k: String, modulus: String): String = s"2 * pi * real_of_num ($k) / real_of_num ($modulus)"

  /** The root of unity of order `SUC p`, which every statement at a successor is about. */
  private val W: String = "cis (2 * pi / real_of_num (SUC (p:num)))"

  /** `sum[h < M] (sum[r < M] f r * cnj(w)^(h r)) * w^(h n)` at `M` and `w` given as text. */
  private def synthesis(modulus: String, root: String): String =
    s"complex_sum (\\h:num. complex_sum (\\r:num. (f:num->complex) r * complex_pow (cnj ($root)) (h * r)) ($modulus) * " +
      s"complex_pow ($root) (h * (n:num))) ($modulus)"

  /** The facts [[Statements]] names, derived with `kit`, the complex numbers' own facts in `held`. */
  def prove(kit: ComplexKit, semiring: Semiring, held: Map[String, Kernel.Thm]): R[Map[String, Kernel.Thm]] =
    ComplexKit.derive(Order, Statements, held)(known => new Proofs(kit, semiring, known))

  private def atComplex(thm: Kernel.Thm): Kernel.Thm = Kernel.instType(Map(Classical.TypeVariable -> Complexes), thm)

  private final class Proofs(val kit: ComplexKit, semiring: Semiring, known: Map[String, Kernel.Thm]) {
    import kit.*

    def k(name: String): Kernel.Thm = known(name)

    private val f = Term.variable("f", Terms)
    private val g = Term.variable("g", Terms)
    private val c = Term.variable("c", Complexes)
    private val m = Term.variable("m", Numbers)
    private val n = Term.variable("n", Numbers)
    private val ff = Term.variable("f", Type.fun(Numbers, Terms))

    def sumSuc: Kernel.Thm = k("COMPLEX_SUM_SUC")
    def sumZero: Kernel.Thm = k("COMPLEX_SUM_ZERO")

    /** `sum (\r. f r * c) n = sum f n * c`. */
    def sumRmul: R[Kernel.Thm] =
      for {
        body <- prop("complex_sum (\\r:num. (f:num->complex) r * (c:complex)) (n:num) = complex_sum f n * c")
        proved <- induct(n, body)(
          base => driver.using(sumZero).identity(base),
          (_, hyp, goal) => driver.using(sumSuc).from(hyp).flatMap(_.identity(goal))
        )
        out <- gen(proved, f, c)
      } yield out

    /** `sum (\r. c * f r) n = c * sum f n`. */
    def sumLmul: R[Kernel.Thm] =
      for {
        body <- prop("complex_sum (\\r:num. (c:complex) * (f:num->complex) r) (n:num) = c * complex_sum f n")
        proved <- induct(n, body)(
          base => driver.using(sumZero).identity(base),
          (_, hyp, goal) => driver.using(sumSuc).from(hyp).flatMap(_.identity(goal))
        )
        out <- gen(proved, f, c)
      } yield out

    /** `sum (\r. f r + g r) n = sum f n + sum g n`. */
    def sumAdd: R[Kernel.Thm] =
      for {
        body <- prop("complex_sum (\\r:num. (f:num->complex) r + (g:num->complex) r) (n:num) = complex_sum f n + complex_sum g n")
        proved <- induct(n, body)(
          base => driver.using(sumZero).identity(base),
          (_, hyp, goal) => driver.using(sumSuc).from(hyp).flatMap(_.identity(goal))
        )
        out <- gen(proved, f, g)
      } yield out

    /** Two sums agree when their terms agree below the bound. */
    def sumCongBelow: R[Kernel.Thm] =
      for {
        body <- prop("(!r:num. r < (n:num) ==> (f:num->complex) r = (g:num->complex) r) ==> complex_sum f n = complex_sum g n")
        ltSuc <- fact("NUM_LT_SUC")
        ltTrans <- fact("NUM_LT_TRANS")
        proved <- induct(n, body)(
          base => underHyps(base)((_, goal) => driver.using(sumZero).identity(goal)),
          (kk, hyp, goal) => underHyps(goal) { (hs, conclusion) =>
            val K = kk.name
            val r = Term.variable("r", Numbers)
            for {
              below <- for {
                rK <- prop(s"(r:num) < $K")
                assumed <- LogicError.lift(Kernel.assume(rK))
                step <- at(ltSuc, s"$K < SUC $K")
                both <- conj(assumed, step)
                rSuc <- at(ltTrans, s"(r:num) < $K /\\ $K < SUC $K ==> r < SUC $K").flatMap(mp(_, both))
                eq <- spec(hs(0), r).flatMap(mp(_, rSuc))
                out <- rules.disch(rK, eq).flatMap(gen(_, r))
              } yield out
              ih <- mp(hyp, below)
              top <- at(ltSuc, s"$K < SUC $K").flatMap(t => specR(Right(hs(0)), nm(K)).flatMap(mp(_, t)))
              out <- driver.using(sumSuc).from(ih, top).flatMap(_.identity(conclusion))
            } yield out
          }
        )
        out <- gen(proved, f, g)
      } yield out

    /** A sum whose terms vanish but at `k` is `g k` when `k` is below the bound, and zero else. */
    def sumDeltaCond: R[Kernel.Thm] = {
      val kv = Term.variable("k", Numbers)
      for {
        body <- prop("complex_sum (\\r:num. COND (r = (k:num)) ((g:num->complex) r) (complex_of_real 0)) (n:num) = " +
          "COND (k < n) (g k) (complex_of_real 0)")
        condTrue <- fact("COND_TRUE").map(atComplex)
        condFalse <- fact("COND_FALSE").map(atComplex)
        notLtZero <- fact("NUM_NOT_LT_ZERO")
        ltIrrefl <- fact("NUM_LT_IRREFL")
        ltSuc <- fact("NUM_LT_SUC")
        ltTrans <- fact("NUM_LT_TRANS")
        ltSucCases <- fact("NUM_LT_SUC_CASES")
        zero <- cx("complex_of_real 0")
        gk <- cx("(g:num->complex) (k:num)")
        proved <- induct(n, body)(
          base => for {
            p <- prop("(k:num) < 0")
            no <- spec(notLtZero, kv)
            c0 <- spec(condFalse, p, gk, zero).flatMap(mp(_, no))
            out <- driver.using(sumZero, c0).identity(base)
          } yield out,
          (kk, hyp, goal) => {
            val K = kk.name
            for {
              gK <- cx(s"(g:num->complex) $K")
              kLt <- prop(s"(k:num) < $K")
              kLtSuc <- prop(s"(k:num) < SUC $K")
              same <- prop(s"$K = (k:num)")
              opened <- at(sumSuc, s"complex_sum (\\r:num. COND (r = (k:num)) ((g:num->complex) r) (complex_of_real 0)) (SUC $K) = " +
                s"complex_sum (\\r:num. COND (r = k) (g r) (complex_of_real 0)) $K + COND ($K = k) (g $K) (complex_of_real 0)")
              withIh <- rw(hyp, opened)
              out <- cases(s"(k:num) < $K")(
                yes => for {
                  c1 <- spec(condTrue, kLt, gk, zero).flatMap(mp(_, yes))
                  notSame <- for {
                    e <- LogicError.lift(Kernel.assume(same))
                    moved <- rw(e, yes)
                    absurd <- spec(ltIrrefl, kv).flatMap(rules.notElim(_, moved))
                    out <- rules.notIntro(same, absurd)
                  } yield out
                  c2 <- spec(condFalse, same, gK, zero).flatMap(mp(_, notSame))
                  step <- at(ltSuc, s"$K < SUC $K")
                  lt <- conj(yes, step).flatMap(b => at(ltTrans, s"(k:num) < $K /\\ $K < SUC $K ==> k < SUC $K").flatMap(mp(_, b)))
                  c3 <- spec(condTrue, kLtSuc, gk, zero).flatMap(mp(_, lt))
                  out <- driver.using(c1, c2, c3).from(withIh).flatMap(_.identity(goal))
                } yield out,
                no => for {
                  c1 <- spec(condFalse, kLt, gk, zero).flatMap(mp(_, no))
                  out <- cases(s"$K = (k:num)")(
                    eq => for {
                      c2 <- spec(condTrue, same, gK, zero).flatMap(mp(_, eq))
                      at0 <- at(ltSuc, s"$K < SUC $K")
                      lt <- at0.conclusion match {
                        case App(App(less, _), bound) =>
                          for {
                            moved <- Conv.apTerm(less, eq).flatMap(Conv.apThm(_, bound))
                            out <- LogicError.lift(Kernel.eqMp(moved, at0))
                          } yield out
                        case other => Left(NotOfForm("a comparison", other))
                      }
                      c3 <- spec(condTrue, kLtSuc, gk, zero).flatMap(mp(_, lt))
                      gEq <- Conv.apTerm(Term.variable("g", Terms), eq)
                      out <- driver.using(c1, c2, c3).from(withIh, gEq).flatMap(_.identity(goal))
                    } yield out,
                    ne => for {
                      c2 <- spec(condFalse, same, gK, zero).flatMap(mp(_, ne))
                      notLt <- for {
                        h <- LogicError.lift(Kernel.assume(kLtSuc))
                        split <- at(ltSucCases, s"(k:num) < SUC $K ==> k < $K \\/ k = $K").flatMap(mp(_, h))
                        first <- prop(s"(k:num) < $K")
                        second <- prop(s"(k:num) = $K")
                        f1 <- LogicError.lift(Kernel.assume(first)).flatMap(a => rules.notElim(no, a))
                        f2 <- LogicError.lift(Kernel.assume(second)).flatMap(a => Conv.sym(a)).flatMap(a => rules.notElim(ne, a))
                        bottom <- rules.disjElim(split, f1, f2)
                        out <- rules.notIntro(kLtSuc, bottom)
                      } yield out
                      c3 <- spec(condFalse, kLtSuc, gk, zero).flatMap(mp(_, notLt))
                      out <- driver.using(c1, c2, c3).from(withIh).flatMap(_.identity(goal))
                    } yield out
                  )
                } yield out
              )
            } yield out
          }
        )
        out <- gen(proved, g, kv)
      } yield out
    }

    /** The same below the bound: the sum is the one term that does not vanish. */
    def sumDelta: R[Kernel.Thm] = {
      val kv = Term.variable("k", Numbers)
      for {
        condTrue <- fact("COND_TRUE").map(atComplex)
        hT <- prop("(k:num) < (n:num)")
        h <- LogicError.lift(Kernel.assume(hT))
        general <- at(k("CSUM_DELTA_COND"), "complex_sum (\\r:num. COND (r = (k:num)) ((g:num->complex) r) (complex_of_real 0)) (n:num) = " +
          "COND (k < n) (g k) (complex_of_real 0)")
        gk <- cx("(g:num->complex) (k:num)")
        zero <- cx("complex_of_real 0")
        c <- spec(condTrue, hT, gk, zero).flatMap(mp(_, h))
        eq <- Conv.trans(general, c)
        out <- rules.disch(hT, eq).flatMap(gen(_, g, kv, n))
      } yield out
    }

    private val p = Term.variable("p", Numbers)
    private val r = Term.variable("r", Numbers)
    private val h = Term.variable("h", Numbers)
    private val Residue = "NUM_MOD (n:num) (SUC (p:num))"
    private val Quotient = "NUM_DIV (n:num) (SUC (p:num))"

    /** The conjugate of the root is its `p`-th power: both are its inverse, since its `SUC p`-th power is one. */
    def cnjRoot: R[Kernel.Thm] =
      for {
        positive <- at(fact("NUM_ZERO_LT_SUC"), "0 < SUC (p:num)")
        unity <- at(k("ROOT_OF_UNITY"), s"0 < SUC (p:num) ==> complex_pow ($W) (SUC p) = complex_of_real 1").flatMap(mp(_, positive))
        opened <- at(k("COMPLEX_POW_SUC"), s"complex_pow ($W) (SUC (p:num)) = ($W) * complex_pow ($W) p")
        product <- Conv.sym(opened).flatMap(Conv.trans(_, unity))
        squared <- at(k("COMPLEX_NORM_SQUARED"), s"complex_norm ($W) * complex_norm ($W) = complex_norm_sq ($W)")
        unit <- at(k("COMPLEX_NORM_CIS"), "complex_norm (cis (2 * pi / real_of_num (SUC (p:num)))) = 1")
        normSq <- rw(unit, squared).flatMap(s => lin(Seq(s), s"complex_norm_sq ($W) = 1"))
        withCnj <- at(k("COMPLEX_MUL_CNJ"), s"($W) * cnj ($W) = complex_of_real (complex_norm_sq ($W))").flatMap(rw(normSq, _))
        regrouped <- identity(s"cnj ($W) * (($W) * complex_pow ($W) (p:num)) = (($W) * cnj ($W)) * complex_pow ($W) p")
        reduced <- rw(product, regrouped).flatMap(rw(withCnj, _))
        out <- driver.from(reduced).flatMap(_.identity(s"cnj ($W) = complex_pow ($W) (p:num)"))
        general <- gen(out, p)
      } yield general

    /** `cnj(w)^(h r) * w^(h n) = w^((n + p r) h)`: the exponent the orthogonality is read at. */
    def rootExponent: R[Kernel.Thm] =
      for {
        conj0 <- at(k("CNJ_ROOT"), s"cnj ($W) = complex_pow ($W) (p:num)")
        nested <- at(k("COMPLEX_POW_MUL"), s"complex_pow ($W) ((p:num) * ((h:num) * (r:num))) = complex_pow (complex_pow ($W) p) (h * r)")
          .flatMap(Conv.sym)
        added <- at(k("COMPLEX_POW_ADD"),
          s"complex_pow ($W) ((p:num) * ((h:num) * (r:num)) + h * (n:num)) = complex_pow ($W) (p * (h * r)) * complex_pow ($W) (h * n)")
          .flatMap(Conv.sym)
        exponent <- prop("(p:num) * ((h:num) * (r:num)) + h * (n:num) = (n + p * r) * h").flatMap(semiring.prove)
        root <- cx(W)
        power <- LogicError.lift(theory.constant(Complex.Power, Type.fun(Complexes, Type.fun(Numbers, Complexes))))
        rootPower <- LogicError.lift(Term.app(power, root))
        goal <- prop(s"complex_pow (cnj ($W)) ((h:num) * (r:num)) * complex_pow ($W) (h * (n:num)) = complex_pow ($W) ((n + p * r) * h)")
        moved <- rewriting(Seq(conj0, nested, added), goal)(_ => Conv.apTerm(rootPower, exponent))
        out <- gen(moved, h, r, n, p)
      } yield out

    /** At the residue of `n`, `SUC p` divides `n + p r`. */
    def dividesAtResidue: R[Kernel.Thm] =
      for {
        hT <- prop(s"(r:num) = $Residue")
        hyp <- LogicError.lift(Kernel.assume(hT))
        division <- at(fact("NUM_DIV_MOD"), s"SUC (p:num) * $Quotient + $Residue = (n:num)")
        atR <- Conv.sym(hyp).flatMap(rw(_, division))
        regrouped <- prop(s"SUC (p:num) * $Quotient + (r:num) + p * r = SUC p * ($Quotient + r)").flatMap(semiring.prove)
        multiple <- rw(atR, regrouped)
        out <- at(fact("NUM_DIVIDES_INTRO"),
          s"(n:num) + (p:num) * (r:num) = SUC p * ($Quotient + r) ==> NUM_DIVIDES (SUC p) (n + p * r)").flatMap(mp(_, multiple))
        general <- rules.disch(hT, out).flatMap(gen(_, p, n, r))
      } yield general

    /** Below the modulus, the only `r` for which `SUC p` divides `n + p r` is the residue of `n`. */
    def residueOfDivides: R[Kernel.Thm] =
      for {
        belowT <- prop("(r:num) < SUC (p:num)")
        below <- LogicError.lift(Kernel.assume(belowT))
        dT <- prop("NUM_DIVIDES (SUC (p:num)) ((n:num) + p * (r:num))")
        d <- LogicError.lift(Kernel.assume(dT))
        ex <- at(fact("NUM_DIVIDES_ELIM"),
          "NUM_DIVIDES (SUC (p:num)) ((n:num) + p * (r:num)) ==> ?k:num. n + p * r = SUC p * k").flatMap(mp(_, d))
        positive <- at(fact("NUM_ZERO_LT_SUC"), "0 < SUC (p:num)")
        residueBelow <- at(fact("NUM_MOD_LT"), s"0 < SUC (p:num) ==> $Residue < SUC p").flatMap(mp(_, positive))
        division <- at(fact("NUM_DIV_MOD"), s"SUC (p:num) * $Quotient + $Residue = (n:num)")
        eq <- choose(ex, "k") { (kv, multiple) =>
          val K = kv.name
          for {
            regrouped <- prop(s"SUC (p:num) * ($Quotient + (r:num)) + $Residue = SUC p * $Quotient + $Residue + p * r + r")
              .flatMap(semiring.prove)
            viaN <- rw(division, regrouped)
            viaK <- rw(multiple, viaN)
            both <- conjs(viaK, residueBelow, below)
            unique <- at(fact("NUM_DIVISION_UNIQUE"),
              s"SUC (p:num) * ($Quotient + (r:num)) + $Residue = SUC p * $K + r /\\ $Residue < SUC p /\\ r < SUC p ==> " +
                s"$Quotient + r = $K /\\ $Residue = r").flatMap(mp(_, both))
            same <- rules.conjElim2(unique).flatMap(Conv.sym)
          } yield same
        }
        out <- rules.disch(dT, eq).flatMap(rules.disch(belowT, _)).flatMap(gen(_, p, n, r))
      } yield out

    /** `f r` times the sum over the roots at `r`'s exponent: the delta at the residue of `n`. */
    def orthogonalAt: R[Kernel.Thm] = {
      val sumAt = s"complex_sum (\\h:num. complex_pow ($W) (((n:num) + p * (r:num)) * h)) (SUC p)"
      val modulus = "complex_of_real (real_of_num (SUC (p:num)))"
      for {
        belowT <- prop("(r:num) < SUC (p:num)")
        below <- LogicError.lift(Kernel.assume(belowT))
        positive <- at(fact("NUM_ZERO_LT_SUC"), "0 < SUC (p:num)")
        condTrue <- fact("COND_TRUE").map(atComplex)
        condFalse <- fact("COND_FALSE").map(atComplex)
        isResidue <- prop(s"(r:num) = $Residue")
        chosen <- cx(s"$modulus * (f:num->complex) (r:num)")
        zero <- cx("complex_of_real 0")
        goal <- prop(s"(f:num->complex) (r:num) * $sumAt = COND (r = $Residue) ($modulus * f r) (complex_of_real 0)")
        out <- cases(s"(r:num) = $Residue")(
          yes => for {
            d <- at(k("DIVIDES_AT_RESIDUE"), s"(r:num) = $Residue ==> NUM_DIVIDES (SUC p) (n + p * r)").flatMap(mp(_, yes))
            both <- conj(positive, d)
            total <- at(k("ROOTS_OF_UNITY_SUM_DIVIDES"),
              s"0 < SUC (p:num) /\\ NUM_DIVIDES (SUC p) ((n:num) + p * (r:num)) ==> $sumAt = $modulus").flatMap(mp(_, both))
            c <- spec(condTrue, isResidue, chosen, zero).flatMap(mp(_, yes))
            out <- driver.using(total, c).identity(goal)
          } yield out,
          no => for {
            notD <- for {
              dT <- prop("NUM_DIVIDES (SUC (p:num)) ((n:num) + p * (r:num))")
              d <- LogicError.lift(Kernel.assume(dT))
              same <- at(k("RESIDUE_OF_DIVIDES"),
                s"(r:num) < SUC (p:num) ==> NUM_DIVIDES (SUC p) ((n:num) + p * r) ==> r = $Residue").flatMap(mp(_, below, d))
              absurd <- rules.notElim(no, same)
              out <- rules.notIntro(dT, absurd)
            } yield out
            both <- conj(positive, notD)
            total <- at(k("ROOTS_OF_UNITY_SUM_NOT_DIVIDES"),
              s"0 < SUC (p:num) /\\ ~NUM_DIVIDES (SUC p) ((n:num) + p * (r:num)) ==> $sumAt = complex_of_real 0").flatMap(mp(_, both))
            c <- spec(condFalse, isResidue, chosen, zero).flatMap(mp(_, no))
            out <- driver.using(total, c).identity(goal)
          } yield out
        )
        general <- rules.disch(belowT, out).flatMap(gen(_, f, p, n, r))
      } yield general
    }

    /** `SUC p * f (n mod SUC p)` is the synthesis of its analysis, at the root of order `SUC p`. */
    def inversionAtSuccessor: R[Kernel.Thm] = {
      val M = "SUC (p:num)"
      val term = s"(f:num->complex) r * complex_pow (cnj ($W)) (h * r)"
      val power = s"complex_pow ($W) (h * (n:num))"
      val modulus = s"complex_of_real (real_of_num ($M))"
      val atExponent = s"complex_pow ($W) ((n + p * r) * h)"
      for {
        pulled <- at(k("CSUM_RMUL"),
          s"complex_sum (\\r:num. $term * $power) ($M) = complex_sum (\\r:num. $term) ($M) * $power").flatMap(Conv.sym)
        inside <- nm(M).flatMap(sumCong(h, pulled, _))
        swapped <- at(k("CSUM_SWAP"),
          s"complex_sum (\\h:num. complex_sum (\\r:num. $term * $power) ($M)) ($M) = " +
            s"complex_sum (\\r:num. complex_sum (\\h:num. $term * $power) ($M)) ($M)")
        perTerm <- for {
          regrouped <- identity(s"$term * $power = f r * (complex_pow (cnj ($W)) (h * r) * $power)")
          exponent <- at(k("ROOT_EXPONENT"), s"complex_pow (cnj ($W)) ((h:num) * (r:num)) * $power = $atExponent")
          moved <- rw(exponent, regrouped)
          summed <- nm(M).flatMap(sumCong(h, moved, _))
          factored <- at(k("CSUM_LMUL"),
            s"complex_sum (\\h:num. (f:num->complex) r * $atExponent) ($M) = f r * complex_sum (\\h:num. $atExponent) ($M)")
          out <- Conv.trans(summed, factored)
        } yield out
        delta <- nm(M).flatMap(sumCong(r, perTerm, _))
        orthogonal <- at(k("ORTHOGONAL_AT"),
          s"(r:num) < $M ==> (f:num->complex) r * complex_sum (\\h:num. $atExponent) ($M) = " +
            s"COND (r = $Residue) ($modulus * f r) (complex_of_real 0)").flatMap(gen(_, r))
        collapsed <- at(k("CSUM_CONG_BELOW"),
          s"(!r:num. r < $M ==> (f:num->complex) r * complex_sum (\\h:num. $atExponent) ($M) = " +
            s"COND (r = $Residue) ($modulus * f r) (complex_of_real 0)) ==> " +
            s"complex_sum (\\r:num. f r * complex_sum (\\h:num. $atExponent) ($M)) ($M) = " +
            s"complex_sum (\\r:num. COND (r = $Residue) ($modulus * f r) (complex_of_real 0)) ($M)").flatMap(mp(_, orthogonal))
        positive <- at(fact("NUM_ZERO_LT_SUC"), "0 < SUC (p:num)")
        residueBelow <- at(fact("NUM_MOD_LT"), s"0 < SUC (p:num) ==> $Residue < SUC p").flatMap(mp(_, positive))
        picked <- at(k("CSUM_DELTA"),
          s"$Residue < $M ==> complex_sum (\\r:num. COND (r = $Residue) ($modulus * (f:num->complex) r) (complex_of_real 0)) ($M) = " +
            s"$modulus * f ($Residue)").flatMap(mp(_, residueBelow))
        forward <- trans(inside, swapped, delta, collapsed, picked)
        out <- Conv.sym(forward).flatMap(gen(_, f, p, n))
      } yield out
    }

    /** The inversion at every positive modulus, from the one at a successor. */
    def complexInversion: R[Kernel.Thm] =
      for {
        statement <- prop(StatementsMap("COMPLEX_DFT_INVERSION"))
        stripped <- Logic.stripForall(statement)
        (bound, body) = stripped
        parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
        (hT, goal) = parts
        hyp <- LogicError.lift(Kernel.assume(hT))
        fv <- bound.headOption.toRight(NotOfForm("a claim about a sequence", statement))
        mv <- bound.lift(1).toRight(NotOfForm("a claim about a modulus", statement))
        nv <- bound.lift(2).toRight(NotOfForm("a claim about an index", statement))
        cs <- specR(fact("NUM_CASES"), Right(mv))
        zeroCase <- for {
          eqT <- logic.destDisj(cs.conclusion).map(_._1).toRight(NotOfForm("a disjunction", cs.conclusion))
          e <- LogicError.lift(Kernel.assume(eqT))
          moved <- rw(e, hyp)
          absurd <- nm("0").flatMap(z => specR(fact("NUM_LT_IRREFL"), Right(z))).flatMap(rules.notElim(_, moved))
          out <- rules.falsityElim(goal, absurd)
        } yield out
        sucCase <- for {
          exT <- logic.destDisj(cs.conclusion).map(_._2).toRight(NotOfForm("a disjunction", cs.conclusion))
          ex <- LogicError.lift(Kernel.assume(exT))
          out <- choose(ex, "p") { (pv, mEq) =>
            for {
              scaled <- spec(k("INVERSION_AT_SUCCESSOR"), fv, pv, nv)
              solved <- solve(scaled, pv)
              back <- Conv.sym(mEq).flatMap(rw(_, solved))
            } yield back
          }
        } yield out
        both <- rules.disjElim(cs, zeroCase, sucCase)
        out <- rules.disch(hT, both).flatMap(gen(_, bound*))
      } yield out

    /** `F = inv M * X` from `M * F = X` at `M = SUC p`, which is not zero. */
    private def solve(scaled: Kernel.Thm, pv: FVar): R[Kernel.Thm] = {
      val P = pv.name
      val M = s"real_of_num (SUC $P)"
      for {
        sides <- Term.destEq(scaled.conclusion).toRight(NotOfForm("an equation", scaled.conclusion))
        (left, right) = sides
        value <- left match {
          case App(App(_, _), v) => Right(v)
          case other => Left(NotOfForm("a product", other))
        }
        suc <- at(fact("NUM_REAL_SUC"), s"real_of_num (SUC $P) = real_of_num $P + 1")
        nonneg <- at(fact("NUM_REAL_NONNEG"), s"0 <= real_of_num $P")
        notZero <- for {
          zT <- prop(s"$M = 0")
          z <- LogicError.lift(Kernel.assume(zT))
          absurd <- lin(Seq(z, suc, nonneg), "F")
          out <- rules.notIntro(zT, absurd)
        } yield out
        inverse <- at(fact("MUL_INVERSE"), s"~($M = 0) ==> $M * inv ($M) = 1").flatMap(mp(_, notZero))
        valueVar = Term.variable("v", Complexes)
        grouped <- identity(s"complex_of_real (inv ($M)) * (complex_of_real ($M) * (v:complex)) = complex_of_real ($M * inv ($M)) * v")
        unit <- rw(inverse, grouped)
        one <- identity("complex_of_real 1 * (v:complex) = v")
        chain <- Conv.trans(unit, one).flatMap(Conv.sym)
        atValue <- LogicError.lift(Kernel.inst(Map(valueVar -> value), chain))
        out <- rw(scaled, atValue)
      } yield out
    }

    private val Root = "cis (2 * pi / real_of_num (m:num))"

    /** `real_of_num k * (2 pi / m)`, which is what De Moivre gives, is the source's `2 pi k / m`. */
    private def angleAt: R[Kernel.Thm] =
      prop(s"!k:num. real_of_num k * (2 * pi / real_of_num (m:num)) = ${angle("k", "m")}").flatMap(ring.prove)

    /** The conjugate of a power is the power of the conjugate. */
    def cnjPow: R[Kernel.Thm] = {
      val z = Term.variable("z", Complexes)
      val kv = Term.variable("k", Numbers)
      for {
        body <- prop("complex_pow (cnj (z:complex)) (k:num) = cnj (complex_pow z k)")
        proved <- induct(kv, body)(
          base => driver.using(k("COMPLEX_POW_ZERO")).identity(base),
          (_, hyp, goal) => driver.using(k("COMPLEX_POW_SUC"), k("CNJ_MUL"), hyp).identity(goal)
        )
        out <- gen(proved, z)
      } yield out
    }

    def reScale: R[Kernel.Thm] = identity("!x:real. !z:complex. Re (complex_of_real x * z) = x * Re z")

    /** The real part of `z` turned by the `k`-th power of the root. */
    def reRotate: R[Kernel.Thm] =
      for {
        angles <- angleAt
        out <- identity(s"!z:complex. !k:num. !m:num. Re (z * complex_pow ($Root) k) = " +
          s"Re z * cos (${angle("k", "m")}) - Im z * sin (${angle("k", "m")})", k("DE_MOIVRE"), angles)
      } yield out

    /** A real coefficient times a power of the conjugate root, read in one part. */
    def conjTerm(part: String, value: String): R[Kernel.Thm] =
      for {
        angles <- angleAt
        out <- identity(s"!a:real. !k:num. !m:num. $part (complex_of_real a * complex_pow (cnj ($Root)) k) = " +
          s"$value (${angle("k", "m")})" + (if (value.contains("(a *")) ")" else ""),
          k("CNJ_POW"), k("DE_MOIVRE"), angles)
      } yield out

    /** The real reading: the real part of the inversion at `complex_of_real o f`, the sums brought into the source's form. */
    def realInversion: R[Kernel.Thm] = {
      val fr = Term.variable("f", Type.fun(Numbers, Reals))
      val cosine = s"Sum (\\r:num. (f:num->real) r * cos (${angle("h * r", "m")})) m"
      val sine = s"Sum (\\r:num. f r * sin (${angle("h * r", "m")})) m"
      val negated = s"Sum (\\r:num. (0 - 1) * (f r * sin (${angle("h * r", "m")}))) m"
      val turned = s"$cosine * cos (${angle("h * n", "m")}) - $negated * sin (${angle("h * n", "m")})"
      val read = s"$cosine / real_of_num m * cos (${angle("h * n", "m")}) + $sine / real_of_num m * sin (${angle("h * n", "m")})"
      for {
        hT <- prop("0 < (m:num)")
        hyp <- LogicError.lift(Kernel.assume(hT))
        lifted <- term("\\r:num. complex_of_real ((f:num->real) r)", Terms)
        inverse <- spec(k("COMPLEX_DFT_INVERSION"), lifted, m, n).flatMap(mp(_, hyp))
        re <- LogicError.lift(theory.constant(Complex.RealPart, Type.fun(Complexes, Reals)))
        taken <- Conv.apTerm(re, inverse)
        steps = Seq(k("RE_OF_REAL"), k("RE_SCALE"), k("RE_SUM"), k("RE_ROTATE"), k("RE_SUM"), k("IM_SUM"),
          k("RE_CONJ_TERM"), k("IM_CONJ_TERM"))
        opened <- steps.foldLeft[R[Kernel.Thm]](Right(taken))((acc, e) => acc.flatMap(rw(e, _)).flatMap(beta))
        scale <- fact("SUM_SCALE")
        inside <- at(scale, s"Sum (\\h:num. inv (real_of_num (m:num)) * ($turned)) m = inv (real_of_num m) * Sum (\\h:num. $turned) m")
          .flatMap(Conv.sym)
        negation <- at(scale, s"$negated = (0 - 1) * $sine")
        pointwiseGoal <- prop(s"inv (real_of_num (m:num)) * ($turned) = $read")
        pointwise <- rewriting(Seq(negation), pointwiseGoal)(ring.prove)
        summed <- nm("m:num").flatMap(sumCongReal(h, pointwise, _))
        out <- trans(opened, inside, summed)
        general <- rules.disch(hT, out).flatMap(gen(_, fr, m, n))
      } yield general
    }

    /** `Sum F n = Sum G n` from `F k = G k` at a variable `k` nothing assumes. */
    private def sumCongReal(kv: FVar, pointwise: Kernel.Thm, bound: Term): R[Kernel.Thm] =
      for {
        lambdas <- LogicError.lift(Kernel.abs(kv, pointwise))
        summation <- LogicError.lift(theory.constant(Series.SumName, Type.fun(Type.fun(Numbers, Reals), Type.fun(Numbers, Reals))))
        out <- Conv.apTerm(summation, lambdas).flatMap(Conv.apThm(_, bound))
      } yield out

    /** The two orders of a finite double sum agree. */
    def sumSwap: R[Kernel.Thm] =
      for {
        body <- prop("complex_sum (\\h:num. complex_sum ((f:num->num->complex) h) (n:num)) (m:num) = " +
          "complex_sum (\\r:num. complex_sum (\\h:num. f h r) m) n")
        zeros <- fact("SUM_OF_ZERO")
        proved <- induct(m, body)(
          base => driver.using(sumZero, zeros).identity(base),
          (kk, hyp, goal) => {
            val K = kk.name
            val r = Term.variable("r", Numbers)
            for {
              opened <- at(sumSuc, s"complex_sum (\\h:num. complex_sum ((f:num->num->complex) h) (n:num)) (SUC $K) = " +
                s"complex_sum (\\h:num. complex_sum (f h) n) $K + complex_sum (f $K) n")
              swapped <- rw(hyp, opened)
              split <- at(k("CSUM_ADD"), s"complex_sum (\\r:num. complex_sum (\\h:num. (f:num->num->complex) h r) $K + f $K r) (n:num) = " +
                s"complex_sum (\\r:num. complex_sum (\\h:num. f h r) $K) n + complex_sum (f $K) n")
              joined <- Conv.sym(split)
              pointwise <- at(sumSuc, s"complex_sum (\\h:num. (f:num->num->complex) h r) (SUC $K) = complex_sum (\\h:num. f h r) $K + f $K r")
              back <- Conv.sym(pointwise)
              inner <- sumCong(r, back, n)
              out <- trans(swapped, joined, inner)
            } yield out
          }
        )
        out <- gen(proved, ff, n)
      } yield out
  }
}
