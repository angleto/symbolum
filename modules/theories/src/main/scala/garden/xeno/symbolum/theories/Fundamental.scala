package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The fundamental theorem of algebra, by the polar route: the modulus of a polynomial of degree at
 * least one attains a least value over the plane, and d'Alembert's lemma says that a value which is
 * not zero is not the least.
 *
 * `Complex` publishes the facts and this is their derivation, as `ExtremeValue` is for `Continuity`:
 * the file that owns the type says what is true of it, and a derivation long enough to bury that is
 * kept beside it. `docs/adr/0061` is the decision, and it is short to read off the statement:
 *
 * {{{
 *   FUNDAMENTAL_THEOREM_OF_ALGEBRA
 *     !c n. 0 < n /\ ~(c n = 0) ==> ?z. complex_sum (\k. c k * complex_pow z k) (SUC n) = 0
 * }}}
 *
 * == A polynomial is its coefficients and a finite sum ==
 *
 * `c : num -> complex` and the sum over `SUC n` terms, with `c n` the leading coefficient and
 * nothing said about `c` past `n`. No constant is declared for it, so the statement is read in the
 * signature the complex numbers already have, and the hypothesis `~(c n = 0)` is what makes `n` the
 * degree rather than a bound on it. `0 < n` is not decoration: at `n = 0` the polynomial is the
 * constant `c 0`, which has no root when it is not zero, and `ComplexSpec` proves exactly that at one.
 *
 * == The minimum on a square, without Bolzano-Weierstrass ==
 *
 * The usual argument takes a minimum of `|p|` on a closed disc by compactness in two dimensions,
 * and the library has compactness in one: [[Continuity.AttainsMinimumWithin]]. What makes one enough
 * is that `|p|` is Lipschitz on every bounded set, with a constant read off the coefficients:
 * `|z^k - w^k| <= k S^k |z - w|` when both lie within `S`, by induction on `k`, and the sum of those
 * over the coefficients. So on the square of half-side `R`, for each `x` the modulus along the
 * vertical line through `x` is continuous and has a least point `g x`, chosen by `select`; the value
 * `|p (x + i g x)|` is Lipschitz in `x` with the same constant, because each line's minimum is at
 * most the other line's value at the same height plus the horizontal distance times the constant;
 * so it has a least point `x0` too, and `x0 + i g x0` is least on the whole square. Outside a large
 * enough disc `|p z| > |c 0| = |p 0|`, which is the growth estimate, so the least point of a square
 * containing that disc is least everywhere.
 *
 * == d'Alembert, after a shift written by Horner ==
 *
 * At a point `z` where `p z` is not zero, `p (z + w)` is a polynomial in `w` with the same leading
 * coefficient. That is the binomial theorem summed twice in the textbook, and here it is an
 * induction on the degree over Horner's form `p z = c 0 + z * p' z`, which needs no binomial
 * coefficient and no exchange of sums: the shifted coefficients are built by `COND` from those of
 * `p'`, and the claim carries that they vanish past the degree, which is what lets the top one come
 * out right. With `b` those coefficients and `k` the least index past zero with `b k` not zero
 * (`NUM_LEAST`), `p (z + w) = b 0 + w^k s w` with `s 0 = b k`; a `k`-th root `u` of `-b 0 / b k`
 * (`COMPLEX_ROOT`) and a small real `t` make `w = t u` give
 * `|p (z + w)| <= (1 - t^k) |b 0| + t^k |u|^k |s w - s 0|`, and the Lipschitz bound on `s` makes the
 * second term at most `t^(k+1)` times a constant, so a small enough `t` lowers the modulus.
 *
 * == What it spends ==
 *
 * Choice, eta and infinity, which is what the complex numbers rest on, and `ComplexSpec` asserts it
 * over every fact they publish. Nothing is asserted here.
 */
private[theories] object Fundamental {

  type R[A] = Either[LogicError, A]

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  // A def rather than a val: `Complex.Statements` reads this object while `Complex` is still being
  // initialised, and a val copied from it then would be null.
  private def Complexes: Type = Complex.Complexes

  /** `complex_sum (\\k. c k * complex_pow z k) n`: the polynomial with coefficients `c` at `z`, over `n` terms. */
  private def sum(c: String, z: String, n: String): String =
    s"complex_sum (\\k:num. ($c) k * complex_pow ($z) k) ($n)"

  /** The same over `SUC n` terms: the polynomial of degree at most `n`. */
  private def poly(c: String, n: String, z: String): String = sum(c, z, s"SUC ($n)")

  /** What `Complex` publishes from here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    "COMPLEX_NORM_OF_REAL" -> "!x:real. complex_norm (complex_of_real x) = abs x",
    "COMPLEX_NORM_NEG" -> "!z:complex. complex_norm (complex_neg z) = complex_norm z",
    "COMPLEX_NORM_POW" -> "!z:complex. !n:num. complex_norm (complex_pow z n) = Power (complex_norm z) n",
    "COMPLEX_NORM_TRIANGLE" -> "!z:complex. !w:complex. complex_norm (z + w) <= complex_norm z + complex_norm w",
    "COMPLEX_POLY_MINIMUM" ->
      ("!c:num->complex. !n:num. 0 < n /\\ ~(c n = complex_of_real 0) ==> " +
        "?z:complex. !w:complex. complex_norm (complex_sum (\\k:num. c k * complex_pow z k) (SUC n)) <= " +
        "complex_norm (complex_sum (\\k:num. c k * complex_pow w k) (SUC n))"),
    "DALEMBERT" ->
      ("!c:num->complex. !n:num. !z:complex. 0 < n /\\ ~(c n = complex_of_real 0) /\\ " +
        "~(complex_sum (\\k:num. c k * complex_pow z k) (SUC n) = complex_of_real 0) ==> " +
        "?w:complex. complex_norm (complex_sum (\\k:num. c k * complex_pow w k) (SUC n)) < " +
        "complex_norm (complex_sum (\\k:num. c k * complex_pow z k) (SUC n))"),
    "FUNDAMENTAL_THEOREM_OF_ALGEBRA" ->
      ("!c:num->complex. !n:num. 0 < n /\\ ~(c n = complex_of_real 0) ==> " +
        "?z:complex. complex_sum (\\k:num. c k * complex_pow z k) (SUC n) = complex_of_real 0")
  )

  /** The lemmas in the order they are proved, each from those before it. */
  private val Order: Vector[(String, Proofs => R[Kernel.Thm])] = Vector(
    "ABS_ZERO" -> (_.absZeroProof),
    "ABS_ONE" -> (_.absOneProof),
    "MUL_LE" -> (_.mulLeProof),
    "SCALE_UP" -> (_.scaleUpProof),
    "HORNER" -> (_.horner),
    "LINEAR" -> (_.linear),
    "TOP_ZERO" -> (_.topZero),
    "AT_ZERO" -> (p => p.atZero(p.k("HORNER"))),
    "ABS_SQUARE" -> (_.absSquare),
    "SQUARE_LE" -> (_.squareLe),
    "ABS_LE" -> (_.absLe),
    "COMPLEX_NORM_OF_REAL" -> (_.normOfReal),
    "COMPLEX_NORM_NEG" -> (_.normNeg),
    "NORM_SUB_SYM" -> (_.normSubSym),
    "COMPLEX_NORM_TRIANGLE" -> (p => p.triangle(p.k("SQUARE_LE"))),
    "COMPLEX_NORM_POW" -> (_.normPow),
    "POW_LE" -> (_.powLe),
    "POW_DIFF" -> (p => p.powDiff(p.k("COMPLEX_NORM_POW"), p.k("POW_LE"))),
    "LIPSCHITZ" -> (p => p.lipschitz(p.k("POW_DIFF"))),
    "BOUND_ABOVE" -> (p => p.boundAbove(p.k("COMPLEX_NORM_POW"))),
    "REGROUP" -> (_.regroup),
    "REVERSE" -> (_.reverse),
    "RE_BELOW_NORM" -> (_.partBelowNorm("Re", "Im")),
    "IM_BELOW_NORM" -> (_.partBelowNorm("Im", "Re")),
    "NORM_COMPLEX_LE" -> (_.normComplexLe),
    "BOUND_NONNEG" -> (_.boundNonneg),
    "GROWTH" -> (_.growth),
    "LIPSCHITZ_CONTINUOUS" -> (_.lipschitzContinuous),
    "SQUARE_LIPSCHITZ" -> (_.squareLipschitz),
    "SQUARE_CORE" -> (p => p.squareCore(p.k("SQUARE_LIPSCHITZ"))),
    "SQUARE_MINIMUM" -> (p => p.squareMinimum(p.k("SQUARE_CORE"))),
    "GLOBAL_MINIMUM" -> (_.globalMinimum),
    "SPLIT" -> (_.splitSum),
    "ONLY_FIRST" -> (_.onlyFirst),
    "SCALE" -> (_.scale),
    "DECOMPOSE" -> (p => p.decompose(p.k("SPLIT"), p.k("ONLY_FIRST"))),
    "SHIFT" -> (_.shift),
    "DALEMBERT" -> (_.dalembert),
    "ROOT_AT_SUCCESSOR" -> (_.rootAtSuccessor),
    "COMPLEX_POLY_MINIMUM" -> (p => p.fromSuccessor(StatementsMap("COMPLEX_POLY_MINIMUM"), p.k("GLOBAL_MINIMUM"))),
    "FUNDAMENTAL_THEOREM_OF_ALGEBRA" -> (p => p.fromSuccessor(StatementsMap("FUNDAMENTAL_THEOREM_OF_ALGEBRA"), p.k("ROOT_AT_SUCCESSOR")))
  )

  private lazy val StatementsMap: Map[String, String] = Statements.toMap

  /**
   * The facts [[Statements]] names, derived with `kit`.
   *
   * `held` answers the complex numbers' own facts and the kit's lookup those of every link below,
   * which is where the reals' order, `abs`, the sums and the extreme value theorem are read from;
   * the kit's `within` is the definition of `continuous_within`, which the minimum on a square is
   * stated with.
   */
  def prove(kit: ComplexKit, held: Map[String, Kernel.Thm]): R[Map[String, Kernel.Thm]] =
    ComplexKit.derive(Order, Statements, held)(known => new Proofs(kit, known))

  /** Every derivation, over one theory, reading what was proved before it from `known`. */
  private final class Proofs(val kit: ComplexKit, known: Map[String, Kernel.Thm]) {
    import kit.*

    def k(name: String): Kernel.Thm = known(name)

    def absZeroProof: R[Kernel.Thm] =
      for {
        h <- lemma("(0:real) <= 0")
        out <- specR(fact("ABS_OF_NONNEG"), re("0:real")).flatMap(rules.mp(_, h))
      } yield out

    def absOneProof: R[Kernel.Thm] =
      for {
        h <- lemma("(0:real) <= 1")
        out <- specR(fact("ABS_OF_NONNEG"), re("1:real")).flatMap(rules.mp(_, h))
      } yield out

    /** `0 <= a ==> a <= b ==> 0 <= u ==> u <= v ==> a * u <= b * v`. */
    def mulLeProof: R[Kernel.Thm] =
      lemma("!a:real. !b:real. !u:real. !v:real. 0 <= a ==> a <= b ==> 0 <= u ==> u <= v ==> a * u <= b * v")

    /** `0 <= u ==> 1 <= s ==> u <= s * u`. */
    def scaleUpProof: R[Kernel.Thm] = lemma("!u:real. !s:real. 0 <= u ==> 1 <= s ==> u <= s * u")



    val Reals: Type = TyApp(Real.TypeName, Nil)
    val Numbers: Type = TyApp(Natural.TypeName, Nil)
    val Complexes: Type = Complex.Complexes
    val Coefficients: Type = Type.fun(Numbers, Complexes)

    val c: FVar = Term.variable("c", Coefficients)
    val z: FVar = Term.variable("z", Complexes)
    val w: FVar = Term.variable("w", Complexes)
    val n: FVar = Term.variable("n", Numbers)
    val x: FVar = Term.variable("x", Reals)
    val y: FVar = Term.variable("y", Reals)


    def sumSuc: Kernel.Thm = k("COMPLEX_SUM_SUC")
    def sumZero: Kernel.Thm = k("COMPLEX_SUM_ZERO")
    def powSuc: Kernel.Thm = k("COMPLEX_POW_SUC")
    def powZero: Kernel.Thm = k("COMPLEX_POW_ZERO")

    /** `sum (SUC n) = c 0 + z * sum[c o SUC] n`. */
    def horner: R[Kernel.Thm] =
      for {
        body <- prop(s"${sum("c:num->complex", "z:complex", "SUC (n:num)")} = c 0 + z * ${sum("\\k:num. c (SUC k)", "z", "n")}")
        proved <- induct(n, body)(
          base => driver.using(sumSuc, sumZero, powZero).identity(base),
          (k, hyp, goal) => driver.using(sumSuc, powSuc).from(hyp).flatMap(_.identity(goal))
        )
        out <- gen(proved, c, z)
      } yield out

    /** `sum[\k. a * u k + v k] n = a * sum[u] n + sum[v] n`. */
    def linear: R[Kernel.Thm] = {
      val a = Term.variable("a", Complexes)
      val u = Term.variable("u", Coefficients)
      val v = Term.variable("v", Coefficients)
      for {
        body <- prop(s"${sum("\\k:num. (a:complex) * (u:num->complex) k + (v:num->complex) k", "z:complex", "n:num")} = a * ${sum("u", "z", "n")} + ${sum("v", "z", "n")}")
        proved <- induct(n, body)(
          base => driver.using(sumZero).identity(base),
          (k, hyp, goal) => driver.using(sumSuc).from(hyp).flatMap(_.identity(goal))
        )
        out <- gen(proved, a, u, v, z)
      } yield out
    }

    /** A top coefficient that vanishes adds nothing. */
    def topZero: R[Kernel.Thm] =
      for {
        hT <- prop("(c:num->complex) (SUC (n:num)) = complex_of_real 0")
        h <- LogicError.lift(Kernel.assume(hT))
        eq <- identity(s"${sum("c", "z:complex", "SUC (SUC n)")} = ${sum("c", "z", "SUC n")}", h, sumSuc)
        out <- rules.disch(hT, eq).flatMap(gen(_, c, z, n))
      } yield out

    /** The polynomial at zero is its constant coefficient. */
    def atZero(hornerT: Kernel.Thm): R[Kernel.Thm] =
      for {
        zero <- cx("complex_of_real 0")
        h <- spec(hornerT, c, zero, n)
        s <- cx(sum("\\k:num. (c:num->complex) (SUC k)", "complex_of_real 0", "n:num"))
        v = Term.variable("s", Complexes)
        general <- identity("(c:num->complex) 0 + complex_of_real 0 * (s:complex) = c 0")
        collapse <- LogicError.lift(Kernel.inst(Map(v -> s), general))
        joined <- Conv.trans(h, collapse)
        out <- gen(joined, c, n)
      } yield out

    /* ------------------------------------------------------------------ norms */

    /** `!x. abs x * abs x = x * x`. */
    def absSquare: R[Kernel.Thm] =
      for {
        mul <- specR(fact("ABS_MUL"), Right(x), Right(x))
        sq <- specR(fact("SQUARE_NONNEG"), Right(x))
        sqrAbs <- specR(fact("ABS_OF_NONNEG"), re("(x:real) * x")).flatMap(rules.mp(_, sq))
        out <- lin(Seq(mul, sqrAbs), "abs (x:real) * abs x = x * x").flatMap(gen(_, x))
      } yield out

    /** `0 <= y ==> x * x <= y * y ==> x <= y`. */
    def squareLe: R[Kernel.Thm] =
      for {
        strict <- lemma("!x:real. !y:real. 0 <= y ==> y < x ==> y * y < x * x")
        y0 <- assume("0 <= (y:real)")
        sq <- assume("(x:real) * x <= y * y")
        goal = "(x:real) <= y"
        proved <- cases("(y:real) < x")(
          yx => for {
            s <- spec(strict, x, y).flatMap(mp(_, y0, yx))
            absurd <- lin(Seq(s, sq), "F")
            g <- prop(goal)
            out <- rules.falsityElim(g, absurd)
          } yield out,
          notYx => specR(fact("LE_OF_NOT_LT"), Right(y), Right(x)).flatMap(rules.mp(_, notYx))
        )
        out <- disch("(x:real) * x <= y * y", proved).flatMap(disch("0 <= (y:real)", _)).flatMap(gen(_, x, y))
      } yield out

    /** `t <= m ==> -t <= m ==> abs t <= m`. */
    def absLe: R[Kernel.Thm] =
      for {
        up <- assume("(x:real) <= y")
        down <- assume("-(x:real) <= y")
        cases0 <- specR(fact("ABS_CASES"), Right(x))
        l <- assume("abs (x:real) = x").flatMap(e => lin(Seq(e, up), "abs x <= y"))
        r <- assume("abs (x:real) = -x").flatMap(e => lin(Seq(e, down), "abs x <= y"))
        both <- rules.disjElim(cases0, l, r)
        out <- disch("-(x:real) <= y", both).flatMap(disch("(x:real) <= y", _)).flatMap(gen(_, x, y))
      } yield out

    /** `complex_norm (complex_of_real x) = abs x`. */
    def normOfReal: R[Kernel.Thm] =
      for {
        sq <- identity("complex_norm_sq (complex_of_real (x:real)) = x * x")
        ax <- re("abs (x:real)")
        asq <- absSquare.flatMap(spec(_, x))
        nonneg <- specR(fact("ABS_NONNEG"), Right(x))
        nsq <- re("complex_norm_sq (complex_of_real (x:real))")
        unique <- specR(fact("SQRT_UNIQUE"), Right(nsq), Right(ax))
        both <- lin(Seq(sq, asq, nonneg), "0 <= abs (x:real) /\\ abs x * abs x = complex_norm_sq (complex_of_real x)")
        rooted <- rules.mp(unique, both)
        unfolded <- cx("complex_of_real (x:real)").flatMap(t => Conv.unfold(normDefinition, List(t)))
        joined <- Conv.trans(unfolded, rooted)
        out <- gen(joined, x)
      } yield out

    def normDefinition: Kernel.Thm = definitions(Complex.Norm)

    /** Two norms agree when the squared norms do. */
    def normsAgree(left: String, right: String): R[Kernel.Thm] =
      for {
        sq <- identity(s"complex_norm_sq ($left) = complex_norm_sq ($right)")
        sqrt <- LogicError.lift(theory.constant("sqrt", Type.fun(Reals, Reals)))
        rooted <- Conv.apTerm(sqrt, sq)
        l <- cx(left).flatMap(t => Conv.unfold(normDefinition, List(t)))
        r <- cx(right).flatMap(t => Conv.unfold(normDefinition, List(t))).flatMap(Conv.sym)
        out <- Conv.trans(l, rooted).flatMap(Conv.trans(_, r))
      } yield out

    def normNeg: R[Kernel.Thm] = normsAgree("complex_neg (z:complex)", "z").flatMap(gen(_, z))
    def normSubSym: R[Kernel.Thm] = normsAgree("(z:complex) - (w:complex)", "w - z").flatMap(gen(_, z, w))

    /** `complex_norm (z + w) <= complex_norm z + complex_norm w`. */
    def triangle(sqLe: Kernel.Thm): R[Kernel.Thm] =
      for {
        sqZ <- specR(fact("COMPLEX_NORM_SQUARED"), Right(z))
        sqW <- specR(fact("COMPLEX_NORM_SQUARED"), Right(w))
        zw <- cx("(z:complex) + (w:complex)")
        sqS <- specR(fact("COMPLEX_NORM_SQUARED"), Right(zw))
        nZ <- specR(fact("COMPLEX_NORM_NONNEG"), Right(z))
        nW <- specR(fact("COMPLEX_NORM_NONNEG"), Right(w))
        expand <- identity("complex_norm_sq ((z:complex) + (w:complex)) = complex_norm_sq z + complex_norm_sq w + 2 * (Re z * Re w + Im z * Im w)")
        lagrange <- identity("(Re (z:complex) * Re (w:complex) + Im z * Im w) * (Re z * Re w + Im z * Im w) + (Re z * Im w - Im z * Re w) * (Re z * Im w - Im z * Re w) = complex_norm_sq z * complex_norm_sq w")
        q <- re("Re (z:complex) * Im (w:complex) - Im z * Re w")
        qq <- specR(fact("SQUARE_NONNEG"), Right(q))
        regroup <- prop("(complex_norm (z:complex) * complex_norm (w:complex)) * (complex_norm z * complex_norm w) = (complex_norm z * complex_norm z) * (complex_norm w * complex_norm w)").flatMap(ring.prove)
        regrouped <- Limit.rewriteInProposition(sqZ, regroup).flatMap(Limit.rewriteInProposition(sqW, _))
        pp <- lin(Seq(lagrange, qq, regrouped),
          "(Re (z:complex) * Re (w:complex) + Im z * Im w) * (Re z * Re w + Im z * Im w) <= (complex_norm z * complex_norm w) * (complex_norm z * complex_norm w)")
        nm <- lin(Seq(nZ, nW), "0 <= complex_norm (z:complex) * complex_norm (w:complex)")
        p <- re("Re (z:complex) * Re (w:complex) + Im z * Im w")
        nmT <- re("complex_norm (z:complex) * complex_norm (w:complex)")
        pLe <- spec(sqLe, p, nmT).flatMap(mp(_, nm, pp))
        s <- re("complex_norm ((z:complex) + (w:complex))")
        tT <- re("complex_norm (z:complex) + complex_norm (w:complex)")
        tNonneg <- lin(Seq(nZ, nW), "0 <= complex_norm (z:complex) + complex_norm (w:complex)")
        ss <- lin(Seq(sqS, expand, pLe, sqZ, sqW),
          "complex_norm ((z:complex) + (w:complex)) * complex_norm (z + w) <= (complex_norm z + complex_norm w) * (complex_norm z + complex_norm w)")
        out <- spec(sqLe, s, tT).flatMap(mp(_, tNonneg, ss)).flatMap(gen(_, z, w))
      } yield out



    val s: FVar = Term.variable("S", Reals)

    def absZero: Kernel.Thm = k("ABS_ZERO")
    def absOne: Kernel.Thm = k("ABS_ONE")
    def mulLe: R[Kernel.Thm] = Right(k("MUL_LE"))
    def scaleUp: R[Kernel.Thm] = Right(k("SCALE_UP"))

    def normPow: R[Kernel.Thm] =
      for {
        body <- prop("complex_norm (complex_pow (z:complex) (n:num)) = Power (complex_norm z) n")
        powerZero <- fact("POWER_ZERO")
        powerSuc <- fact("POWER_SUC")
        normMul <- fact("COMPLEX_NORM_MUL")
        proved <- induct(n, body)(
          base => rewriting(Seq(powZero, k("COMPLEX_NORM_OF_REAL"), absOne, powerZero), base)(ring.prove),
          (kk, hyp, goal) => rewriting(Seq(powSuc, normMul, powerSuc, hyp), goal)(ring.prove)
        )
        out <- gen(proved, z)
      } yield out

    def powLe: R[Kernel.Thm] =
      for {
        body <- prop("0 <= (x:real) ==> x <= (y:real) ==> Power x (n:num) <= Power y n")
        powerZero <- fact("POWER_ZERO")
        powerSuc <- fact("POWER_SUC")
        ml <- mulLe
        proved <- induct(n, body)(
          base => underHyps(base)((_, g) => linAfter(Seq(powerZero), Nil, g)),
          (kk, hyp, goal) => underHyps(goal) { (hs, g) =>
            for {
              ih <- mp(hyp, hs(0), hs(1))
              px <- specR(fact("POWER_NONNEG"), Right(x)).flatMap(rules.mp(_, hs(0))).flatMap(spec(_, kk))
              pxT <- re(s"Power (x:real) ${kk.name}")
              pyT <- re(s"Power (y:real) ${kk.name}")
              m <- spec(ml, x, y, pxT, pyT).flatMap(mp(_, hs(0), hs(1), px, ih))
              out <- linAfter(Seq(powerSuc), Seq(m), g)
            } yield out
          }
        )
        out <- gen(proved, x, y)
      } yield out

    /** `|z^n - w^n| <= n S^n |z - w|` for `|z|, |w| <= S` and `1 <= S`. */
    def powDiff(normPowT: Kernel.Thm, powLeT: Kernel.Thm): R[Kernel.Thm] =
      for {
        body <- prop("complex_norm (z:complex) <= (S:real) ==> complex_norm (w:complex) <= S ==> 1 <= S ==> " +
          "complex_norm (complex_pow z (n:num) - complex_pow w n) <= real_of_num n * Power S n * complex_norm (z - w)")
        powerZero <- fact("POWER_ZERO")
        powerSuc <- fact("POWER_SUC")
        realZero <- fact("NUM_REAL_ZERO")
        realSuc <- fact("NUM_REAL_SUC")
        normMul <- fact("COMPLEX_NORM_MUL")
        ml <- mulLe
        up <- scaleUp
        proved <- induct(n, body)(
          base => underHyps(base) { (_, g) =>
            for {
              zero <- identity("complex_pow (z:complex) 0 - complex_pow (w:complex) 0 = complex_of_real 0", powZero)
              out <- linAfter(Seq(zero, k("COMPLEX_NORM_OF_REAL"), absZero, realZero, powerZero), Nil, g)
            } yield out
          },
          (kk, hyp, goal) => underHyps(goal) { (hs, g) =>
            val K = kk.name
            for {
              ih <- mp(hyp, hs*)
              ident <- identity(s"complex_pow (z:complex) (SUC $K) - complex_pow (w:complex) (SUC $K) = " +
                s"z * (complex_pow z $K - complex_pow w $K) + (z - w) * complex_pow w $K", powSuc)
              aT <- cx(s"z * (complex_pow (z:complex) $K - complex_pow (w:complex) $K)")
              bT <- cx(s"((z:complex) - (w:complex)) * complex_pow w $K")
              tri <- spec(k("COMPLEX_NORM_TRIANGLE"), aT, bT)
              dT <- cx(s"complex_pow (z:complex) $K - complex_pow (w:complex) $K")
              zw <- cx("(z:complex) - (w:complex)")
              wk <- cx(s"complex_pow (w:complex) $K")
              nm1 <- spec(normMul, z, dT)
              nm2 <- spec(normMul, zw, wk)
              np <- spec(normPowT, w, kk)
              nZ <- specR(fact("COMPLEX_NORM_NONNEG"), Right(z))
              nW <- specR(fact("COMPLEX_NORM_NONNEG"), Right(w))
              nD <- specR(fact("COMPLEX_NORM_NONNEG"), Right(dT))
              nZW <- specR(fact("COMPLEX_NORM_NONNEG"), Right(zw))
              normW <- re("complex_norm (w:complex)")
              pl <- spec(powLeT, normW, s, kk).flatMap(mp(_, nW, hs(1)))
              sNonneg <- lin(Seq(hs(2)), "0 <= (S:real)")
              pS <- specR(fact("POWER_NONNEG"), Right(s)).flatMap(rules.mp(_, sNonneg)).flatMap(spec(_, kk))
              pW <- specR(fact("POWER_NONNEG"), Right(normW)).flatMap(rules.mp(_, nW)).flatMap(spec(_, kk))
              normZ <- re("complex_norm (z:complex)")
              aN <- re(s"complex_norm (complex_pow (z:complex) $K - complex_pow (w:complex) $K)")
              xT <- re(s"real_of_num $K * Power (S:real) $K * complex_norm ((z:complex) - (w:complex))")
              m1 <- spec(ml, normZ, s, aN, xT).flatMap(mp(_, nZ, hs(0), nD, ih))
              dN <- re("complex_norm ((z:complex) - (w:complex))")
              pwT <- re(s"Power (complex_norm (w:complex)) $K")
              psT <- re(s"Power (S:real) $K")
              dd <- lin(Nil, "complex_norm ((z:complex) - (w:complex)) <= complex_norm (z - w)")
              m2 <- spec(ml, dN, dN, pwT, psT).flatMap(mp(_, nZW, dd, pW, pl))
              uT <- re(s"complex_norm ((z:complex) - (w:complex)) * Power (S:real) $K")
              zeroR <- re("0:real")
              z0 <- lin(Nil, "(0:real) <= 0")
              u0 <- spec(ml, zeroR, dN, zeroR, psT).flatMap(mp(_, z0, nZW, z0, pS))
              u0b <- lin(Seq(u0), s"0 <= complex_norm ((z:complex) - (w:complex)) * Power (S:real) $K")
              ex <- spec(up, uT, s).flatMap(mp(_, u0b, hs(2)))
              nm2p <- Limit.rewriteInProposition(np, nm2)
              out <- linAfter(Seq(ident, realSuc, powerSuc), Seq(tri, nm1, nm2p, m1, m2, ex), g)
            } yield out
          }
        )
        out <- gen(proved, z, w, s)
      } yield out

    val lipschitzBound: String = "Sum (\\k:num. complex_norm ((c:num->complex) k) * (real_of_num k * Power (S:real) k))"

    /** `|p z - p w| <= L |z - w|` over `n` terms, for `|z|, |w| <= S` and `1 <= S`. */
    def lipschitz(powDiffT: Kernel.Thm): R[Kernel.Thm] =
      for {
        body <- prop("complex_norm (z:complex) <= (S:real) ==> complex_norm (w:complex) <= S ==> 1 <= S ==> " +
          s"complex_norm (${sum("c:num->complex", "z", "n:num")} - ${sum("c", "w", "n")}) <= $lipschitzBound n * complex_norm (z - w)")
        sumZeroR <- fact("SUM_ZERO")
        sumSucR <- fact("SUM_SUC")
        normMul <- fact("COMPLEX_NORM_MUL")
        ml <- mulLe
        proved <- induct(n, body)(
          base => underHyps(base) { (_, g) =>
            for {
              zero <- identity(s"${sum("c:num->complex", "z:complex", "0")} - ${sum("c", "w:complex", "0")} = complex_of_real 0", sumZero)
              out <- linAfter(Seq(zero, k("COMPLEX_NORM_OF_REAL"), absZero, sumZeroR), Nil, g)
            } yield out
          },
          (kk, hyp, goal) => underHyps(goal) { (hs, g) =>
            val K = kk.name
            for {
              ih <- mp(hyp, hs*)
              ident <- identity(s"${sum("c:num->complex", "z:complex", s"SUC $K")} - ${sum("c", "w:complex", s"SUC $K")} = " +
                s"(${sum("c", "z", K)} - ${sum("c", "w", K)}) + c $K * (complex_pow z $K - complex_pow w $K)", sumSuc)
              aT <- cx(s"${sum("c:num->complex", "z:complex", K)} - ${sum("c", "w:complex", K)}")
              ck <- cx(s"(c:num->complex) $K")
              dT <- cx(s"complex_pow (z:complex) $K - complex_pow (w:complex) $K")
              bT <- cx(s"(c:num->complex) $K * (complex_pow (z:complex) $K - complex_pow (w:complex) $K)")
              tri <- spec(k("COMPLEX_NORM_TRIANGLE"), aT, bT)
              nm <- spec(normMul, ck, dT)
              pd <- spec(powDiffT, z, w, s, kk).flatMap(mp(_, hs*))
              nC <- specR(fact("COMPLEX_NORM_NONNEG"), Right(ck))
              nD <- specR(fact("COMPLEX_NORM_NONNEG"), Right(dT))
              cN <- re(s"complex_norm ((c:num->complex) $K)")
              dN <- re(s"complex_norm (complex_pow (z:complex) $K - complex_pow (w:complex) $K)")
              xT <- re(s"real_of_num $K * Power (S:real) $K * complex_norm ((z:complex) - (w:complex))")
              cc <- lin(Nil, s"complex_norm ((c:num->complex) $K) <= complex_norm (c $K)")
              m <- spec(ml, cN, cN, dN, xT).flatMap(mp(_, nC, cc, nD, pd))
              out <- linAfter(Seq(ident, sumSucR), Seq(tri, nm, m, ih), g)
            } yield out
          }
        )
        out <- gen(proved, c, z, w, s)
      } yield out

    /** `|p z| <= (sum of |c k|) |z|^n` for `1 <= |z|`. */
    def boundAbove(normPowT: Kernel.Thm): R[Kernel.Thm] =
      for {
        body <- prop(s"1 <= complex_norm (z:complex) ==> complex_norm (${poly("c:num->complex", "n:num", "z")}) <= " +
          "Sum (\\k:num. complex_norm (c k)) (SUC n) * Power (complex_norm z) n")
        sumZeroR <- fact("SUM_ZERO")
        sumSucR <- fact("SUM_SUC")
        powerZero <- fact("POWER_ZERO")
        powerSuc <- fact("POWER_SUC")
        normMul <- fact("COMPLEX_NORM_MUL")
        ml <- mulLe
        up <- scaleUp
        coefficientsNonneg <- for {
          k <- Right(Term.variable("k", Numbers))
          ck <- cx("(c:num->complex) k")
          one <- specR(fact("COMPLEX_NORM_NONNEG"), Right(ck))
          all <- rules.gen(k, one)
          fT <- term("\\k:num. complex_norm ((c:num->complex) k)", Type.fun(Numbers, Reals))
          out <- specR(fact("SUM_NONNEGATIVE"), Right(fT)).flatMap(rules.mp(_, all))
        } yield out
        proved <- induct(n, body)(
          base => underHyps(base) { (_, g) =>
            for {
              e0 <- identity(s"${sum("c:num->complex", "z:complex", "SUC 0")} = c 0", sumSuc, sumZero, powZero)
              out <- linAfter(Seq(e0, sumSucR, sumZeroR, powerZero), Nil, g)
            } yield out
          },
          (kk, hyp, goal) => underHyps(goal) { (hs, g) =>
            val K = kk.name
            for {
              ih <- mp(hyp, hs*)
              fT <- term("\\k:num. (c:num->complex) k * complex_pow (z:complex) k", Type.fun(Numbers, Complexes))
              sk <- nm(s"SUC $K")
              e <- spec(sumSuc, fT, sk)
              aT <- cx(sum("c:num->complex", "z:complex", s"SUC $K"))
              top <- cx(s"(c:num->complex) (SUC $K) * complex_pow (z:complex) (SUC $K)")
              tri <- spec(k("COMPLEX_NORM_TRIANGLE"), aT, top)
              ck <- cx(s"(c:num->complex) (SUC $K)")
              zk <- cx(s"complex_pow (z:complex) (SUC $K)")
              nmT <- spec(normMul, ck, zk)
              np <- spec(normPowT, z, sk)
              normZ <- re("complex_norm (z:complex)")
              nZ <- specR(fact("COMPLEX_NORM_NONNEG"), Right(z))
              pk <- specR(fact("POWER_NONNEG"), Right(normZ)).flatMap(rules.mp(_, nZ)).flatMap(spec(_, kk))
              pkT <- re(s"Power (complex_norm (z:complex)) $K")
              mono <- spec(up, pkT, normZ).flatMap(mp(_, pk, hs(0)))
              ps <- spec(powerSuc, normZ, kk)
              gT <- term("\\k:num. complex_norm ((c:num->complex) k)", Type.fun(Numbers, Reals))
              bNonneg <- spec(coefficientsNonneg, sk)
              bT <- re(s"Sum (\\k:num. complex_norm ((c:num->complex) k)) (SUC $K)")
              psT <- re(s"Power (complex_norm (z:complex)) (SUC $K)")
              pkle <- lin(Seq(mono, ps), s"Power (complex_norm (z:complex)) $K <= Power (complex_norm z) (SUC $K)")
              bb <- lin(Nil, s"Sum (\\k:num. complex_norm ((c:num->complex) k)) (SUC $K) <= Sum (\\k:num. complex_norm (c k)) (SUC $K)")
              m <- spec(ml, bT, bT, pkT, psT).flatMap(mp(_, bNonneg, bb, pk, pkle))
              ss <- spec(sumSucR, gT, sk)
              nmp <- Limit.rewriteInProposition(np, nmT)
              out <- linAfter(Seq(e, ss), Seq(tri, nmp, ih, m), g)
            } yield out
          }
        )
        out <- gen(proved, c, z)
      } yield out

    val Functions: Type = Type.fun(Reals, Reals)

    /** `v = (u + v) + complex_neg u`. */
    def regroup: R[Kernel.Thm] = identity("!u:complex. !v:complex. v = (u + v) + complex_neg u")

    /** `abs (complex_norm z - complex_norm w) <= complex_norm (z - w)`. */
    def reverse: R[Kernel.Thm] =
      for {
        e1 <- identity("(z:complex) = (z - (w:complex)) + w")
        e2 <- identity("(w:complex) = (w - (z:complex)) + z")
        zw <- cx("(z:complex) - (w:complex)")
        wz <- cx("(w:complex) - (z:complex)")
        t1 <- spec(k("COMPLEX_NORM_TRIANGLE"), zw, w)
        t2 <- spec(k("COMPLEX_NORM_TRIANGLE"), wz, z)
        s1 <- Conv.sym(e1).flatMap(Limit.rewriteInProposition(_, t1))
        s2 <- Conv.sym(e2).flatMap(Limit.rewriteInProposition(_, t2))
        sym <- spec(k("NORM_SUB_SYM"), w, z)
        a <- re("complex_norm (z:complex) - complex_norm (w:complex)")
        b <- re("complex_norm ((z:complex) - (w:complex))")
        up <- lin(Seq(s1), "complex_norm (z:complex) - complex_norm (w:complex) <= complex_norm (z - w)")
        down <- lin(Seq(s2, sym), "-(complex_norm (z:complex) - complex_norm (w:complex)) <= complex_norm (z - w)")
        out <- spec(k("ABS_LE"), a, b).flatMap(mp(_, up, down)).flatMap(gen(_, z, w))
      } yield out

    /** `abs (Re z) <= complex_norm z` and the same of `Im`. */
    def partBelowNorm(part: String, other: String): R[Kernel.Thm] =
      for {
        pz <- re(s"$part (z:complex)")
        nz <- re("complex_norm (z:complex)")
        ap <- re(s"abs ($part (z:complex))")
        sq <- spec(k("ABS_SQUARE"), pz)
        os <- re(s"$other (z:complex)").flatMap(t => specR(fact("SQUARE_NONNEG"), Right(t)))
        nsq <- specR(fact("COMPLEX_NORM_SQUARED"), Right(z))
        open <- identity("complex_norm_sq (z:complex) = Re z * Re z + Im z * Im z")
        nonneg <- specR(fact("COMPLEX_NORM_NONNEG"), Right(z))
        le <- lin(Seq(sq, os, nsq, open), s"abs ($part (z:complex)) * abs ($part z) <= complex_norm z * complex_norm z")
        out <- spec(k("SQUARE_LE"), ap, nz).flatMap(mp(_, nonneg, le)).flatMap(gen(_, z))
      } yield out

    /** `complex_norm (COMPLEX x y) <= abs x + abs y`. */
    def normComplexLe: R[Kernel.Thm] =
      for {
        reC <- fact(Complex.ReOfConstructor)
        imC <- fact(Complex.ImOfConstructor)
        cT <- cx("COMPLEX (x:real) (y:real)")
        nsq <- specR(fact("COMPLEX_NORM_SQUARED"), Right(cT))
        open <- identity("complex_norm_sq (COMPLEX (x:real) (y:real)) = x * x + y * y", reC, imC)
        sx <- spec(k("ABS_SQUARE"), x)
        sy <- spec(k("ABS_SQUARE"), y)
        ax <- specR(fact("ABS_NONNEG"), Right(x))
        ay <- specR(fact("ABS_NONNEG"), Right(y))
        axy <- lin(Seq(ax, ay), "0 <= abs (x:real) * abs (y:real)")
        le <- lin(Seq(nsq, open, sx, sy, axy),
          "complex_norm (COMPLEX (x:real) (y:real)) * complex_norm (COMPLEX x y) <= (abs x + abs y) * (abs x + abs y)")
        nonneg <- lin(Seq(ax, ay), "0 <= abs (x:real) + abs (y:real)")
        nT <- re("complex_norm (COMPLEX (x:real) (y:real))")
        sT <- re("abs (x:real) + abs (y:real)")
        out <- spec(k("SQUARE_LE"), nT, sT).flatMap(mp(_, nonneg, le)).flatMap(gen(_, x, y))
      } yield out

    /** `0 <= S ==> 0 <= Sum (\k. |c k| * (k * S^k)) n`. */
    def boundNonneg: R[Kernel.Thm] =
      for {
        hS <- assume("0 <= (S:real)")
        i = Term.variable("i", Numbers)
        ci <- cx("(c:num->complex) i")
        nC <- specR(fact("COMPLEX_NORM_NONNEG"), Right(ci))
        nI <- specR(fact("NUM_REAL_NONNEG"), Right(i))
        sT <- re("S:real")
        pS <- specR(fact("POWER_NONNEG"), Right(sT)).flatMap(rules.mp(_, hS)).flatMap(spec(_, i))
        ip <- lin(Seq(nI, pS), "0 <= real_of_num i * Power (S:real) i")
        one <- lin(Seq(nC, ip), "0 <= complex_norm ((c:num->complex) i) * (real_of_num i * Power (S:real) i)")
        all <- rules.gen(i, one)
        fT <- term("\\k:num. complex_norm ((c:num->complex) k) * (real_of_num k * Power (S:real) k)", Type.fun(Numbers, Reals))
        out <- specR(fact("SUM_NONNEGATIVE"), Right(fT)).flatMap(rules.mp(_, all))
        done <- disch("0 <= (S:real)", out).flatMap(gen(_, c, s))
      } yield done

    /* ------------------------------------------------------------------ the growth */

    def growth: R[Kernel.Thm] = {
      val P = poly("c:num->complex", "SUC (m:num)", "z:complex")
      val Pm = poly("c", "m", "z")
      val top = "c (SUC m) * complex_pow z (SUC m)"
      for {
        hT <- prop("~((c:num->complex) (SUC (m:num)) = complex_of_real 0)")
        h <- LogicError.lift(Kernel.assume(hT))
        cm <- cx("(c:num->complex) (SUC (m:num))")
        aZeroT <- prop("complex_norm ((c:num->complex) (SUC (m:num))) = 0")
        aNonzero <- for {
          zeroed <- LogicError.lift(Kernel.assume(aZeroT)).flatMap(a => specR(fact("COMPLEX_NORM_ZERO"), Right(cm)).flatMap(rules.mp(_, a)))
          absurd <- rules.notElim(h, zeroed)
          out <- rules.notIntro(aZeroT, absurd)
        } yield out
        aNonneg <- specR(fact("COMPLEX_NORM_NONNEG"), Right(cm))
        aT <- re("complex_norm ((c:num->complex) (SUC (m:num)))")
        av <- specR(fact("MUL_INVERSE"), Right(aT)).flatMap(rules.mp(_, aNonzero))
        aPos <- {
          // 0 < a: a is not negative and is not zero
          for {
            leT <- prop("complex_norm ((c:num->complex) (SUC (m:num))) <= 0")
            notLe <- for {
              le <- LogicError.lift(Kernel.assume(leT))
              zT <- re("0:real")
              eq <- specR(fact("LE_ANTISYMMETRIC"), Right(aT), Right(zT)).flatMap(mp(_, le, aNonneg))
              absurd <- rules.notElim(aNonzero, eq)
              out <- rules.notIntro(leT, absurd)
            } yield out
            zT <- re("0:real")
            out <- specR(fact("LT_OF_NOT_LE"), Right(aT), Right(zT)).flatMap(rules.mp(_, notLe))
          } yield out
        }
        vPos <- specR(fact("INV_POSITIVE"), Right(aT)).flatMap(rules.mp(_, aPos))
        bS = "Sum (\\k:num. complex_norm ((c:num->complex) k)) (SUC (m:num))"
        c0S = "complex_norm ((c:num->complex) 0)"
        bNonneg <- for {
          i <- Right(Term.variable("i", Numbers))
          ci <- cx("(c:num->complex) i")
          one <- specR(fact("COMPLEX_NORM_NONNEG"), Right(ci))
          all <- rules.gen(i, one)
          fT <- term("\\k:num. complex_norm ((c:num->complex) k)", Type.fun(Numbers, Reals))
          sm <- nm("SUC (m:num)")
          out <- specR(fact("SUM_NONNEGATIVE"), Right(fT)).flatMap(rules.mp(_, all)).flatMap(spec(_, sm))
        } yield out
        c0 <- cx("(c:num->complex) 0")
        c0Nonneg <- specR(fact("COMPLEX_NORM_NONNEG"), Right(c0))
        v = s"inv (complex_norm ((c:num->complex) (SUC (m:num))))"
        rT = s"(($bS + $c0S + 1) * $v + 1)"
        rTerm <- re(rT)
        prod <- lin(Seq(vPos, bNonneg, c0Nonneg), s"0 <= ($bS + $c0S + 1) * $v")
        rGe1 <- lin(Seq(prod), s"1 <= $rT")
        aR0 <- prop(s"complex_norm ((c:num->complex) (SUC (m:num))) * $rT = ($bS + $c0S + 1) * (complex_norm (c (SUC m)) * $v) + complex_norm (c (SUC m))")
          .flatMap(ring.prove)
        aR <- Limit.rewriteInProposition(av, aR0)
        normPow = k("COMPLEX_NORM_POW")
        boundAbove = k("BOUND_ABOVE")
        // for a z with R <= |z|
        zR <- prop(s"$rT <= complex_norm (z:complex)")
        hz <- LogicError.lift(Kernel.assume(zR))
        fT <- term("\\k:num. (c:num->complex) k * complex_pow (z:complex) k", Type.fun(Numbers, Complexes))
        sm <- nm("SUC (m:num)")
        e <- spec(sumSuc, fT, sm)
        pmT <- cx(Pm)
        topT <- cx(top)
        grouped <- spec(k("REGROUP"), pmT, topT)
        sumT <- cx(s"$Pm + $top")
        negPm <- cx(s"complex_neg ($Pm)")
        tri0 <- spec(k("COMPLEX_NORM_TRIANGLE"), sumT, negPm)
        tri <- Conv.sym(grouped).flatMap(Limit.rewriteInProposition(_, tri0))
        nn <- spec(k("COMPLEX_NORM_NEG"), pmT)
        cmz <- cx("complex_pow (z:complex) (SUC (m:num))")
        nmul <- specR(fact("COMPLEX_NORM_MUL"), Right(cm), Right(cmz))
        np <- spec(normPow, z, sm)
        topNorm <- Limit.rewriteInProposition(np, nmul)
        normZ <- re("complex_norm (z:complex)")
        ps <- specR(fact("POWER_SUC"), Right(normZ), Right(m))
        rGe1z <- lin(Seq(rGe1, hz), "1 <= complex_norm (z:complex)")
        bound <- spec(boundAbove, c, z, m).flatMap(rules.mp(_, rGe1z))
        oneT <- re("1:real")
        zero1 <- lemma("(0:real) <= 1")
        pl <- spec(k("POW_LE"), oneT, normZ, m).flatMap(mp(_, zero1, rGe1z))
        pone <- specR(fact("POWER_ONE"), Right(m))
        rNonneg <- lin(Seq(rGe1), s"0 <= $rT")
        aa <- lin(Nil, "complex_norm ((c:num->complex) (SUC (m:num))) <= complex_norm (c (SUC m))")
        ar <- spec(k("MUL_LE"), aT, aT, rTerm, normZ).flatMap(mp(_, aNonneg, aa, rNonneg, hz))
        qT <- re(s"complex_norm ((c:num->complex) (SUC (m:num))) * complex_norm (z:complex) - $bS")
        q0 <- lin(Seq(ar, aR, c0Nonneg, aNonneg), s"0 <= complex_norm ((c:num->complex) (SUC (m:num))) * complex_norm (z:complex) - $bS")
        pT <- re("Power (complex_norm (z:complex)) (m:num)")
        pm1 <- lin(Seq(pl, pone), "1 <= Power (complex_norm (z:complex)) (m:num)")
        key <- spec(k("SCALE_UP"), qT, pT).flatMap(mp(_, q0, pm1))
        goalT <- prop(s"$c0S < complex_norm ($P)")
        topNorm2 <- Limit.rewriteInProposition(ps, topNorm)
        reached <- linAfter(Seq(e), Seq(tri, nn, topNorm2, bound, ar, aR, key, aNonneg), goalT)
        forZ <- rules.disch(zR, reached).flatMap(rules.gen(z, _))
        both <- rules.conjIntro(rGe1, forZ)
        ex <- existsIntro(s"?R:real. 1 <= R /\\ (!z:complex. R <= complex_norm z ==> $c0S < complex_norm ($P))", rTerm, both)
        out <- rules.disch(hT, ex).flatMap(gen(_, c, m))
      } yield out
    }

    /* ------------------------------------------------------------------ continuity from a Lipschitz bound */

    def lipschitzContinuous: R[Kernel.Thm] = {
      val fv = Term.variable("f", Functions)
      val a = Term.variable("a", Reals)
      val b = Term.variable("b", Reals)
      val l = Term.variable("L", Reals)
      val e = Term.variable("e", Reals)
      val lipText = "!x:real. !y:real. (a:real) <= x /\\ x <= (b:real) /\\ a <= y /\\ y <= b ==> abs ((f:real->real) x - f y) <= (L:real) * abs (x - y)"
      val steps = Continuity.Steps(logic, linarith, theory, notation, within)
      for {
        hL <- assume("0 <= (L:real)")
        lip <- assume(lipText)
        hxT <- prop("(a:real) <= (x:real) /\\ x <= (b:real)")
        hx <- LogicError.lift(Kernel.assume(hxT))
        hxs <- split(hx)
        unfolded <- Conv.unfold(within, List(fv, a, b, x))
        right <- Term.destEq(unfolded.conclusion).map(_._2).toRight(NotOfForm("an equation", unfolded.conclusion))
        normal <- Conv.betaNormalise(right)
        opened <- Conv.trans(unfolded, normal)
        eT <- prop("0 < (e:real)")
        he <- LogicError.lift(Kernel.assume(eT))
        share <- Continuity.portion(steps, reals, "L:real", hL, 1, he)
        dT <- re(share.term)
        yT <- prop(s"(a:real) <= (y:real) /\\ y <= (b:real) /\\ abs (y - (x:real)) < ${share.term}")
        hy <- LogicError.lift(Kernel.assume(yT))
        hys <- split(hy)
        inner <- for {
          both <- conjs(hys(0), hys(1), hxs(0), hxs(1))
          bound <- spec(lip, y, x).flatMap(rules.mp(_, both))
          ay <- re("abs ((y:real) - (x:real))")
          ayNonneg <- specR(fact("ABS_NONNEG"), re("(y:real) - (x:real)"))
          ayLe <- lin(Seq(hys(2)), s"abs ((y:real) - (x:real)) <= ${share.term}")
          ll <- lin(Nil, "(L:real) <= L")
          lT <- re("L:real")
          scaled <- spec(k("MUL_LE"), lT, lT, ay, dT).flatMap(mp(_, hL, ll, ayNonneg, ayLe))
          out <- lin(Seq(bound, scaled, share.equation, share.positive), "abs ((f:real->real) (y:real) - f (x:real)) < (e:real)")
        } yield out
        everyY <- rules.disch(yT, inner).flatMap(rules.gen(y, _))
        radius <- rules.conjIntro(share.positive, everyY)
        witnessed <- existsIntro(
          "?d:real. 0 < d /\\ (!y:real. (a:real) <= y /\\ y <= (b:real) /\\ abs (y - (x:real)) < d ==> abs ((f:real->real) y - f x) < (e:real))",
          dT, radius)
        statement <- rules.disch(eT, witnessed).flatMap(rules.gen(e, _))
        folded <- Conv.sym(opened).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, statement)))
        everyX <- rules.disch(hxT, folded).flatMap(rules.gen(x, _))
        out <- disch(lipText, everyX).flatMap(disch("0 <= (L:real)", _)).flatMap(gen(_, fv, a, b, l))
      } yield out
    }



    val rr: FVar = Term.variable("R", Reals)
    val g: FVar = Term.variable("g", Functions)
    val u: FVar = Term.variable("u", Reals)
    val v: FVar = Term.variable("v", Reals)
    /** `|p (COMPLEX a b)|`, the modulus at a point of the plane. */
    def h(a: String, b: String): String = s"complex_norm (${poly("c:num->complex", "n:num", s"COMPLEX ($a) ($b)")})"

    def inR(t: String): String = s"-(R:real) <= ($t) /\\ ($t) <= R"

    val bound: String = "Sum (\\k:num. complex_norm ((c:num->complex) k) * (real_of_num k * Power ((R:real) + R + 1) k)) (SUC (n:num))"

    /** Both ends of `-R <= t <= R` from the conjunction. */
    def ends(t: Kernel.Thm): R[(Kernel.Thm, Kernel.Thm)] = split(t).map(v => (v(0), v(1)))

    /** `abs t <= R` from `-R <= t <= R`. */
    def absIn(t: String, inT: Kernel.Thm): R[Kernel.Thm] =
      for {
        e <- ends(inT)
        up <- lin(Seq(e._2), s"($t) <= (R:real)")
        down <- lin(Seq(e._1), s"-($t) <= (R:real)")
        tT <- re(t)
        out <- spec(k("ABS_LE"), tT, rr).flatMap(mp(_, up, down))
      } yield out

    /**
     * `abs (h x y - h u v) <= L * (abs (x - u) + abs (y - v))` on the square of half-side `R`.
     */
    def squareLipschitz: R[Kernel.Thm] =
      for {
        hx <- assume(inR("x:real"))
        hy <- assume(inR("y:real"))
        hu <- assume(inR("u:real"))
        hv <- assume(inR("v:real"))
        ax <- absIn("x:real", hx)
        ay <- absIn("y:real", hy)
        au <- absIn("u:real", hu)
        av <- absIn("v:real", hv)
        zT <- cx("COMPLEX (x:real) (y:real)")
        wT <- cx("COMPLEX (u:real) (v:real)")
        nz <- spec(k("NORM_COMPLEX_LE"), x, y)
        nw <- spec(k("NORM_COMPLEX_LE"), u, v)
        sT <- re("(R:real) + R + 1")
        zS <- lin(Seq(nz, ax, ay), "complex_norm (COMPLEX (x:real) (y:real)) <= (R:real) + R + 1")
        wS <- lin(Seq(nw, au, av), "complex_norm (COMPLEX (u:real) (v:real)) <= (R:real) + R + 1")
        rNonneg <- ends(hx).flatMap(e => lin(Seq(e._1, e._2), "0 <= (R:real)"))
        s1 <- lin(Seq(rNonneg), "1 <= (R:real) + R + 1")
        sn <- nm("SUC (n:num)")
        lip <- spec(k("LIPSCHITZ"), c, zT, wT, sT, sn).flatMap(mp(_, zS, wS, s1))
        pz <- cx(poly("c:num->complex", "n:num", "COMPLEX (x:real) (y:real)"))
        pw <- cx(poly("c:num->complex", "n:num", "COMPLEX (u:real) (v:real)"))
        rev <- spec(k("REVERSE"), pz, pw)
        reC <- fact(Complex.ReOfConstructor)
        imC <- fact(Complex.ImOfConstructor)
        diff <- identity("COMPLEX (x:real) (y:real) - COMPLEX (u:real) (v:real) = COMPLEX (x - u) (y - v)", reC, imC)
        xu <- re("(x:real) - (u:real)")
        yv <- re("(y:real) - (v:real)")
        nd <- spec(k("NORM_COMPLEX_LE"), xu, yv)
        nd2 <- Conv.sym(diff).flatMap(Limit.rewriteInProposition(_, nd))
        lT <- re(bound)
        sNonneg <- lin(Seq(rNonneg), "0 <= (R:real) + R + 1")
        lNonneg <- spec(k("BOUND_NONNEG"), c, sT).flatMap(rules.mp(_, sNonneg)).flatMap(spec(_, sn))
        ll <- lin(Nil, s"$bound <= $bound")
        dN <- re("complex_norm (COMPLEX (x:real) (y:real) - COMPLEX (u:real) (v:real))")
        eT <- re("abs ((x:real) - (u:real)) + abs ((y:real) - (v:real))")
        dNonneg <- specR(fact("COMPLEX_NORM_NONNEG"), cx("COMPLEX (x:real) (y:real) - COMPLEX (u:real) (v:real)"))
        scaled <- spec(k("MUL_LE"), lT, lT, dN, eT).flatMap(mp(_, lNonneg, ll, dNonneg, nd2))
        out <- lin(Seq(rev, lip, scaled), s"abs (${h("x:real", "y:real")} - ${h("u:real", "v:real")}) <= $bound * (abs (x - u) + abs (y - v))")
        done <- disch(inR("v:real"), out).flatMap(disch(inR("u:real"), _)).flatMap(disch(inR("y:real"), _)).flatMap(disch(inR("x:real"), _))
          .flatMap(gen(_, x, y, u, v))
      } yield done

    /** `abs (t - t) = t - t`, which `Linarith` then reads as zero. */
    def absSelf(t: String): R[Kernel.Thm] =
      for {
        nonneg <- lin(Nil, s"0 <= ($t) - ($t)")
        tt <- re(s"($t) - ($t)")
        out <- specR(fact("ABS_OF_NONNEG"), Right(tt)).flatMap(rules.mp(_, nonneg))
      } yield out

    /**
     * Given a function `g` choosing, for each `x` of `[-R, R]`, a `y` of `[-R, R]` where the modulus
     * on the vertical line through `x` is least, the modulus has a least value on the square.
     */
    def squareCore(sqLip: Kernel.Thm): R[Kernel.Thm] = {
      val choice = s"!x:real. ${inR("x")} ==> ${inR("(g:real->real) x")} /\\ (!u:real. ${inR("u")} ==> ${h("x", "g x")} <= ${h("x", "u")})"
      for {
        hR <- assume("0 <= (R:real)")
        hg <- assume(choice)
        // the modulus along the chosen points is Lipschitz in x
        gx1 = "(g:real->real) (u:real)"
        gx2 = "(g:real->real) (v:real)"
        hu <- assume(inR("u:real"))
        hv <- assume(inR("v:real"))
        cu <- spec(hg, u).flatMap(rules.mp(_, hu)).flatMap(split)
        cv <- spec(hg, v).flatMap(rules.mp(_, hv)).flatMap(split)
        inGu <- conj(cu(0), cu(1))
        inGv <- conj(cv(0), cv(1))
        guT <- re(gx1)
        gvT <- re(gx2)
        // at u: h u (g u) <= h u (g v), and h u (g v) is within L |u - v| of h v (g v)
        minU <- spec(cu(2), gvT).flatMap(rules.mp(_, inGv))
        minV <- spec(cv(2), guT).flatMap(rules.mp(_, inGu))
        l1 <- spec(sqLip, u, gvT, v, gvT).flatMap(mp(_, hu, inGv, hv, inGv))
        l2 <- spec(sqLip, v, guT, u, guT).flatMap(mp(_, hv, inGu, hu, inGu))
        s1 <- absSelf(gx2)
        s2 <- absSelf(gx1)
        d1 <- re(s"${h("u:real", gx2)} - ${h("v:real", gx2)}").flatMap(t => specR(fact("ABS_ABOVE"), Right(t)))
        d2 <- re(s"${h("v:real", gx1)} - ${h("u:real", gx1)}").flatMap(t => specR(fact("ABS_ABOVE"), Right(t)))
        uv <- re("(u:real) - (v:real)")
        vu <- re("(v:real) - (u:real)")
        symAbs <- for {
          a <- specR(fact("ABS_ABOVE"), Right(uv))
          b <- specR(fact("ABS_ABOVE_NEG"), Right(uv))
          cs <- specR(fact("ABS_CASES"), Right(vu))
          out <- {
            val goal = "abs ((v:real) - (u:real)) <= abs (u - v)"
            for {
              l <- assume("abs ((v:real) - (u:real)) = v - u").flatMap(e => lin(Seq(e, b), goal))
              r <- assume("abs ((v:real) - (u:real)) = -(v - u)").flatMap(e => lin(Seq(e, a), goal))
              o <- rules.disjElim(cs, l, r)
            } yield o
          }
        } yield out
        lT <- re(bound)
        sT <- re("(R:real) + R + 1")
        sNonneg <- lin(Seq(hR), "0 <= (R:real) + R + 1")
        sn <- nm("SUC (n:num)")
        lNonneg <- spec(k("BOUND_NONNEG"), c, sT).flatMap(rules.mp(_, sNonneg)).flatMap(spec(_, sn))
        ll <- lin(Nil, s"$bound <= $bound")
        avu <- re("abs ((v:real) - (u:real))")
        auv <- re("abs ((u:real) - (v:real))")
        avuNonneg <- specR(fact("ABS_NONNEG"), Right(vu))
        scaledSym <- spec(k("MUL_LE"), lT, lT, avu, auv).flatMap(mp(_, lNonneg, ll, avuNonneg, symAbs))
        gT = s"${h("u:real", gx1)} - ${h("v:real", gx2)}"
        l1s <- Limit.rewriteInProposition(s1, l1)
        l2s <- Limit.rewriteInProposition(s2, l2)
        up <- lin(Seq(minU, l1s, d1), s"$gT <= $bound * abs ((u:real) - (v:real))")
        down <- lin(Seq(minV, l2s, d2, scaledSym), s"-($gT) <= $bound * abs ((u:real) - (v:real))")
        gTerm <- re(gT)
        lu <- re(s"$bound * abs ((u:real) - (v:real))")
        gLip <- spec(k("ABS_LE"), gTerm, lu).flatMap(mp(_, up, down))
        // in the form the continuity lemma asks, read off its own antecedent
        gFun <- term(s"\\x:real. ${h("x", "(g:real->real) x")}", Functions)
        lo <- re("-(R:real)")
        lc <- spec(k("LIPSCHITZ_CONTINUOUS"), gFun, lo, rr, lT).flatMap(rules.mp(_, lNonneg))
        wanted <- logic.destImp(lc.conclusion).map(_._1).toRight(NotOfForm("an implication", lc.conclusion))
        bothT <- prop(s"${inR("u:real")} /\\ ${inR("v:real")}")
        gLip2 <- for {
          bothA <- LogicError.lift(Kernel.assume(bothT))
          parts <- split(bothA)
          hu2 <- conj(parts(0), parts(1))
          hv2 <- conj(parts(2), parts(3))
          withU <- rules.disch(hu.conclusion, gLip).flatMap(rules.disch(hv.conclusion, _))
          applied <- rules.mp(withU, hv2).flatMap(rules.mp(_, hu2))
          out <- rules.disch(bothT, applied).flatMap(gen(_, u, v))
        } yield out
        gLip3 <- if (gLip2.conclusion == wanted) Right(gLip2)
                 else Left(NotOfForm("the Lipschitz bound the continuity lemma asks for along the chosen points", gLip2.conclusion))
        continuous <- rules.mp(lc, gLip3)
        rBelow <- lin(Seq(hR), "-(R:real) <= R")
        attains <- specR(fact(Continuity.AttainsMinimumWithin), Right(gFun), Right(lo), Right(rr)).flatMap(mp(_, rBelow, continuous))
        out <- choose(attains, "x0") { (x0, held) =>
          for {
            parts <- split(held)
            least = parts(2)
            // the point
            zT <- cx(s"COMPLEX ${x0.name} ((g:real->real) ${x0.name})")
            hx <- assume(inR("x:real"))
            hy <- assume(inR("y:real"))
            atX <- spec(least, x).flatMap(rules.mp(_, hx))
            cx0 <- spec(hg, x).flatMap(rules.mp(_, hx)).flatMap(split)
            atY <- spec(cx0(2), y).flatMap(rules.mp(_, hy))
            le <- lin(Seq(atX, atY), s"${h(x0.name, s"(g:real->real) ${x0.name}")} <= ${h("x:real", "y:real")}")
            bothXY <- prop(s"${inR("x:real")} /\\ ${inR("y:real")}")
            general <- for {
              assumed <- LogicError.lift(Kernel.assume(bothXY))
              ps <- split(assumed)
              a1 <- conj(ps(0), ps(1))
              a2 <- conj(ps(2), ps(3))
              d <- rules.disch(hy.conclusion, le).flatMap(rules.disch(hx.conclusion, _))
              o <- rules.mp(d, a1).flatMap(rules.mp(_, a2))
              back <- rules.disch(bothXY, o).flatMap(gen(_, x, y))
            } yield back
            ex <- existsIntro(
              s"?z:complex. !x:real. !y:real. ${inR("x")} /\\ ${inR("y")} ==> complex_norm (${poly("c:num->complex", "n:num", "z")}) <= ${h("x", "y")}",
              zT, general)
          } yield ex
        }
        done <- disch(choice, out).flatMap(disch("0 <= (R:real)", _)).flatMap(gen(_, c, n, rr, g))
      } yield done
    }

    /** The least modulus on the square, with the choice of `g` made by `select`. */
    def squareMinimum(core: Kernel.Thm): R[Kernel.Thm] =
      for {
        hR <- assume("0 <= (R:real)")
        hx <- assume(inR("x:real"))
        // on the vertical line through x the modulus is continuous and has a least value
        yFun <- term(s"\\y:real. ${h("x:real", "y")}", Functions)
        lo <- re("-(R:real)")
        lT <- re(bound)
        sT <- re("(R:real) + R + 1")
        sNonneg <- lin(Seq(hR), "0 <= (R:real) + R + 1")
        sn <- nm("SUC (n:num)")
        lNonneg <- spec(k("BOUND_NONNEG"), c, sT).flatMap(rules.mp(_, sNonneg)).flatMap(spec(_, sn))
        lc <- spec(k("LIPSCHITZ_CONTINUOUS"), yFun, lo, rr, lT).flatMap(rules.mp(_, lNonneg))
        wanted <- logic.destImp(lc.conclusion).map(_._1).toRight(NotOfForm("an implication", lc.conclusion))
        lineLip <- {
          val y1 = Term.variable("y1", Reals)
          val y2 = Term.variable("y2", Reals)
          for {
            bothT <- prop(s"${inR("y1:real")} /\\ ${inR("y2:real")}")
            assumed <- LogicError.lift(Kernel.assume(bothT))
            ps <- split(assumed)
            a1 <- conj(ps(0), ps(1))
            a2 <- conj(ps(2), ps(3))
            l <- spec(k("SQUARE_LIPSCHITZ"), x, y1, x, y2).flatMap(mp(_, hx, a1, hx, a2))
            self <- absSelf("x:real")
            ls <- Limit.rewriteInProposition(self, l)
            out <- lin(Seq(ls), s"abs (${h("x:real", "y1:real")} - ${h("x:real", "y2:real")}) <= $bound * abs (y1 - y2)")
            back <- rules.disch(bothT, out).flatMap(gen(_, y1, y2))
          } yield back
        }
        lineLip2 <- if (lineLip.conclusion == wanted) Right(lineLip)
                    else Left(NotOfForm("the Lipschitz bound the continuity lemma asks for along a vertical line", lineLip.conclusion))
        continuous <- rules.mp(lc, lineLip2)
        rBelow <- lin(Seq(hR), "-(R:real) <= R")
        attains <- specR(fact(Continuity.AttainsMinimumWithin), Right(yFun), Right(lo), Right(rr)).flatMap(mp(_, rBelow, continuous))
        // the chosen point, by select
        chosen <- classical.witness(attains).flatMap(beta)
        predicate <- logic.destExistsPredicate(attains.conclusion).toRight(NotOfForm("an existential", attains.conclusion))
        selectConst <- LogicError.lift(theory.constant(Classical.Select, Type.fun(Type.fun(Reals, Type.Bool), Reals)))
        selected <- LogicError.lift(Term.app(selectConst, predicate))
        gTerm <- LogicError.lift(Term.abs(x, selected))
        forX <- rules.disch(hx.conclusion, chosen).flatMap(rules.gen(x, _))
        inst <- spec(core, c, n, rr, gTerm)
        // the core, at that g, reduced
        afterR <- rules.mp(inst, hR)
        wantedChoice <- logic.destImp(afterR.conclusion).map(_._1).toRight(NotOfForm("an implication", afterR.conclusion))
        forX2 <- if (forX.conclusion == wantedChoice) Right(forX)
                 else Left(NotOfForm("the choice of a least point on each vertical line, as the square's lemma asks for it", forX.conclusion))
        out <- rules.mp(afterR, forX2)
        done <- rules.disch(hR.conclusion, out).flatMap(gen(_, c, n, rr))
      } yield done

    /** The modulus of a polynomial of degree at least one has a least value over the plane. */
    def globalMinimum: R[Kernel.Thm] = {
      val P = (t: String) => poly("c:num->complex", "SUC (m:num)", t)
      for {
        hT <- prop("~((c:num->complex) (SUC (m:num)) = complex_of_real 0)")
        h0 <- LogicError.lift(Kernel.assume(hT))
        gr <- spec(k("GROWTH"), c, m).flatMap(rules.mp(_, h0))
        out <- choose(gr, "R0") { (r0, held) =>
          val R0 = r0.name
          for {
            parts <- split(held)
            r1 = parts(0)
            grow = parts(1)
            r0Nonneg <- lin(Seq(r1), s"0 <= ($R0:real)")
            sm <- nm("SUC (m:num)")
            sq <- spec(k("SQUARE_MINIMUM"), c, sm, r0).flatMap(rules.mp(_, r0Nonneg))
            found <- choose(sq, "z0") { (z0, least) =>
              val Z0 = z0.name
              val goal = s"complex_norm (${P(Z0)}) <= complex_norm (${P("w:complex")})"
              for {
                zeroIn <- lin(Seq(r0Nonneg), s"-($R0:real) <= (0:real) /\\ (0:real) <= $R0 /\\ -$R0 <= (0:real) /\\ (0:real) <= $R0")
                zero <- re("0:real")
                at00 <- spec(least, zero, zero).flatMap(rules.mp(_, zeroIn))
                ofReal = definitions(Complex.OfReal)
                unf <- Conv.unfold(ofReal, List(zero)).flatMap(Conv.sym)
                at0 <- rw(unf, at00)
                atZ <- spec(k("AT_ZERO"), c, sm)
                at <- rw(atZ, at0)
                proved <- cases(s"($R0:real) <= complex_norm (w:complex)")(
                  far => for {
                    bigger <- spec(grow, w).flatMap(rules.mp(_, far))
                    o <- lin(Seq(at, bigger), goal)
                  } yield o,
                  near => for {
                    nT <- re("complex_norm (w:complex)")
                    lt <- specR(fact("LT_OF_NOT_LE"), Right(r0), Right(nT)).flatMap(rules.mp(_, near))
                    rb <- spec(k("RE_BELOW_NORM"), w)
                    ib <- spec(k("IM_BELOW_NORM"), w)
                    reW <- re("Re (w:complex)")
                    imW <- re("Im (w:complex)")
                    ra <- specR(fact("ABS_ABOVE"), Right(reW))
                    rn <- specR(fact("ABS_ABOVE_NEG"), Right(reW))
                    ia <- specR(fact("ABS_ABOVE"), Right(imW))
                    in <- specR(fact("ABS_ABOVE_NEG"), Right(imW))
                    inSq <- lin(Seq(lt, rb, ib, ra, rn, ia, in),
                      s"-($R0:real) <= Re (w:complex) /\\ Re w <= $R0 /\\ -$R0 <= Im w /\\ Im w <= $R0")
                    atW <- spec(least, reW, imW).flatMap(rules.mp(_, inSq))
                    surj <- specR(fact(Complex.Surjective), Right(w)).flatMap(Conv.sym)
                    o <- rw(surj, atW)
                  } yield o
                )
                all <- rules.gen(w, proved)
                ex <- existsIntro(s"?z:complex. !w:complex. complex_norm (${P("z")}) <= complex_norm (${P("w")})", z0, all)
              } yield ex
            }
          } yield found
        }
        done <- rules.disch(hT, out).flatMap(gen(_, c, m))
      } yield done
    }



    val b: FVar = Term.variable("b", Coefficients)
    val a: FVar = Term.variable("a", Complexes)
    val r: FVar = Term.variable("r", Numbers)
    val m: FVar = Term.variable("m", Numbers)
    val p: FVar = Term.variable("p", Numbers)
    val j: FVar = Term.variable("j", Numbers)
    val i: FVar = Term.variable("i", Numbers)
    val sumF: FVar = Term.variable("f", Coefficients)

    def atComplex(thm: Kernel.Thm): Kernel.Thm = Kernel.instType(Map(Classical.TypeVariable -> Complexes), thm)

    /** `holds` is the predicate of `?x. P x` at `witness`, beta-normal; the existential is returned. */
    def exists(text: String, witness: Term, holds: Kernel.Thm): R[Kernel.Thm] =
      for {
        statement <- Parser.proposition(theory, notation, text)
        predicate <- logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement))
        applied <- LogicError.lift(Term.app(predicate, witness))
        root <- Conv.betaRoot(applied)
        expected <- Term.destEq(root.conclusion).map(_._2).toRight(NotOfForm("an equation", root.conclusion))
        normalEq <- Conv.betaNormalise(expected)
        back <- Conv.sym(normalEq)
        reached <- LogicError.lift(Kernel.eqMp(back, holds))
        out <- rules.existsIntro(predicate, witness, reached)
      } yield out

    /** `complex_sum f (m + r) = complex_sum f m + complex_sum (\i. f (m + i)) r`. */
    def splitSum: R[Kernel.Thm] =
      for {
        body <- prop("complex_sum (f:num->complex) ((m:num) + (r:num)) = complex_sum f m + complex_sum (\\i:num. f (m + i)) r")
        addZero <- fact("NUM_ADD_ZERO")
        addSuc <- fact("NUM_ADD_SUC")
        proved <- induct(r, body)(
          base => driver.using(addZero, sumZero).identity(base),
          (_, hyp, goal) => driver.using(addSuc, sumSuc).from(hyp).flatMap(_.identity(goal))
        )
        out <- gen(proved, sumF, m)
      } yield out

    /** A sum whose terms past the first vanish is its first term. */
    def onlyFirst: R[Kernel.Thm] =
      for {
        body <- prop("(!j:num. 0 < j /\\ j < SUC (m:num) ==> (f:num->complex) j = complex_of_real 0) ==> complex_sum f (SUC m) = f 0")
        ltTrans <- fact("NUM_LT_TRANS")
        ltSuc <- fact("NUM_LT_SUC")
        zeroLt <- fact("NUM_ZERO_LT_SUC")
        proved <- induct(m, body)(
          base => underHyps(base)((_, g) => driver.using(sumSuc, sumZero).identity(g)),
          (kk, hyp, goal) => underHyps(goal) { (hs, g) =>
            val K = kk.name
            for {
              weaker <- for {
                hjT <- prop(s"0 < (j:num) /\\ j < SUC $K")
                hj <- LogicError.lift(Kernel.assume(hjT))
                parts <- split(hj)
                sk <- nm(s"SUC $K")
                ssk <- nm(s"SUC (SUC $K)")
                lt <- spec(ltSuc, sk)
                further <- spec(ltTrans, j, sk, ssk).flatMap(t => conj(parts(1), lt).flatMap(rules.mp(t, _)))
                both <- conj(parts(0), further)
                out <- spec(hs(0), j).flatMap(rules.mp(_, both))
                back <- rules.disch(hjT, out).flatMap(rules.gen(j, _))
              } yield back
              ih <- rules.mp(hyp, weaker)
              sk <- nm(s"SUC $K")
              top <- for {
                pos <- spec(zeroLt, kk)
                lt <- spec(ltSuc, sk)
                both <- conj(pos, lt)
                out <- spec(hs(0), sk).flatMap(rules.mp(_, both))
              } yield out
              out <- driver.using(sumSuc).from(ih, top).flatMap(_.identity(g))
            } yield out
          }
        )
        out <- gen(proved, sumF)
      } yield out


    /** `SUC n = k + SUC (n - k)` for `k <= n`. */
    def lengths(kT: Term, nT: Term, le: Kernel.Thm): R[Kernel.Thm] =
      for {
        subAdd <- specR(fact("NUM_SUB_ADD"), Right(nT), Right(kT)).flatMap(rules.mp(_, le))
        dT <- LogicError.lift(theory.constant("NUM_SUB", Type.fun(Numbers, Type.fun(Numbers, Numbers))))
          .flatMap(s => LogicError.lift(Term.app(s, nT)).flatMap(x => LogicError.lift(Term.app(x, kT))))
        addSuc <- specR(fact("NUM_ADD_SUC"), Right(kT), Right(dT))
        sym <- specR(fact("NUM_ADD_SYM"), Right(kT), Right(dT))
        inner <- Conv.trans(sym, subAdd)
        suc <- LogicError.lift(theory.constant("SUC", Type.fun(Numbers, Numbers)))
        lifted <- Conv.apTerm(suc, inner)
        joined <- Conv.trans(addSuc, lifted)
        out <- Conv.sym(joined)
      } yield out

    /**
     * At the least `SUC p` past zero where a coefficient survives, the polynomial is its constant term
     * plus `w^(SUC p)` times the polynomial of the coefficients from there on.
     */
    val decomposeText: String =
      s"SUC (p:num) <= (n:num) ==> (!j:num. 0 < j /\\ j < SUC p ==> (b:num->complex) j = complex_of_real 0) ==> " +
        s"${poly("b", "n", "w:complex")} = b 0 + complex_pow w (SUC p) * ${sum("\\i:num. b (SUC p + i)", "w", "SUC (NUM_SUB n (SUC p))")}"

    def decompose(splitT: Kernel.Thm, onlyFirstT: Kernel.Thm): R[Kernel.Thm] =
      for {
        goal <- prop(decomposeText)
        out <- underHyps(goal) { (hs, g) =>
          for {
            sp <- nm("SUC (p:num)")
            len <- lengths(sp, n, hs(0))
            fT <- term(s"\\k:num. (b:num->complex) k * complex_pow (w:complex) k", Coefficients)
            summation <- LogicError.lift(theory.constant(Complex.Summation, Type.fun(Coefficients, Type.fun(Numbers, Complexes))))
            sumOfF <- LogicError.lift(Term.app(summation, fT))
            reLen <- Conv.apTerm(sumOfF, len)
            dT <- nm("SUC (NUM_SUB (n:num) (SUC (p:num)))")
            parts <- spec(splitT, fT, sp, dT)
            whole <- Conv.trans(reLen, parts)
            // the head: every term past the first vanishes
            headZero <- for {
              hjT <- prop("0 < (j:num) /\\ j < SUC (p:num)")
              hj <- LogicError.lift(Kernel.assume(hjT))
              zero <- spec(hs(1), j).flatMap(rules.mp(_, hj))
              out <- identity("(b:num->complex) j * complex_pow (w:complex) j = complex_of_real 0", zero)
              back <- rules.disch(hjT, out).flatMap(rules.gen(j, _))
            } yield back
            head <- spec(onlyFirstT, fT, p).flatMap(rules.mp(_, headZero))
            head0 <- identity("(b:num->complex) 0 * complex_pow (w:complex) 0 = b 0", powZero)
            // the tail: w^(SUC p + i) = w^(SUC p) * w^i
            powAdd <- fact("COMPLEX_POW_ADD")
            pointwise <- identity("(b:num->complex) (SUC (p:num) + i) * complex_pow (w:complex) (SUC p + i) = " +
              "complex_pow w (SUC p) * (b (SUC p + i) * complex_pow w i)", powAdd)
            tailCong <- sumCong(i, pointwise, dT)
            gT <- term("\\i:num. (b:num->complex) (SUC (p:num) + i) * complex_pow (w:complex) i", Coefficients)
            wp <- cx("complex_pow (w:complex) (SUC (p:num))")
            scaled <- spec(k("SCALE"), wp, gT, dT)
            e1 <- rw(head, whole).flatMap(rw(head0, _))
            e2 <- beta(tailCong).flatMap(t => rw(t, e1)).flatMap(rw(scaled, _))
            out <- if (e2.conclusion == g) Right(e2) else
              Left(NotOfForm("the polynomial as its constant term plus the rest from the least surviving index on", e2.conclusion))
          } yield out
        }
        done <- gen(out, b, n, p, w)
      } yield done

    /** `complex_sum (\i. a * u i) n = a * complex_sum u n`. */
    def scale: R[Kernel.Thm] = {
      val u = Term.variable("u", Coefficients)
      for {
        body <- prop("complex_sum (\\i:num. (a:complex) * (u:num->complex) i) (n:num) = a * complex_sum u n")
        proved <- induct(n, body)(
          base => driver.using(sumZero).identity(base),
          (_, hyp, goal) => driver.using(sumSuc).from(hyp).flatMap(_.identity(goal))
        )
        out <- gen(proved, a, u)
      } yield out
    }

    /* ------------------------------------------------------------------ the shift */

    def shiftBody(nT: String): String =
      s"!c:num->complex. ?b:num->complex. b ($nT) = c ($nT) /\\ (!j:num. ($nT) < j ==> b j = complex_of_real 0) /\\ " +
        s"(!w:complex. ${poly("c", nT, "(a:complex) + w")} = ${poly("b", nT, "w")})"

    def shift: R[Kernel.Thm] =
      for {
        body <- prop(shiftBody("n:num"))
        condTrue <- fact("COND_TRUE").map(atComplex)
        condFalse <- fact("COND_FALSE").map(atComplex)
        preSuc <- fact("NUM_PRE_SUC")
        sucNotZero <- fact("NUM_SUC_NOT_ZERO")
        ltIrrefl <- fact("NUM_LT_IRREFL")
        notLtZero <- fact("NUM_NOT_LT_ZERO")
        ltSuc <- fact("NUM_LT_SUC")
        ltTrans <- fact("NUM_LT_TRANS")
        ltSucCases <- fact("NUM_LT_SUC_CASES")
        numCases <- fact("NUM_CASES")
        zeroN <- nm("0")
        zeroZero = Conv.refl(zeroN)
        proved <- induct(n, body)(
          base => {
            val bT = "\\j:num. COND (j = 0) ((c:num->complex) 0) (complex_of_real 0)"
            for {
              witness <- term(bT, Coefficients)
              cond0 <- prop("COND ((0:num) = 0) ((c:num->complex) 0) (complex_of_real 0) = c 0").flatMap { _ =>
                for {
                  c0 <- cx("(c:num->complex) 0")
                  z0 <- cx("complex_of_real 0")
                  eq0 <- prop("(0:num) = 0")
                  t <- spec(condTrue, eq0, c0, z0).flatMap(rules.mp(_, zeroZero))
                } yield t
              }
              above <- for {
                hjT <- prop("0 < (j:num)")
                hj <- LogicError.lift(Kernel.assume(hjT))
                eqT <- prop("(j:num) = 0")
                notZero <- for {
                  e <- LogicError.lift(Kernel.assume(eqT))
                  moved <- Limit.rewriteInProposition(e, hj)
                  absurd <- spec(ltIrrefl, zeroN).flatMap(rules.notElim(_, moved))
                  out <- rules.notIntro(eqT, absurd)
                } yield out
                c0 <- cx("(c:num->complex) 0")
                z0 <- cx("complex_of_real 0")
                out <- spec(condFalse, eqT, c0, z0).flatMap(rules.mp(_, notZero))
                back <- rules.disch(hjT, out).flatMap(rules.gen(j, _))
              } yield back
              same <- identity(s"${poly("c:num->complex", "0", "(a:complex) + (w:complex)")} = ${poly(bT, "0", "w")}", sumSuc, sumZero, powZero, cond0)
              sameEverywhere <- rules.gen(w, same)
              all <- conjs(cond0, above, sameEverywhere)
              ex <- exists(s"?b:num->complex. b 0 = (c:num->complex) 0 /\\ (!j:num. 0 < j ==> b j = complex_of_real 0) /\\ " +
                s"(!w:complex. ${poly("c", "0", "(a:complex) + w")} = ${poly("b", "0", "w")})", witness, all)
              out <- rules.gen(c, ex)
            } yield out
          },
          (kk, hyp, goal) => {
            val K = kk.name
            for {
              shifted <- term("\\j:num. (c:num->complex) (SUC j)", Coefficients)
              ih <- spec(hyp, shifted)
              out <- choose(ih, "b1") { (b1, held) =>
                val B1 = s"(${b1.name}:num->complex)"
                val bT = s"\\j:num. COND (j = 0) ((c:num->complex) 0 + (a:complex) * $B1 0) (a * $B1 j + $B1 (PRE j))"
                for {
                  parts <- split(held)
                  topEq = parts(0)
                  beyond = parts(1)
                  moved = parts(2)
                  witness <- term(bT, Coefficients)
                  sk <- nm(s"SUC $K")
                  // (i) the top coefficient
                  atTop <- for {
                    eqT <- prop(s"SUC $K = 0")
                    notZero <- spec(sucNotZero, kk)
                    x1 <- cx(s"(c:num->complex) 0 + (a:complex) * $B1 0")
                    y1 <- cx(s"(a:complex) * $B1 (SUC $K) + $B1 (PRE (SUC $K))")
                    e1 <- spec(condFalse, eqT, x1, y1).flatMap(rules.mp(_, notZero))
                    zeroTop <- spec(beyond, sk).flatMap(t => spec(ltSuc, kk).flatMap(rules.mp(t, _)))
                    pre <- spec(preSuc, kk)
                    e2 <- identity(s"(a:complex) * $B1 (SUC $K) + $B1 (PRE (SUC $K)) = (c:num->complex) (SUC $K)", zeroTop, pre, topEq)
                    out <- Conv.trans(e1, e2)
                  } yield out
                  // (ii) past the top
                  past <- for {
                    hjT <- prop(s"SUC $K < (j:num)")
                    hj <- LogicError.lift(Kernel.assume(hjT))
                    eqT <- prop("(j:num) = 0")
                    notZero <- for {
                      e <- LogicError.lift(Kernel.assume(eqT))
                      movedJ <- Limit.rewriteInProposition(e, hj)
                      absurd <- spec(notLtZero, sk).flatMap(rules.notElim(_, movedJ))
                      out <- rules.notIntro(eqT, absurd)
                    } yield out
                    x1 <- cx(s"(c:num->complex) 0 + (a:complex) * $B1 0")
                    y1 <- cx(s"(a:complex) * $B1 j + $B1 (PRE j)")
                    e1 <- spec(condFalse, eqT, x1, y1).flatMap(rules.mp(_, notZero))
                    kj <- spec(ltTrans, kk, sk, j).flatMap(t => spec(ltSuc, kk).flatMap(l => conj(l, hj)).flatMap(rules.mp(t, _)))
                    zj <- spec(beyond, j).flatMap(rules.mp(_, kj))
                    cases <- spec(numCases, j)
                    zeroCase <- for {
                      e <- assume("(j:num) = 0")
                      absurd <- rules.notElim(notZero, e)
                      g <- prop(s"$B1 (PRE (j:num)) = complex_of_real 0")
                      out <- rules.falsityElim(g, absurd)
                    } yield out
                    sucCase <- for {
                      exT <- prop("?q:num. (j:num) = SUC q")
                      ex <- LogicError.lift(Kernel.assume(exT))
                      out <- choose(ex, "q") { (q, jq) =>
                        for {
                          pre <- LogicError.lift(theory.constant("PRE", Type.fun(Numbers, Numbers))).flatMap(Conv.apTerm(_, jq))
                          preQ <- spec(preSuc, q).flatMap(Conv.trans(pre, _))
                          lt0 <- Limit.rewriteInProposition(jq, hj)
                          split0 <- spec(ltSucCases, q, sk).flatMap(rules.mp(_, lt0))
                          kq <- for {
                            ltk <- spec(ltSuc, kk)
                            l <- assume(s"SUC $K < ${q.name}").flatMap(h => spec(ltTrans, kk, sk, q).flatMap(t => conj(ltk, h).flatMap(rules.mp(t, _))))
                            rr <- assume(s"SUC $K = ${q.name}").flatMap(h => Limit.rewriteInProposition(h, ltk))
                            o <- rules.disjElim(split0, l, rr)
                          } yield o
                          zq <- spec(beyond, q).flatMap(rules.mp(_, kq))
                          o <- Conv.sym(preQ).flatMap(Limit.rewriteInProposition(_, zq))
                        } yield o
                      }
                    } yield out
                    zpre <- rules.disjElim(cases, zeroCase, sucCase)
                    e2 <- identity(s"(a:complex) * $B1 (j:num) + $B1 (PRE j) = complex_of_real 0", zj, zpre)
                    out <- Conv.trans(e1, e2).flatMap(rules.disch(hjT, _)).flatMap(rules.gen(j, _))
                  } yield out
                  // (iii) the polynomial moves with the point
                  along <- for {
                    aw <- cx("(a:complex) + (w:complex)")
                    l1 <- spec(k("HORNER"), c, aw, sk)
                    shiftedEq <- spec(moved, w)
                    l2 <- rw(shiftedEq, l1)
                    r1 <- spec(k("HORNER"), witness, w, sk)
                    c0 <- cx(s"(c:num->complex) 0 + (a:complex) * $B1 0")
                    y0 <- cx(s"(a:complex) * $B1 0 + $B1 (PRE 0)")
                    eq0 <- prop("(0:num) = 0")
                    condAt0 <- spec(condTrue, eq0, c0, y0).flatMap(rules.mp(_, zeroZero))
                    pointwise <- for {
                      eqT <- prop("SUC (i:num) = 0")
                      notZero <- spec(sucNotZero, i)
                      x1 <- cx(s"(c:num->complex) 0 + (a:complex) * $B1 0")
                      y1 <- cx(s"(a:complex) * $B1 (SUC (i:num)) + $B1 (PRE (SUC i))")
                      e1 <- spec(condFalse, eqT, x1, y1).flatMap(rules.mp(_, notZero))
                      pre <- spec(preSuc, i)
                      e2 <- identity(s"(a:complex) * $B1 (SUC (i:num)) + $B1 (PRE (SUC i)) = a * $B1 (SUC i) + $B1 i", pre)
                      eC <- Conv.trans(e1, e2)
                      mul <- LogicError.lift(theory.constant(Complex.Multiplication, Type.fun(Complexes, Type.fun(Complexes, Complexes))))
                      wi <- cx("complex_pow (w:complex) (i:num)")
                      out <- Conv.apTerm(mul, eC).flatMap(Conv.apThm(_, wi))
                    } yield out
                    cong <- sumCong(i, pointwise, sk)
                    shiftT <- term(s"\\i:num. $B1 (SUC i)", Coefficients)
                    lin0 <- spec(k("LINEAR"), a, shiftT, b1, w, sk)
                    r2 <- rw(condAt0, r1).flatMap(t => beta(cong).flatMap(rw(_, t))).flatMap(rw(lin0, _))
                    // P1 = b1 0 + w Q, by Horner and the vanishing top
                    h2 <- spec(k("HORNER"), b1, w, sk)
                    zeroTop <- spec(beyond, sk).flatMap(t => spec(ltSuc, kk).flatMap(rules.mp(t, _)))
                    tz <- spec(k("TOP_ZERO"), b1, w, kk).flatMap(rules.mp(_, zeroTop))
                    p1eq <- Conv.sym(tz).flatMap(Conv.trans(_, h2))
                    middle <- identity(s"(c:num->complex) 0 + ((a:complex) + (w:complex)) * ${poly(B1, K, "w")} = " +
                      s"(c 0 + a * $B1 0) + w * (a * ${sum(s"\\i:num. $B1 (SUC i)", "w", s"SUC $K")} + ${poly(B1, K, "w")})", p1eq)
                    joined <- Conv.trans(l2, middle).flatMap(t => Conv.sym(r2).flatMap(Conv.trans(t, _)))
                    out <- rules.gen(w, joined)
                  } yield out
                  all <- conjs(atTop, past, along)
                  ex <- exists(s"?b:num->complex. b (SUC $K) = (c:num->complex) (SUC $K) /\\ (!j:num. SUC $K < j ==> b j = complex_of_real 0) /\\ " +
                    s"(!w:complex. ${poly("c", s"SUC $K", "(a:complex) + w")} = ${poly("b", s"SUC $K", "w")})", witness, all)
                } yield ex
              }
              done <- rules.gen(c, out)
            } yield done
          }
        )
        out <- gen(proved, a)
      } yield out



    /** `0 < |t|` from `~(t = 0)`. */
    def normPositive(tText: String, notZero: Kernel.Thm): R[Kernel.Thm] =
      for {
        t <- cx(tText)
        nT <- re(s"complex_norm ($tText)")
        zT <- re("0:real")
        nonneg <- specR(fact("COMPLEX_NORM_NONNEG"), Right(t))
        leT <- prop(s"complex_norm ($tText) <= 0")
        notLe <- for {
          le <- LogicError.lift(Kernel.assume(leT))
          eq <- specR(fact("LE_ANTISYMMETRIC"), Right(nT), Right(zT)).flatMap(mp(_, le, nonneg))
          zero <- specR(fact("COMPLEX_NORM_ZERO"), Right(t)).flatMap(rules.mp(_, eq))
          absurd <- rules.notElim(notZero, zero)
          out <- rules.notIntro(leT, absurd)
        } yield out
        out <- specR(fact("LT_OF_NOT_LE"), Right(nT), Right(zT)).flatMap(rules.mp(_, notLe))
      } yield out

    val dalembertText: String =
      s"0 < (n:num) /\\ ~((c:num->complex) n = complex_of_real 0) /\\ ~(${poly("c", "n", "z:complex")} = complex_of_real 0) ==> " +
        s"?w:complex. complex_norm (${poly("c", "n", "w")}) < complex_norm (${poly("c", "n", "z")})"

    def dalembert: R[Kernel.Thm] =
      for {
        goal <- prop(dalembertText)
        out <- underHyps(goal) { (assumed, g) =>
          for {
            hs <- split(assumed(0))
            (hn, hc, hz) = (hs(0), hs(1), hs(2))
            shifted <- spec(k("SHIFT"), z, n, c)
            found <- choose(shifted, "b") { (bv, held) =>
              val B = s"(${bv.name}:num->complex)"
              for {
                parts <- split(held)
                (topEq, beyond, moved) = (parts(0), parts(1), parts(2))
                // b 0 is the value at z
                zero <- cx("complex_of_real 0")
                at0 <- spec(moved, zero)
                addZero <- specR(fact("COMPLEX_ADD_ZERO"), Right(z))
                at0b <- rw(addZero, at0)
                atZero <- spec(k("AT_ZERO"), bv, n)
                valueEq <- rw(atZero, at0b) // poly c n z = b 0
                b0NotZero <- Limit.rewriteInProposition(valueEq, hz)
                bnNotZero <- Conv.sym(topEq).flatMap(e => Limit.rewriteInProposition(e, hc))
                // the least index past zero with a coefficient that survives
                pT <- term(s"\\j:num. 0 < j /\\ ~($B j = complex_of_real 0)", Type.fun(Numbers, Type.Bool))
                least <- specR(fact("NUM_LEAST"), Right(pT))
                hasOne <- conj(hn, bnNotZero).flatMap(both =>
                  exists(s"?j:num. 0 < j /\\ ~($B j = complex_of_real 0)", n, both))
                leastAt <- rules.mp(least, hasOne)
                result <- choose(leastAt, "k") { (kv, kHeld) =>
                  val K = s"(${kv.name}:num)"
                  for {
                    kTop <- split(kHeld)
                    kParts <- split(kTop(0))
                    kPos = kParts(0)
                    bkNotZero = kParts(1)
                    minimal = kTop(1)
                    kLeN <- for {
                      ltT <- prop(s"(n:num) < $K")
                      notLt <- for {
                        lt <- LogicError.lift(Kernel.assume(ltT))
                        not <- spec(minimal, n).flatMap(rules.mp(_, lt))
                        both <- conj(hn, bnNotZero)
                        absurd <- rules.notElim(not, both)
                        out <- rules.notIntro(ltT, absurd)
                      } yield out
                      out <- specR(fact("NUM_LE_OF_NOT_LT"), Right(n), Right(kv)).flatMap(rules.mp(_, notLt))
                    } yield out
                    below <- for {
                      jv <- Right(Term.variable("j", Numbers))
                      hjT <- prop(s"0 < (j:num) /\\ j < $K")
                      hj <- LogicError.lift(Kernel.assume(hjT))
                      hjs <- split(hj)
                      not <- spec(minimal, jv).flatMap(rules.mp(_, hjs(1)))
                      out <- cases(s"$B (j:num) = complex_of_real 0")(
                        yes => Right(yes),
                        no => for {
                          both <- conj(hjs(0), no)
                          absurd <- rules.notElim(not, both)
                          g0 <- prop(s"$B (j:num) = complex_of_real 0")
                          o <- rules.falsityElim(g0, absurd)
                        } yield o
                      )
                      back <- rules.disch(hjT, out).flatMap(rules.gen(jv, _))
                    } yield back
                    // k = SUC p
                    cs <- specR(fact("NUM_CASES"), Right(kv))
                    zeroCase <- for {
                      e <- assume(s"$K = 0")
                      moved0 <- Limit.rewriteInProposition(e, kPos)
                      zN <- nm("0")
                      absurd <- specR(fact("NUM_LT_IRREFL"), Right(zN)).flatMap(rules.notElim(_, moved0))
                      o <- rules.falsityElim(g, absurd)
                    } yield o
                    sucCase <- for {
                      exT <- prop(s"?p:num. $K = SUC p")
                      ex <- LogicError.lift(Kernel.assume(exT))
                      o <- choose(ex, "p") { (pv, kEq) =>
                        for {
                          leS <- Limit.rewriteInProposition(kEq, kLeN)
                          belowS <- rw(kEq, below)
                          bkS <- Limit.rewriteInProposition(kEq, bkNotZero)
                          posS <- Limit.rewriteInProposition(kEq, kPos)
                          o <- descent(B, bv, pv, valueEq, moved, leS, belowS, bkS, posS, b0NotZero, g)
                        } yield o
                      }
                    } yield o
                    o <- rules.disjElim(cs, zeroCase, sucCase)
                  } yield o
                }
              } yield result
            }
          } yield found
        }
        done <- gen(out, c, n, z)
      } yield done

    /**
     * The descent itself, at the least index `SUC p` past zero with `b (SUC p)` not zero: a small real
     * multiple `t` of a `SUC p`-th root `u` of `-b 0 / b (SUC p)` lowers the modulus.
     */
    def descent(
      B: String,
      bv: FVar,
      pv: FVar,
      valueEq: Kernel.Thm,
      moved: Kernel.Thm,
      kLeN: Kernel.Thm,
      below: Kernel.Thm,
      bkNotZero: Kernel.Thm,
      kPos: Kernel.Thm,
      b0NotZero: Kernel.Thm,
      goal: Term
    ): R[Kernel.Thm] = {
      val P = pv.name
      val Kt = s"SUC $P"
      val d = s"\\i:num. $B (SUC $P + i)"
      val len = s"NUM_SUB (n:num) (SUC $P)"
      for {
        kT <- nm(Kt)
        root <- cx(s"complex_neg ($B 0 * complex_inv ($B ($Kt)))")
        roots <- spec(k("COMPLEX_ROOT"), root, kT).flatMap(rules.mp(_, kPos))
        out <- choose(roots, "u") { (uv, uk) =>
          val U = s"(${uv.name}:complex)"
          for {
            // b k * u^k = -b 0
            bk <- cx(s"$B ($Kt)")
            inverse <- specR(fact("COMPLEX_MUL_INVERSE"), Right(bk)).flatMap(rules.mp(_, bkNotZero))
            g1 <- identity(s"$B ($Kt) * complex_neg ($B 0 * complex_inv ($B ($Kt))) = complex_neg ($B 0 * ($B ($Kt) * complex_inv ($B ($Kt))))")
            g2 <- rw(inverse, g1)
            g3 <- identity(s"complex_neg ($B 0 * complex_of_real 1) = complex_neg ($B 0)")
            bkUk0 <- Conv.trans(g2, g3)
            bkUk <- Conv.sym(uk).flatMap(e => rw(e, bkUk0))
            // the magnitudes
            uN = s"complex_norm $U"
            sT = s"($uN + 1)"
            lText = s"Sum (\\k:num. complex_norm ($B (SUC $P + k)) * (real_of_num k * Power $sT k)) (SUC ($len))"
            aText = s"($lText * ($uN * Power ($uN) ($Kt)))"
            b0N = s"complex_norm ($B 0)"
            uNonneg <- specR(fact("COMPLEX_NORM_NONNEG"), cx(U))
            sNonneg <- lin(Seq(uNonneg), s"0 <= $sT")
            dT <- term(d, Coefficients)
            lenT <- nm(s"SUC ($len)")
            sTerm <- re(sT)
            lNonneg <- spec(k("BOUND_NONNEG"), dT, sTerm).flatMap(rules.mp(_, sNonneg)).flatMap(spec(_, lenT))
            uNT <- re(uN)
            pu <- specR(fact("POWER_NONNEG"), Right(uNT)).flatMap(rules.mp(_, uNonneg)).flatMap(spec(_, kT))
            upu <- lin(Seq(uNonneg, pu), s"0 <= $uN * Power ($uN) ($Kt)")
            aNonneg <- lin(Seq(lNonneg, upu), s"0 <= $aText")
            b0Pos <- normPositive(s"$B 0", b0NotZero)
            // t = min 1 (|b0| * inv (2 * (A + 1)))
            cText = s"(2 * ($aText + 1))"
            cPos <- lin(Seq(aNonneg), s"0 < $cText")
            cT <- re(cText)
            cNotZero <- lin(Seq(cPos), s"0 < $cText").flatMap { pos =>
              for {
                eqT <- prop(s"$cText = 0")
                o <- LogicError.lift(Kernel.assume(eqT)).flatMap(e => lin(Seq(e, pos), "F")).flatMap(rules.notIntro(eqT, _))
              } yield o
            }
            cInv <- specR(fact("MUL_INVERSE"), Right(cT)).flatMap(rules.mp(_, cNotZero))
            vPos <- specR(fact("INV_POSITIVE"), Right(cT)).flatMap(rules.mp(_, cPos))
            tT = s"($b0N * inv $cText)"
            tPos <- lin(Seq(b0Pos, vPos), s"0 < $tT")
            tEq0 <- prop(s"$tT * $cText = $b0N * ($cText * inv $cText)").flatMap(ring.prove)
            tEq <- Limit.rewriteInProposition(cInv, tEq0)
            small = s"min 1 $tT"
            oneT <- re("1:real")
            ttT <- re(tT)
            minCases <- specR(fact("MIN_CASES"), Right(oneT), Right(ttT))
            smallPos <- for {
              l <- assume(s"$small = 1").flatMap(e => lin(Seq(e), s"0 < $small"))
              r <- assume(s"$small = $tT").flatMap(e => lin(Seq(e, tPos), s"0 < $small"))
              o <- rules.disjElim(minCases, l, r)
            } yield o
            smallLe1 <- specR(fact("MIN_BELOW_LEFT"), Right(oneT), Right(ttT))
            smallLeT <- specR(fact("MIN_BELOW_RIGHT"), Right(oneT), Right(ttT))
            smallT <- re(small)
            aT <- re(aText)
            aa <- lin(Nil, s"$aText <= $aText")
            smallNonneg <- lin(Seq(smallPos), s"0 <= $small")
            tA <- spec(k("MUL_LE"), smallT, ttT, aT, aT).flatMap(mp(_, smallNonneg, smallLeT, aNonneg, aa))
            gap <- lin(Seq(tA, tEq, tPos, aNonneg), s"0 < $b0N - $small * $aText")
            // the point
            wText = s"(complex_of_real ($small) * $U)"
            wT <- cx(wText)
            nmW <- specR(fact("COMPLEX_NORM_MUL"), cx(s"complex_of_real ($small)"), cx(U))
            nrT <- spec(k("COMPLEX_NORM_OF_REAL"), smallT)
            absT <- specR(fact("ABS_OF_NONNEG"), Right(smallT)).flatMap(rules.mp(_, smallNonneg))
            normW <- rw(nrT, nmW).flatMap(rw(absT, _)) // |w| = t * |u|
            wLeS <- for {
              uu <- lin(Nil, s"$uN <= $uN")
              m <- spec(k("MUL_LE"), smallT, oneT, uNT, uNT).flatMap(mp(_, smallNonneg, smallLe1, uNonneg, uu))
              o <- lin(Seq(normW, m), s"complex_norm $wText <= $sT")
            } yield o
            zero <- cx("complex_of_real 0")
            zeroR <- re("0:real")
            zeroNorm <- spec(k("COMPLEX_NORM_OF_REAL"), zeroR).flatMap(t => rw(absZero, t))
            zeroLeS <- lin(Seq(zeroNorm, sNonneg), s"complex_norm (complex_of_real 0) <= $sT")
            oneLeS <- lin(Seq(uNonneg), s"1 <= $sT")
            lip <- spec(k("LIPSCHITZ"), dT, wT, zero, sTerm, lenT).flatMap(mp(_, wLeS, zeroLeS, oneLeS))
            subZero <- identity(s"$wText - complex_of_real 0 = $wText")
            lenN <- nm(len)
            atZ <- spec(k("AT_ZERO"), dT, lenN)
            addZeroN <- specR(fact("NUM_ADD_ZERO"), nm(Kt))
            atZ2 <- rw(addZeroN, atZ) // s(0) = b k
            lip2 <- rw(subZero, lip).flatMap(rw(atZ2, _)).flatMap(rw(normW, _))
            // the polynomial at w
            dec <- spec(k("DECOMPOSE"), bv, n, pv, wT).flatMap(mp(_, kLeN, below))
            // w^k = complex_of_real (t^k) * u^k
            mp1 <- specR(fact("COMPLEX_MUL_POW"), cx(s"complex_of_real ($small)"), cx(U), Right(kT))
            por <- specR(fact("COMPLEX_POW_OF_REAL"), Right(smallT), Right(kT))
            wk <- rw(por, mp1)
            dec2 <- rw(wk, dec)
            // regroup: b0 + (T u^k) s = b0 + T (b k u^k) + (T u^k) (s - b k)
            vB0 = Term.variable("B0", Complexes)
            vBK = Term.variable("BK", Complexes)
            vTT = Term.variable("TT", Complexes)
            vUK = Term.variable("UK", Complexes)
            vSS = Term.variable("SS", Complexes)
            generic <- identity("(B0:complex) + ((TT:complex) * (UK:complex)) * (SS:complex) = B0 + TT * ((BK:complex) * UK) + (TT * UK) * (SS - BK)")
            sOfW <- cx(sum(d, wText, s"SUC ($len)"))
            b0 <- cx(s"$B 0")
            tPow <- cx(s"complex_of_real (Power ($small) ($Kt))")
            ukT <- cx(s"complex_pow $U ($Kt)")
            regroup <- LogicError.lift(Kernel.inst(Map(vB0 -> b0, vBK -> bk, vTT -> tPow, vUK -> ukT, vSS -> sOfW), generic))
            regroup2 <- rw(bkUk, regroup)
            vX = Term.variable("X", Reals)
            generic2 <- identity("(B0:complex) + complex_of_real (X:real) * complex_neg B0 = complex_of_real (1 - X) * B0")
            tkT <- re(s"Power ($small) ($Kt)")
            collapse <- LogicError.lift(Kernel.inst(Map(vB0 -> b0, vX -> tkT), generic2))
            regroup3 <- rw(collapse, regroup2)
            shape <- Conv.trans(dec2, regroup3) // p(b, n, w) = (1 - t^k) b0 + (T u^k)(s - bk)
            // the estimate
            aPartText = s"complex_of_real (1 - Power ($small) ($Kt)) * $B 0"
            bPartText = s"(complex_of_real (Power ($small) ($Kt)) * complex_pow $U ($Kt)) * (${sum(d, wText, s"SUC ($len)")} - $B ($Kt))"
            aPart <- cx(aPartText)
            bPart <- cx(bPartText)
            tri <- spec(k("COMPLEX_NORM_TRIANGLE"), aPart, bPart)
            normMul <- fact("COMPLEX_NORM_MUL")
            tri2 <- rw(normMul, tri).flatMap(rw(k("COMPLEX_NORM_OF_REAL"), _)).flatMap(rw(k("COMPLEX_NORM_POW"), _))
            tkLe1 <- for {
              l <- spec(k("POW_LE"), smallT, oneT, kT).flatMap(mp(_, smallNonneg, smallLe1))
              one <- specR(fact("POWER_ONE"), Right(kT))
              o <- lin(Seq(l, one), s"Power ($small) ($Kt) <= 1")
            } yield o
            tkPos <- specR(fact("POWER_POSITIVE"), Right(smallT)).flatMap(rules.mp(_, smallPos)).flatMap(spec(_, kT))
            oneMinus <- re(s"1 - Power ($small) ($Kt)")
            absOneMinus <- lin(Seq(tkLe1), s"0 <= 1 - Power ($small) ($Kt)").flatMap(h =>
              specR(fact("ABS_OF_NONNEG"), Right(oneMinus)).flatMap(rules.mp(_, h)))
            tkNonneg <- lin(Seq(tkPos), s"0 <= Power ($small) ($Kt)")
            absTk <- specR(fact("ABS_OF_NONNEG"), Right(tkT)).flatMap(rules.mp(_, tkNonneg))
            tri3 <- rw(absOneMinus, tri2).flatMap(rw(absTk, _))
            // |s(w) - bk| <= L * (t * |u|), scaled by t^k |u|^k
            pk <- specR(fact("POWER_NONNEG"), Right(uNT)).flatMap(rules.mp(_, uNonneg)).flatMap(spec(_, kT))
            factorT <- re(s"Power ($small) ($Kt) * Power ($uN) ($Kt)")
            factor0 <- lin(Seq(tkNonneg, pk), s"0 <= Power ($small) ($Kt) * Power ($uN) ($Kt)")
            ff <- lin(Nil, s"Power ($small) ($Kt) * Power ($uN) ($Kt) <= Power ($small) ($Kt) * Power ($uN) ($Kt)")
            sDiffN <- re(s"complex_norm ($sOfW - $B ($Kt))")
            sDiff0 <- specR(fact("COMPLEX_NORM_NONNEG"), cx(s"$sOfW - $B ($Kt)"))
            boundT <- re(s"$lText * ($small * $uN)")
            scaled <- spec(k("MUL_LE"), factorT, factorT, sDiffN, boundT).flatMap(mp(_, factor0, ff, sDiff0, lip2))
            product <- lemma("!p:real. !q:real. 0 < p ==> 0 < q ==> 0 < p * q")
            qT <- re(s"$b0N - $small * $aText")
            pq <- spec(product, tkT, qT).flatMap(mp(_, tkPos, gap))
            parts0 <- lin(Seq(tri3, scaled, pq), s"complex_norm ($aPartText + $bPartText) < $b0N")
            estimate <- Conv.sym(shape).flatMap(rw(_, parts0))
            // back to c, at z + w
            at <- spec(moved, wT)
            back <- Conv.sym(at).flatMap(e => rw(e, estimate))
            norm <- LogicError.lift(theory.constant(Complex.Norm, Type.fun(Complexes, Reals)))
            normEq <- Conv.apTerm(norm, valueEq)
            rhs <- re(s"complex_norm (${poly("c:num->complex", "n:num", "z:complex")})")
            goalT <- back.conclusion match {
              case App(lt, _) => LogicError.lift(Term.app(lt, rhs))
              case other => Left(NotOfForm("an inequality", other))
            }
            final0 <- linT(Seq(back, normEq), goalT)
            witness <- cx(s"(z:complex) + $wText")
            o <- exists(s"?w:complex. complex_norm (${poly("c:num->complex", "n:num", "w")}) < complex_norm (${poly("c", "n", "z:complex")})", witness, final0)
          } yield o
        }
      } yield out
    }

    /** A root, at a degree written `SUC m`: the least value of the modulus is zero, by d'Alembert. */
    def rootAtSuccessor: R[Kernel.Thm] =
      for {
        hT <- prop("~((c:num->complex) (SUC (m:num)) = complex_of_real 0)")
        cm <- LogicError.lift(Kernel.assume(hT))
        least <- spec(k("GLOBAL_MINIMUM"), c, m).flatMap(rules.mp(_, cm))
        found <- choose(least, "z0") { (z0, atLeast) =>
          val Z0 = z0.name
          val goal = s"?z:complex. ${poly("c:num->complex", "SUC (m:num)", "z")} = complex_of_real 0"
          cases(s"${poly("c:num->complex", "SUC (m:num)", s"$Z0:complex")} = complex_of_real 0")(
            yes => exists(goal, z0, yes),
            no => for {
              sm <- nm("SUC (m:num)")
              pos <- specR(fact("NUM_ZERO_LT_SUC"), Right(m))
              hyps <- conjs(pos, cm, no)
              lower <- spec(k("DALEMBERT"), c, sm, z0).flatMap(rules.mp(_, hyps))
              g <- prop(goal)
              o <- choose(lower, "w1") { (w1, smaller) =>
                for {
                  notSmaller <- spec(atLeast, w1)
                  absurd <- lin(Seq(smaller, notSmaller), "F")
                  o <- rules.falsityElim(g, absurd)
                } yield o
              }
            } yield o
          )
        }
        out <- rules.disch(hT, found).flatMap(gen(_, c, m))
      } yield out

    /**
     * `!c n. 0 < n /\ ~(c n = 0) ==> Q n` from the same claim at `SUC m` with `~(c (SUC m) = 0)`:
     * `n` is not zero, so it is a successor, and the claim is read back at `n`.
     */
    def fromSuccessor(text: String, atSuccessor: Kernel.Thm): R[Kernel.Thm] =
      for {
        statement <- prop(text)
        stripped <- Logic.stripForall(statement)
        (bound, body) = stripped
        parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
        (hT, goal) = parts
        h <- LogicError.lift(Kernel.assume(hT))
        hs <- split(h)
        nv <- bound.lift(1).toRight(NotOfForm("a claim about a degree", statement))
        cv <- bound.headOption.toRight(NotOfForm("a claim about coefficients", statement))
        cs <- specR(fact("NUM_CASES"), Right(nv))
        zeroCase <- for {
          eqT <- logic.destDisj(cs.conclusion).map(_._1).toRight(NotOfForm("a disjunction", cs.conclusion))
          e <- LogicError.lift(Kernel.assume(eqT))
          moved <- Limit.rewriteInProposition(e, hs(0))
          zN <- nm("0")
          absurd <- specR(fact("NUM_LT_IRREFL"), Right(zN)).flatMap(rules.notElim(_, moved))
          o <- rules.falsityElim(goal, absurd)
        } yield o
        sucCase <- for {
          exT <- logic.destDisj(cs.conclusion).map(_._2).toRight(NotOfForm("a disjunction", cs.conclusion))
          ex <- LogicError.lift(Kernel.assume(exT))
          o <- choose(ex, "m") { (mv, nEq) =>
            for {
              cm <- Limit.rewriteInProposition(nEq, hs(1))
              reached <- spec(atSuccessor, cv, mv).flatMap(rules.mp(_, cm))
              back <- Conv.sym(nEq).flatMap(rw(_, reached))
            } yield back
          }
        } yield o
        both <- rules.disjElim(cs, zeroCase, sucCase)
        out <- rules.disch(hT, both).flatMap(gen(_, bound*))
      } yield out
  }
}
