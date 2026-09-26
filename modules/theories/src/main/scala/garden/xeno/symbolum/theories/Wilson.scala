package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Wilson's theorem on `num`, and the lemma about products over paired indices it was waiting on.
 *
 * {{{
 *   NUM_WILSON       !p. NUM_PRIME p ==> NUM_DIVIDES p (SUC (NUM_FACT (PRE p)))
 *   NUM_PROD_PAIRED  !m f t n. <t is an involution of [0, n) with no fixed point> ==>
 *                      (!i. i < n ==> NUM_CONG m (f i * f (t i)) (SUC 0)) ==>
 *                      NUM_CONG m (NUM_PROD f n) (SUC 0)
 * }}}
 *
 * `(p - 1)! = -1 (mod p)`, written without a negative, since `num` has none.
 *
 * Not a development: it declares nothing, and `Primes` publishes both facts under names it
 * declares, the arrangement `Euler` has.
 *
 * == Why a permutation was not enough ==
 *
 * `NUM_PROD_PERMUTE`, which `Euler` needed, says a product survives a reindexing. Multiplying the
 * residues by their inverses reindexes them, and all that gives is `P * P = 1 (mod p)`, which does
 * not say which square root of one `P` is. The classical argument **pairs** each residue with its
 * inverse, and what it needs is that a product over indices an involution splits into pairs is the
 * product of the pairs. That lemma was not here, and since there are no finite sets it is written
 * over a function `t` on `[0, n)` that is its own inverse and moves every index.
 *
 * == The pairing, by strong induction on the length ==
 *
 * At length zero the product is one, and length one has no fixed-point-free involution. At
 * `SUC (SUC w)` the top index `SUC w` is paired with `k = t (SUC w)`, and the swap `s` of `k` and `w`
 * brings the pair to the top two places: `NUM_PROD_PERMUTE` leaves the product alone, the two top
 * factors multiply to one, and `s o t o s` is a fixed-point-free involution of `[0, w)` under which
 * the rest pairs off, so the claim at `w` applies. The induction quantifies `f` and `t` inside the
 * claim, since the step needs it at a different pair of functions.
 *
 * == Wilson, from the pairing ==
 *
 * `p = 2` is a computation. For `p = n + 3`, `(p - 1)!` is `M * (p - 1)` with `M` the product of
 * the residues `2 .. p - 2`, which is `NUM_PROD (\i. SUC (SUC i)) n`. Each `u` there has an inverse
 * `v` in the same range: it is `NUM_MOD` of the one `NUM_INVERSE` gives, chosen with `select`, and
 * it is neither `0`, `1` nor `p - 1`, because each of those would make `u` itself `0`, `1` or
 * `p - 1`. Distinct from `u`, because `u * u = 1` would make `p` divide `(u - 1) * (u + 1)`, which
 * Euclid refuses. And the inverse of `v` is `u`, because an inverse is unique modulo `p`. So the
 * pairing gives `M = 1`, and `(p - 1)! + 1 = p - 1 + 1 = p = 0`.
 *
 * == What it found ==
 *
 *   - **The pairing lemma was missing**, the carenza the card that asked for this predicted.
 *   - **`SUC a < SUC b` from `a < b` was missing**, the strict half of what `Pigeonhole` found for
 *     `<=`; it is two lines through `NUM_ADD_LT_MONOTONE` here and not published.
 *   - **SEMIRING reads `SUC x` as an atom.** Every identity with a successor in it is rewritten with
 *     `SUC x = x + 1` first, which terminates because the `1` it writes is a numeral.
 */
private[theories] object Wilson {

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Fun: Type = Type.fun(Num, Num)

  /** The variables this derivation's texts use. `t` is a function here, the involution. */
  private val Types: Map[String, Type] =
    List("m", "n", "w", "k", "i", "j", "x", "y", "p", "q", "r", "u", "v", "a", "b", "c", "d", "e", "y1", "i2")
      .map(_ -> Num).toMap ++ Map("f" -> Fun, "t" -> Fun, "g" -> Fun)

  /** Both facts, derived over the kit `Primes` builds and a ground that finds `Euler`'s facts too. */
  def derive(kit: Steps.Kit, ground: Moves.Ground): Either[LogicError, Map[String, Kernel.Thm]] =
    try {
      val proof = new Proof(kit, ground)
      Right(Map(Primes.ProdPaired -> proof.paired, Primes.Wilson -> proof.wilson))
    } catch { case refused: Moves.RefusedHere => Left(refused.error) }

  private final class Proof(kit: Steps.Kit, ground: Moves.Ground) extends Moves(ground, Types, Moves.Written) {

    def fct(name: String): Kernel.Thm = force(ground.fact(name))

    /** Specialise at terms rather than texts, and reduce. */
    def specT(theorem: Kernel.Thm, arguments: Term*): Kernel.Thm =
      reduced(force(rules.specAll(theorem, arguments.toList)))

    /** Every occurrence of the left side of `equation` in `theorem`'s conclusion replaced by its right. */
    def rewritten(equation: Kernel.Thm, theorem: Kernel.Thm): Kernel.Thm =
      force(Limit.rewriteInProposition(equation, theorem))

    /* ------------------------------------------------------------------ arithmetic */

    /** `|- !x. SUC x = x + 1`, with the numeral `1`, which is what lets SEMIRING read a successor. */
    lazy val sucRule: Kernel.Thm = {
      val plusOne = trans(spec(pf(Peano.AddAtSuccessor), "x", "0"), congruent("SUC", spec(pf(Peano.AddAtZero), "x")))
      val numeral = transport(sym(pf(Peano.NumeralOneIsSuccessorOfZero)), "NUM_ADD x zz = SUC x", plusOne)
      generalised(sym(numeral), "x")
    }

    /** `|- left = right`, an identity of the semiring once every successor is written `+ 1`. */
    def ring(left: String, right: String): Kernel.Thm =
      force(Steps.equate(kit, term(left, Num), term(right, Num), Vector(sucRule), Vector(sucRule)))

    def ltSuc(x: String): Kernel.Thm = spec(pf(Peano.BelowSuccessor), x)

    def ltTrans(a: String, b: String, c: String, first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm =
      mp(spec(pf(Peano.StrictTransitive), a, b, c), conj(first, second))

    /** `SUC a < SUC b` from `a < b`. */
    def sucLt(a: String, b: String, below: Kernel.Thm): Kernel.Thm = {
      val shifted = mp(spec(pf(Peano.AddStrictlyMonotone), "1", a, b), below)
      val left = transport(ring(s"NUM_ADD 1 ($a)", s"SUC ($a)"), s"NUM_LT zz (NUM_ADD 1 ($b))", shifted)
      transport(ring(s"NUM_ADD 1 ($b)", s"SUC ($b)"), s"NUM_LT (SUC ($a)) zz", left)
    }

    /** `a < b` from `SUC a < SUC b`. */
    def sucLtCancel(a: String, b: String, below: Kernel.Thm): Kernel.Thm =
      mp(spec(pf(Peano.BelowThenAtMost), a, s"SUC ($a)", b),
        conj(ltSuc(a), mp(spec(pf(Peano.AtMostBelowSuccessor), b, s"SUC ($a)"), below)))

    /** `x < n` from `x < SUC n` and `~(x = n)`. */
    def belowOfNot(x: String, n: String, below: Kernel.Thm, not: Kernel.Thm): Kernel.Thm =
      byDisjunction(mp(spec(pf(Peano.BelowSuccessorCases), n, x), below))(
        identity,
        same => exFalso(prop(s"NUM_LT ($x) ($n)"), absurd(not, same))
      )

    /** `~(b = a)` from `a < b`. */
    def aboveNot(a: String, b: String, below: Kernel.Thm): Kernel.Thm =
      refuted(prop(s"($b) = ($a)")) { same =>
        absurd(spec(pf(Peano.StrictIrreflexive), a), transport(same, s"NUM_LT ($a) zz", below))
      }

    /* ------------------------------------------------------------- congruences */

    private def congParts(theorem: Kernel.Thm): (Term, Term, Term) = theorem.conclusion match {
      case App(App(App(_, modulus), left), right) => (modulus, left, right)
      case other => refuse("a congruence", other)
    }

    def congRefl(m: String, x: String): Kernel.Thm = spec(fct("NUM_CONG_REFL"), m, x)

    def congSym(c: Kernel.Thm): Kernel.Thm = {
      val (m, a, b) = congParts(c)
      mp(specT(fct("NUM_CONG_SYM"), m, a, b), c)
    }

    def congTrans(first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm = {
      val (m, a, b) = congParts(first)
      val (_, _, c) = congParts(second)
      mp(specT(fct("NUM_CONG_TRANS"), m, a, b, c), first, second)
    }

    def congMul(first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm = {
      val (m, a, b) = congParts(first)
      val (_, c, d) = congParts(second)
      mp(specT(fct("NUM_CONG_MUL"), m, a, b, c, d), first, second)
    }

    def congAdd(first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm = {
      val (m, a, b) = congParts(first)
      val (_, c, d) = congParts(second)
      mp(specT(fct("NUM_CONG_ADD"), m, a, b, c, d), first, second)
    }

    /** `a = b` from `NUM_CONG m a b` with both below the modulus. */
    def congBelow(c: Kernel.Thm, aBelow: Kernel.Thm, bBelow: Kernel.Thm): Kernel.Thm = {
      val (m, a, b) = congParts(c)
      val toB = mp(specT(fct("NUM_MOD_OF_CONG"), m, a, b), c, bBelow)
      val toA = mp(specT(fct("NUM_MOD_OF_CONG"), m, a, a), specT(fct("NUM_CONG_REFL"), m, a), aBelow)
      trans(sym(toA), toB)
    }

    /* ------------------------------------------------------------- the pairing */

    def h1(y: String): String = s"(!i:num. NUM_LT i $y ==> NUM_LT (t i) $y)"
    def h2(y: String): String = s"(!i:num. NUM_LT i $y ==> t (t i) = i)"
    def h3(y: String): String = s"(!i:num. NUM_LT i $y ==> ~(t i = i))"
    def h4(y: String): String = s"(!i:num. NUM_LT i $y ==> NUM_CONG m (f i * f (t i)) (SUC 0))"
    def goal(y: String): String = s"NUM_CONG m (NUM_PROD f $y) (SUC 0)"

    /** The claim at a length, with the two functions quantified inside. */
    def claim(y: String): String =
      s"(!f:num->num. !t:num->num. ${h1(y)} ==> ${h2(y)} ==> ${h3(y)} ==> ${h4(y)} ==> ${goal(y)})"

    /** The claim at `y`, from its conclusion under the four hypotheses assumed at free `f` and `t`. */
    def claimed(y: String)(reach: (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm) => Kernel.Thm): Kernel.Thm = {
      val result = reach(assume(h1(y)), assume(h2(y)), assume(h3(y)), assume(h4(y)))
      generalised(discharged(result, h1(y), h2(y), h3(y), h4(y)), "f", "t")
    }

    lazy val atZero: Kernel.Thm = claimed("0") { (_, _, _, _) =>
      transport(sym(spec(fct("NUM_PROD_ZERO"), "f")), "NUM_CONG m zz (SUC 0)", congRefl("m", "SUC 0"))
    }

    lazy val atOne: Kernel.Thm = claimed("(SUC 0)") { (range, _, moves, _) =>
      val below = mp(spec(range, "0"), ltSuc("0"))
      val atZeroIndex = byDisjunction(mp(spec(pf(Peano.BelowSuccessorCases), "0", "t 0"), below))(
        under => exFalso(prop("t 0 = 0"), absurd(spec(pf(Peano.NotBelowZero), "t 0"), under)),
        identity
      )
      exFalso(prop(goal("(SUC 0)")), absurd(mp(spec(moves, "0"), ltSuc("0")), atZeroIndex))
    }

    /** The swap of `k` and `w`, at an argument. */
    def sw(x: String): String = s"(COND ($x = k) w (COND ($x = w) k $x))"

    /** The claim at `SUC (SUC w)`, from the claim at `w` for every pair of functions. */
    def atTwoMore(claimAtW: Kernel.Thm): Kernel.Thm = {
      val n = "(SUC (SUC w))"
      claimed(n) { (range, involution, moves, pairs) =>
        val topBelow = ltSuc("SUC w")
        val named = witnessed(prop("?k:num. k = t (SUC w)"), List("t (SUC w)"), Conv.refl(term("t (SUC w)", Num)))
        opened(named, "k") { kIs =>
          val kBelow = transport(sym(kIs), s"NUM_LT zz $n", mp(spec(range, "SUC w"), topBelow))
          val kNotTop = transport(sym(kIs), "~(zz = SUC w)", mp(spec(moves, "SUC w"), topBelow))
          val kBelowTop = belowOfNot("k", "SUC w", kBelow, kNotTop)
          val wBelowTop = ltSuc("w")
          val wBelow = ltTrans("w", "SUC w", n, wBelowTop, topBelow)

          /* The swap's three values, and that it undoes itself. */
          def atK(xk: Kernel.Thm, x: String): Kernel.Thm = whenHolds(xk, "w", s"(COND ($x = w) k $x)")
          def atW(notK: Kernel.Thm, xw: Kernel.Thm, x: String): Kernel.Thm =
            trans(whenFails(notK, "w", s"(COND ($x = w) k $x)"), whenHolds(xw, "k", x))
          def elsewhere(notK: Kernel.Thm, notW: Kernel.Thm, x: String): Kernel.Thm =
            trans(whenFails(notK, "w", s"(COND ($x = w) k $x)"), whenFails(notW, "k", x))
          def swapCases(x: String)(onK: Kernel.Thm => Kernel.Thm, onW: (Kernel.Thm, Kernel.Thm) => Kernel.Thm,
              other: (Kernel.Thm, Kernel.Thm) => Kernel.Thm): Kernel.Thm =
            cases(prop(s"$x = k"))(
              xk => onK(xk),
              notK => cases(prop(s"$x = w"))(xw => onW(notK, xw), notW => other(notK, notW))
            )
          def under(fn: String, equation: Kernel.Thm): Kernel.Thm = reduced(congruent(fn, equation))
          val swapLambda = s"\\z0:num. ${sw("z0")}"

          /** `sw w = k`, both when `w` is `k` and when it is not. */
          val swapW = cases(prop("w = k"))(
            wk => trans(atK(wk, "w"), wk),
            notK => atW(notK, Conv.refl(term("w", Num)), "w")
          )
          /** `sw k = w`. */
          val swapK = atK(Conv.refl(term("k", Num)), "k")

          def undone(x: String): Kernel.Thm = {
            val target = prop(s"${sw(sw(x))} = $x")
            val proof = swapCases(x)(
              xk => {
                val inner = under(swapLambda, atK(xk, x))
                trans(inner, trans(swapW, sym(xk)))
              },
              (notK, xw) => {
                val inner = under(swapLambda, atW(notK, xw, x))
                trans(inner, trans(swapK, sym(xw)))
              },
              (notK, notW) => {
                val value = elsewhere(notK, notW, x)
                trans(under(swapLambda, value), value)
              }
            )
            if (proof.conclusion != target) refuse("the swap undoing itself", proof.conclusion)
            proof
          }

          /** The swap maps `[0, SUC (SUC w))` into itself. */
          def swapBelow(x: String, below: Kernel.Thm): Kernel.Thm = swapCases(x)(
            xk => transport(sym(atK(xk, x)), s"NUM_LT zz $n", wBelow),
            (notK, xw) => transport(sym(atW(notK, xw, x)), s"NUM_LT zz $n", kBelow),
            (notK, notW) => transport(sym(elsewhere(notK, notW, x)), s"NUM_LT zz $n", below)
          )

          /** Below `SUC w` and not `k`, the swap lands below `w`. */
          def swapBelowW(x: String, below: Kernel.Thm, notK: Kernel.Thm): Kernel.Thm =
            cases(prop(s"$x = w"))(
              xw => {
                val kNotW = refuted(prop("k = w")) { kw => absurd(notK, trans(xw, sym(kw))) }
                transport(sym(atW(notK, xw, x)), "NUM_LT zz w", belowOfNot("k", "w", kBelowTop, kNotW))
              },
              notW => transport(sym(elsewhere(notK, notW, x)), "NUM_LT zz w", belowOfNot(x, "w", below, notW))
            )

          /* The permutation, as NUM_PROD_PERMUTE asks for it. */
          val permuted = {
            val rangeAll = {
              val below = assume(s"NUM_LT x $n")
              generalised(discharged(swapBelow("x", below), s"NUM_LT x $n"), "x")
            }
            val injective = {
              val same = assume(s"${sw("x")} = ${sw("y")}")
              val both = under(swapLambda, same)
              val result = trans(trans(sym(undone("x")), both), undone("y"))
              generalised(discharged(result, s"NUM_LT x $n", s"NUM_LT y $n", s"${sw("x")} = ${sw("y")}"), "x", "y")
            }
            val onto = {
              val below = assume(s"NUM_LT j $n")
              val found = witnessed(prop(s"?i:num. NUM_LT i $n /\\ ${sw("i")} = j"), List(sw("j")),
                conj(swapBelow("j", below), undone("j")))
              generalised(discharged(found, s"NUM_LT j $n"), "j")
            }
            val statement = spec(fct(Primes.ProdPermute), "f", n, swapLambda)
            mp(statement, reduced(rangeAll), reduced(injective), reduced(onto))
          }

          /* The rest pairs off under the conjugated involution, on [0, w). */
          val shiftedF = s"\\z0:num. f ${sw("z0")}"
          val shiftedT = s"\\z0:num. ${sw(s"(t ${sw("z0")})")}"
          val instance = spec(claimAtW, shiftedF, shiftedT)
          val iBelow = assume("NUM_LT i w")
          // `sw i` is below `SUC w` and is not `k`.
          val (jBelowTop, jNotK) = {
            val result = cases(prop("i = k"))(
              ik => {
                val kBelowW = transport(ik, "NUM_LT zz w", iBelow)
                val wNotK = aboveNot("k", "w", kBelowW)
                val value = atK(ik, "i")
                conj(transport(sym(value), "NUM_LT zz (SUC w)", wBelowTop), transport(sym(value), "~(zz = k)", wNotK))
              },
              notK => {
                val notW = unequalSym(aboveNot("i", "w", iBelow))
                val value = elsewhere(notK, notW, "i")
                conj(transport(sym(value), "NUM_LT zz (SUC w)", ltTrans("i", "w", "SUC w", iBelow, wBelowTop)),
                  transport(sym(value), "~(zz = k)", notK))
              }
            )
            (left(result), right(result))
          }
          val j = sw("i")
          val jBelow = ltTrans(j, "SUC w", n, jBelowTop, topBelow)
          val tj = s"(t $j)"
          val tjBelow = mp(spec(range, j), jBelow)
          val backAtJ = mp(spec(involution, j), jBelow)
          val tjNotTop = refuted(prop(s"$tj = SUC w")) { same =>
            val toK = trans(trans(sym(backAtJ), congruent("t", same)), sym(kIs))
            absurd(jNotK, toK)
          }
          val tjNotK = refuted(prop(s"$tj = k")) { same =>
            val topBack = transport(sym(kIs), "t zz = SUC w", mp(spec(involution, "SUC w"), topBelow))
            val toTop = trans(trans(sym(backAtJ), congruent("t", same)), topBack)
            absurd(spec(pf(Peano.StrictIrreflexive), "SUC w"), transport(toTop, "NUM_LT zz (SUC w)", jBelowTop))
          }
          val tjBelowTop = belowOfNot(tj, "SUC w", tjBelow, tjNotTop)

          val rangeW = generalised(discharged(swapBelowW(tj, tjBelowTop, tjNotK), "NUM_LT i w"), "i")
          val involutionW = {
            val inner = under(s"\\z0:num. ${sw("(t z0)")}", undone(tj))
            val back = under(swapLambda, backAtJ)
            generalised(discharged(trans(trans(inner, back), undone("i")), "NUM_LT i w"), "i")
          }
          val movesW = {
            val fixed = refuted(prop(s"${sw(tj)} = i")) { same =>
              val atJ = trans(sym(undone(tj)), under(swapLambda, same))
              absurd(mp(spec(moves, j), jBelow), atJ)
            }
            generalised(discharged(fixed, "NUM_LT i w"), "i")
          }
          val pairsW = {
            val atJ = mp(spec(pairs, j), jBelow)
            val moved = transport(sym(undone(tj)), s"NUM_CONG m (f $j * f zz) (SUC 0)", atJ)
            generalised(discharged(moved, "NUM_LT i w"), "i")
          }
          val restPairs = mp(instance, reduced(rangeW), reduced(involutionW), reduced(movesW), reduced(pairsW))

          /* The two top factors, and the product put back together. */
          val topPair = transport(sym(kIs), "NUM_CONG m (f (SUC w) * f zz) (SUC 0)", mp(spec(pairs, "SUC w"), topBelow))
          val product = congMul(restPairs, topPair)
          val prodF = s"(\\z0:num. f ${sw("z0")})"
          val swapTop = elsewhere(
            refuted(prop("SUC w = k")) { same => absurd(kNotTop, sym(same)) },
            spec(pf(Peano.SuccessorNotSelf), "w"),
            "(SUC w)"
          )
          val outer = spec(fct("NUM_PROD_SUC"), prodF, "SUC w")
          val inner = spec(fct("NUM_PROD_SUC"), prodF, "w")
          val atTop = rewritten(swapTop, rewritten(inner, outer))
          val expanded = rewritten(swapW, atTop)
          val regrouped = trans(expanded,
            ring(s"NUM_MUL (NUM_MUL (NUM_PROD $prodF w) (f k)) (f (SUC w))",
              s"NUM_MUL (NUM_PROD $prodF w) (NUM_MUL (f (SUC w)) (f k))"))
          val onProduct = transport(sym(regrouped), "NUM_CONG m zz (NUM_MUL (SUC 0) (SUC 0))", product)
          val onOne = transport(ring("NUM_MUL (SUC 0) (SUC 0)", "SUC 0"), s"NUM_CONG m (NUM_PROD $prodF $n) zz", onProduct)
          transport(permuted, "NUM_CONG m zz (SUC 0)", onOne)
        }
      }
    }

    /** [[Primes.ProdPaired]]. */
    lazy val paired: Kernel.Thm = {
      val strong = spec(pf(Peano.StrongInduction), s"\\y:num. ${claim("y")}")
      val ih = assume(s"!z:num. NUM_LT z y ==> ${claim("z")}")
      val atY = byDisjunction(spec(nf(Natural.ZeroOrSuccessor), "y"))(
        zero => transport(sym(zero), claim("zz"), atZero),
        successor => opened(successor, "y1") { yIs =>
          byDisjunction(spec(nf(Natural.ZeroOrSuccessor), "y1"))(
            zero => transport(sym(trans(yIs, congruent("SUC", zero))), claim("zz"), atOne),
            again => opened(again, "w") { y1Is =>
              val yIsTwoMore = trans(yIs, congruent("SUC", y1Is))
              val wBelowY = transport(sym(yIsTwoMore), "NUM_LT w zz",
                ltTrans("w", "SUC w", "SUC (SUC w)", ltSuc("w"), ltSuc("SUC w")))
              transport(sym(yIsTwoMore), claim("zz"), atTwoMore(mp(spec(ih, "w"), wBelowY)))
            }
          )
        }
      )
      val step = generalised(discharged(atY, s"!z:num. NUM_LT z y ==> ${claim("z")}"), "y")
      val all = spec(mp(strong, reduced(step)), "n", "f", "t")
      generalised(all, "m", "f", "t", "n")
    }

    /* --------------------------------------------------------------- Wilson */

    /** `|- NUM_FACT (SUC k) = NUM_PROD (\i. SUC (SUC i)) k`, the factorial from two on. */
    lazy val factorialFromTwo: Kernel.Thm = {
      val shifted = "(\\z0:num. SUC (SUC z0))"
      val induction = spec(nf(Natural.Induction), s"\\k:num. NUM_FACT (SUC k) = NUM_PROD $shifted k")
      val base = {
        val one = trans(spec(fct("NUM_FACT_SUC"), "0"), ring("NUM_MUL (NUM_FACT 0) (SUC 0)", "NUM_FACT 0"))
        trans(trans(one, fct("NUM_FACT_ZERO")), sym(spec(fct("NUM_PROD_ZERO"), shifted)))
      }
      val step = {
        val hypothesis = assume(s"NUM_FACT (SUC k) = NUM_PROD $shifted k")
        val unfold = spec(fct("NUM_FACT_SUC"), "SUC k")
        val product = spec(fct("NUM_PROD_SUC"), shifted, "k")
        val moved = transport(hypothesis, "NUM_FACT (SUC (SUC k)) = NUM_MUL zz (SUC (SUC k))", unfold)
        generalised(discharged(trans(moved, sym(product)), s"NUM_FACT (SUC k) = NUM_PROD $shifted k"), "k")
      }
      mp(induction, conj(reduced(base), reduced(step)))
    }

    /** `|- NUM_CONG p (NUM_MOD x p) x` for `0 < p`. */
    def modCong(x: String, p: String, positive: Kernel.Thm): Kernel.Thm = {
      val split = mp(spec(fct("NUM_DIVISION"), p, x), positive)
      opened(split, "q") { afterQ =>
        opened(afterQ, "r") { body =>
          val xIs = left(body)
          val rBelow = right(body)
          val identity = ring(s"NUM_ADD (NUM_ADD (NUM_MUL $p q) r) (NUM_MUL $p 0)", s"NUM_ADD r (NUM_MUL $p q)")
          val atX = transport(sym(xIs), s"NUM_ADD zz (NUM_MUL $p 0) = NUM_ADD r (NUM_MUL $p q)", identity)
          val xToR = mp(spec(fct("NUM_CONG_INTRO"), p, x, "r", "0", "q"), atX)
          val modIs = mp(spec(fct("NUM_MOD_OF_CONG"), p, x, "r"), xToR, rBelow)
          congSym(transport(sym(modIs), s"NUM_CONG $p $x zz", xToR))
        }
      }
    }

    val P = "(SUC (SUC (SUC n)))"
    val Top = "(SUC (SUC n))"
    def inverse(x: String): String = s"(NUM_MOD (select (\\z1:num. NUM_CONG $P (NUM_MUL $x z1) (SUC 0))) $P)"
    def residue(i: String): String = s"(SUC (SUC $i))"

    /** [[Primes.Wilson]]. */
    lazy val wilson: Kernel.Thm = {
      val primeText = "NUM_PRIME p"
      val prime = assume(primeText)
      val aboveOne = mp(spec(fct("NUM_PRIME_ABOVE_ONE"), "p"), prime)
      val goalText = "NUM_DIVIDES p (SUC (NUM_FACT (PRE p)))"
      val result = byDisjunction(spec(nf(Natural.ZeroOrSuccessor), "p"))(
        zero => exFalso(prop(goalText),
          absurd(spec(pf(Peano.NotBelowZero), "SUC 0"), transport(zero, "NUM_LT (SUC 0) zz", aboveOne))),
        s1 => opened(s1, "a") { pIs =>
          byDisjunction(spec(nf(Natural.ZeroOrSuccessor), "a"))(
            aZero => {
              val one = transport(trans(pIs, congruent("SUC", aZero)), "NUM_LT (SUC 0) zz", aboveOne)
              exFalso(prop(goalText), absurd(spec(pf(Peano.StrictIrreflexive), "SUC 0"), one))
            },
            s2 => opened(s2, "b") { aIs =>
              val pIsTwoMore = trans(pIs, congruent("SUC", aIs))
              byDisjunction(spec(nf(Natural.ZeroOrSuccessor), "b"))(
                bZero => {
                  val pIsTwo = trans(pIsTwoMore, congruent("SUC", congruent("SUC", bZero)))
                  transport(sym(pIsTwo), "NUM_DIVIDES zz (SUC (NUM_FACT (PRE zz)))", atTwo)
                },
                s3 => opened(s3, "n") { bIs =>
                  val pIsGeneral = trans(pIsTwoMore, congruent("SUC", congruent("SUC", bIs)))
                  val primeHere = transport(pIsGeneral, "NUM_PRIME zz", prime)
                  transport(sym(pIsGeneral), "NUM_DIVIDES zz (SUC (NUM_FACT (PRE zz)))", general(primeHere))
                }
              )
            }
          )
        }
      )
      generalised(discharged(result, primeText), "p")
    }

    /** At two, where `1! + 1 = 2`. */
    lazy val atTwo: Kernel.Thm = {
      val two = "(SUC (SUC 0))"
      val pre = spec(pf(Peano.PreAtSuccessor), "SUC 0")
      val fact = trans(spec(fct("NUM_FACT_SUC"), "0"), trans(
        ring("NUM_MUL (NUM_FACT 0) (SUC 0)", "NUM_FACT 0"), fct("NUM_FACT_ZERO")))
      val value = congruent("SUC", trans(congruent("NUM_FACT", pre), fact))
      transport(sym(value), s"NUM_DIVIDES $two zz", spec(fct("NUM_DIVIDES_REFL"), two))
    }

    /** Wilson at `p = n + 3`, from its primality. */
    def general(prime: Kernel.Thm): Kernel.Thm = {
      val positive = spec(pf(Peano.SuccessorPositive), s"SUC (SUC n)")
      val topBelowP = ltSuc(Top)
      val oneBelowP = ltTrans("SUC 0", Top, P, sucLt("0", "SUC n", spec(pf(Peano.SuccessorPositive), "n")), topBelowP)

      /** A residue strictly between `0` and `p` is coprime to `p`. */
      def coprime(x: String, xPositive: Kernel.Thm, xBelow: Kernel.Thm): Kernel.Thm = {
        val pNonZero = spec(nf(Natural.SuccessorNotZero), Top)
        val either = disjoined(prop(s"~($x = 0) \\/ ~($P = 0)"), pNonZero)
        val gcd = s"(NUM_GCD $x $P)"
        val divides = mp(spec(fct("NUM_GCD_DIVIDES_RIGHT"), x, P), either)
        byDisjunction(mp(spec(fct("NUM_PRIME_DIVISOR"), P, gcd), prime, divides))(
          identity,
          isP => {
            val dividesX = transport(isP, s"NUM_DIVIDES zz $x", mp(spec(fct("NUM_GCD_DIVIDES_LEFT"), x, P), either))
            val xNonZero = aboveNot("0", x, xPositive)
            byDisjunction(mp(spec(fct("NUM_DIVIDES_LE"), P, x), dividesX))(
              atMost => exFalso(prop(s"$gcd = SUC 0"),
                absurd(mp(spec(pf(Peano.BelowExcludesAtMost), x, P), xBelow), atMost)),
              zero => exFalso(prop(s"$gcd = SUC 0"), absurd(xNonZero, zero))
            )
          }
        )
      }

      /** The chosen inverse of a unit: it inverts, and it is below `p`. */
      def inverts(x: String, unit: Kernel.Thm): (Kernel.Thm, Kernel.Thm) = {
        val exists = mp(spec(fct("NUM_INVERSE"), P, x), positive, unit)
        val chosen = reduced(force(classical.witness(exists)))
        val selected = s"(select (\\z1:num. NUM_CONG $P (NUM_MUL $x z1) (SUC 0)))"
        val reducedMod = congMul(congRefl(P, x), modCong(selected, P, positive))
        (congTrans(reducedMod, chosen), mp(spec(fct("NUM_MOD_LT"), selected, P), positive))
      }

      // The residues 2 .. p - 2, as `SUC (SUC i)` for `i < n`.
      val i = "i"
      val iBelow = assume("NUM_LT i n")
      val u = residue(i)
      val uBelowTop = sucLt("SUC i", "SUC n", sucLt(i, "n", iBelow))
      val uBelowP = ltTrans(u, Top, P, uBelowTop, topBelowP)
      val uPositive = spec(pf(Peano.SuccessorPositive), "SUC i")
      val (inverted, vBelowP) = inverts(u, coprime(u, uPositive, uBelowP))
      val v = inverse(u)

      // The inverse is none of 0, 1 and p - 1, since each would make u one of them.
      val vNotZero = refuted(prop(s"$v = 0")) { zero =>
        val atZero = rewritten(ring(s"NUM_MUL $u 0", "0"), rewritten(zero, inverted))
        val same = congBelow(atZero, spec(pf(Peano.SuccessorPositive), Top), oneBelowP)
        absurd(unequalSym(spec(nf(Natural.SuccessorNotZero), "0")), same)
      }
      val vNotOne = refuted(prop(s"$v = SUC 0")) { one =>
        val atOne = rewritten(ring(s"NUM_MUL $u (SUC 0)", u), rewritten(one, inverted))
        val same = congBelow(atOne, uBelowP, oneBelowP)
        absurd(spec(nf(Natural.SuccessorNotZero), "i"), mp(spec(nf(Natural.SuccessorInjective), "SUC i", "0"), same))
      }
      val vNotTop = refuted(prop(s"$v = $Top")) { top =>
        val atTop = rewritten(top, inverted)
        val plus = congAdd(atTop, congRefl(P, u))
        val multiple = ring(s"NUM_ADD (NUM_MUL $u $Top) $u", s"NUM_MUL $u $P")
        val toZero = mp(spec(fct("NUM_CONG_INTRO"), P, s"NUM_MUL $u $P", "0", "0", u),
          ring(s"NUM_ADD (NUM_MUL $u $P) (NUM_MUL $P 0)", s"NUM_ADD 0 (NUM_MUL $P $u)"))
        val zeroToSum = congTrans(congSym(toZero), transport(multiple, s"NUM_CONG $P zz (NUM_ADD (SUC 0) $u)", plus))
        val sumBelow = transport(ring(s"SUC $u", s"NUM_ADD (SUC 0) $u"), s"NUM_LT zz $P", sucLt(u, Top, uBelowTop))
        val same = congBelow(zeroToSum, spec(pf(Peano.SuccessorPositive), Top), sumBelow)
        absurd(unequalSym(transport(ring(s"SUC $u", s"NUM_ADD (SUC 0) $u"), "~(zz = 0)", spec(nf(Natural.SuccessorNotZero), u))), same)
      }
      val vBelowTop = belowOfNot(v, Top, vBelowP, vNotTop)

      // So v is SUC (SUC c) for some c below n, and the involution is `c`.
      val tText = s"(\\z0:num. PRE (PRE ${inverse(residue("z0"))}))"
      val twoUp = byDisjunction(spec(nf(Natural.ZeroOrSuccessor), v))(
        z => exFalso(prop(s"$v = SUC (SUC (PRE (PRE $v)))"), absurd(vNotZero, z)),
        s => opened(s, "c") { vIs =>
          byDisjunction(spec(nf(Natural.ZeroOrSuccessor), "c"))(
            cz => exFalso(prop(s"$v = SUC (SUC (PRE (PRE $v)))"), absurd(vNotOne, trans(vIs, congruent("SUC", cz)))),
            cs => opened(cs, "d") { cIs =>
              val vIsD = trans(vIs, congruent("SUC", cIs))
              val pre = trans(congruent("PRE", congruent("PRE", vIsD)),
                trans(congruent("PRE", spec(pf(Peano.PreAtSuccessor), "SUC d")), spec(pf(Peano.PreAtSuccessor), "d")))
              trans(vIsD, sym(congruent("SUC", congruent("SUC", pre))))
            }
          )
        }
      )
      val c = s"(PRE (PRE $v))"
      val cBelow = sucLtCancel(c, "n", sucLtCancel(s"SUC $c", "SUC n", transport(twoUp, s"NUM_LT zz $Top", vBelowTop)))

      // The inverse of v is u: an inverse is unique modulo p.
      val vUnit = coprime(v, transport(sym(twoUp), "NUM_LT 0 zz", spec(pf(Peano.SuccessorPositive), s"SUC $c")), vBelowP)
      val (vInverted, w2Below) = inverts(v, vUnit)
      val w2 = inverse(v)
      val uniqueness = {
        // u = u * (v * w2) = (u * v) * w2 = w2, modulo p; both are below p, so they are equal.
        val first = congSym(congMul(congRefl(P, u), vInverted))
        val regrouped = transport(ring(s"NUM_MUL $u (NUM_MUL $v $w2)", s"NUM_MUL (NUM_MUL $u $v) $w2"),
          s"NUM_CONG $P (NUM_MUL $u (SUC 0)) zz", first)
        val second = congMul(inverted, congRefl(P, w2))
        val joined = congTrans(regrouped, second)
        val left = transport(ring(s"NUM_MUL $u (SUC 0)", u), s"NUM_CONG $P zz (NUM_MUL (SUC 0) $w2)", joined)
        val both = transport(ring(s"NUM_MUL (SUC 0) $w2", w2), s"NUM_CONG $P $u zz", left)
        sym(congBelow(both, uBelowP, w2Below))
      }

      // No fixed point: u * u = 1 would put p under (u - 1) * (u + 1).
      val distinct = refuted(prop(s"$v = $u")) { same =>
        val square = rewritten(same, inverted)
        val factored = ring(s"NUM_MUL $u $u", s"NUM_ADD (NUM_MUL (SUC $i) (SUC (SUC (SUC $i)))) (SUC 0)")
        val moved = transport(factored, s"NUM_CONG $P zz (SUC 0)", square)
        opened(mp(spec(fct("NUM_CONG_ELIM"), P, s"NUM_ADD (NUM_MUL (SUC $i) (SUC (SUC (SUC $i)))) (SUC 0)", "SUC 0"), moved), "x") { ax =>
          opened(ax, "y") { body =>
            // (a b + 1) + p x = 1 + p y, so a b + p x = p y, so p divides a b + p x and p x.
            val cancelled = mp(spec(pf(Peano.AddCancelsLeft),
              s"NUM_ADD (NUM_MUL (SUC $i) (SUC (SUC (SUC $i)))) (NUM_MUL $P x)", s"NUM_MUL $P y", "SUC 0"),
              trans(ring(s"NUM_ADD (SUC 0) (NUM_ADD (NUM_MUL (SUC $i) (SUC (SUC (SUC $i)))) (NUM_MUL $P x))",
                s"NUM_ADD (NUM_ADD (NUM_MUL (SUC $i) (SUC (SUC (SUC $i)))) (SUC 0)) (NUM_MUL $P x)"), body))
            val dividesSum = transport(sym(cancelled), s"NUM_DIVIDES $P zz",
              mp(spec(fct("NUM_DIVIDES_INTRO"), P, s"NUM_MUL $P y", "y"), Conv.refl(term(s"NUM_MUL $P y", Num))))
            val product = mp(spec(fct("NUM_DIVIDES_SUMMAND"), P, s"NUM_MUL $P x",
              s"NUM_MUL (SUC $i) (SUC (SUC (SUC $i)))"),
              mp(spec(fct("NUM_DIVIDES_INTRO"), P, s"NUM_MUL $P x", "x"), Conv.refl(term(s"NUM_MUL $P x", Num))),
              transport(ring(s"NUM_ADD (NUM_MUL (SUC $i) (SUC (SUC (SUC $i)))) (NUM_MUL $P x)",
                s"NUM_ADD (NUM_MUL $P x) (NUM_MUL (SUC $i) (SUC (SUC (SUC $i))))"), s"NUM_DIVIDES $P zz", dividesSum))
            def tooSmall(factor: String, below: Kernel.Thm, divides: Kernel.Thm): Kernel.Thm =
              byDisjunction(mp(spec(fct("NUM_DIVIDES_LE"), P, factor), divides))(
                atMost => absurd(mp(spec(pf(Peano.BelowExcludesAtMost), factor, P), below), atMost),
                zero => absurd(spec(nf(Natural.SuccessorNotZero), factor.stripPrefix("(SUC ").stripSuffix(")")), zero)
              )
            val lowBelow = ltTrans(s"(SUC $i)", u, P, ltSuc(s"SUC $i"), uBelowP)
            val highBelow = sucLt(u, Top, uBelowTop)
            byDisjunction(mp(spec(fct("NUM_EUCLID"), P, s"(SUC $i)", s"(SUC (SUC (SUC $i)))"), prime, product))(
              low => tooSmall(s"(SUC $i)", lowBelow, low),
              high => tooSmall(s"(SUC (SUC (SUC $i)))", highBelow, high)
            )
          }
        }
      }

      // The four hypotheses of the pairing, at the residues.
      val range = generalised(discharged(cBelow, "NUM_LT i n"), "i")
      val involution = {
        // t (t i) = PRE (PRE (inverse (SUC (SUC c)))) = PRE (PRE (inverse v)) = PRE (PRE u) = i.
        val toV = reduced(congruent(s"\\z0:num. PRE (PRE ${inverse("z0")})", sym(twoUp)))
        val toU = reduced(congruent("\\z0:num. PRE (PRE z0)", uniqueness))
        val pre = trans(congruent("PRE", spec(pf(Peano.PreAtSuccessor), "SUC i")), spec(pf(Peano.PreAtSuccessor), "i"))
        generalised(discharged(trans(trans(toV, toU), pre), "NUM_LT i n"), "i")
      }
      val moves = {
        val fixed = refuted(prop(s"$c = i")) { same =>
          absurd(distinct, trans(twoUp, congruent("SUC", congruent("SUC", same))))
        }
        generalised(discharged(fixed, "NUM_LT i n"), "i")
      }
      val pairs = {
        val atTwoUp = transport(twoUp, s"NUM_CONG $P (NUM_MUL $u zz) (SUC 0)", inverted)
        generalised(discharged(atTwoUp, "NUM_LT i n"), "i")
      }
      val middle = mp(spec(paired, P, "\\z0:num. SUC (SUC z0)", tText, "n"),
        reduced(range), reduced(involution), reduced(moves), reduced(pairs))

      // (p - 1)! = M * (p - 1), and M = 1, so (p - 1)! + 1 = p - 1 + 1 = p = 0.
      val pre = spec(pf(Peano.PreAtSuccessor), Top)
      val fact = trans(congruent("NUM_FACT", pre), trans(spec(factorialFromTwo, "SUC n"),
        spec(fct("NUM_PROD_SUC"), "\\z0:num. SUC (SUC z0)", "n")))
      val m = "(NUM_PROD (\\z0:num. SUC (SUC z0)) n)"
      opened(mp(spec(fct("NUM_CONG_ELIM"), P, m, "SUC 0"), middle), "x") { ax =>
        opened(ax, "y") { body =>
          // SUC (M * top) + p * (x * top) = p * (SUC (y * top)), from M + p x = 1 + p y.
          val scaled = congruent(s"\\z0:num. NUM_ADD (NUM_MUL z0 $Top) (SUC 0)", body)
          val lhs = ring(s"NUM_ADD (NUM_MUL (NUM_ADD $m (NUM_MUL $P x)) $Top) (SUC 0)",
            s"NUM_ADD (SUC (NUM_MUL $m (SUC (SUC n)))) (NUM_MUL $P (NUM_MUL x $Top))")
          val rhs = ring(s"NUM_ADD (NUM_MUL (NUM_ADD (SUC 0) (NUM_MUL $P y)) $Top) (SUC 0)",
            s"NUM_MUL $P (NUM_ADD (SUC 0) (NUM_MUL y $Top))")
          val joined = trans(trans(sym(lhs), reduced(scaled)), rhs)
          val whole = mp(spec(fct("NUM_DIVIDES_INTRO"), P,
            s"NUM_ADD (SUC (NUM_MUL $m (SUC (SUC n)))) (NUM_MUL $P (NUM_MUL x $Top))",
            s"NUM_ADD (SUC 0) (NUM_MUL y $Top)"), joined)
          val swapped = transport(ring(s"NUM_ADD (SUC (NUM_MUL $m (SUC (SUC n)))) (NUM_MUL $P (NUM_MUL x $Top))",
            s"NUM_ADD (NUM_MUL $P (NUM_MUL x $Top)) (SUC (NUM_MUL $m (SUC (SUC n))))"), s"NUM_DIVIDES $P zz", whole)
          val part = mp(spec(fct("NUM_DIVIDES_INTRO"), P, s"NUM_MUL $P (NUM_MUL x $Top)", s"NUM_MUL x $Top"),
            Conv.refl(term(s"NUM_MUL $P (NUM_MUL x $Top)", Num)))
          val divides = mp(spec(fct("NUM_DIVIDES_SUMMAND"), P, s"NUM_MUL $P (NUM_MUL x $Top)",
            s"SUC (NUM_MUL $m (SUC (SUC n)))"), part, swapped)
          transport(sym(fact), s"NUM_DIVIDES $P (SUC zz)", divides)
        }
      }
    }
  }
}
