package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The `t`-th iterate of the shortcut Collatz map as a discrete Fourier series over the residues
 * modulo `2^t`: form (C) of `collatz@8b991e5` `documents/02-closed-form-formula.md` section 2.3,
 * which that repository is the source of truth for.
 *
 * Not a development: it declares nothing. The map is `T n = n / 2` on even `n` and `(3 n + 1) / 2`
 * on odd `n`, and it is given by the two equations that characterise it, `step (2 k) = k` and
 * `step (2 k + 1) = 3 k + 2`, with its iterate by the two of a recursion. The theorems are stated
 * over any `step` and `iterate` satisfying the four, and `COLLATZ_SHORTCUT_EXISTS` exhibits a pair
 * that does, so the hypotheses are not vacuous; a constant for the map would be a row in
 * `docs/reading-register.md` for what four equations say already. `docs/adr/0062` is the decision.
 *
 * == Affine on each class, by a shift rather than by residues of residues ==
 *
 * The source derives (C) from the parity sequence of `n` depending only on `n mod 2^t`. What is
 * proved here is the form that statement takes over the integers, and the induction is on a shift:
 * `iterate (r + 2^t q) t = iterate r t + c q` for a `c` depending on `r` and `t` alone (`SHIFT`). One
 * step more is one step of the map first (`COMMUTED`), and on `r = 2 j` it halves `2 (j + 2^t q)`
 * to `j + 2^t q`, on `r = 2 j + 1` it takes `2 (j + 2^t q) + 1` to `(3 j + 2) + 2^t (3 q)`, and the
 * hypothesis at `j` or at `3 j + 2` finishes it; nothing about a residue of a residue is needed. At
 * `r = n mod 2^t` and `q = n div 2^t` the shift is `iterate n t`, and dividing by `2^t` gives the
 * slope and the offset of the class (`COLLATZ_AFFINE_ON_CLASSES`).
 *
 * == The series ==
 *
 * The slope and the offset are functions of the residue, so each is its own finite Fourier series
 * by `REAL_DFT_INVERSION` at `m = 2^t`, and the two collect into the source's one sum of
 * `(A_s n + B_s) cos (2 pi s n / 2^t) + (C_s n + D_s) sin (2 pi s n / 2^t)` with each coefficient the
 * transform of the slope or of the offset (`COLLATZ_DFT_FORM`). The statement keeps the class form
 * beside the series, so a reader holding `a` and `b` knows they are the slope and the offset.
 *
 * == What it does not say ==
 *
 * The slope is `3^s / 2^t` with `s` the number of odd steps, which is the source's Theorem 1 and is
 * not proved here; neither is any closed form for the coefficients, which the source says has none.
 */
private[theories] object CollatzFourier {

  type R[A] = Either[LogicError, A]

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Maps: Type = Type.fun(Numbers, Numbers)
  private val Iterates: Type = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  /** The shortcut map and its iterate, by the equations that characterise them. */
  private val Shortcut: String =
    "(!k:num. step (2 * k) = k) /\\ (!k:num. step (2 * k + 1) = 3 * k + 2) /\\ " +
      "(!x:num. iterate x 0 = x) /\\ (!x:num. !t:num. iterate x (SUC t) = step (iterate x t))"

  private def over(claim: String): String = s"!step:num->num. !iterate:num->num->num. $Shortcut ==> $claim"

  private val Modulus = "NUM_POW 2 t"
  private def angle(k: String): String = s"2 * pi * real_of_num ($k) / real_of_num ($Modulus)"
  private def coefficient(f: String, trig: String): String =
    s"Sum (\\r:num. $f r * $trig (${angle("s * r")})) ($Modulus) / real_of_num ($Modulus)"

  private val Affine: String =
    s"!n:num. real_of_num (iterate n t) = a (NUM_MOD n ($Modulus)) * real_of_num n + b (NUM_MOD n ($Modulus))"

  private val Spectral: String =
    s"!n:num. real_of_num (iterate n t) = Sum (\\s:num. " +
      s"(${coefficient("a", "cos")} * real_of_num n + ${coefficient("b", "cos")}) * cos (${angle("s * n")}) + " +
      s"(${coefficient("a", "sin")} * real_of_num n + ${coefficient("b", "sin")}) * sin (${angle("s * n")})) ($Modulus)"

  /** What `Complex` publishes from here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    "COLLATZ_SHORTCUT_EXISTS" -> s"?step:num->num. ?iterate:num->num->num. $Shortcut",
    "COLLATZ_AFFINE_ON_CLASSES" -> over(s"!t:num. ?a:num->real. ?b:num->real. $Affine"),
    "COLLATZ_DFT_FORM" -> over(s"!t:num. ?a:num->real. ?b:num->real. ($Affine) /\\ ($Spectral)")
  )

  private lazy val StatementsMap: Map[String, String] = Statements.toMap

  private val Order: Vector[(String, Proofs => R[Kernel.Thm])] = Vector(
    "TWO_POSITIVE" -> (_.twoPositive),
    "PARITY" -> (_.parity),
    "COMMUTED" -> (_.commuted),
    "SHIFT" -> (_.shift),
    "COLLATZ_AFFINE_ON_CLASSES" -> (_.affine),
    "COLLATZ_DFT_FORM" -> (_.dftForm),
    "COLLATZ_SHORTCUT_EXISTS" -> (_.exists)
  )

  /** The facts [[Statements]] names, derived with `kit`; `held` holds the inversion `FiniteFourier` proved. */
  def prove(kit: ComplexKit, semiring: Semiring, recursion: Kernel.Thm, held: Map[String, Kernel.Thm]): R[Map[String, Kernel.Thm]] =
    ComplexKit.derive(Order, Statements, held)(known => new Proofs(kit, semiring, recursion, known))

  private final class Proofs(val kit: ComplexKit, semiring: Semiring, recursion: Kernel.Thm, known: Map[String, Kernel.Thm]) {
    import kit.*

    def k(name: String): Kernel.Thm = known(name)

    private val step = Term.variable("step", Maps)
    private val iterate = Term.variable("iterate", Iterates)
    private val t = Term.variable("t", Numbers)
    private val x = Term.variable("x", Numbers)
    private val r = Term.variable("r", Numbers)
    private val q = Term.variable("q", Numbers)
    private val n = Term.variable("n", Numbers)

    private def num(text: String): R[Kernel.Thm] = prop(text).flatMap(semiring.prove)

    /** `l = l` for the goal `l = r` when rewriting left both sides the same. */
    private def byRefl(goal: Term): R[Kernel.Thm] =
      Term.destEq(goal).map(e => Conv.refl(e._1)).toRight(NotOfForm("an equation", goal))

    /** `f a = f b` from `a = b`, for `f` the head of `like` applied to one argument. */
    private def under(like: String, ty: Type, eq: Kernel.Thm): R[Kernel.Thm] =
      term(like, ty).flatMap {
        case App(fn, _) => Conv.apTerm(fn, eq)
        case other => Left(NotOfForm("an application", other))
      }

    /** The shortcut's four equations, assumed, and what `body` proves from them discharged. */
    private def shortcut(body: Vector[Kernel.Thm] => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        hT <- prop(Shortcut)
        h <- LogicError.lift(Kernel.assume(hT))
        hs <- split(h)
        proved <- body(hs)
        out <- rules.disch(hT, proved).flatMap(gen(_, step, iterate))
      } yield out

    private def hypotheses(name: String): R[Vector[Kernel.Thm]] =
      for {
        hT <- prop(Shortcut)
        h <- LogicError.lift(Kernel.assume(hT))
        inst <- spec(k(name), step, iterate).flatMap(mp(_, h))
      } yield Vector(inst)

    /** `2 = SUC (SUC 0)`: `Semiring` reads a numeral as a sum of ones and keeps `SUC` an atom, so the bridge is two steps of addition. */
    private def two: R[Kernel.Thm] =
      for {
        ones <- num("2 = SUC 0 + SUC 0")
        addSuc <- fact("NUM_ADD_SUC")
        addZero <- fact("NUM_ADD_ZERO")
        out <- rw(addSuc, ones).flatMap(rw(addZero, _))
      } yield out

    /** `0 < 2` over the naturals. */
    def twoPositive: R[Kernel.Thm] =
      for {
        atSuc <- at(fact("NUM_ZERO_LT_SUC"), "0 < SUC (SUC 0)")
        out <- two.flatMap(Conv.sym).flatMap(rw(_, atSuc))
      } yield out

    /** Every natural is `2 j` or `2 j + 1`. */
    def parity: R[Kernel.Thm] =
      for {
        divided <- at(fact("NUM_DIVISION"), "(0:num) < 2 ==> ?k:num. ?i:num. (r:num) = 2 * k + i /\\ i < 2").flatMap(mp(_, k("TWO_POSITIVE")))
        out <- choose(divided, "j") { (jv, inner) =>
          choose(inner, "i") { (iv, both) =>
            val J = s"(${jv.name}:num)"
            val I = s"(${iv.name}:num)"
            for {
              parts <- split(both)
              below <- two.flatMap(rw(_, parts(1)))
              cases1 <- at(fact("NUM_LT_SUC_CASES"), s"$I < SUC (SUC 0) ==> $I < SUC 0 \\/ $I = SUC 0").flatMap(mp(_, below))
              wanted = s"?j:num. (r:num) = 2 * j \\/ r = 2 * j + 1"
              jT <- nm(J)
              small <- for {
                lt1T <- prop(s"$I < SUC 0")
                atZero <- LogicError.lift(Kernel.assume(lt1T))
                cases0 <- at(fact("NUM_LT_SUC_CASES"), s"$I < SUC 0 ==> $I < 0 \\/ $I = 0").flatMap(mp(_, atZero))
                impossible <- for {
                  lt0T <- prop(s"$I < 0")
                  lt0 <- LogicError.lift(Kernel.assume(lt0T))
                  absurd <- specR(fact("NUM_NOT_LT_ZERO"), Right(iv)).flatMap(rules.notElim(_, lt0))
                  goal <- prop(wanted)
                  out <- rules.falsityElim(goal, absurd)
                } yield out
                zero <- for {
                  eqT <- prop(s"$I = 0")
                  eq <- LogicError.lift(Kernel.assume(eqT))
                  even <- rw(eq, parts(0)).flatMap(e => num(s"2 * $J + 0 = 2 * $J").flatMap(rw(_, e)))
                  disj <- prop(s"(r:num) = 2 * $J + 1").flatMap(rules.disjIntro1(_, even))
                  out <- existsIntro(wanted, jT, disj)
                } yield out
                out <- rules.disjElim(cases0, impossible, zero)
              } yield out
              unit <- for {
                eqT <- prop(s"$I = SUC 0")
                eq <- LogicError.lift(Kernel.assume(eqT))
                odd <- rw(eq, parts(0)).flatMap(e => fact("NUM_ONE_SUC").flatMap(Conv.sym).flatMap(rw(_, e)))
                disj <- prop(s"(r:num) = 2 * $J").flatMap(rules.disjIntro2(_, odd))
                out <- existsIntro(wanted, jT, disj)
              } yield out
              out <- rules.disjElim(cases1, small, unit)
            } yield out
          }
        }
        general <- gen(out, r)
      } yield general

    /** The iterate takes its first step first: `iterate x (SUC t) = (iterate:num->num->num) (step x) t`. */
    def commuted: R[Kernel.Thm] =
      shortcut { hs =>
        for {
          body <- prop("!x:num. iterate x (SUC (t:num)) = (iterate:num->num->num) (step x) t")
          proved <- induct(t, body)(
            base => for {
              goal <- prop("(iterate:num->num->num) (x:num) (SUC 0) = (iterate:num->num->num) (step x) 0")
              out <- rewriting(Seq(hs(3), hs(2)), goal)(byRefl).flatMap(gen(_, x))
            } yield out,
            (kk, hyp, goal) => {
              val K = s"(${kk.name}:num)"
              for {
                opened <- at(hs(3), s"(iterate:num->num->num) (x:num) (SUC (SUC $K)) = (step:num->num) (iterate x (SUC $K))")
                ih <- spec(hyp, x)
                moved <- under("(step:num->num) (0:num)", Numbers, ih)
                closed <- at(hs(3), s"(iterate:num->num->num) (step (x:num)) (SUC $K) = (step:num->num) (iterate (step x) $K)").flatMap(Conv.sym)
                out <- trans(opened, moved, closed).flatMap(gen(_, x))
              } yield out
            }
          )
        } yield proved
      }

    /** Moving the start by a multiple of `2^t` moves the `t`-th iterate by a multiple of the same count. */
    def shift: R[Kernel.Thm] =
      shortcut { hs =>
        for {
          commutedHere <- hypotheses("COMMUTED").map(_.head)
          powSuc <- fact("NUM_POW_SUC")
          powZero <- fact("NUM_POW_ZERO")
          body <- prop("!r:num. ?c:num. !q:num. (iterate:num->num->num) (r + NUM_POW 2 (t:num) * q) t = iterate r t + c * q")
          proved <- induct(t, body)(
            base => for {
              goal <- prop("!q:num. (iterate:num->num->num) ((r:num) + NUM_POW 2 0 * q) 0 = iterate r 0 + 1 * q")
              closed <- Logic.stripForall(goal).flatMap { case (vs, g) =>
                rewriting(Seq(hs(2), powZero), g)(semiring.prove).flatMap(gen(_, vs*))
              }
              one <- nm("1")
              found <- existsIntro("?c:num. !q:num. (iterate:num->num->num) ((r:num) + NUM_POW 2 0 * q) 0 = iterate r 0 + c * q", one, closed)
              out <- gen(found, r)
            } yield out,
            (kk, hyp, _) => {
              val K = s"(${kk.name}:num)"
              val P = s"NUM_POW 2 (SUC $K) * (q:num)"
              val wanted = s"?c:num. !q:num. (iterate:num->num->num) ((r:num) + NUM_POW 2 (SUC $K) * q) (SUC $K) = iterate r (SUC $K) + c * q"
              for {
                split <- at(k("PARITY"), "?j:num. (r:num) = 2 * j \\/ r = 2 * j + 1")
                out <- choose(split, "j") { (jv, cases) =>
                  val J = s"(${jv.name}:num)"
                  for {
                    evenCase <- for {
                      eT <- prop(s"(r:num) = 2 * $J")
                      e <- LogicError.lift(Kernel.assume(eT))
                      ih <- at(hyp, s"?c:num. !q:num. (iterate:num->num->num) ($J + NUM_POW 2 $K * q) $K = iterate $J $K + c * q")
                      out <- choose(ih, "c") { (cv, moved) =>
                        val C = s"(${cv.name}:num)"
                        for {
                          first <- at(commutedHere, s"(iterate:num->num->num) (2 * $J + $P) (SUC $K) = (iterate:num->num->num) (step (2 * $J + $P)) $K")
                          regroup <- prop(s"2 * $J + $P = 2 * ($J + NUM_POW 2 $K * q)").flatMap(g => rewriting(Seq(powSuc), g)(semiring.prove))
                          halved <- at(hs(0), s"(step:num->num) (2 * ($J + NUM_POW 2 $K * (q:num))) = $J + NUM_POW 2 $K * q")
                          stepped <- under("(step:num->num) (0:num)", Numbers, regroup).flatMap(Conv.trans(_, halved))
                          inside <- under(s"(iterate:num->num->num) (0:num)", Maps, stepped).flatMap(Conv.apThm(_, kk))
                          shifted <- spec(moved, q)
                          left <- trans(first, inside, shifted)
                          start <- at(commutedHere, s"(iterate:num->num->num) (2 * $J) (SUC $K) = (iterate:num->num->num) (step (2 * $J)) $K")
                          base <- at(hs(0), s"(step:num->num) (2 * $J) = $J")
                          right <- under("(iterate:num->num->num) (0:num)", Maps, base).flatMap(Conv.apThm(_, kk)).flatMap(Conv.trans(start, _))
                          goal <- prop(s"(iterate:num->num->num) (2 * $J + $P) (SUC $K) = (iterate:num->num->num) (2 * $J) (SUC $K) + $C * q")
                          proved <- rewriting(Seq(left, right), goal)(byRefl)
                          back <- Conv.sym(e).flatMap(rw(_, proved)).flatMap(gen(_, q))
                          cT <- nm(C)
                          out <- existsIntro(wanted, cT, back)
                        } yield out
                      }
                    } yield (eT, out)
                    oddCase <- for {
                      oT <- prop(s"(r:num) = 2 * $J + 1")
                      o <- LogicError.lift(Kernel.assume(oT))
                      ih <- at(hyp, s"?c:num. !q:num. (iterate:num->num->num) (3 * $J + 2 + NUM_POW 2 $K * q) $K = (iterate:num->num->num) (3 * $J + 2) $K + c * q")
                      out <- choose(ih, "c") { (cv, moved) =>
                        val C = s"(${cv.name}:num)"
                        for {
                          first <- at(commutedHere, s"(iterate:num->num->num) (2 * $J + 1 + $P) (SUC $K) = (iterate:num->num->num) (step (2 * $J + 1 + $P)) $K")
                          regroup <- prop(s"2 * $J + 1 + $P = 2 * ($J + NUM_POW 2 $K * q) + 1").flatMap(g => rewriting(Seq(powSuc), g)(semiring.prove))
                          tripled <- at(hs(1), s"(step:num->num) (2 * ($J + NUM_POW 2 $K * (q:num)) + 1) = 3 * ($J + NUM_POW 2 $K * q) + 2")
                          spread <- num(s"3 * ($J + NUM_POW 2 $K * (q:num)) + 2 = 3 * $J + 2 + NUM_POW 2 $K * (3 * q)")
                          stepped <- under("(step:num->num) (0:num)", Numbers, regroup).flatMap(trans(_, tripled, spread))
                          inside <- under(s"(iterate:num->num->num) (0:num)", Maps, stepped).flatMap(Conv.apThm(_, kk))
                          three <- nm("3 * (q:num)")
                          shifted <- spec(moved, three)
                          scaled <- num(s"$C * (3 * (q:num)) = (3 * $C) * q")
                          left <- trans(first, inside, shifted).flatMap(rw(scaled, _))
                          start <- at(commutedHere, s"(iterate:num->num->num) (2 * $J + 1) (SUC $K) = (iterate:num->num->num) (step (2 * $J + 1)) $K")
                          base <- at(hs(1), s"(step:num->num) (2 * $J + 1) = 3 * $J + 2")
                          right <- under("(iterate:num->num->num) (0:num)", Maps, base).flatMap(Conv.apThm(_, kk)).flatMap(Conv.trans(start, _))
                          goal <- prop(s"(iterate:num->num->num) (2 * $J + 1 + $P) (SUC $K) = (iterate:num->num->num) (2 * $J + 1) (SUC $K) + (3 * $C) * q")
                          proved <- rewriting(Seq(left, right), goal)(byRefl)
                          back <- Conv.sym(o).flatMap(rw(_, proved)).flatMap(gen(_, q))
                          cT <- nm(s"3 * $C")
                          out <- existsIntro(wanted, cT, back)
                        } yield out
                      }
                    } yield (oT, out)
                    out <- rules.disjElim(cases, evenCase._2, oddCase._2)
                  } yield out
                }
                general <- gen(out, r)
              } yield general
            }
          )
        } yield proved
      }

    /** `term` with free variables replaced, through the kernel's own substitution. */
    private def substitute(map: Map[FVar, Term], term: Term): R[Term] =
      LogicError.lift(Kernel.inst(map, Conv.refl(term))).flatMap(th =>
        Term.destEq(th.conclusion).map(_._1).toRight(NotOfForm("an equation", th.conclusion)))

    /** `?x. P x` from `holds`, which proves `P witness` up to beta. */
    private def introduce(predicate: Term, witness: Term, holds: Kernel.Thm): R[Kernel.Thm] =
      for {
        applied <- LogicError.lift(Term.app(predicate, witness))
        root <- Conv.betaRoot(applied)
        wanted <- Term.destEq(root.conclusion).map(_._2).toRight(NotOfForm("an equation", root.conclusion))
        toNormal <- Conv.betaNormalise(wanted)
        fromHolds <- Conv.betaNormalise(holds.conclusion)
        back <- Conv.sym(toNormal)
        bridge <- Conv.trans(fromHolds, back)
        moved <- LogicError.lift(Kernel.eqMp(bridge, holds))
        out <- rules.existsIntro(predicate, witness, moved)
      } yield out

    /** `a * w = b * w` from `a = b`, for `times` the product. */
    private def scaleRight(times: Term, eq: Kernel.Thm, w: Term): R[Kernel.Thm] =
      Conv.apTerm(times, eq).flatMap(Conv.apThm(_, w))

    private def predicateOf(text: String): R[Term] =
      prop(text).flatMap(e => logic.destExistsPredicate(e).toRight(NotOfForm("an existential", e)))

    /**
     * On each class modulo `2^t` the `t`-th iterate is affine in the start.
     *
     * The shift says `iterate (r + 2^t q) t = iterate r t + c_r q`, with `c_r` named by choice. At
     * `r = n mod 2^t` and `q = n div 2^t` that is `iterate n t`, and `q = (n - r) / 2^t` makes it
     * `c_r / 2^t * n + (iterate r t - c_r / 2^t * r)`: the slope and the offset of the class.
     */
    def affine: R[Kernel.Thm] =
      shortcut { hs =>
        val av = Term.variable("a", Type.fun(Numbers, Reals))
        val bv = Term.variable("b", Type.fun(Numbers, Reals))
        val cv = Term.variable("cvar", Numbers)
        for {
          shifted <- hypotheses("SHIFT").map(_.head)
          classOf <- spec(shifted, t, r)
          named <- classical.witness(classOf).flatMap(beta)
          chosen <- Logic.stripForall(named.conclusion).flatMap { case (_, body) =>
            Term.destEq(body).flatMap(e => e._2 match {
              case App(App(_, _), App(App(_, c), _)) => Some(c)
              case _ => None
            }).toRight(NotOfForm("an affine shift", body))
          }
          slopeAt <- term(s"real_of_num (cvar:num) / real_of_num ($Modulus)", Reals).flatMap(substitute(Map(cv -> chosen), _))
          slope <- LogicError.lift(Term.abs(r, slopeAt))
          offsetAt <- term(s"real_of_num ((iterate:num->num->num) (r:num) t) - real_of_num (cvar:num) / real_of_num ($Modulus) * real_of_num r", Reals)
            .flatMap(substitute(Map(cv -> chosen), _))
          offset <- LogicError.lift(Term.abs(r, offsetAt))
          residue <- nm(s"NUM_MOD (n:num) ($Modulus)")
          quotient <- nm(s"NUM_DIV (n:num) ($Modulus)")
          division <- at(fact("NUM_DIV_MOD"), s"$Modulus * NUM_DIV (n:num) ($Modulus) + NUM_MOD n ($Modulus) = n")
          atClass <- LogicError.lift(Kernel.inst(Map(r -> residue), named)).flatMap(spec(_, quotient))
          reordered <- num(s"NUM_MOD (n:num) ($Modulus) + $Modulus * NUM_DIV n ($Modulus) = $Modulus * NUM_DIV n ($Modulus) + NUM_MOD n ($Modulus)")
            .flatMap(Conv.trans(_, division))
          atN <- rw(reordered, atClass)
          realOf <- LogicError.lift(theory.constant(Peano.EmbeddingName, Type.fun(Numbers, Reals)))
          realAdd <- fact("NUM_REAL_ADD")
          realMul <- fact("NUM_REAL_MUL")
          inReals <- Conv.apTerm(realOf, atN).flatMap(rw(realAdd, _)).flatMap(rw(realMul, _))
          nReal <- Conv.apTerm(realOf, division).flatMap(rw(realAdd, _)).flatMap(rw(realMul, _)).flatMap(Conv.sym)
          positive <- at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $Modulus").flatMap(mp(_, k("TWO_POSITIVE")))
          above <- at(fact("NUM_REAL_LT"), s"(0:num) < $Modulus ==> real_of_num 0 + 1 <= real_of_num ($Modulus)").flatMap(mp(_, positive))
          zero <- fact("NUM_REAL_ZERO")
          bigEnough <- rw(zero, above)
          notZero <- for {
            zT <- prop(s"real_of_num ($Modulus) = 0")
            z <- LogicError.lift(Kernel.assume(zT))
            absurd <- lin(Seq(z, bigEnough), "F")
            out <- rules.notIntro(zT, absurd)
          } yield out
          inverse <- at(fact("MUL_INVERSE"),
            s"~(real_of_num ($Modulus) = 0) ==> real_of_num ($Modulus) * inv (real_of_num ($Modulus)) = 1").flatMap(mp(_, notZero))
          cancel <- for {
            yT <- prop("~((y:real) = 0)")
            y <- LogicError.lift(Kernel.assume(yT))
            spread <- prop("(x:real) / (y:real) * y = x * (y * inv y)").flatMap(ring.prove)
            inv <- at(fact("MUL_INVERSE"), "~((y:real) = 0) ==> y * inv y = 1").flatMap(mp(_, y))
            one <- prop("(x:real) * 1 = x").flatMap(ring.prove)
            out <- rw(inv, spread).flatMap(Conv.trans(_, one))
          } yield (yT, out)
          chosenAt <- substitute(Map(r -> residue), chosen)
          slopeTerm <- LogicError.lift(Term.app(realOf, chosenAt))
          modulusTerm <- term(s"real_of_num ($Modulus)", Reals)
          quotientTerm <- LogicError.lift(Term.app(realOf, quotient))
          xv = Term.variable("x", Reals)
          yv = Term.variable("y", Reals)
          cancelled <- rules.disch(cancel._1, cancel._2)
            .flatMap(th => LogicError.lift(Kernel.inst(Map(xv -> slopeTerm, yv -> modulusTerm), th)))
            .flatMap(mp(_, notZero))
          scaledCancel <- Term.destEq(cancelled.conclusion) match {
            case Some((App(App(times, _), _), _)) => scaleRight(times, cancelled, quotientTerm)
            case _ => Left(NotOfForm("a product", cancelled.conclusion))
          }
          goalAll <- prop(Affine).flatMap(substitute(Map(av -> slope, bv -> offset), _)).flatMap(normal)
          stripped <- Logic.stripForall(goalAll)
          (bound, body) = stripped
          nv <- bound.headOption.toRight(NotOfForm("a claim about every start", goalAll))
          renamed <- LogicError.lift(Kernel.inst(Map(n -> nv), inReals))
          renamedN <- LogicError.lift(Kernel.inst(Map(n -> nv), nReal))
          renamedCancel <- LogicError.lift(Kernel.inst(Map(n -> nv), scaledCancel))
          atEvery <- linAfter(Seq(renamedN), Seq(renamed, renamedCancel), body).flatMap(gen(_, nv))
          forB <- predicateOf(s"?b:num->real. $Affine").flatMap(substitute(Map(av -> slope), _))
          withB <- introduce(forB, offset, atEvery)
          forA <- predicateOf(s"?a:num->real. ?b:num->real. $Affine")
          withA <- introduce(forA, slope, withB)
          out <- gen(withA, t)
        } yield out
      }

    /**
     * The source's form (C): the slope and the offset of the class are functions of the residue,
     * so each is its own discrete Fourier series over the residues, and the two series are one.
     */
    def dftForm: R[Kernel.Thm] =
      shortcut { hs =>
        val cosineAt = s"cos (${angle("s * (n:num)")})"
        val sineAt = s"sin (${angle("s * (n:num)")})"
        def series(f: String): String =
          s"${coefficient(f, "cos")} * $cosineAt + ${coefficient(f, "sin")} * $sineAt"
        val x = "real_of_num (n:num)"
        for {
          classes <- hypotheses("COLLATZ_AFFINE_ON_CLASSES").map(_.head)
          atT <- spec(classes, t)
          out <- choose(atT, "a") { (av, withA) =>
            choose(withA, "b") { (bv, affineHolds) =>
              for {
                positive <- at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $Modulus").flatMap(mp(_, k("TWO_POSITIVE")))
                modulus <- nm(Modulus)
                slopeSeries <- spec(k("REAL_DFT_INVERSION"), av, modulus, n).flatMap(mp(_, positive))
                offsetSeries <- spec(k("REAL_DFT_INVERSION"), bv, modulus, n).flatMap(mp(_, positive))
                atN <- spec(affineHolds, n)
                expanded <- rw(slopeSeries, atN).flatMap(rw(offsetSeries, _))
                inside <- at(fact("SUM_SCALE_RIGHT"),
                  s"Sum (\\s:num. (${series("a")}) * $x) ($Modulus) = Sum (\\s:num. ${series("a")}) ($Modulus) * $x").flatMap(Conv.sym)
                joined <- at(fact("SUM_ADD"),
                  s"Sum (\\s:num. (${series("a")}) * $x + (${series("b")})) ($Modulus) = " +
                    s"Sum (\\s:num. (${series("a")}) * $x) ($Modulus) + Sum (\\s:num. ${series("b")}) ($Modulus)").flatMap(Conv.sym)
                pointwise <- prop(s"(${series("a")}) * $x + (${series("b")}) = " +
                  s"(${coefficient("a", "cos")} * $x + ${coefficient("b", "cos")}) * $cosineAt + " +
                  s"(${coefficient("a", "sin")} * $x + ${coefficient("b", "sin")}) * $sineAt").flatMap(ring.prove)
                sv = Term.variable("s", Numbers)
                regrouped <- sumCongReal(sv, pointwise, modulus)
                movedIn <- rw(inside, expanded)
                spectral <- trans(movedIn, joined, regrouped).flatMap(gen(_, n))
                both <- conj(affineHolds, spectral)
                forB <- predicateOf(s"?b:num->real. ($Affine) /\\ ($Spectral)")
                withB <- introduce(forB, bv, both)
                forA <- predicateOf(s"?a:num->real. ?b:num->real. ($Affine) /\\ ($Spectral)")
                out <- introduce(forA, av, withB)
              } yield out
            }
          }
          general <- gen(out, t)
        } yield general
      }

    /** `Sum F n = Sum G n` from `F k = G k` at a variable `k` nothing assumes. */
    private def sumCongReal(kv: FVar, pointwise: Kernel.Thm, bound: Term): R[Kernel.Thm] =
      for {
        lambdas <- LogicError.lift(Kernel.abs(kv, pointwise))
        summation <- LogicError.lift(theory.constant(Series.SumName, Type.fun(Type.fun(Numbers, Reals), Type.fun(Numbers, Reals))))
        out <- Conv.apTerm(summation, lambdas).flatMap(Conv.apThm(_, bound))
      } yield out
    /**
     * The hypotheses can all hold at once, so the two theorems over them are not vacuous: the map
     * by cases on the remainder, and its iterate by the recursion theorem at `num -> num`.
     */
    def exists: R[Kernel.Thm] = {
      val Map2 = "\\m:num. COND (NUM_MOD m 2 = 0) (NUM_DIV m 2) (3 * NUM_DIV m 2 + 2)"
      val kv = Term.variable("k", Numbers)
      def atNum(thm: Kernel.Thm): Kernel.Thm = Kernel.instType(Map(Classical.TypeVariable -> Numbers), thm)
      for {
        shortcutMap <- term(Map2, Maps)
        condTrue <- fact("COND_TRUE").map(atNum)
        condFalse <- fact("COND_FALSE").map(atNum)
        unique <- fact("NUM_DIVISION_UNIQUE")
        oneSuc <- fact("NUM_ONE_SUC")
        twoSuc <- two.flatMap(t2 => Conv.sym(oneSuc).flatMap(rw(_, t2)))
        oneBelow <- at(fact("NUM_LT_SUC"), "1 < SUC 1").flatMap(lt => Conv.sym(twoSuc).flatMap(rw(_, lt)))
        oneNotZero <- at(fact("NUM_SUC_NOT_ZERO"), "~(SUC 0 = 0)").flatMap(nz => Conv.sym(oneSuc).flatMap(rw(_, nz)))
        zeroRefl <- nm("0").map(Conv.refl)
        evenClause <- for {
          applied <- term(s"($Map2) (2 * (k:num))", Numbers).flatMap(Conv.betaRoot)
          division <- at(fact("NUM_DIV_MOD"), "2 * NUM_DIV (2 * (k:num)) 2 + NUM_MOD (2 * k) 2 = 2 * k")
          padded <- num("2 * (k:num) = 2 * k + 0").flatMap(Conv.trans(division, _))
          below <- at(fact("NUM_MOD_LT"), "(0:num) < 2 ==> NUM_MOD (2 * (k:num)) 2 < 2").flatMap(mp(_, k("TWO_POSITIVE")))
          both <- conjs(padded, below, k("TWO_POSITIVE"))
          parts <- at(unique, "2 * NUM_DIV (2 * (k:num)) 2 + NUM_MOD (2 * k) 2 = 2 * k + 0 /\\ NUM_MOD (2 * k) 2 < 2 /\\ (0:num) < 2 ==> " +
            "NUM_DIV (2 * k) 2 = k /\\ NUM_MOD (2 * k) 2 = 0").flatMap(mp(_, both)).flatMap(split)
          tailGoal <- prop("COND (NUM_MOD (2 * (k:num)) 2 = 0) (NUM_DIV (2 * k) 2) (3 * NUM_DIV (2 * k) 2 + 2) = k")
          tail <- rewriting(Seq(parts(1), parts(0)), tailGoal) { reduced =>
            for {
              kk <- nm("k:num")
              other <- nm("3 * (k:num) + 2")
              isZero <- prop("(0:num) = 0")
              c <- spec(condTrue, isZero, kk, other).flatMap(mp(_, zeroRefl))
            } yield c
          }
          out <- Conv.trans(applied, tail).flatMap(gen(_, kv))
        } yield out
        oddClause <- for {
          applied <- term(s"($Map2) (2 * (k:num) + 1)", Numbers).flatMap(Conv.betaRoot)
          division <- at(fact("NUM_DIV_MOD"), "2 * NUM_DIV (2 * (k:num) + 1) 2 + NUM_MOD (2 * k + 1) 2 = 2 * k + 1")
          below <- at(fact("NUM_MOD_LT"), "(0:num) < 2 ==> NUM_MOD (2 * (k:num) + 1) 2 < 2").flatMap(mp(_, k("TWO_POSITIVE")))
          both <- conjs(division, below, oneBelow)
          parts <- at(unique, "2 * NUM_DIV (2 * (k:num) + 1) 2 + NUM_MOD (2 * k + 1) 2 = 2 * k + 1 /\\ NUM_MOD (2 * k + 1) 2 < 2 /\\ (1:num) < 2 ==> " +
            "NUM_DIV (2 * k + 1) 2 = k /\\ NUM_MOD (2 * k + 1) 2 = 1").flatMap(mp(_, both)).flatMap(split)
          tailGoal <- prop("COND (NUM_MOD (2 * (k:num) + 1) 2 = 0) (NUM_DIV (2 * k + 1) 2) (3 * NUM_DIV (2 * k + 1) 2 + 2) = 3 * k + 2")
          tail <- rewriting(Seq(parts(1), parts(0)), tailGoal) { reduced =>
            for {
              kk <- nm("k:num")
              other <- nm("3 * (k:num) + 2")
              isZero <- prop("(1:num) = 0")
              c <- spec(condFalse, isZero, kk, other).flatMap(mp(_, oneNotZero))
            } yield c
          }
          out <- Conv.trans(applied, tail).flatMap(gen(_, kv))
        } yield out
        recursive <- Right(Kernel.instType(Map("a" -> Maps), recursion))
        identityMap <- term("\\x:num. x", Maps)
        stepper <- term(s"\\g:num->num. \\i:num. \\x:num. ($Map2) (g x)", Type.fun(Maps, Type.fun(Numbers, Maps)))
        made <- spec(recursive, identityMap, stepper)
        out <- choose(made, "fn") { (fn, clauses) =>
          for {
            parts <- split(clauses)
            iterateTerm <- term("\\x:num. \\t:num. (fn:num->num->num) t x", Iterates)
            atZero <- for {
              applied <- Conv.apThm(parts(0), x)
              reduced <- beta(applied)
              lhs <- term("(\\x:num. \\t:num. (fn:num->num->num) t x) (x:num) 0", Numbers).flatMap(Conv.betaNormalise)
              out <- Conv.trans(lhs, reduced).flatMap(gen(_, x))
            } yield out
            atSuc <- for {
              opened <- spec(parts(1), t)
              applied <- Conv.apThm(opened, x).flatMap(beta)
              lhs <- term("(\\x:num. \\t:num. (fn:num->num->num) t x) (x:num) (SUC t)", Numbers).flatMap(Conv.betaNormalise)
              rhs <- term(s"($Map2) ((\\x:num. \\t:num. (fn:num->num->num) t x) (x:num) t)", Numbers).flatMap(Conv.betaNormalise)
              out <- Conv.trans(lhs, applied).flatMap(e => Conv.sym(rhs).flatMap(Conv.trans(e, _))).flatMap(gen(_, x, t))
            } yield out
            all <- conjs(evenClause, oddClause, atZero, atSuc)
            forIterate <- predicateOf(s"?iterate:num->num->num. $Shortcut").flatMap(substitute(Map(step -> shortcutMap), _))
            withIterate <- introduce(forIterate, iterateTerm, all)
            forStep <- predicateOf(StatementsMap("COLLATZ_SHORTCUT_EXISTS"))
            out <- introduce(forStep, shortcutMap, withIterate)
          } yield out
        }
      } yield out
    }
  }
}
