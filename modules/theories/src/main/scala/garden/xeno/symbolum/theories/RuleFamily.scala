package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The family of three-cell rules `R(l, c, r) = l XOR h(c, r)` as maps on the naturals, proved once for
 * every `h : bool -> bool -> bool`, with two instances: Rule 30's map (`h = OR`, in [[RuleThirty]]) and
 * the Pascal map `D n = n XOR 2 n` (`h c r = c`, here). `docs/adr/0067` is the decision, and Mycelium
 * note 917b3939 is the account a reader without the kernel can follow.
 *
 * Not a development: it declares nothing, and `Complex` publishes what it proves.
 *
 * == The equations ==
 *
 * The library has no bitwise operations, so a member of the family is given, as Rule 30's map was, by
 * two equations on halving through `g p q n`, the map with the two bits below `n` given as `p` (just
 * below) and `q`: `g p q (2 m)` and `g p q (2 m + 1)` are the low bit of the value, `h p q` or its
 * negation, plus twice `g` at `m`. The map itself is `g F F`. Both equations hold at `m = 0`, which
 * forces `g F F 0 = COND (h F F) 1 0 + 2 * g F F 0`; over the naturals that has a solution exactly
 * when `h F F` is false, which is why `RULE_FAMILY_EXISTS` asks for it: a rule that turns a white
 * background black has no map on the naturals, its rows being infinite.
 *
 * == What is proved for every member ==
 *
 * `RULE_FAMILY_STEP` folds the two equations into one. The low `k` bits of the value depend only on
 * the low `k` bits of the argument, and equal values modulo `2^k` come from equal arguments modulo
 * `2^k`: both are inductions on `k` through the step, and together with `TRIANGULAR_OF_INJECTIVE` they
 * make every member triangular (`RULE_FAMILY_TRIANGULAR`, `docs/adr/0066`). The case analysis is on the
 * proposition `h p q` itself, never on `p` and `q`, so nothing in it depends on which `h` it is. The three
 * bit theorems say what the equations mean: bit `j + 2` of `g p q x` is bit `j + 2` of `x` XOR `h` of
 * the two bits below it, which is the rule. `RULE_FAMILY_EXISTS` builds `g` with a counter that halves
 * its argument a given number of times and stops changing once two to that number passes the argument.
 *
 * == What it does not say ==
 *
 * Nothing about a single orbit or the centre column of any member: those are the open questions the
 * note describes, and for the Pascal map the closed form through Lucas' theorem is not proved here.
 */
private[theories] object RuleFamily {

  type R[A] = Either[LogicError, A]

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Rules: Type = Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool))
  private val Steps: Type = Type.fun(Type.Bool, Type.fun(Type.Bool, Type.fun(Numbers, Numbers)))

  private val H = "(h:bool->bool->bool)"
  private val G = "(g:bool->bool->num->num)"

  /** Bit `j` of `y`. */
  private def bit(j: String, y: String): String = s"NUM_MOD (NUM_DIV ($y) (NUM_POW 2 ($j))) 2 = 1"

  /**
   * The two equations on halving of the member whose rule is `rule`, for the map named `g`: the text
   * every instance writes, so that the family's equations at `rule` are its equations up to beta.
   */
  private[theories] def equations(rule: (String, String) => String, g: String = G): String =
    s"(!p:bool. !q:bool. !m:num. $g p q (2 * m) = COND (${rule("p", "q")}) 1 0 + 2 * $g F p m) /\\ " +
      s"(!p:bool. !q:bool. !m:num. $g p q (2 * m + 1) = COND (${rule("p", "q")}) 0 1 + 2 * $g T p m)"

  private val Family: String = equations((a, b) => s"$H $a $b")

  /** The Pascal map's rule: the new bit is the old one XOR the bit just below. */
  private val Pascal: String = equations((a, _) => a)

  private def overFamily(claim: String): String = s"!h:bool->bool->bool. !g:bool->bool->num->num. $Family ==> $claim"

  private def overPascal(claim: String): String = s"!g:bool->bool->num->num. $Pascal ==> $claim"

  private val Map0: String => String = x => s"$G F F ($x)"

  /** What `Complex` publishes from here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    "RULE_FAMILY_STEP" -> overFamily(
      s"!p:bool. !q:bool. !n:num. $G p q n = COND (~(($H p q) = (NUM_MOD n 2 = 1))) 1 0 + 2 * $G (NUM_MOD n 2 = 1) p (NUM_DIV n 2)"),
    "RULE_FAMILY_TRIANGULAR" -> overFamily(Triangular.triangular(Map0)),
    "RULE_FAMILY_EXISTS" -> s"!h:bool->bool->bool. ~($H F F) ==> ?g:bool->bool->num->num. $Family",
    "RULE_FAMILY_BIT_ZERO" -> overFamily(s"!p:bool. !q:bool. !x:num. (${bit("0", s"$G p q x")}) = ~(($H p q) = (NUM_MOD x 2 = 1))"),
    "RULE_FAMILY_BIT_SUC" -> overFamily(
      s"!j:num. !p:bool. !q:bool. !x:num. (${bit("SUC j", s"$G p q x")}) = (${bit("j", s"$G (NUM_MOD x 2 = 1) p (NUM_DIV x 2)")})"),
    "RULE_FAMILY_BIT_RULE" -> overFamily(
      s"!j:num. !p:bool. !q:bool. !x:num. (${bit("SUC (SUC j)", s"$G p q x")}) = " +
        s"~((${bit("SUC (SUC j)", "x")}) = $H (${bit("SUC j", "x")}) (${bit("j", "x")}))"),
    "PASCAL_MAP_EXISTS" -> s"?g:bool->bool->num->num. $Pascal",
    "PASCAL_MAP_TRIANGULAR" -> overPascal(Triangular.triangular(Map0)),
    "PASCAL_MAP_BITS" -> overPascal(
      s"!x:num. ((${bit("0", Map0("x"))}) = (${bit("0", "x")})) /\\ " +
        s"(!j:num. (${bit("SUC j", Map0("x"))}) = ~((${bit("SUC j", "x")}) = (${bit("j", "x")})))")
  )

  private lazy val StatementsMap: Map[String, String] = Statements.toMap

  private val Order: Vector[(String, Proofs => R[Kernel.Thm])] = Vector(
    "MOD_ONE" -> (_.steps.modOneTheorem),
    "COND_BELOW_TWO" -> (_.steps.condBelowTwoTheorem),
    "MOD_DOUBLE" -> (_.steps.modDoubleTheorem),
    "DIV_MOD_SHIFT" -> (_.steps.divModShiftTheorem),
    "MOD_TWO_SHIFT" -> (_.steps.modTwoShiftTheorem),
    "BELOW_POWER" -> (_.steps.belowPowerTheorem),
    "NUM_NOT_LE" -> (_.steps.notLeTheorem),
    "DIV_ONE" -> (_.steps.divOneTheorem),
    "BIT_HALVE" -> (_.steps.bitHalveTheorem),
    "BIT_LOW" -> (_.steps.bitLowTheorem),
    "RULE_FAMILY_STEP" -> (_.step),
    "FAMILY_RESIDUES" -> (_.residues),
    "FAMILY_INJECTIVE" -> (_.injective),
    "RULE_FAMILY_TRIANGULAR" -> (_.triangular),
    "RULE_FAMILY_EXISTS" -> (_.exists),
    "RULE_FAMILY_BIT_ZERO" -> (_.bitZero),
    "RULE_FAMILY_BIT_SUC" -> (_.bitSuc),
    "RULE_FAMILY_BIT_RULE" -> (_.bitRule),
    "PASCAL_MAP_EXISTS" -> (_.pascalExists),
    "PASCAL_MAP_TRIANGULAR" -> (_.pascalTriangular),
    "PASCAL_MAP_BITS" -> (_.pascalBits)
  )

  /** The facts [[Statements]] names, derived with `kit`; `held` must carry `TRIANGULAR_OF_INJECTIVE`. */
  def prove(kit: ComplexKit, semiring: Semiring, recursion: Kernel.Thm, held: Map[String, Kernel.Thm]): R[Map[String, Kernel.Thm]] = {
    val steps = new NumberSteps(kit, semiring)
    ComplexKit.derive(Order, Statements, held)(known => new Proofs(kit, steps, recursion, known))
  }

  private[theories] final class Proofs(val kit: ComplexKit, val steps: NumberSteps, recursion: Kernel.Thm, known: Map[String, Kernel.Thm]) {
    import kit.*
    import steps.*

    def k(name: String): Kernel.Thm = known(name)

    private val hvar = Term.variable("h", Rules)
    private val gvar = Term.variable("g", Steps)

    /** The family's equations assumed, and what `body` proves from them discharged over `h` and `g`. */
    private def familyRule(body: Vector[Kernel.Thm] => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        hT <- prop(Family)
        h <- LogicError.lift(Kernel.assume(hT))
        hs <- split(h)
        proved <- body(hs)
        out <- rules.disch(hT, proved).flatMap(gen(_, hvar, gvar))
      } yield out

    /** A fact about the family, at the equations assumed. */
    private def underFamily(name: String): R[Kernel.Thm] =
      for {
        hT <- prop(Family)
        h <- LogicError.lift(Kernel.assume(hT))
        out <- spec(k(name), hvar, gvar).flatMap(mp(_, h))
      } yield out

    /** `h pb qb`, the proposition every case analysis below splits on. */
    private def ruleAt(p: String, q: String): R[Term] = prop(s"$H $p $q")

    /** The two equations as one: `g p q n` is its low bit and twice the map of the half. */
    def step: R[Kernel.Thm] =
      familyRule { hs =>
        val P = "(pb:bool)"; val Q = "(qb:bool)"; val N = "(nb:num)"
        val D = s"NUM_DIV $N 2"; val Mo = s"NUM_MOD $N 2"; val E = s"($Mo = 1)"
        val (pv, qv, nv) = (Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("nb", Numbers))
        for {
          goal <- prop(s"$G $P $Q $N = COND (~(($H $P $Q) = $E)) 1 0 + 2 * $G $E $P ($D)")
          dm <- at(fact("NUM_DIV_MOD"), s"2 * $D + $Mo = $N")
          lt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> $Mo < 2").flatMap(mp(_, t2)))
          either <- binary(Mo, lt)
          zeroF <- zeroOneFalse
          oneT <- oneOneTrue
          atom <- ruleAt(P, Q)
          close = byCases(List(atom))(lits => deciding(lits)(numClose)) _
          even <- for {
            h <- assumed(s"$Mo = 0")
            inst <- at(hs(0), s"$G $P $Q (2 * $D) = COND ($H $P $Q) 1 0 + 2 * $G F $P ($D)")
            noZero <- at(fact("NUM_ADD_ZERO"), s"2 * $D + 0 = 2 * $D")
            twice <- rw(h._2, dm).flatMap(rw(noZero, _))
            atN <- rw(twice, inst)
            out <- rewriting(Seq(atN, h._2, zeroF), goal)(close)
          } yield out
          odd <- for {
            h <- assumed(s"$Mo = 1")
            inst <- at(hs(1), s"$G $P $Q (2 * $D + 1) = COND ($H $P $Q) 0 1 + 2 * $G T $P ($D)")
            twice <- rw(h._2, dm)
            atN <- rw(twice, inst)
            out <- rewriting(Seq(atN, h._2, oneT), goal)(close)
          } yield out
          out <- rules.disjElim(either, even, odd).flatMap(gen(_, pv, qv, nv))
        } yield out
      }

    /** The low `k` bits of the value depend only on the low `k` bits of the argument. */
    def residues: R[Kernel.Thm] =
      familyRule { _ =>
        val (kv, pv, qv, nv) = (Term.variable("kb", Numbers), Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("nb", Numbers))
        def claim(K: String) =
          s"NUM_MOD ($G (pb:bool) (qb:bool) (nb:num)) (NUM_POW 2 ($K)) = NUM_MOD ($G pb qb (NUM_MOD nb (NUM_POW 2 ($K)))) (NUM_POW 2 ($K))"
        for {
          stepHere <- underFamily("RULE_FAMILY_STEP")
          body <- prop(s"!pb:bool. !qb:bool. !nb:num. ${claim("kb:num")}")
          proved <- induct(kv, body)(
            _ =>
              for {
                goal <- prop(claim("0"))
                powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
                out <- rewriting(Seq(powZero, k("MOD_ONE")), goal)(byBeta).flatMap(gen(_, pv, qv, nv))
              } yield out,
            (kk, hyp, _) => {
              val K = v(kk.name); val M = s"NUM_POW 2 $K"; val P2 = s"NUM_POW 2 (SUC $K)"
              val N = "(nb:num)"; val Pb = "(pb:bool)"; val Qb = "(qb:bool)"
              val E = s"(NUM_MOD $N 2 = 1)"; val D = s"NUM_DIV $N 2"; val Rr = s"NUM_MOD $N ($P2)"
              val C = s"COND (~(($H $Pb $Qb) = $E)) 1 0"
              val X = s"$G $E $Pb ($D)"; val Xr = s"$G $E $Pb (NUM_MOD ($D) ($M))"
              for {
                goal <- prop(claim(s"SUC $K"))
                atN <- at(stepHere, s"$G $Pb $Qb $N = $C + 2 * $X")
                atR <- at(stepHere, s"$G $Pb $Qb ($Rr) = COND (~(($H $Pb $Qb) = (NUM_MOD ($Rr) 2 = 1))) 1 0 + 2 * $G (NUM_MOD ($Rr) 2 = 1) $Pb (NUM_DIV ($Rr) 2)")
                shifts <- at(k("DIV_MOD_SHIFT"), s"NUM_DIV ($Rr) 2 = NUM_MOD ($D) ($M) /\\ NUM_MOD ($Rr) 2 = NUM_MOD $N 2").flatMap(split)
                small <- at(k("COND_BELOW_TWO"), s"$C < (2:num)")
                swap1 <- num(s"$C + 2 * $X = 2 * $X + $C")
                swap2 <- num(s"$C + 2 * $Xr = 2 * $Xr + $C")
                d1 <- at(k("MOD_DOUBLE"), s"$C < (2:num) ==> NUM_MOD (2 * $X + $C) ($P2) = 2 * NUM_MOD ($X) ($M) + $C").flatMap(mp(_, small))
                d2 <- at(k("MOD_DOUBLE"), s"$C < (2:num) ==> NUM_MOD (2 * $Xr + $C) ($P2) = 2 * NUM_MOD ($Xr) ($M) + $C").flatMap(mp(_, small))
                ih <- at(hyp, s"NUM_MOD ($X) ($M) = NUM_MOD ($G $E $Pb (NUM_MOD ($D) ($M))) ($M)")
                out <- rewriting(Seq(atN, atR) ++ shifts ++ Seq(swap1, swap2, d1, d2, ih), goal)(byBeta).flatMap(gen(_, pv, qv, nv))
              } yield out
            }
          )
        } yield proved
      }

    /** `a = b` for two numbers below 2 whose being 1 is the same proposition. */
    private def equalFromBits(a: String, b: String, aBelow: Kernel.Thm, bBelow: Kernel.Thm, iff: Kernel.Thm): R[Kernel.Thm] =
      for {
        ea <- binary(a, aBelow)
        eb <- binary(b, bBelow)
        wanted <- prop(s"$a = $b")
        zeroOne <- zeroNotOne
        same = (x: Kernel.Thm, y: Kernel.Thm) => rewriting(Seq(x, y), wanted)(byBeta)
        mixed = (x: Kernel.Thm, y: Kernel.Thm) =>
          for {
            moved <- rw(x, iff).flatMap(rw(y, _))
            one <- nm("1").map(Conv.refl)
            zeroIsOne <- LogicError.lift(Kernel.eqMp(moved, one)).orElse(Conv.sym(moved).flatMap(s => LogicError.lift(Kernel.eqMp(s, one))))
            contra <- rules.notElim(zeroOne, zeroIsOne)
            out <- rules.falsityElim(wanted, contra)
          } yield out
        a0 <- assumed(s"$a = 0"); a1 <- assumed(s"$a = 1")
        b0 <- assumed(s"$b = 0"); b1 <- assumed(s"$b = 1")
        c00 <- same(a0._2, b0._2); c01 <- mixed(a0._2, b1._2)
        c10 <- mixed(a1._2, b0._2); c11 <- same(a1._2, b1._2)
        whenA0 <- rules.disjElim(eb, c00, c01)
        whenA1 <- rules.disjElim(eb, c10, c11)
        out <- rules.disjElim(ea, whenA0, whenA1)
      } yield out

    /** Modulo `2^k` the map is injective: equal values come from equal residues. */
    def injective: R[Kernel.Thm] =
      familyRule { _ =>
        val (kv, pv, qv, mv, nv) = (Term.variable("kb", Numbers), Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool),
          Term.variable("mb", Numbers), Term.variable("nb", Numbers))
        val Pb = "(pb:bool)"; val Qb = "(qb:bool)"
        def claim(K: String) =
          s"NUM_MOD ($G $Pb $Qb (mb:num)) (NUM_POW 2 ($K)) = NUM_MOD ($G pb qb (nb:num)) (NUM_POW 2 ($K)) ==> " +
            s"NUM_MOD mb (NUM_POW 2 ($K)) = NUM_MOD nb (NUM_POW 2 ($K))"
        for {
          stepHere <- underFamily("RULE_FAMILY_STEP")
          body <- prop(s"!pb:bool. !qb:bool. !mb:num. !nb:num. ${claim("kb:num")}")
          proved <- induct(kv, body)(
            _ =>
              for {
                goal <- prop(claim("0"))
                powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
                out <- underHyps(goal)((_, c) => rewriting(Seq(powZero, k("MOD_ONE")), c)(byBeta)).flatMap(gen(_, pv, qv, mv, nv))
              } yield out,
            (kk, hyp, _) => {
              val K = v(kk.name); val M = s"NUM_POW 2 $K"; val P2 = s"NUM_POW 2 (SUC $K)"
              def E(z: String) = s"(NUM_MOD ($z:num) 2 = 1)"
              def D(z: String) = s"NUM_DIV ($z:num) 2"
              def C(z: String) = s"COND (~(($H $Pb $Qb) = ${E(z)})) (1:num) 0"
              def X(z: String) = s"$G ${E(z)} $Pb (${D(z)})"
              for {
                goal <- prop(claim(s"SUC $K"))
                out <- underHyps(goal) { (hs_, _) =>
                  val h = hs_.head
                  for {
                    sides <- Seq("mb", "nb").foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, z) =>
                      for {
                        done <- acc
                        atZ <- at(stepHere, s"$G $Pb $Qb ($z:num) = ${C(z)} + 2 * ${X(z)}")
                        swap <- num(s"${C(z)} + 2 * ${X(z)} = 2 * ${X(z)} + ${C(z)}")
                        small <- at(k("COND_BELOW_TWO"), s"${C(z)} < (2:num)")
                        dbl <- at(k("MOD_DOUBLE"), s"${C(z)} < (2:num) ==> NUM_MOD (2 * ${X(z)} + ${C(z)}) ($P2) = 2 * NUM_MOD (${X(z)}) ($M) + ${C(z)}").flatMap(mp(_, small))
                      } yield done ++ Vector(atZ, swap, dbl, small)
                    }
                    reduced <- Seq(0, 1, 2, 4, 5, 6).foldLeft[R[Kernel.Thm]](Right(h))((acc, ix) => acc.flatMap(th => rw(sides(ix), th)))
                    unique <- at(fact("NUM_DIVISION_UNIQUE"),
                      s"2 * NUM_MOD (${X("mb")}) ($M) + ${C("mb")} = 2 * NUM_MOD (${X("nb")}) ($M) + ${C("nb")} /\\ ${C("mb")} < (2:num) /\\ ${C("nb")} < (2:num) ==> " +
                        s"NUM_MOD (${X("mb")}) ($M) = NUM_MOD (${X("nb")}) ($M) /\\ ${C("mb")} = ${C("nb")}")
                    parts <- conjs(reduced, sides(3), sides(7)).flatMap(mp(unique, _)).flatMap(split)
                    (xs, cs) = (parts(0), parts(1))
                    bits <- for {
                      wanted <- prop(s"${E("mb")} = ${E("nb")}")
                      atoms <- Seq(s"$H $Pb $Qb", E("mb"), E("nb")).foldLeft[R[List[Term]]](Right(Nil))((acc, t_) => for { d <- acc; p_ <- prop(t_) } yield d :+ p_)
                      out <- byCases(atoms)(lits => g =>
                        tauto(lits, g).orElse(
                          for {
                            values <- conditionals(cs.conclusion).distinct.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, c) =>
                              for { done <- acc; vv <- condValue(c, lits) } yield done ++ vv.toVector
                            }
                            decided <- values.foldLeft[R[Kernel.Thm]](Right(cs))((acc, e) => acc.flatMap(rw(e, _)))
                            zeroOne <- zeroNotOne
                            contra <- rules.notElim(zeroOne, decided).orElse(Conv.sym(decided).flatMap(rules.notElim(zeroOne, _)))
                            out <- rules.falsityElim(g, contra)
                          } yield out))(wanted)
                    } yield out
                    aligned <- Conv.sym(bits).flatMap(rw(_, xs))
                    ih <- at(hyp, s"NUM_MOD (${X("mb")}) ($M) = NUM_MOD ($G ${E("mb")} $Pb (${D("nb")})) ($M) ==> NUM_MOD (${D("mb")}) ($M) = NUM_MOD (${D("nb")}) ($M)")
                    halves <- mp(ih, aligned)
                    residues <- Seq("mb", "nb").foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, z) =>
                      for {
                        done <- acc
                        dm <- at(fact("NUM_DIV_MOD"), s"2 * ${D(z)} + NUM_MOD ($z:num) 2 = $z")
                        lt <- two.flatMap(t2 => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> NUM_MOD ($z:num) 2 < 2").flatMap(mp(_, t2)))
                        dbl <- at(k("MOD_DOUBLE"), s"NUM_MOD ($z:num) 2 < 2 ==> NUM_MOD (2 * ${D(z)} + NUM_MOD $z 2) ($P2) = 2 * NUM_MOD (${D(z)}) ($M) + NUM_MOD $z 2")
                          .flatMap(mp(_, lt)).flatMap(rw(dm, _))
                      } yield done ++ Vector(dbl, lt)
                    }
                    lows <- equalFromBits("NUM_MOD (mb:num) 2", "NUM_MOD (nb:num) 2", residues(1), residues(3), bits)
                    out <- rewriting(Seq(residues(0), residues(2), halves, lows), goalConclusion(goal))(byBeta)
                  } yield out
                }.flatMap(gen(_, pv, qv, mv, nv))
              } yield out
            }
          )
        } yield proved
      }

    /** Every member is triangular: residues are kept and separated, by `TRIANGULAR_OF_INJECTIVE`. */
    def triangular: R[Kernel.Thm] =
      familyRule { _ =>
        val (kv, mv, nv) = (Term.variable("kb", Numbers), Term.variable("mb", Numbers), Term.variable("nb", Numbers))
        val Kb = "(kb:num)"; val Mb = "(mb:num)"; val Nb = "(nb:num)"; val M = s"NUM_POW 2 $Kb"
        for {
          kept <- underFamily("FAMILY_RESIDUES")
          separated <- underFamily("FAMILY_INJECTIVE")
          keeps <- for {
            held <- assumed(Triangular.agree(Mb, Nb, Kb))
            rm <- at(kept, s"NUM_MOD (${Map0(Mb)}) ($M) = NUM_MOD (${Map0(s"NUM_MOD $Mb ($M)")}) ($M)")
            rn <- at(kept, s"NUM_MOD (${Map0(Nb)}) ($M) = NUM_MOD (${Map0(s"NUM_MOD $Nb ($M)")}) ($M)")
            moved <- rw(held._2, rm)
            out <- Conv.sym(rn).flatMap(trans(moved, _)).flatMap(rules.disch(held._1, _)).flatMap(gen(_, kv, mv, nv))
          } yield out
          separates <- at(separated, s"${Triangular.agree(Map0(Mb), Map0(Nb), Kb)} ==> ${Triangular.agree(Mb, Nb, Kb)}").flatMap(gen(_, kv, mv, nv))
          both <- conj(keeps, separates)
          out <- at(k("TRIANGULAR_OF_INJECTIVE"), s"${Triangular.keepsAndSeparates(Map0)} ==> ${Triangular.triangular(Map0)}").flatMap(mp(_, both))
        } yield out
      }

    /**
     * Every member whose rule keeps a white background white has a map. It is built with a counter:
     * `fn d` halves its argument `d` times and is right on every argument below `2^d`, it stops changing
     * once `2^d` passes the argument, and `g p q n = fn n p q n`. Without `~(h F F)` the base `fn 0`
     * would be wrong at 0, where the map has to add `COND (h F F) 1 0` at every bit above the top.
     */
    def exists: R[Kernel.Thm] = {
      val Fn = "(fn:num->bool->bool->num->num)"
      val Base = s"\\p:bool. \\q:bool. \\n:num. COND ($H p q) 1 0 + 2 * COND ($H F p) 1 0"
      val Stepper = "\\fh:bool->bool->num->num. \\d:num. \\p:bool. \\q:bool. \\n:num. " +
        s"COND (NUM_MOD n 2 = 0) (COND ($H p q) 1 0 + 2 * fh F p (NUM_DIV n 2)) (COND ($H p q) 0 1 + 2 * fh T p (NUM_DIV n 2))"
      val (dv, ev, pv, qv, nv, mv) = (Term.variable("db", Numbers), Term.variable("eb", Numbers), Term.variable("pb", Type.Bool),
        Term.variable("qb", Type.Bool), Term.variable("nb", Numbers), Term.variable("mb", Numbers))
      val Pb = "(pb:bool)"; val Qb = "(qb:bool)"; val N = "(nb:num)"; val Mb = "(mb:num)"
      for {
        white <- assumed(s"~($H F F)")
        (whiteT, whiteH) = white
        atomPQ <- ruleAt(Pb, Qb)
        atomFP <- ruleAt("F", Pb)
        // the base and one more halving agree at 0 once h F F is false
        settle = byCases(List(atomPQ, atomFP), Vector(whiteH))(lits => deciding(lits)(numClose)) _
        recursive <- Right(Kernel.instType(Map("a" -> Steps), recursion))
        base <- term(Base, Steps)
        stepper <- term(Stepper, Type.fun(Steps, Type.fun(Numbers, Steps)))
        made <- spec(recursive, base, stepper)
        out <- choose(made, "fn") { (fn, clauses) =>
          for {
            parts <- split(clauses)
            atZero <- Conv.apThm(parts(0), pv).flatMap(Conv.apThm(_, qv)).flatMap(Conv.apThm(_, nv)).flatMap(beta).flatMap(gen(_, pv, qv, nv))
            atSuc <- spec(parts(1), dv).flatMap(Conv.apThm(_, pv)).flatMap(Conv.apThm(_, qv)).flatMap(Conv.apThm(_, nv)).flatMap(beta)
              .flatMap(gen(_, dv, pv, qv, nv))
            t2 <- two
            m0 <- at(fact("NUM_DIV_MOD_BELOW"), "(0:num) < 2 ==> NUM_DIV 0 2 = 0 /\\ NUM_MOD 0 2 = 0").flatMap(mp(_, t2)).flatMap(split)
            powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
            // one more halving changes nothing below 2^d
            stable <- for {
              body <- prop(s"!pb:bool. !qb:bool. !nb:num. nb < NUM_POW 2 (db:num) ==> $Fn (SUC db) pb qb nb = $Fn db pb qb nb")
              out <- induct(dv, body)(
                _ =>
                  for {
                    goal <- prop(s"$N < NUM_POW 2 0 ==> $Fn (SUC 0) $Pb $Qb $N = $Fn 0 $Pb $Qb $N")
                    out <- underHyps(goal) { (h, c) =>
                      for {
                        zero <- numLin(Seq(h.head, powZero), prop(s"$N = 0").toOption.get)
                        out <- rewriting(Seq(zero, atSuc, atZero) ++ m0, c)(settle)
                      } yield out
                    }.flatMap(gen(_, pv, qv, nv))
                  } yield out,
                (kk, hyp, _) => {
                  val D = v(kk.name); val Hf = s"NUM_DIV $N 2"
                  for {
                    goal <- prop(s"$N < NUM_POW 2 (SUC $D) ==> $Fn (SUC (SUC $D)) $Pb $Qb $N = $Fn (SUC $D) $Pb $Qb $N")
                    out <- underHyps(goal) { (h, c) =>
                      for {
                        dm <- at(fact("NUM_DIV_MOD"), s"2 * $Hf + NUM_MOD $N 2 = $N")
                        ps <- at(fact("NUM_POW_SUC"), s"NUM_POW 2 (SUC $D) = NUM_POW 2 $D * 2")
                        halfBelow <- for {
                          a <- assumed(s"NUM_POW 2 $D <= $Hf")
                          over <- numLin(Seq(a._2, dm, ps), prop(s"NUM_POW 2 (SUC $D) <= $N").toOption.get)
                          not <- at(fact("NUM_LT_NOT_LE"), s"$N < NUM_POW 2 (SUC $D) ==> ~(NUM_POW 2 (SUC $D) <= $N)").flatMap(mp(_, h.head))
                          refuted <- rules.notElim(not, over).flatMap(rules.notIntro(a._1, _))
                          out <- at(k("NUM_NOT_LE"), s"~(NUM_POW 2 $D <= $Hf) ==> $Hf < NUM_POW 2 $D").flatMap(mp(_, refuted))
                        } yield out
                        left <- at(atSuc, s"$Fn (SUC (SUC $D)) $Pb $Qb $N = COND (NUM_MOD $N 2 = 0) (COND ($H $Pb $Qb) 1 0 + 2 * $Fn (SUC $D) F $Pb ($Hf)) (COND ($H $Pb $Qb) 0 1 + 2 * $Fn (SUC $D) T $Pb ($Hf))")
                        right <- at(atSuc, s"$Fn (SUC $D) $Pb $Qb $N = COND (NUM_MOD $N 2 = 0) (COND ($H $Pb $Qb) 1 0 + 2 * $Fn $D F $Pb ($Hf)) (COND ($H $Pb $Qb) 0 1 + 2 * $Fn $D T $Pb ($Hf))")
                        ihF <- at(hyp, s"$Hf < NUM_POW 2 $D ==> $Fn (SUC $D) F $Pb ($Hf) = $Fn $D F $Pb ($Hf)").flatMap(mp(_, halfBelow))
                        ihT <- at(hyp, s"$Hf < NUM_POW 2 $D ==> $Fn (SUC $D) T $Pb ($Hf) = $Fn $D T $Pb ($Hf)").flatMap(mp(_, halfBelow))
                        out <- rewriting(Seq(left, right, ihF, ihT), c)(byBeta)
                      } yield out
                    }.flatMap(gen(_, pv, qv, nv))
                  } yield out
                }
              )
            } yield out
            // and so no number of further halvings does
            settled <- for {
              body <- prop(s"!db:num. !pb:bool. !qb:bool. !nb:num. nb < NUM_POW 2 db ==> $Fn (db + (eb:num)) pb qb nb = $Fn db pb qb nb")
              out <- induct(ev, body)(
                _ =>
                  for {
                    goal <- prop(s"(nb:num) < NUM_POW 2 (db:num) ==> $Fn (db + 0) $Pb $Qb nb = $Fn db $Pb $Qb nb")
                    plus <- at(fact("NUM_ADD_ZERO"), "(db:num) + 0 = db")
                    out <- underHyps(goal)((_, c) => rewriting(Seq(plus), c)(byBeta)).flatMap(gen(_, dv, pv, qv, nv))
                  } yield out,
                (kk, hyp, _) => {
                  val E = v(kk.name); val Db = "(db:num)"
                  for {
                    goal <- prop(s"$N < NUM_POW 2 $Db ==> $Fn ($Db + SUC $E) $Pb $Qb $N = $Fn $Db $Pb $Qb $N")
                    out <- underHyps(goal) { (h, c) =>
                      for {
                        succ <- at(fact("NUM_ADD_SUC"), s"$Db + SUC $E = SUC ($Db + $E)")
                        powAdd <- at(fact("NUM_POW_ADD"), s"NUM_POW 2 ($Db + $E) = NUM_POW 2 $Db * NUM_POW 2 $E")
                        pos <- at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < NUM_POW 2 $E").flatMap(mp(_, t2))
                        one <- numLinText(Seq(pos), s"1 <= NUM_POW 2 $E")
                        mono <- at(fact("NUM_MUL_MONOTONE"), s"1 <= NUM_POW 2 $E ==> NUM_POW 2 $Db * 1 <= NUM_POW 2 $Db * NUM_POW 2 $E").flatMap(mp(_, one))
                        unit <- num(s"NUM_POW 2 $Db * 1 = NUM_POW 2 $Db")
                        wider <- numLin(Seq(h.head, powAdd, mono, unit), prop(s"$N < NUM_POW 2 ($Db + $E)").toOption.get)
                        once <- at(stable, s"$N < NUM_POW 2 ($Db + $E) ==> $Fn (SUC ($Db + $E)) $Pb $Qb $N = $Fn ($Db + $E) $Pb $Qb $N").flatMap(mp(_, wider))
                        rest <- at(hyp, s"$N < NUM_POW 2 $Db ==> $Fn ($Db + $E) $Pb $Qb $N = $Fn $Db $Pb $Qb $N").flatMap(mp(_, h.head))
                        out <- rewriting(Seq(succ, once, rest), c)(byBeta)
                      } yield out
                    }.flatMap(gen(_, dv, pv, qv, nv))
                  } yield out
                }
              )
            } yield out
            fuel <- at(k("BELOW_POWER"), s"$Mb < NUM_POW 2 $Mb")
            gTerm <- term(s"\\p:bool. \\q:bool. \\n:num. $Fn n p q n", Steps)
            apart <- zeroNotOne
            oneNotZero <- for { h <- assumed("(1:num) = 0"); s <- Conv.sym(h._2); c <- rules.notElim(apart, s); out <- rules.notIntro(h._1, c) } yield out
            evenClause <- for {
              goal <- prop(s"$Fn (2 * $Mb) $Pb $Qb (2 * $Mb) = COND ($H $Pb $Qb) 1 0 + 2 * $Fn $Mb F $Pb $Mb")
              mT <- prop(s"$Mb = 0")
              isZero <- for {
                h <- assumed(s"$Mb = 0")
                twice <- num("2 * 0 = (0:num)")
                out <- rewriting(Seq(h._2, twice, atZero), goal)(settle)
              } yield out
              nonZero <- for {
                h <- assumed(s"~($Mb = 0)")
                pos <- positiveOf(h._2, Mb)
                le <- numLinText(Seq(pos), s"1 <= $Mb")
                sub <- at(fact("NUM_REAL_SUB"), s"1 <= $Mb ==> real_of_num (NUM_SUB $Mb 1) = real_of_num $Mb - real_of_num 1").flatMap(mp(_, le))
                fuelEq <- numLinText(Seq(sub), s"SUC ($Mb + NUM_SUB $Mb 1) = 2 * $Mb")
                opened <- at(atSuc, s"$Fn (SUC ($Mb + NUM_SUB $Mb 1)) $Pb $Qb (2 * $Mb) = COND (NUM_MOD (2 * $Mb) 2 = 0) " +
                  s"(COND ($H $Pb $Qb) 1 0 + 2 * $Fn ($Mb + NUM_SUB $Mb 1) F $Pb (NUM_DIV (2 * $Mb) 2)) (COND ($H $Pb $Qb) 0 1 + 2 * $Fn ($Mb + NUM_SUB $Mb 1) T $Pb (NUM_DIV (2 * $Mb) 2))")
                  .flatMap(rw(fuelEq, _))
                mod <- at(k("MOD_TWO_SHIFT"), s"NUM_MOD (2 * $Mb + 0) 2 = NUM_MOD 0 2").flatMap(e => num(s"2 * $Mb + 0 = 2 * $Mb").flatMap(rw(_, e))).flatMap(rw(m0(1), _))
                div <- for {
                  eq <- num(s"2 * $Mb = 2 * $Mb + 0")
                  u <- at(fact("NUM_DIV_MOD_UNIQUE"), s"2 * $Mb = 2 * $Mb + 0 /\\ (0:num) < 2 ==> $Mb = NUM_DIV (2 * $Mb) 2 /\\ 0 = NUM_MOD (2 * $Mb) 2")
                  out <- conj(eq, t2).flatMap(mp(u, _)).flatMap(rules.conjElim1).flatMap(Conv.sym)
                } yield out
                same <- at(settled, s"$Mb < NUM_POW 2 $Mb ==> $Fn ($Mb + NUM_SUB $Mb 1) F $Pb $Mb = $Fn $Mb F $Pb $Mb").flatMap(mp(_, fuel))
                out <- rewriting(Seq(opened, mod, div, same), goal)(deciding(Seq.empty)(numClose))
              } yield out
              out <- classical.cases(mT, isZero, nonZero).flatMap(gen(_, pv, qv, mv))
            } yield out
            oddClause <- for {
              goal <- prop(s"$Fn (2 * $Mb + 1) $Pb $Qb (2 * $Mb + 1) = COND ($H $Pb $Qb) 0 1 + 2 * $Fn $Mb T $Pb $Mb")
              fuelEq <- numLinText(Seq.empty, s"SUC ($Mb + $Mb) = 2 * $Mb + 1")
              opened <- at(atSuc, s"$Fn (SUC ($Mb + $Mb)) $Pb $Qb (2 * $Mb + 1) = COND (NUM_MOD (2 * $Mb + 1) 2 = 0) " +
                s"(COND ($H $Pb $Qb) 1 0 + 2 * $Fn ($Mb + $Mb) F $Pb (NUM_DIV (2 * $Mb + 1) 2)) (COND ($H $Pb $Qb) 0 1 + 2 * $Fn ($Mb + $Mb) T $Pb (NUM_DIV (2 * $Mb + 1) 2))")
                .flatMap(rw(fuelEq, _))
              oneLt <- numLinText(Seq.empty, "(1:num) < 2")
              m1 <- at(fact("NUM_DIV_MOD_BELOW"), "(1:num) < 2 ==> NUM_DIV 1 2 = 0 /\\ NUM_MOD 1 2 = 1").flatMap(mp(_, oneLt)).flatMap(split)
              mod <- at(k("MOD_TWO_SHIFT"), s"NUM_MOD (2 * $Mb + 1) 2 = NUM_MOD 1 2").flatMap(rw(m1(1), _))
              div <- for {
                u <- at(fact("NUM_DIV_MOD_UNIQUE"), s"2 * $Mb + 1 = 2 * $Mb + 1 /\\ (1:num) < 2 ==> $Mb = NUM_DIV (2 * $Mb + 1) 2 /\\ 1 = NUM_MOD (2 * $Mb + 1) 2")
                refl <- term(s"2 * $Mb + 1", Numbers).map(Conv.refl)
                out <- conj(refl, oneLt).flatMap(mp(u, _)).flatMap(rules.conjElim1).flatMap(Conv.sym)
              } yield out
              same <- at(settled, s"$Mb < NUM_POW 2 $Mb ==> $Fn ($Mb + $Mb) T $Pb $Mb = $Fn $Mb T $Pb $Mb").flatMap(mp(_, fuel))
              out <- rewriting(Seq(opened, mod, div, same), goal)(deciding(Seq(oneNotZero))(numClose)).flatMap(gen(_, pv, qv, mv))
            } yield out
            both <- conj(evenClause, oddClause)
            forG <- prop(s"?g:bool->bool->num->num. $Family").flatMap(e => logic.destExistsPredicate(e).toRight(NotOfForm("an existential", e)))
            out <- introduce(forG, gTerm, both)
          } yield out
        }
        general <- rules.disch(whiteT, out).flatMap(gen(_, hvar))
      } yield general
    }

    /** Bit 0 of the map is the XOR of bit 0 of its argument with the rule at the two bits below. */
    def bitZero: R[Kernel.Thm] =
      familyRule { _ =>
        val (pv, qv, xv) = (Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("xb", Numbers))
        val Pb = "(pb:bool)"; val Qb = "(qb:bool)"; val X = "(xb:num)"
        val E = s"(NUM_MOD $X 2 = 1)"; val C = s"COND (~(($H $Pb $Qb) = $E)) (1:num) 0"; val Y = s"$G $E $Pb (NUM_DIV $X 2)"
        for {
          stepHere <- underFamily("RULE_FAMILY_STEP")
          st <- at(stepHere, s"$G $Pb $Qb $X = $C + 2 * $Y")
          swap <- num(s"$C + 2 * $Y = 2 * $Y + $C")
          low <- at(k("BIT_LOW"), s"((${bit("0", s"$G $Pb $Qb $X")}) = (NUM_MOD ($G $Pb $Qb $X) 2 = 1)) /\\ " +
            s"(!j:num. (${bit("SUC j", s"$G $Pb $Qb $X")}) = (${bit("j", s"NUM_DIV ($G $Pb $Qb $X) 2")}))").flatMap(rules.conjElim1)
          shift <- at(k("MOD_TWO_SHIFT"), s"NUM_MOD (2 * $Y + $C) 2 = NUM_MOD ($C) 2")
          goal <- prop(s"(${bit("0", s"$G $Pb $Qb $X")}) = ~(($H $Pb $Qb) = $E)")
          zeroF <- zeroOneFalse; oneT <- oneOneTrue
          t2 <- two; oneLt <- numLinText(Seq.empty, "(1:num) < 2")
          m0 <- at(fact("NUM_DIV_MOD_BELOW"), "(0:num) < 2 ==> NUM_DIV 0 2 = 0 /\\ NUM_MOD 0 2 = 0").flatMap(mp(_, t2)).flatMap(rules.conjElim2)
          m1 <- at(fact("NUM_DIV_MOD_BELOW"), "(1:num) < 2 ==> NUM_DIV 1 2 = 0 /\\ NUM_MOD 1 2 = 1").flatMap(mp(_, oneLt)).flatMap(rules.conjElim2)
          atoms <- Seq(s"$H $Pb $Qb", s"NUM_MOD $X 2 = 1").foldLeft[R[List[Term]]](Right(Nil))((acc, t_) => for { d <- acc; p_ <- prop(t_) } yield d :+ p_)
          out <- rewriting(Seq(low), goal)(g1 => rewriting(Seq(st, swap, shift), g1)(byCases(atoms)(lits => deciding(lits)(g =>
            rewriting(Seq(m0, m1, zeroF, oneT), g)(gg => tauto(lits, gg))))))
          general <- gen(out, pv, qv, xv)
        } yield general
      }

    /** Bit `SUC j` of the map is bit `j` of the map at the half, carrying bit 0 down. */
    def bitSuc: R[Kernel.Thm] =
      familyRule { _ =>
        val (jv, pv, qv, xv) = (Term.variable("jb", Numbers), Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("xb", Numbers))
        val Pb = "(pb:bool)"; val Qb = "(qb:bool)"; val X = "(xb:num)"; val J = "(jb:num)"
        val E = s"(NUM_MOD $X 2 = 1)"; val C = s"COND (~(($H $Pb $Qb) = $E)) (1:num) 0"; val Y = s"$G $E $Pb (NUM_DIV $X 2)"
        for {
          stepHere <- underFamily("RULE_FAMILY_STEP")
          st <- at(stepHere, s"$G $Pb $Qb $X = $C + 2 * $Y")
          swap <- num(s"$C + 2 * $Y = 2 * $Y + $C")
          small <- at(k("COND_BELOW_TWO"), s"$C < (2:num)")
          half <- at(k("BIT_HALVE"), s"$C < (2:num) ==> ((${bit(s"SUC $J", s"2 * $Y + $C")}) = (${bit(J, Y)}))").flatMap(mp(_, small))
          goal <- prop(s"(${bit(s"SUC $J", s"$G $Pb $Qb $X")}) = (${bit(J, Y)})")
          out <- rewriting(Seq(st, swap, half), goal)(byBeta).flatMap(gen(_, jv, pv, qv, xv))
        } yield out
      }

    /** Two bits up, the map is the rule on bits `SUC (SUC j)`, `SUC j` and `j` of its argument. */
    def bitRule: R[Kernel.Thm] =
      familyRule { _ =>
        val (jv, pv, qv, xv) = (Term.variable("jb", Numbers), Term.variable("pb", Type.Bool), Term.variable("qb", Type.Bool), Term.variable("xb", Numbers))
        def claim(J: String, P: String, Q: String, X: String) =
          s"(${bit(s"SUC (SUC ($J))", s"$G $P $Q ($X)")}) = ~((${bit(s"SUC (SUC ($J))", X)}) = $H (${bit(s"SUC ($J)", X)}) (${bit(J, X)}))"
        def bit0(y: String) = s"NUM_MOD ($y) 2 = 1"
        val X = "(xb:num)"; val Hf = s"NUM_DIV $X 2"; val H2 = s"NUM_DIV ($Hf) 2"
        val E = s"(${bit0(X)})"; val E1 = s"(${bit0(Hf)})"
        for {
          zero <- underFamily("RULE_FAMILY_BIT_ZERO")
          succ <- underFamily("RULE_FAMILY_BIT_SUC")
          body <- prop(s"!pb:bool. !qb:bool. !xb:num. ${claim("jb:num", "pb", "qb", "xb")}")
          proved <- induct(jv, body)(
            _ =>
              for {
                goal <- prop(claim("0", "(pb:bool)", "(qb:bool)", "(xb:num)"))
                a <- at(succ, s"(${bit("SUC (SUC 0)", s"$G (pb:bool) (qb:bool) $X")}) = (${bit("SUC 0", s"$G $E (pb:bool) ($Hf)")})")
                b <- at(succ, s"(${bit("SUC 0", s"$G $E (pb:bool) ($Hf)")}) = (${bit("0", s"$G $E1 $E ($H2)")})")
                c <- at(zero, s"(${bit("0", s"$G $E1 $E ($H2)")}) = ~(($H $E1 $E) = (${bit0(H2)}))")
                lows <- Seq(X, Hf, H2).foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, y) =>
                  for {
                    done <- acc
                    l <- at(k("BIT_LOW"), s"((${bit("0", y)}) = (${bit0(y)})) /\\ (!j:num. (${bit("SUC j", y)}) = (${bit("j", s"NUM_DIV ($y) 2")}))").flatMap(split)
                  } yield done ++ l
                }
                out <- rewriting(Seq(a, b, c) ++ lows, goal)(g => tauto(Seq.empty, g)).flatMap(gen(_, pv, qv, xv))
              } yield out,
            (kk, hyp, _) => {
              val J = v(kk.name)
              for {
                goal <- prop(claim(s"SUC $J", "(pb:bool)", "(qb:bool)", X))
                a <- at(succ, s"(${bit(s"SUC (SUC (SUC $J))", s"$G (pb:bool) (qb:bool) $X")}) = (${bit(s"SUC (SUC $J)", s"$G $E (pb:bool) ($Hf)")})")
                ih <- at(hyp, claim(J, E, "(pb:bool)", Hf))
                low <- at(k("BIT_LOW"), s"((${bit("0", X)}) = (${bit0(X)})) /\\ (!j:num. (${bit("SUC j", X)}) = (${bit("j", Hf)}))")
                  .flatMap(rules.conjElim2)
                out <- rewriting(Seq(a, ih, low), goal)(byBeta).flatMap(gen(_, pv, qv, xv))
              } yield out
            }
          )
        } yield proved
      }

    /* ------------------------------------------------------------ the Pascal map */

    private def first: R[Term] = term("\\p:bool. \\q:bool. p", Rules)

    /** The Pascal map exists: its rule keeps the white background white. */
    def pascalExists: R[Kernel.Thm] =
      for {
        rule <- first
        some <- spec(k("RULE_FAMILY_EXISTS"), rule)
        white <- prop("~F").flatMap(tauto(Seq.empty, _))
        out <- mp(some, white)
      } yield out

    /** The Pascal map is triangular, as every member is. */
    def pascalTriangular: R[Kernel.Thm] =
      for {
        rule <- first
        out <- spec(k("RULE_FAMILY_TRIANGULAR"), rule, gvar).flatMap(gen(_, gvar))
      } yield out

    /** Bit 0 of the Pascal map is bit 0 of its argument, and every bit above is its own XOR the one below. */
    def pascalBits: R[Kernel.Thm] = {
      val (xv, jv) = (Term.variable("xb", Numbers), Term.variable("jb", Numbers))
      val X = "(xb:num)"; val Hf = s"NUM_DIV $X 2"; val E = s"(NUM_MOD $X 2 = 1)"
      def claim(J: String) = s"(${bit(s"SUC ($J)", Map0(X))}) = ~((${bit(s"SUC ($J)", X)}) = (${bit(J, X)}))"
      for {
        rule <- first
        hT <- prop(Pascal)
        held <- LogicError.lift(Kernel.assume(hT))
        zero <- spec(k("RULE_FAMILY_BIT_ZERO"), rule, gvar).flatMap(mp(_, held))
        succ <- spec(k("RULE_FAMILY_BIT_SUC"), rule, gvar).flatMap(mp(_, held))
        upper <- spec(k("RULE_FAMILY_BIT_RULE"), rule, gvar).flatMap(mp(_, held))
        lows <- at(k("BIT_LOW"), s"((${bit("0", X)}) = (NUM_MOD $X 2 = 1)) /\\ (!j:num. (${bit("SUC j", X)}) = (${bit("j", Hf)}))").flatMap(split)
        halfLow <- at(k("BIT_LOW"), s"((${bit("0", Hf)}) = (NUM_MOD ($Hf) 2 = 1)) /\\ (!j:num. (${bit("SUC j", Hf)}) = (${bit("j", s"NUM_DIV ($Hf) 2")}))")
          .flatMap(rules.conjElim1)
        low <- for {
          z <- at(zero, s"(${bit("0", Map0(X))}) = ~(F = $E)")
          goal <- prop(s"(${bit("0", Map0(X))}) = (${bit("0", X)})")
          out <- tauto(Seq(z, lows(0)), goal)
        } yield out
        body <- prop(claim("jb:num"))
        above <- induct(jv, body)(
          _ =>
            for {
              goal <- prop(claim("0"))
              s1 <- at(succ, s"(${bit("SUC 0", Map0(X))}) = (${bit("0", s"$G $E F ($Hf)")})")
              z1 <- at(zero, s"(${bit("0", s"$G $E F ($Hf)")}) = ~($E = (NUM_MOD ($Hf) 2 = 1))")
              l1 <- at(lows(1), s"(${bit("SUC 0", X)}) = (${bit("0", Hf)})")
              out <- tauto(Seq(s1, z1, l1, halfLow, lows(0)), goal)
            } yield out,
          (kk, _, _) => {
            val J = v(kk.name)
            for {
              goal <- prop(claim(s"SUC $J"))
              r <- at(upper, s"(${bit(s"SUC (SUC $J)", Map0(X))}) = ~((${bit(s"SUC (SUC $J)", X)}) = (${bit(s"SUC $J", X)}))")
              out <- rewriting(Seq(r), goal)(byBeta)
            } yield out
          }
        )
        both <- conj(low, above)
        out <- gen(both, xv).flatMap(rules.disch(hT, _)).flatMap(gen(_, gvar))
      } yield out
    }
  }
}
