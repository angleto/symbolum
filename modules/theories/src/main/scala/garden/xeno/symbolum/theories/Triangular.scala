package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Triangular maps on the naturals: the structure Rule 30's map, `n -> 3 n + 1` and their kin share,
 * proved once over a hypothesis rather than once per map.
 *
 * A map `f : num -> num` is triangular when two things hold for every `k`. Agreeing modulo `2^k`
 * is kept: `m` and `n` agreeing there makes `f m` and `f n` agree there. And bit `k` is flipped
 * with bit `k`: when `m` and `n` agree modulo `2^k` and not modulo `2^(k + 1)`, so do `f m` and
 * `f n`. Read on binary digits, bit `j` of `f n` is bit `j` of `n` XOR something that depends only
 * on the bits below `j`, which is the shape of a triangular matrix with a full diagonal, and the
 * name. The hypothesis is written out wherever it is used; nothing is declared, as in
 * `docs/adr/0062`, `0064` and `0065`. `docs/adr/0066` is the decision, and Mycelium note 917b3939,
 * part 4, strategy 1, is the account a reader without the kernel can follow.
 *
 * Not a development: it declares nothing, and `Complex` publishes what it proves beside
 * `RuleThirty`, which reads it.
 *
 * == What the statements say ==
 *
 * `TRIANGULAR_INJECTIVE` and `TRIANGULAR_OF_INJECTIVE` are the two halves of one characterisation:
 * a map is triangular exactly when it keeps agreement modulo every `2^k` and is injective on the
 * residues modulo every `2^k`, so that it permutes them. `TRIANGULAR_COMPOSE` and
 * `TRIANGULAR_ITERATE` close the class under composition and iteration, which is why everything
 * proved for a map holds for its iterates. `TRIANGULAR_BALANCED`: over the residues modulo
 * `2^(j + 1)`, bit `j` of the value is on as often as off. `TRIANGULAR_PERIOD`: if an orbit returns
 * modulo `2^k` after `p` steps, it returns modulo `2^(k + 1)` after `2 p`, so the period of an
 * orbit modulo `2^(k + 1)` is the period modulo `2^k` or twice it, and every such period is a power
 * of two. `TRIANGULAR_AFFINE`: `n -> a n + b` is triangular for every odd `a`, which is `3 n + 1` and
 * the odometer `n + 1` among others.
 *
 * == What they do not say ==
 *
 * Anything about Collatz's own map: halving reads bit `k + 1` into bit `k`, so it is not
 * triangular, and that is where the structure stops. Nor anything about the centre column of
 * Rule 30, which reads a bit that moves with the time.
 */
private[theories] object Triangular {

  type R[A] = Either[LogicError, A]

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  /** `x` and `y` agree modulo `2^k`. */
  private[theories] def agree(x: String, y: String, k: String): String =
    s"NUM_MOD ($x) (NUM_POW 2 ($k)) = NUM_MOD ($y) (NUM_POW 2 ($k))"

  /** The map whose value at `x` is `apply(x)` is triangular, as two clauses. */
  private[theories] def triangular(apply: String => String): String =
    s"(!k:num. !m:num. !n:num. ${agree("m", "n", "k")} ==> ${agree(apply("m"), apply("n"), "k")}) /\\ " +
      s"(!k:num. !m:num. !n:num. ${agree("m", "n", "k")} /\\ ~(${agree("m", "n", "SUC k")}) ==> ~(${agree(apply("m"), apply("n"), "SUC k")}))"

  /** The map keeps agreement modulo every `2^k`, and is injective on the residues modulo every `2^k`. */
  private[theories] def keepsAndSeparates(apply: String => String): String =
    s"(!k:num. !m:num. !n:num. ${agree("m", "n", "k")} ==> ${agree(apply("m"), apply("n"), "k")}) /\\ " +
      s"(!k:num. !m:num. !n:num. ${agree(apply("m"), apply("n"), "k")} ==> ${agree("m", "n", "k")})"

  private val F: String => String = x => s"(f:num->num) ($x)"
  private val G: String => String = x => s"(g:num->num) ($x)"
  private val It = "(iterate:num->num->num)"

  /** The iterate of `f`, by the two equations that characterise it. */
  private val Iteration: String = s"(!n:num. $It n 0 = n) /\\ (!n:num. !t:num. $It n (SUC t) = (f:num->num) ($It n t))"

  /** Bit `j` of `y`. */
  private def bit(j: String, y: String): String = s"NUM_MOD (NUM_DIV ($y) (NUM_POW 2 ($j))) 2 = 1"

  /** `+1` for a bit that is off and `-1` for one that is on. */
  private def sign(b: String): String = s"COND ($b) (0 - 1) (1:real)"

  /** What `Complex` publishes from here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    "TRIANGULAR_INJECTIVE" ->
      s"!f:num->num. ${triangular(F)} ==> !k:num. !m:num. !n:num. ${agree(F("m"), F("n"), "k")} ==> ${agree("m", "n", "k")}",
    "TRIANGULAR_OF_INJECTIVE" -> s"!f:num->num. ${keepsAndSeparates(F)} ==> ${triangular(F)}",
    "TRIANGULAR_COMPOSE" -> s"!f:num->num. !g:num->num. ${triangular(F)} /\\ ${triangular(G)} ==> ${triangular(x => F(s"(${G(x)})"))}",
    "TRIANGULAR_ITERATE" ->
      s"!f:num->num. !iterate:num->num->num. ${triangular(F)} /\\ $Iteration ==> !t:num. ${triangular(x => s"$It $x (t:num)")}",
    "TRIANGULAR_BALANCED" ->
      s"!f:num->num. ${triangular(F)} ==> !j:num. Sum (\\n:num. ${sign(bit("j", F("n")))}) (NUM_POW 2 (SUC j)) = 0",
    "TRIANGULAR_PERIOD" ->
      (s"!f:num->num. !iterate:num->num->num. ${triangular(F)} /\\ $Iteration ==> " +
        s"!p:num. !k:num. !n:num. ${agree(s"$It n p", "n", "k")} ==> ${agree(s"$It n (p + p)", "n", "SUC k")}"),
    "TRIANGULAR_AFFINE" -> s"!a:num. !b:num. NUM_MOD a 2 = 1 ==> ${triangular(x => s"(a:num) * $x + (b:num)")}"
  )

  private val Order: Vector[(String, Proofs => R[Kernel.Thm])] = Vector(
    "TRIANGULAR_INJECTIVE" -> (_.injective),
    "TRIANGULAR_OF_INJECTIVE" -> (_.ofInjective),
    "TRIANGULAR_COMPOSE" -> (_.compose),
    "TRIANGULAR_ITERATE" -> (_.iterate),
    "ITERATE_ADD" -> (_.iterateAdd),
    "TRIANGULAR_BALANCED" -> (_.balanced),
    "TRIANGULAR_PERIOD" -> (_.period),
    "MOD_CONG" -> (_.modCong),
    "TRIANGULAR_AFFINE" -> (_.affine)
  )

  /** The facts [[Statements]] names, derived with `kit`. */
  def prove(kit: ComplexKit, semiring: Semiring, held: Map[String, Kernel.Thm]): R[Map[String, Kernel.Thm]] = {
    val steps = new NumberSteps(kit, semiring)
    ComplexKit.derive(Order, Statements, held)(known => new Proofs(kit, steps, known))
  }

  private final class Proofs(val kit: ComplexKit, val steps: NumberSteps, known: Map[String, Kernel.Thm]) {
    import kit.*
    import steps.*

    private val fv = Term.variable("f", Type.fun(Numbers, Numbers))
    private val gv = Term.variable("g", Type.fun(Numbers, Numbers))
    private val itv = Term.variable("iterate", Type.fun(Numbers, Type.fun(Numbers, Numbers)))
    private val kv = Term.variable("kb", Numbers)
    private val mv = Term.variable("mb", Numbers)
    private val nv = Term.variable("nb", Numbers)
    private val tv = Term.variable("t", Numbers)
    private val pv = Term.variable("p", Numbers)
    private val qv = Term.variable("q", Numbers)
    private val jv = Term.variable("j", Numbers)
    private val av = Term.variable("a", Numbers)
    private val bv = Term.variable("b", Numbers)

    private val K = "(kb:num)"; private val M = "(mb:num)"; private val N = "(nb:num)"

    /** The first clause of a triangular map at `x`, `y` and `k`: agreement modulo `2^k` is kept. */
    private def keeps(clause: Kernel.Thm, apply: String => String, x: String, y: String, k: String): R[Kernel.Thm] =
      at(clause, s"${agree(x, y, k)} ==> ${agree(apply(x), apply(y), k)}")

    /** The second clause at `x`, `y` and `k`: a disagreement first appearing at bit `k` is kept. */
    private def flips(clause: Kernel.Thm, apply: String => String, x: String, y: String, k: String): R[Kernel.Thm] =
      at(clause, s"${agree(x, y, k)} /\\ ~(${agree(x, y, s"SUC ($k)")}) ==> ~(${agree(apply(x), apply(y), s"SUC ($k)")})")

    /** Agreeing modulo `2^(k + 1)` is agreeing modulo `2^k` and at bit `k`. */
    private def splitAt(x: String, y: String, k: String): R[Kernel.Thm] =
      at(modEqSplitTheorem,
        s"(${agree(x, y, s"SUC ($k)")}) = (${agree(x, y, k)} /\\ ((${bit(k, x)}) = (${bit(k, y)})))")

    /** The two clauses of a triangular map, assumed. */
    private def assumedTriangular(apply: String => String): R[(Term, Kernel.Thm, Kernel.Thm)] =
      for {
        held <- assumed(triangular(apply))
        parts <- split(held._2)
      } yield (held._1, parts(0), parts(1))

    /**
     * Injective on the residues modulo `2^k`, by induction on `k`. Modulo 1 everything agrees. If the
     * values agree modulo `2^(k + 1)` they agree modulo `2^k`, so the arguments do; and if the
     * arguments disagreed at bit `k`, the second clause would make the values disagree there too.
     */
    private def separates(apply: String => String, keepsClause: Kernel.Thm, flipsClause: Kernel.Thm): R[Kernel.Thm] = {
      def claim(k: String) = s"${agree(apply(M), apply(N), k)} ==> ${agree(M, N, k)}"
      for {
        body <- prop(s"!mb:num. !nb:num. ${claim(K)}")
        proved <- induct(kv, body)(
          _ =>
            for {
              goal <- prop(claim("0"))
              powZero <- at(fact("NUM_POW_ZERO"), "NUM_POW 2 0 = SUC 0")
              modOne <- modOneTheorem
              out <- underHyps(goal)((_, c) => rewriting(Seq(powZero, modOne), c)(byBeta)).flatMap(gen(_, mv, nv))
            } yield out,
          (kk, hyp, _) => {
            val Kk = v(kk.name)
            for {
              goal <- prop(claim(s"SUC $Kk"))
              out <- underHyps(goal) { (h, c) =>
                for {
                  splitValues <- splitAt(apply(M), apply(N), Kk)
                  low <- LogicError.lift(Kernel.eqMp(splitValues, h.head)).flatMap(rules.conjElim1)
                  below <- at(hyp, s"${agree(apply(M), apply(N), Kk)} ==> ${agree(M, N, Kk)}").flatMap(mp(_, low))
                  out <- cases(agree(M, N, s"SUC $Kk"))(
                    yes => Right(yes),
                    no =>
                      for {
                        apart <- conj(below, no).flatMap(both => flips(flipsClause, apply, M, N, Kk).flatMap(mp(_, both)))
                        contra <- rules.notElim(apart, h.head)
                        out <- rules.falsityElim(c, contra)
                      } yield out)
                } yield out
              }.flatMap(gen(_, mv, nv))
            } yield out
          }
        )
      } yield proved
    }

    def injective: R[Kernel.Thm] =
      for {
        held <- assumedTriangular(F)
        (hT, keepsClause, flipsClause) = held
        proved <- separates(F, keepsClause, flipsClause)
        out <- rules.disch(hT, proved).flatMap(gen(_, fv))
      } yield out

    /** The second clause from injectivity one bit up: agreeing values modulo `2^(k + 1)` would make the arguments agree there. */
    def ofInjective: R[Kernel.Thm] =
      for {
        held <- assumed(keepsAndSeparates(F))
        (hT, h) = held
        parts <- split(h)
        flipsClause <- for {
          held <- assumed(s"${agree(M, N, K)} /\\ ~(${agree(M, N, s"SUC $K")})")
          (cT, c) = held
          apart <- rules.conjElim2(c)
          valuesAgree <- assumed(agree(F(M), F(N), s"SUC $K"))
          argumentsAgree <- at(parts(1), s"${agree(F(M), F(N), s"SUC $K")} ==> ${agree(M, N, s"SUC $K")}").flatMap(mp(_, valuesAgree._2))
          contra <- rules.notElim(apart, argumentsAgree)
          refuted <- rules.notIntro(valuesAgree._1, contra)
          out <- rules.disch(cT, refuted).flatMap(gen(_, kv, mv, nv))
        } yield out
        both <- conj(parts(0), flipsClause)
        out <- rules.disch(hT, both).flatMap(gen(_, fv))
      } yield out

    /**
     * `x -> outer (inner x)` is triangular when both are. Agreement passes through `inner` and then
     * `outer`; a disagreement first appearing at bit `k` passes through `inner` by its second clause,
     * with agreement below by its first, and then through `outer` by its second.
     */
    private def composed(
      outer: String => String, outerKeeps: Kernel.Thm, outerFlips: Kernel.Thm,
      inner: String => String, innerKeeps: Kernel.Thm, innerFlips: Kernel.Thm
    ): R[Kernel.Thm] =
      for {
        keepsClause <- for {
          held <- assumed(agree(M, N, K))
          once <- keeps(innerKeeps, inner, M, N, K).flatMap(mp(_, held._2))
          twice <- keeps(outerKeeps, outer, s"(${inner(M)})", s"(${inner(N)})", K).flatMap(mp(_, once))
          out <- rules.disch(held._1, twice).flatMap(gen(_, kv, mv, nv))
        } yield out
        flipsClause <- for {
          held <- assumed(s"${agree(M, N, K)} /\\ ~(${agree(M, N, s"SUC $K")})")
          parts <- split(held._2)
          low <- keeps(innerKeeps, inner, M, N, K).flatMap(mp(_, parts(0)))
          apart <- flips(innerFlips, inner, M, N, K).flatMap(mp(_, held._2))
          out <- conj(low, apart).flatMap(c => flips(outerFlips, outer, s"(${inner(M)})", s"(${inner(N)})", K).flatMap(mp(_, c)))
            .flatMap(rules.disch(held._1, _)).flatMap(gen(_, kv, mv, nv))
        } yield out
        out <- conj(keepsClause, flipsClause)
      } yield out

    def compose: R[Kernel.Thm] =
      for {
        held <- assumed(s"${triangular(F)} /\\ ${triangular(G)}")
        (hT, h) = held
        parts <- split(h)
        out <- composed(F, parts(0), parts(1), G, parts(2), parts(3))
        general <- rules.disch(hT, out).flatMap(gen(_, fv, gv))
      } yield general

    /** The identity is triangular: both clauses are their own hypotheses. */
    private def identity: R[Kernel.Thm] =
      for {
        keepsClause <- assumed(agree(M, N, K)).flatMap(h => rules.disch(h._1, h._2)).flatMap(gen(_, kv, mv, nv))
        flipsClause <- assumed(s"${agree(M, N, K)} /\\ ~(${agree(M, N, s"SUC $K")})")
          .flatMap(h => rules.conjElim2(h._2).flatMap(rules.disch(h._1, _))).flatMap(gen(_, kv, mv, nv))
        out <- conj(keepsClause, flipsClause)
      } yield out

    /** Every iterate is triangular, by induction on the number of steps: the identity, then one more `f` outside. */
    def iterate: R[Kernel.Thm] =
      for {
        held <- assumed(s"${triangular(F)} /\\ $Iteration")
        (hT, h) = held
        parts <- split(h)
        at0 = parts(2); atSuc = parts(3)
        body <- prop(triangular(x => s"$It $x (t:num)"))
        proved <- induct(tv, body)(
          goal => identity.flatMap(id => rewriting(Seq(at0), goal)(landsOn(id))),
          (tt, hyp, goal) => {
            val T = v(tt.name)
            for {
              inner <- split(hyp)
              step <- composed(F, parts(0), parts(1), x => s"$It $x $T", inner(0), inner(1))
              out <- rewriting(Seq(atSuc), goal)(landsOn(step))
            } yield out
          }
        )
        out <- rules.disch(hT, proved).flatMap(gen(_, fv, itv))
      } yield out

    /** `iterate n (p + q) = iterate (iterate n p) q`, by induction on `q`. */
    def iterateAdd: R[Kernel.Thm] =
      for {
        held <- assumed(Iteration)
        (hT, h) = held
        parts <- split(h)
        body <- prop(s"!p:num. !nb:num. $It nb (p + (q:num)) = $It ($It nb p) q")
        proved <- induct(qv, body)(
          _ =>
            for {
              goal <- prop(s"$It $N ((p:num) + 0) = $It ($It $N p) 0")
              addZero <- at(fact("NUM_ADD_ZERO"), "(p:num) + 0 = p")
              out <- rewriting(Seq(addZero, parts(0)), goal)(byBeta).flatMap(gen(_, pv, nv))
            } yield out,
          (qq, hyp, _) => {
            val Q = v(qq.name)
            for {
              goal <- prop(s"$It $N ((p:num) + SUC $Q) = $It ($It $N p) (SUC $Q)")
              moved <- numLinText(Seq.empty, s"(p:num) + SUC $Q = SUC (p + $Q)")
              ih <- at(hyp, s"$It $N ((p:num) + $Q) = $It ($It $N p) $Q")
              out <- rewriting(Seq(moved, parts(1), ih), goal)(byBeta).flatMap(gen(_, pv, nv))
            } yield out
          }
        )
        out <- rules.disch(hT, proved).flatMap(gen(_, fv, itv))
      } yield out

    /**
     * Over the residues modulo `2^(j + 1)`, bit `j` of the value is on as often as off. The residues
     * pair as `m` and `2^j + m`, which agree modulo `2^j` and differ at bit `j`; by the two clauses
     * so do their values, so in each pair one value has bit `j` on and the other off.
     */
    def balanced: R[Kernel.Thm] = {
      val J = "(j:num)"; val P = s"NUM_POW 2 $J"; val P2 = s"NUM_POW 2 (SUC $J)"
      def term_(n: String) = sign(bit(J, F(n)))
      for {
        held <- assumedTriangular(F)
        (hT, keepsClause, flipsClause) = held
        goal <- prop(s"Sum (\\n:num. ${term_("n")}) ($P2) = 0")
        double <- for {
          s1 <- at(fact("NUM_POW_SUC"), s"$P2 = $P * 2")
          s2 <- num(s"$P * 2 = $P + $P")
          out <- trans(s1, s2)
        } yield out
        halves <- at(fact("SUM_HALVES"),
          s"Sum (\\n:num. ${term_("n")}) ($P + $P) = Sum (\\n:num. ${term_("n")}) ($P) + Sum (\\m:num. ${term_(s"$P + m")}) ($P)")
        added <- at(fact("SUM_ADD"),
          s"Sum (\\m:num. ${term_("m")} + ${term_(s"$P + m")}) ($P) = Sum (\\n:num. ${term_("n")}) ($P) + Sum (\\m:num. ${term_(s"$P + m")}) ($P)")
          .flatMap(Conv.sym)
        pairedT <- term(s"Sum (\\m:num. ${term_("m")} + ${term_(s"$P + m")}) ($P)", TyApp(Real.TypeName, Nil))
        paired <- belowBound(pairedT, "\\m:num. (0:real)", P) { (m, mBelow) =>
          val A = F(m); val B = F(s"$P + $m")
          for {
            own <- at(fact("NUM_DIV_MOD_BELOW"), s"$m < $P ==> NUM_DIV $m ($P) = 0 /\\ NUM_MOD $m ($P) = $m").flatMap(mp(_, mBelow)).flatMap(rules.conjElim2)
            shifted <- at(fact("NUM_DIV_MOD_STEP"), s"$m < $P ==> NUM_DIV ($P + $m) ($P) = SUC 0 /\\ NUM_MOD ($P + $m) ($P) = $m")
              .flatMap(mp(_, mBelow)).flatMap(rules.conjElim2)
            argumentsLow <- Conv.sym(shifted).flatMap(trans(own, _))
            argumentsApart <- for {
              held <- assumed(agree(m, s"$P + $m", s"SUC $J"))
              splitS <- splitAt(m, s"$P + $m", J)
              bitsSame <- LogicError.lift(Kernel.eqMp(splitS, held._2)).flatMap(rules.conjElim2)
              off <- at(bitAboveTheorem, s"$m < $P ==> ~(${bit(J, m)})").flatMap(mp(_, mBelow))
              on <- at(bitTopTheorem, s"$m < $P ==> ${bit(J, s"$P + $m")}").flatMap(mp(_, mBelow))
              falsity <- prop("F")
              contra <- tauto(Seq(bitsSame, off, on), falsity)
              out <- rules.notIntro(held._1, contra)
            } yield out
            valuesLow <- keeps(keepsClause, F, m, s"$P + $m", J).flatMap(mp(_, argumentsLow))
            valuesApart <- conj(argumentsLow, argumentsApart).flatMap(c => flips(flipsClause, F, m, s"$P + $m", J).flatMap(mp(_, c)))
            apart <- for {
              held <- assumed(s"(${bit(J, A)}) = (${bit(J, B)})")
              splitV <- splitAt(A, B, J)
              agreeing <- conj(valuesLow, held._2).flatMap(c => Conv.sym(splitV).flatMap(s => LogicError.lift(Kernel.eqMp(s, c))))
              contra <- rules.notElim(valuesApart, agreeing)
              out <- rules.notIntro(held._1, contra)
            } yield out
            atoms <- Seq(bit(J, A), bit(J, B)).foldLeft[R[List[Term]]](Right(Nil))((acc, t_) => for { d <- acc; p_ <- prop(t_) } yield d :+ p_)
          } yield (Seq.empty, Seq(apart), atoms)
        }
        none <- at(fact("SUM_OF_ZERO"), s"Sum (\\m:num. 0) ($P) = 0")
        chain <- trans(halves, added, paired, none)
        proved <- rewriting(Seq(double), goal)(landsOn(chain)).flatMap(gen(_, jv))
        out <- rules.disch(hT, proved).flatMap(gen(_, fv))
      } yield out
    }

    /**
     * An orbit back modulo `2^k` after `p` steps is back modulo `2^(k + 1)` after `2 p`. Write `g` for
     * the `p`-th iterate and `m = g n`. If `m` agrees with `n` modulo `2^(k + 1)`, so does `g m` by the
     * first clause. If not, they differ at bit `k` only, and the second clause makes `g m` differ from
     * `g n = m` at bit `k` too: two flips of one bit, so `g m` agrees with `n` there.
     */
    def period: R[Kernel.Thm] =
      for {
        held <- assumed(s"${triangular(F)} /\\ $Iteration")
        (hT, h) = held
        parts <- split(h)
        iteration <- conj(parts(2), parts(3))
        everyStep <- at(known("TRIANGULAR_ITERATE"),
          s"${triangular(F)} /\\ $Iteration ==> !t:num. ${triangular(x => s"$It $x (t:num)")}").flatMap(mp(_, h))
        g = (x: String) => s"$It $x (p:num)"
        atP <- at(everyStep, triangular(g))
        clauses <- split(atP)
        adds <- at(known("ITERATE_ADD"), s"$Iteration ==> !q:num. !p:num. !n:num. $It n (p + q) = $It ($It n p) q").flatMap(mp(_, iteration))
        twice <- at(adds, s"$It $N ((p:num) + p) = $It ($It $N p) p")
        mm = s"($It $N (p:num))"
        back <- assumed(agree(mm, N, K))
        goal <- prop(agree(s"$It $N ((p:num) + p)", N, s"SUC $K"))
        proved <- rewriting(Seq(twice), goal) { g_ =>
          cases(agree(mm, N, s"SUC $K"))(
            yes =>
              for {
                kept <- keeps(clauses(0), g, mm, N, s"SUC $K").flatMap(mp(_, yes))
                out <- trans(kept, yes)
              } yield out,
            no =>
              for {
                low <- keeps(clauses(0), g, mm, N, K).flatMap(mp(_, back._2))
                apart <- conj(back._2, no).flatMap(c => flips(clauses(1), g, mm, N, K).flatMap(mp(_, c)))
                lowToN <- trans(low, back._2)
                s1 <- splitAt(g(mm), mm, K)
                s2 <- splitAt(mm, N, K)
                s3 <- splitAt(g(mm), N, K)
                out <- tauto(Seq(low, apart, back._2, no, lowToN, s1, s2, s3), g_)
              } yield out)
        }
        general <- rules.disch(back._1, proved).flatMap(gen(_, pv, kv, nv))
        out <- rules.disch(hT, general).flatMap(gen(_, fv, itv))
      } yield out

    /** Agreeing modulo `2^k` is congruence modulo `2^k`. */
    def modCong: R[Kernel.Thm] = {
      val (xv, yv) = (Term.variable("x", Numbers), Term.variable("y", Numbers))
      val Mod = s"NUM_POW 2 $K"
      def parts(z: String) = (s"NUM_DIV ($z:num) ($Mod)", s"NUM_MOD ($z:num) ($Mod)")
      val (qx, rx) = parts("x"); val (qy, ry) = parts("y")
      for {
        positive <- two.flatMap(t2 => at(fact("NUM_POW_POSITIVE"), s"(0:num) < 2 ==> 0 < $Mod").flatMap(mp(_, t2)))
        dx <- at(fact("NUM_DIV_MOD"), s"$Mod * $qx + $rx = x")
        dy <- at(fact("NUM_DIV_MOD"), s"$Mod * $qy + $ry = y")
        forward <- for {
          held <- assumed(agree("x:num", "y:num", K))
          sum <- numLinText(Seq(dx, dy, held._2), s"(x:num) + $Mod * $qy = y + $Mod * $qx")
          out <- at(fact("NUM_CONG_INTRO"), s"(x:num) + $Mod * $qy = y + $Mod * $qx ==> NUM_CONG ($Mod) x y").flatMap(mp(_, sum))
        } yield out
        backward <- for {
          held <- assumed(s"NUM_CONG ($Mod) (x:num) (y:num)")
          mulZero <- at(fact("NUM_MUL_ZERO"), s"$Mod * 0 = 0")
          own <- numLinText(Seq(dy, mulZero), s"(y:num) + $Mod * 0 = $ry + $Mod * $qy")
          toResidue <- at(fact("NUM_CONG_INTRO"), s"(y:num) + $Mod * 0 = $ry + $Mod * $qy ==> NUM_CONG ($Mod) y ($ry)").flatMap(mp(_, own))
          chained <- at(fact("NUM_CONG_TRANS"), s"NUM_CONG ($Mod) (x:num) (y:num) ==> NUM_CONG ($Mod) y ($ry) ==> NUM_CONG ($Mod) x ($ry)")
            .flatMap(mp(_, held._2, toResidue))
          small <- at(fact("NUM_MOD_LT"), s"0 < $Mod ==> $ry < $Mod").flatMap(mp(_, positive))
          out <- at(fact("NUM_MOD_OF_CONG"), s"NUM_CONG ($Mod) (x:num) ($ry) ==> $ry < $Mod ==> NUM_MOD x ($Mod) = $ry")
            .flatMap(mp(_, chained, small))
        } yield out
        general <- gen(Kernel.deductAntisym(backward, forward), kv, xv, yv)
      } yield general
    }

    /**
     * `n -> a n + b` is triangular for odd `a`. It keeps congruences, which is the first clause, and
     * is injective on residues modulo `2^k`: from `a m + b` congruent to `a n + b`, `2^k` divides
     * `a` times the difference of `m` and `n`, and two does not divide `a`, so `2^k` divides the
     * difference. `TRIANGULAR_OF_INJECTIVE` gives the second clause from that.
     */
    def affine: R[Kernel.Thm] = {
      val A = "(a:num)"; val B = "(b:num)"; val Mod = s"NUM_POW 2 $K"
      val apply: String => String = x => s"$A * $x + $B"
      def congText(x: String, y: String) = s"NUM_CONG ($Mod) ($x) ($y)"
      def toCong(x: String, y: String, agreeing: Kernel.Thm): R[Kernel.Thm] =
        at(known("MOD_CONG"), s"(${agree(x, y, K)}) = ${congText(x, y)}").flatMap(e => LogicError.lift(Kernel.eqMp(e, agreeing)))
      def toAgree(x: String, y: String, cong: Kernel.Thm): R[Kernel.Thm] =
        at(known("MOD_CONG"), s"(${agree(x, y, K)}) = ${congText(x, y)}").flatMap(Conv.sym).flatMap(e => LogicError.lift(Kernel.eqMp(e, cong)))
      for {
        odd <- assumed(s"NUM_MOD $A 2 = 1")
        notTwo <- for {
          held <- assumed(s"NUM_DIVIDES 2 $A")
          ex <- at(fact("NUM_DIVIDES_ELIM"), s"NUM_DIVIDES 2 $A ==> ?k:num. $A = 2 * k").flatMap(mp(_, held._2))
          contra <- choose(ex, "c") { (_, eq) =>
            for {
              t2 <- two
              zero <- at(fact("NUM_DIV_MOD_UNIQUE"), s"$A = 2 * (c:num) + 0 /\\ (0:num) < 2 ==> c = NUM_DIV $A 2 /\\ 0 = NUM_MOD $A 2")
                .flatMap(u => numLinText(Seq(eq), s"$A = 2 * (c:num) + 0").flatMap(e => conj(e, t2)).flatMap(mp(u, _)))
                .flatMap(rules.conjElim2)
              zeroIsOne <- trans(zero, odd._2)
              apart <- zeroNotOne
              out <- rules.notElim(apart, zeroIsOne)
            } yield out
          }
          out <- rules.notIntro(held._1, contra)
        } yield out
        keepsClause <- for {
          held <- assumed(agree(M, N, K))
          cong <- toCong(M, N, held._2)
          refA <- at(fact("NUM_CONG_REFL"), congText(A, A))
          refB <- at(fact("NUM_CONG_REFL"), congText(B, B))
          product <- at(fact("NUM_CONG_MUL"), s"${congText(A, A)} ==> ${congText(M, N)} ==> ${congText(s"$A * $M", s"$A * $N")}").flatMap(mp(_, refA, cong))
          sum <- at(fact("NUM_CONG_ADD"), s"${congText(s"$A * $M", s"$A * $N")} ==> ${congText(B, B)} ==> ${congText(apply(M), apply(N))}")
            .flatMap(mp(_, product, refB))
          out <- toAgree(apply(M), apply(N), sum).flatMap(rules.disch(held._1, _)).flatMap(gen(_, kv, mv, nv))
        } yield out
        separatesClause <- for {
          held <- assumed(agree(apply(M), apply(N), K))
          cong <- toCong(apply(M), apply(N), held._2)
          ex <- at(fact("NUM_CONG_ELIM"), s"${congText(apply(M), apply(N))} ==> ?i:num. ?j:num. ${apply(M)} + $Mod * i = ${apply(N)} + $Mod * j")
            .flatMap(mp(_, cong))
          congruent <- choose(ex, "i") { (_, inner) =>
            choose(inner, "j") { (_, eq) =>
              eitherOrder(M, N) { (lo, hi, le) =>
                // the side with the smaller argument carries the larger multiple of 2^k
                val (big, small) = if (lo == M) ("(i:num)", "(j:num)") else ("(j:num)", "(i:num)")
                val D = s"NUM_SUB $hi $lo"
                for {
                  add <- at(fact("NUM_SUB_ADD"), s"$lo <= $hi ==> $D + $lo = $hi").flatMap(mp(_, le))
                  spread <- num(s"$A * ($D + $lo) = $A * $D + $A * $lo").flatMap(rw(add, _))
                  difference <- numLinText(Seq(eq, spread), s"$Mod * $big = $Mod * $small + $A * $D")
                  whole <- at(fact("NUM_DIVIDES_INTRO"), s"$Mod * $big = $Mod * $big ==> NUM_DIVIDES ($Mod) ($Mod * $big)")
                    .flatMap(d => term(s"$Mod * $big", Numbers).flatMap(t => mp(d, Kernel.refl(t))))
                    .flatMap(rw(difference, _))
                  part <- at(fact("NUM_DIVIDES_INTRO"), s"$Mod * $small = $Mod * $small ==> NUM_DIVIDES ($Mod) ($Mod * $small)")
                    .flatMap(d => term(s"$Mod * $small", Numbers).flatMap(t => mp(d, Kernel.refl(t))))
                  product <- at(fact("NUM_DIVIDES_SUMMAND"),
                    s"NUM_DIVIDES ($Mod) ($Mod * $small) ==> NUM_DIVIDES ($Mod) ($Mod * $small + $A * $D) ==> NUM_DIVIDES ($Mod) ($A * $D)")
                    .flatMap(mp(_, part, whole))
                  twoIs <- numLinText(Seq.empty, "(2:num) = SUC (SUC 0)")
                  prime <- fact("NUM_PRIME_TWO").flatMap(p => Conv.sym(twoIs).flatMap(rw(_, p)))
                  cancelled <- at(fact("NUM_PRIME_POW_CANCEL"),
                    s"NUM_PRIME 2 ==> ~(NUM_DIVIDES 2 $A) ==> NUM_DIVIDES ($Mod) ($A * $D) ==> NUM_DIVIDES ($Mod) ($D)")
                    .flatMap(mp(_, prime, notTwo, product))
                  multiple <- at(fact("NUM_DIVIDES_ELIM"), s"NUM_DIVIDES ($Mod) ($D) ==> ?k:num. $D = $Mod * k").flatMap(mp(_, cancelled))
                  out <- choose(multiple, "e") { (_, de) =>
                    for {
                      mulZero <- at(fact("NUM_MUL_ZERO"), s"$Mod * 0 = 0")
                      sum <- numLinText(Seq(add, de, mulZero), s"$hi + $Mod * 0 = $lo + $Mod * (e:num)")
                      hiLo <- at(fact("NUM_CONG_INTRO"), s"$hi + $Mod * 0 = $lo + $Mod * (e:num) ==> ${congText(hi, lo)}").flatMap(mp(_, sum))
                      out <- if (hi == N) at(fact("NUM_CONG_SYM"), s"${congText(N, M)} ==> ${congText(M, N)}").flatMap(mp(_, hiLo)) else Right(hiLo)
                    } yield out
                  }
                } yield out
              }
            }
          }
          out <- toAgree(M, N, congruent).flatMap(rules.disch(held._1, _)).flatMap(gen(_, kv, mv, nv))
        } yield out
        both <- conj(keepsClause, separatesClause)
        out <- at(known("TRIANGULAR_OF_INJECTIVE"), s"${keepsAndSeparates(apply)} ==> ${triangular(apply)}").flatMap(mp(_, both))
          .flatMap(rules.disch(odd._1, _)).flatMap(gen(_, av, bv))
      } yield out
    }

    /** One conclusion from both orders of `a` and `b`: `close(lo, hi, le)` proves it under `lo <= hi`. */
    private def eitherOrder(a: String, b: String)(close: (String, String, Kernel.Thm) => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        total <- at(fact("NUM_LE_TOTAL"), s"$a <= $b \\/ $b <= $a")
        one <- assume(s"$a <= $b").flatMap(close(a, b, _))
        other <- assume(s"$b <= $a").flatMap(close(b, a, _))
        out <- rules.disjElim(total, one, other)
      } yield out
  }
}
