package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Case E6a of the essay on the use and harm of history for language models
 * (`thinktank/utitlita_e_danno`, `experiments/toy_model/sim.py`, `e6_exact`), derived in the kernel.
 *
 * E5 with one bit more. Beside the frame `g` the memory keeps a condition `c`, which says the
 * stored case is the same task as the question with reliability `r`: `c = 1` with probability `r` on
 * a familiar task and `1 - r` on a new one. The reader sees `(s, g, c)`, one signal
 * `t = 2 (8 s + g) + c` of the hundred and twenty-eight, and is the same well-specified Bayesian.
 *
 * Three values per `r`, each a theorem with no hypothesis, written for `r = 1` and `r = 9/10`:
 * the value on average ([[EssayMemory.Average]]), and the reader's rule scored on familiar tasks
 * ([[EssayMemory.Familiar]]) and on new ones ([[EssayMemory.NewTask]]). In closed form, with
 * `q = 7/20`, they are `r/2 + (1 - r)/16 + q/2`, `r + q (1 - r)` and `(1 - r)/8 + q r`.
 *
 * The rule follows `g` when `c = 1` and `s` when `c = 0`, strictly at every signal and at both
 * values of `r`. It does so for `26/35 < r <= 1` and not below, which the essay's
 * `e6_rule_interval.py` measures and this file does not need: at a written `r` it reads the rule
 * off the scores. The argument is written once, in `genericRule`, over four reals standing for
 * the two likelihoods of `s` and the frame's two weights, with the three comparisons each side
 * needs as hypotheses; three case splits on `s = a`, `g = a` and `s = g` and `ARGMAX_UNIQUE` give
 * it, and each `(r, c)` is an instance with its comparisons settled by the numbers. Deriving it at
 * each `(r, c)` instead took 1.56 million inferences of the 6.2 million the six values cost, and
 * the six did not fit beside the chain in the test fork's heap: 964 MB retained beside 581, against
 * 180 now, measured on 2026-10-23. The decision alone, `g` without `c`, is E5's `Full`, so its two
 * values are `EssayCase.Average` and `EssayCase.NewTask` and are not derived again here.
 */
private[theories] object EssayMemory {


  type R[A] = Either[LogicError, A]

  private val Hit = "((7:real) / 20)"
  private val Miss = "((13:real) / 140)"

  /** The frame's weight given the condition, `phi P(c | familiar) [g = y] + (1 - phi)/8 P(c | new)`. */
  private def frame(r: String, c: String, gIsY: String): String =
    if (c == "1") s"((1:real) / 2 * $gIsY * $r + 1 / 16 * (1 - $r))"
    else s"((1:real) / 2 * $gIsY * (1 - $r) + 1 / 16 * $r)"

  private val S_ = "NUM_DIV (NUM_DIV t 2) 8"
  private val G_ = "NUM_MOD (NUM_DIV t 2) 8"
  private val C_ = "NUM_MOD t 2"

  def raw(r: String): String =
    s"(\\y:num. \\t:num. COND ($S_ = y) $Hit $Miss * COND ($C_ = 1) " +
      s"${frame(r, "1", s"COND ($G_ = y) (1:real) 0")} ${frame(r, "0", s"COND ($G_ = y) (1:real) 0")})"

  def familiar(r: String): String =
    s"(\\y:num. \\t:num. COND ($S_ = y) $Hit $Miss * (COND ($G_ = y) (1:real) 0 * COND ($C_ = 1) $r (1 - $r)))"

  def novel(r: String): String =
    s"(\\y:num. \\t:num. COND ($S_ = y) $Hit $Miss * ((1:real) / 8 * COND ($C_ = 1) (1 - $r) $r))"

  private val Prior = EssayCase.Prior
  private val Utility = EssayCase.Utility

  private def rule(r: String, t: String): String =
    s"Argmax (\\a:num. Sum (\\z:num. $Prior z * ${raw(r)} z $t * $Utility a z) 8) 7"

  def averageText(r: String, value: String): String =
    s"VALUE 8 (2 * (8 * 8)) 7 $Prior ${raw(r)} $Utility = $value"

  private def scored(channel: String, r: String, value: String): String =
    s"Sum (\\t:num. Sum (\\y:num. $Prior y * $channel y t * $Utility (${rule(r, "t")}) y) 8) (2 * (8 * 8)) = $value"

  def familiarText(r: String, value: String): String = scored(familiar(r), r, value)
  def newTaskText(r: String, value: String): String = scored(novel(r), r, value)

  /** The six statements, for `r = 1` and `r = 9/10`, as (name, text). */
  val One = "(1:real)"
  val NineTenths = "((9:real) / 10)"
  val Statements: Vector[(String, String)] = Vector(
    "E6A_AVERAGE_R1" -> averageText(One, "(27:real) / 40"),
    "E6A_FAMILIAR_R1" -> familiarText(One, "(1:real)"),
    "E6A_NEW_TASK_R1" -> newTaskText(One, "(7:real) / 20"),
    "E6A_AVERAGE_R9" -> averageText(NineTenths, "(101:real) / 160"),
    "E6A_FAMILIAR_R9" -> familiarText(NineTenths, "(187:real) / 200"),
    "E6A_NEW_TASK_R9" -> newTaskText(NineTenths, "(131:real) / 400")
  )

  def derive(decision: Decision, successor: Successor): R[Map[String, Kernel.Thm]] = {
    val shared = new EssaySteps(decision, successor)
    import shared.*
    import shared.steps.*
    import shared.steps.kit.*

    /* ------------------------------------------------------------ the condition's two values */

    val zeroIsNotOne: R[Kernel.Thm] = for { z <- nm("0"); o <- nm("1"); out <- successor.distinct(z, o) } yield out

    /** `|- c < 2` at the literal `c`. */
    def belowTwo(c: String): R[Kernel.Thm] =
      for {
        two <- nm("2").flatMap(successor.spell)
        one <- nm("1").flatMap(successor.spell)
        lt <- if (c == "1") at(fact("NUM_LT_SUC"), "SUC (0:num) < SUC (SUC 0)")
              else for {
                a <- at(fact("NUM_LT_SUC"), "(0:num) < SUC 0")
                b <- at(fact("NUM_LT_SUC"), "SUC (0:num) < SUC (SUC 0)")
                both <- conj(a, b)
                out <- at(fact("NUM_LT_TRANS"), "(0:num) < SUC 0 /\\ SUC 0 < SUC (SUC 0) ==> 0 < SUC (SUC 0)").flatMap(mp(_, both))
              } yield out
        backTwo <- Conv.sym(two)
        backOne <- Conv.sym(one)
        moved <- rw(backTwo, lt)
        out <- rw(backOne, moved)
      } yield out

    /** `NUM_DIV (2 * u + c) 2 = u` and `NUM_MOD (2 * u + c) 2 = c`. */
    def halves(u: String, c: String): R[Seq[Kernel.Thm]] =
      for {
        t <- nm(s"2 * ($u) + $c")
        lt <- belowTwo(c)
        both <- conj(Kernel.refl(t), lt)
        unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
          s"2 * ($u) + $c = 2 * ($u) + $c /\\ ($c:num) < 2 ==> $u = NUM_DIV (2 * ($u) + $c) 2 /\\ $c = NUM_MOD (2 * ($u) + $c) 2")
          .flatMap(mp(_, both))
        parts <- split(unique)
        div <- Conv.sym(parts(0))
        mod <- Conv.sym(parts(1))
      } yield Seq(div, mod)

    /** `|- !x z. COND (c = 1) x z = x` at `c = 1`, and `= z` at `c = 0`: a rule that reaches under binders. */
    def settled(c: String): R[Kernel.Thm] =
      for {
        x <- prop0("x:real").flatMap { case v: FVar => Right(v); case o => Left(NotOfForm("a variable", o)) }
        z <- prop0("z:real").flatMap { case v: FVar => Right(v); case o => Left(NotOfForm("a variable", o)) }
        one <- nm("1")
        at <- if (c == "1") condOn("(1:num) = 1", "(x:real)", "(z:real)", Kernel.refl(one))
              else zeroIsNotOne.flatMap(ne => condOff("(0:num) = 1", "(x:real)", "(z:real)", ne))
        out <- rules.genAll(at, List(x, z))
      } yield out

    /* -------------------------------------------- the score, the strict maximum, the rule */

    def score(r: String, c: String, S: String, G: String, A: String): String =
      s"(1:real) / 8 * (COND ($S = $A) $Q $Qr * ${frame(r, c, s"COND ($G = $A) (1:real) 0")})"

    def inner(r: String, c: String, S: String, G: String, A: String): String =
      s"Sum (\\y:num. (1:real) / 8 * (COND ($S = y) $Q $Qr * ${frame(r, c, s"COND ($G = y) (1:real) 0")}) * " +
        s"COND (y = $A) (1:real) 0) 8"

    // The same two, over four reals nothing fixes: the likelihood of `s` when it is or is not the
    // action, and the frame's weight when `g` is or is not. The rule's argument is the same at every
    // `(r, c)` and is written once over these, with the three comparisons it needs as hypotheses.
    val Lq = "(q:real)"; val Lqr = "(qr:real)"; val F1 = "(f1:real)"; val F0 = "(f0:real)"
    def gScore(S: String, G: String, A: String): String =
      s"(1:real) / 8 * (COND ($S = $A) $Lq $Lqr * COND ($G = $A) $F1 $F0)"
    def gInner(S: String, G: String, A: String): String =
      s"Sum (\\y:num. (1:real) / 8 * (COND ($S = y) $Lq $Lqr * COND ($G = y) $F1 $F0) * COND (y = $A) (1:real) 0) 8"

    /** What the rule at `g` (`c = 1`) or at `s` (`c = 0`) needs of the four, one per case left standing. */
    def comparisons(c: String): Seq[String] =
      if (c == "1") Seq(s"$Lq * $F0 < $Lqr * $F1", s"$Lqr * $F0 < $Lqr * $F1", s"$Lqr * $F0 < $Lq * $F1")
      else Seq(s"$Lqr * $F1 < $Lq * $F0", s"$Lqr * $F0 < $Lq * $F0", s"$Lqr * $F0 < $Lq * $F1")

    /** The leaves of a case split on each proposition in turn, `Right` where it holds and `Left` where it fails. */
    def splits(props: List[String], held: Map[String, Either[Kernel.Thm, Kernel.Thm]])(
      leaf: Map[String, Either[Kernel.Thm, Kernel.Thm]] => R[Kernel.Thm]
    ): R[Kernel.Thm] = props match {
      case Nil => leaf(held)
      case p :: rest => cases(p)(yes => splits(rest, held + (p -> Right(yes)))(leaf), no => splits(rest, held + (p -> Left(no)))(leaf))
    }

    /** `score a < score w` for `a <> w`, `w` being `g` or `s`, by the three equalities among `s`, `g`, `a`. */
    def strictly(hyps: Seq[Kernel.Thm], S: String, G: String, A: String, W: String, other: Kernel.Thm): R[Kernel.Thm] =
      for {
        goal <- prop(s"${gScore(S, G, A)} < ${gScore(S, G, W)}")
        sT <- prop0(S)
        gT <- prop0(G)
        sA = s"$S = $A"; gA = s"$G = $A"; sg = s"$S = $G"
        out <- splits(List(sA, gA, sg), Map.empty) { held =>
          def absurd(thm: R[Kernel.Thm]): R[Kernel.Thm] = thm.flatMap(f => rules.falsityElim(goal, f))
          (held(sA), held(gA), held(sg)) match {
            case (Right(x), Right(y), Left(n)) => absurd(Conv.sym(y).flatMap(trans(x, _)).flatMap(rules.notElim(n, _)))
            case (Right(x), Left(n), Right(z)) => absurd(Conv.sym(z).flatMap(trans(_, x)).flatMap(rules.notElim(n, _)))
            case (Left(n), Right(y), Right(z)) => absurd(trans(z, y).flatMap(rules.notElim(n, _)))
            case (_, Right(y), _) if W == G => absurd(Conv.sym(y).flatMap(rules.notElim(other, _)))
            case (Right(x), _, _) if W == S => absurd(Conv.sym(x).flatMap(rules.notElim(other, _)))
            case (hsA, hgA, hsg) =>
              for {
                e1 <- hsA.fold(n => condOff(sA, Lq, Lqr, n), y => condOn(sA, Lq, Lqr, y))
                e2 <- hgA.fold(n => condOff(gA, F1, F0, n), y => condOn(gA, F1, F0, y))
                atW <-
                  if (W == G)
                    for {
                      a <- hsg.fold(n => condOff(sg, Lq, Lqr, n), y => condOn(sg, Lq, Lqr, y))
                      b <- condOn(s"$G = $G", F1, F0, Kernel.refl(gT))
                    } yield Seq(a, b)
                  else
                    for {
                      a <- condOn(s"$S = $S", Lq, Lqr, Kernel.refl(sT))
                      gs = s"$G = $S"
                      b <- hsg.fold(
                        n => flip(S, G).flatMap(e => rw(e, n)).flatMap(condOff(gs, F1, F0, _)),
                        y => Conv.sym(y).flatMap(condOn(gs, F1, F0, _)))
                    } yield Seq(a, b)
                out <- exact(Seq(e1, e2) ++ atW, hyps, goal)
              } yield out
          }
        }
      } yield out

    /** `inner a = score a` for every `a <= 7`. */
    def collapsed(S: String, G: String): R[Kernel.Thm] =
      for {
        each <- prop(s"!a:num. a <= 7 ==> ${gInner(S, G, "a")} = ${gScore(S, G, "a")}")
        out <- every(each) { (as, ahs, _) =>
          val A = num(as(0))
          belowEight(A, ahs(0)).flatMap(lt =>
            at(k(Decision.SumIndicator), s"$A < 8 ==> ${gInner(S, G, A)} = ${gScore(S, G, A)}").flatMap(mp(_, lt)))
        }
      } yield out

    /** `Maximum (\a. inner a) 7 = score w` and `Argmax (\a. inner a) 7 = w`. */
    def best(hyps: Seq[Kernel.Thm], S: String, G: String, W: FVar, wLe: Kernel.Thm): R[(Kernel.Thm, Kernel.Thm)] = {
      val Wt = num(W)
      for {
        pointwise <- collapsed(S, G)
        same <- at(k(Decision.MaximumCongruenceBelow),
          s"(!a:num. a <= 7 ==> (\\a:num. ${gInner(S, G, "a")}) a = (\\a:num. ${gScore(S, G, "a")}) a) ==> " +
            s"Maximum (\\a:num. ${gInner(S, G, "a")}) 7 = Maximum (\\a:num. ${gScore(S, G, "a")}) 7")
          .flatMap(mp(_, pointwise))
        fT <- prop0(s"\\a:num. ${gScore(S, G, "a")}")
        seven <- nm("7")
        upper <- spec(k(Decision.MaximumUpper), fT, seven, W).flatMap(mp(_, wLe))
        // the strict comparison once, and read by both the bound and the rule below
        strictGoal <- prop(s"!a:num. a <= 7 ==> ~(a = $Wt) ==> ${gScore(S, G, "a")} < ${gScore(S, G, Wt)}")
        strictAll <- every(strictGoal) { (as, ahs, _) => strictly(hyps, S, G, num(as(0)), Wt, ahs(1)) }
        bound <- prop(s"!a:num. a <= 7 ==> (\\a:num. ${gScore(S, G, "a")}) a <= ${gScore(S, G, Wt)}")
        bounded <- every(bound) { (as, ahs, g) =>
          val A = num(as(0))
          cases(s"$A = $Wt")(
            equal => exact(Seq(equal), Seq.empty, g),
            other => at(strictAll, s"$A <= 7 ==> ~($A = $Wt) ==> ${gScore(S, G, A)} < ${gScore(S, G, Wt)}")
              .flatMap(mp(_, ahs(0), other)).flatMap(lt => exact(Seq.empty, Seq(lt), g))
          )
        }
        cT <- prop0(gScore(S, G, Wt))
        least <- spec(k(Decision.MaximumLeast), fT, seven, cT).flatMap(mp(_, bounded))
        maxGoal <- prop(s"Maximum (\\a:num. ${gInner(S, G, "a")}) 7 = ${gScore(S, G, Wt)}")
        maximum <- exact(Seq(same), Seq(upper, least), maxGoal)
        strict <- prop(s"!i:num. i <= 7 ==> ~(i = $Wt) ==> " +
          s"(\\a:num. ${gInner(S, G, "a")}) i < (\\a:num. ${gInner(S, G, "a")}) $Wt")
        below <- every(strict) { (is, ihs, goal) =>
          val I = num(is(0))
          for {
            atI <- at(pointwise, s"$I <= 7 ==> ${gInner(S, G, I)} = ${gScore(S, G, I)}").flatMap(mp(_, ihs(0)))
            atW <- at(pointwise, s"$Wt <= 7 ==> ${gInner(S, G, Wt)} = ${gScore(S, G, Wt)}").flatMap(mp(_, wLe))
            lt <- at(strictAll, s"$I <= 7 ==> ~($I = $Wt) ==> ${gScore(S, G, I)} < ${gScore(S, G, Wt)}")
              .flatMap(mp(_, ihs(0), ihs(1)))
            out <- exact(Seq(atI, atW), Seq(lt), goal)
          } yield out
        }
        gT <- prop0(s"\\a:num. ${gInner(S, G, "a")}")
        theRule <- spec(k(Decision.ArgmaxUnique), gT, seven, W).flatMap(mp(_, wLe, below))
      } yield (maximum, theRule)
    }

    /**
     * The rule over the four reals, once for each side it can fall on: `|- !q qr f1 f0. H1 ==> H2 ==> H3 ==>
     * !ss gg. ss < 8 ==> gg < 8 ==> Maximum ... = score w /\ Argmax ... = w`.
     */
    val generic = scala.collection.mutable.Map.empty[String, Kernel.Thm]
    def genericRule(c: String): R[Kernel.Thm] = generic.get(c).map(Right(_)).getOrElse {
      val win = if (c == "1") "gg" else "ss"
      for {
        hypTerms <- comparisons(c).foldLeft[R[Vector[Term]]](Right(Vector.empty))((acc, h) => acc.flatMap(v => prop(h).map(v :+ _)))
        hyps <- hypTerms.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, h) => acc.flatMap(v => LogicError.lift(Kernel.assume(h)).map(v :+ _)))
        goal <- prop(s"!ss:num. !gg:num. ss < 8 ==> gg < 8 ==> " +
          s"Maximum (\\a:num. ${gInner("ss", "gg", "a")}) 7 = ${gScore("ss", "gg", win)} /\\ " +
          s"Argmax (\\a:num. ${gInner("ss", "gg", "a")}) 7 = $win")
        proved <- every(goal) { (vs, hs, _) =>
          val (sV, gV) = (vs(0), vs(1))
          val (wV, wBelow) = if (c == "1") (gV, hs(1)) else (sV, hs(0))
          for {
            wLe <- atMostSeven(num(wV), wBelow)
            b <- best(hyps, num(sV), num(gV), wV, wLe)
            out <- conj(b._1, b._2)
          } yield out
        }
        discharged <- hypTerms.reverse.foldLeft[R[Kernel.Thm]](Right(proved))((acc, h) => acc.flatMap(rules.disch(h, _)))
        vars <- Seq(Lq, Lqr, F1, F0).foldLeft[R[List[FVar]]](Right(Nil))((acc, t) => acc.flatMap(l => prop0(t).flatMap {
          case x: FVar => Right(l :+ x); case o => Left(NotOfForm("a variable", o)) }))
        out <- rules.genAll(discharged, vars)
      } yield { generic(c) = out; out }
    }

    /**
     * `genericRule` at `q = 7/20`, `qr = 13/140` and the frame's two weights at `(r, c)`, its three
     * comparisons settled by the numbers, and read back in the form the values use: the frame at the
     * indicator of `g = y` rather than an indicator choosing between the frame's two weights.
     */
    val bests = scala.collection.mutable.Map.empty[(String, String), Kernel.Thm]
    def bestAt(r: String, c: String, s: FVar, g: FVar, sBelow: Kernel.Thm, gBelow: Kernel.Thm): R[(Kernel.Thm, Kernel.Thm)] = {
      val win = if (c == "1") "gg" else "ss"
      val one = frame(r, c, "(1:real)")
      val zero = frame(r, c, "0")
      val general: R[Kernel.Thm] = bests.get((r, c)).map(Right(_)).getOrElse(
        for {
          rule <- genericRule(c)
          values <- Seq(Q, Qr, one, zero).foldLeft[R[List[Term]]](Right(Nil))((acc, t) => acc.flatMap(l => prop0(t).map(l :+ _)))
          inst <- spec(rule, values*)
          settled <- comparisons(c).foldLeft[R[Kernel.Thm]](Right(inst)) { (acc, h) =>
            val numeric = h.replace(Lqr, Qr).replace(Lq, Q).replace(F1, one).replace(F0, zero)
            for { thm <- acc; t <- prop(numeric); lt <- exact(Seq.empty, Seq.empty, t); out <- mp(thm, lt) } yield out
          }
          // `COND (gg = y) one zero = frame (COND (gg = y) 1 0)` at every `gg` and `y`, by cases
          bridgeGoal <- prop(s"!gg:num. !y:num. COND (gg = y) $one $zero = ${frame(r, c, "COND (gg = y) (1:real) 0")}")
          bridge <- every(bridgeGoal) { (vs, _, g0) =>
            val eq = s"${num(vs(0))} = ${num(vs(1))}"
            cases(eq)(
              on => for { a <- condOn(eq, one, zero, on); b <- condOn(eq, "(1:real)", "0", on); out <- exact(Seq(a, b), Seq.empty, g0) } yield out,
              off => for { a <- condOff(eq, one, zero, off); b <- condOff(eq, "(1:real)", "0", off); out <- exact(Seq(a, b), Seq.empty, g0) } yield out
            )
          }
          set <- Rewrite.Rule.all(logic, Vector(bridge))
          moved <- Rewrite.rewrite(set, settled.conclusion)
          read <- LogicError.lift(Kernel.eqMp(moved, settled))
          goal <- prop(s"!ss:num. !gg:num. ss < 8 ==> gg < 8 ==> " +
            s"Maximum (\\a:num. ${inner(r, c, "ss", "gg", "a")}) 7 = ${score(r, c, "ss", "gg", win)} /\\ " +
            s"Argmax (\\a:num. ${inner(r, c, "ss", "gg", "a")}) 7 = $win")
          out <- if (read.conclusion == goal) Right(read) else Left(NotOfForm(goal.toString, read.conclusion))
        } yield { bests((r, c)) = out; out })
      for {
        g0 <- general
        inst <- spec(g0, s, g)
        both <- mp(inst, sBelow, gBelow)
        parts <- split(both)
      } yield (parts(0), parts(1))
    }

    /* ---------------------------------------------------------------- the sums over signals */

    /**
     * A sum over the hundred and twenty-eight signals of `term(t)`, read in pairs `2 u + c` and the
     * `u` in blocks `8 s + g`, whose two terms at a pair `(s, g)` add to `COND (g = s) x z`.
     */
    def overSignals(term: String => String, x: String, z: String,
      cell: (FVar, FVar, Kernel.Thm, Kernel.Thm, String) => R[Kernel.Thm], whole: Seq[Kernel.Thm], total: String
    ): R[Kernel.Thm] = {
      val pair = (u: String) => s"${term(s"(2 * $u + 0)")} + ${term(s"(2 * $u + 1)")}"
      for {
        outer <- at(k(Decision.SumGroups),
          s"Sum (\\t:num. ${term("t")}) (2 * (8 * 8)) = Sum (\\u:num. Sum (\\c:num. ${term("(2 * u + c)")}) 2) (8 * 8)")
        // the two conditions of each pair, by the recurrence at `SUC (SUC 0)` and the spellings back
        twoEach <- prop(s"!u:num. Sum (\\c:num. ${term("(2 * u + c)")}) 2 = ${pair("u")}")
        opened <- every(twoEach) { (us, _, goal) =>
          val U = num(us(0))
          for {
            two <- nm("2").flatMap(successor.spell)
            one <- nm("1").flatMap(successor.spell)
            backOne <- Conv.sym(one)
            s2 <- at(fact("SUM_SUC"), s"Sum (\\c:num. ${term(s"(2 * $U + c)")}) (SUC (SUC 0)) = " +
              s"Sum (\\c:num. ${term(s"(2 * $U + c)")}) (SUC 0) + ${term(s"(2 * $U + SUC 0)")}")
            s1 <- at(fact("SUM_SUC"), s"Sum (\\c:num. ${term(s"(2 * $U + c)")}) (SUC 0) = " +
              s"Sum (\\c:num. ${term(s"(2 * $U + c)")}) 0 + ${term(s"(2 * $U + 0)")}")
            s0 <- fact("SUM_ZERO")
            unrolled <- prop(s"Sum (\\c:num. ${term(s"(2 * $U + c)")}) (SUC (SUC 0)) = " +
              s"${term(s"(2 * $U + 0)")} + ${term(s"(2 * $U + SUC 0)")}")
            raw <- exact(Seq(s2, s1, s0), Seq.empty, unrolled)
            back2 <- Conv.sym(two)
            numerals2 <- rw(back2, raw)
            out <- rw(backOne, numerals2)
          } yield out
        }
        spread <- at(fact("SUM_CONGRUENCE"),
          s"(!u:num. Sum (\\c:num. ${term("(2 * u + c)")}) 2 = (\\u:num. ${pair("u")}) u) ==> " +
            s"(!n:num. Sum (\\u:num. Sum (\\c:num. ${term("(2 * u + c)")}) 2) n = Sum (\\u:num. ${pair("u")}) n)")
          .flatMap(mp(_, opened)).flatMap(t => at(t, s"Sum (\\u:num. Sum (\\c:num. ${term("(2 * u + c)")}) 2) (8 * 8) = " +
            s"Sum (\\u:num. ${pair("u")}) (8 * 8)"))
        blocks <- at(k(Decision.SumGroups),
          s"Sum (\\u:num. ${pair("u")}) (8 * 8) = Sum (\\s:num. Sum (\\g:num. ${pair("(8 * s + g)")}) 8) 8")
        row = s"($x + (real_of_num 8 - 1) * $z)"
        perS <- prop(s"!s:num. s < 8 ==> Sum (\\g:num. ${pair("(8 * s + g)")}) 8 = $row")
        rows <- every(perS) { (ss, shs, rowGoal) =>
          val S = num(ss(0))
          val Cell = s"(\\g:num. COND (g = $S) $x $z)"
          for {
            perG <- prop(s"!g:num. g < 8 ==> ${pair(s"(8 * $S + g)")} = $Cell g")
            cells <- every(perG) { (gs, ghs, cellGoal) => cell(ss(0), gs(0), shs(0), ghs(0), cellGoal.toString) }
            spreadG <- at(fact("SUM_CONGRUENCE_BELOW"),
              s"(!g:num. g < 8 ==> ${pair(s"(8 * $S + g)")} = $Cell g) ==> Sum (\\g:num. ${pair(s"(8 * $S + g)")}) 8 = Sum $Cell 8")
              .flatMap(mp(_, cells))
            counted <- at(k(Decision.SumCondCount),
              s"$S < 8 ==> Sum (\\g:num. COND (g = $S) $x $z) 8 = $x + (real_of_num 8 - 1) * $z").flatMap(mp(_, shs(0)))
            out <- trans(spreadG, counted)
          } yield out
        }
        collect <- at(fact("SUM_CONGRUENCE_BELOW"),
          s"(!s:num. s < 8 ==> Sum (\\g:num. ${pair("(8 * s + g)")}) 8 = (\\s:num. $row) s) ==> " +
            s"Sum (\\s:num. Sum (\\g:num. ${pair("(8 * s + g)")}) 8) 8 = Sum (\\s:num. $row) 8")
          .flatMap(mp(_, rows))
        flat <- at(fact("SUM_CONSTANT"), s"Sum (\\s:num. $row) 8 = real_of_num 8 * ($row)")
        numerals <- realNumerals
        goal <- prop(total)
        // the steps meet end to end, so they compose by transitivity rather than by rewriting a goal
        // the size of the hundred and twenty-eight terms; only the last line is arithmetic
        chained <- trans(outer, (Seq(spread, blocks, collect, flat))*)
        joined <- whole.headOption.fold[R[Kernel.Thm]](Right(chained))(trans(_, chained))
        out <- rewriting(Seq(joined), goal)(g => exact(numerals, Seq.empty, g))
      } yield out
    }

    /** The decoding of the signals `2 (8 s + g) + 0` and `+ 1` and the condition settled, as rewrite rules. */
    def decoded(S: String, G: String, gBelow: Kernel.Thm): R[Seq[Kernel.Thm]] =
      for {
        h0 <- halves(s"8 * $S + $G", "0")
        h1 <- halves(s"8 * $S + $G", "1")
        co <- coordinates(S, G, gBelow)
        c0 <- settled("0")
        c1 <- settled("1")
      } yield h0 ++ h1 ++ co ++ Seq(c0, c1)

    /** The equalities among `s` and `g` settled on each side of `g = s`, for the conditionals left at a winner. */
    def atWinners(S: String, G: String, x: String, z: String, sT: Term, gT: Term)(close: Seq[Kernel.Thm] => R[Kernel.Thm]): R[Kernel.Thm] =
      cases(s"$G = $S")(
        same =>
          for {
            cell <- condOn(s"$G = $S", x, z, same)
            back <- Conv.sym(same)
            sg <- condOn(s"$S = $G", Q, Qr, back)
            gg <- condOn(s"$G = $G", "(1:real)", "0", Kernel.refl(gT))
            ss <- condOn(s"$S = $S", Q, Qr, Kernel.refl(sT))
            gs <- condOn(s"$G = $S", "(1:real)", "0", same)
            out <- close(Seq(cell, sg, gg, ss, gs))
          } yield out,
        apart =>
          for {
            cell <- condOff(s"$G = $S", x, z, apart)
            turned <- flip(G, S).flatMap(e => rw(e, apart))
            sg <- condOff(s"$S = $G", Q, Qr, turned)
            gg <- condOn(s"$G = $G", "(1:real)", "0", Kernel.refl(gT))
            ss <- condOn(s"$S = $S", Q, Qr, Kernel.refl(sT))
            gs <- condOff(s"$G = $S", "(1:real)", "0", apart)
            out <- close(Seq(cell, sg, gg, ss, gs))
          } yield out
      )

    def avgTerm(r: String)(t: String): String =
      s"Maximum (\\a:num. Sum (\\y:num. (1:real) / 8 * (COND (NUM_DIV (NUM_DIV $t 2) 8 = y) $Q $Qr * " +
        s"COND (NUM_MOD $t 2 = 1) ${frame(r, "1", s"COND (NUM_MOD (NUM_DIV $t 2) 8 = y) (1:real) 0")} " +
        s"${frame(r, "0", s"COND (NUM_MOD (NUM_DIV $t 2) 8 = y) (1:real) 0")}) * COND (y = a) (1:real) 0) 8) 7"

    def ruleAt(r: String, t: String): String =
      s"Argmax (\\a:num. Sum (\\z:num. (1:real) / 8 * (COND (NUM_DIV (NUM_DIV $t 2) 8 = z) $Q $Qr * " +
        s"COND (NUM_MOD $t 2 = 1) ${frame(r, "1", s"COND (NUM_MOD (NUM_DIV $t 2) 8 = z) (1:real) 0")} " +
        s"${frame(r, "0", s"COND (NUM_MOD (NUM_DIV $t 2) 8 = z) (1:real) 0")}) * COND (z = a) (1:real) 0) 8) 7"

    /** The familiar or new channel's weight at `y`, with the condition still to be settled. */
    def famWeight(r: String, t: String, y: String): String =
      s"(COND (NUM_DIV (NUM_DIV $t 2) 8 = $y) $Q $Qr * (COND (NUM_MOD (NUM_DIV $t 2) 8 = $y) (1:real) 0 * COND (NUM_MOD $t 2 = 1) $r (1 - $r)))"
    def newWeight(r: String, t: String, y: String): String =
      s"(COND (NUM_DIV (NUM_DIV $t 2) 8 = $y) $Q $Qr * ((1:real) / 8 * COND (NUM_MOD $t 2 = 1) (1 - $r) $r))"

    def scoredTerm(r: String, weight: (String, String, String) => String)(t: String): String =
      s"Sum (\\y:num. (1:real) / 8 * ${weight(r, t, "y")} * COND (y = ${ruleAt(r, t)}) (1:real) 0) 8"

    /** The settled weights, at `y` and at the literal condition. */
    def famSettled(r: String, c: String, S: String, G: String, y: String): String =
      s"(COND ($S = $y) $Q $Qr * (COND ($G = $y) (1:real) 0 * ${if (c == "1") r else s"(1 - $r)"}))"
    def newSettled(r: String, c: String, S: String, G: String, y: String): String =
      s"(COND ($S = $y) $Q $Qr * ((1:real) / 8 * ${if (c == "1") s"(1 - $r)" else r}))"

    def average(r: String, total: String): R[Kernel.Thm] = {
      for {
        whole <- unfold(Decision.ValueName, "8:num", "2 * ((8:num) * 8)", "7:num", Prior, raw(r), Utility)
        xT = s"((1:real) / 8 * ($Q * ${frame(r, "0", "(1:real)")}) + (1:real) / 8 * ($Q * ${frame(r, "1", "(1:real)")}))"
        zT = s"((1:real) / 8 * ($Q * ${frame(r, "0", "0")}) + (1:real) / 8 * ($Qr * ${frame(r, "1", "(1:real)")}))"
        out <- overSignals(avgTerm(r), xT, zT,
          (s, g, sBelow, gBelow, _) => {
            val (sN, gN) = (num(s), num(g))
            for {
              codes <- decoded(sN, gN, gBelow)
              b0 <- bestAt(r, "0", s, g, sBelow, gBelow)
              b1 <- bestAt(r, "1", s, g, sBelow, gBelow)
              goal <- prop(s"${avgTerm(r)(s"(2 * (8 * $sN + $gN) + 0)")} + ${avgTerm(r)(s"(2 * (8 * $sN + $gN) + 1)")} = " +
                s"COND ($gN = $sN) $xT $zT")
              out <- atWinners(sN, gN, xT, zT, s, g)(eqs => exact(codes ++ Seq(b0._1, b1._1) ++ eqs, Seq.empty, goal))
            } yield out
          },
          Seq(whole), averageText(r, total))
      } yield out
    }

    def scoredValue(r: String, total: String, weight: (String, String, String) => String,
      settledWeight: (String, String, String, String, String) => String, text: String, xT: String, zT: String): R[Kernel.Thm] =
      overSignals(scoredTerm(r, weight), xT, zT,
        (s, g, sBelow, gBelow, _) => {
          val (sN, gN) = (num(s), num(g))
          for {
            codes <- decoded(sN, gN, gBelow)
            b0 <- bestAt(r, "0", s, g, sBelow, gBelow)
            b1 <- bestAt(r, "1", s, g, sBelow, gBelow)
            p0 <- at(k(Decision.SumIndicator),
              s"$sN < 8 ==> Sum (\\y:num. (1:real) / 8 * ${settledWeight(r, "0", sN, gN, "y")} * COND (y = $sN) (1:real) 0) 8 = " +
                s"(1:real) / 8 * ${settledWeight(r, "0", sN, gN, sN)}").flatMap(mp(_, sBelow))
            p1 <- at(k(Decision.SumIndicator),
              s"$gN < 8 ==> Sum (\\y:num. (1:real) / 8 * ${settledWeight(r, "1", sN, gN, "y")} * COND (y = $gN) (1:real) 0) 8 = " +
                s"(1:real) / 8 * ${settledWeight(r, "1", sN, gN, gN)}").flatMap(mp(_, gBelow))
            goal <- prop(s"${scoredTerm(r, weight)(s"(2 * (8 * $sN + $gN) + 0)")} + ${scoredTerm(r, weight)(s"(2 * (8 * $sN + $gN) + 1)")} = " +
              s"COND ($gN = $sN) $xT $zT")
            out <- atWinners(sN, gN, xT, zT, s, g)(eqs => exact(codes ++ Seq(b0._2, b1._2, p0, p1) ++ eqs, Seq.empty, goal))
          } yield out
        },
        Seq.empty, text)

    def familiarValue(r: String, total: String): R[Kernel.Thm] =
      scoredValue(r, total, famWeight, famSettled, familiarText(r, total),
        s"((1:real) / 8 * ($Q * ((1:real) * (1 - $r))) + (1:real) / 8 * ($Q * ((1:real) * $r)))",
        s"((1:real) / 8 * ($Q * (0 * (1 - $r))) + (1:real) / 8 * ($Qr * ((1:real) * $r)))")

    def newValue(r: String, total: String): R[Kernel.Thm] =
      scoredValue(r, total, newWeight, newSettled, newTaskText(r, total),
        s"((1:real) / 8 * ($Q * ((1:real) / 8 * $r)) + (1:real) / 8 * ($Q * ((1:real) / 8 * (1 - $r))))",
        s"((1:real) / 8 * ($Q * ((1:real) / 8 * $r)) + (1:real) / 8 * ($Qr * ((1:real) / 8 * (1 - $r))))")

    for {
      a1 <- average(One, "(27:real) / 40")
      f1 <- familiarValue(One, "(1:real)")
      n1 <- newValue(One, "(7:real) / 20")
      a9 <- average(NineTenths, "(101:real) / 160")
      f9 <- familiarValue(NineTenths, "(187:real) / 200")
      n9 <- newValue(NineTenths, "(131:real) / 400")
    } yield Map(
      "E6A_AVERAGE_R1" -> a1, "E6A_FAMILIAR_R1" -> f1, "E6A_NEW_TASK_R1" -> n1,
      "E6A_AVERAGE_R9" -> a9, "E6A_FAMILIAR_R9" -> f9, "E6A_NEW_TASK_R9" -> n9
    )
  }
}
