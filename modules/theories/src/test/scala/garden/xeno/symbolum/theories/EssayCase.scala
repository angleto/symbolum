package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Case E5 of the essay on the use and harm of history for language models
 * (`thinktank/utitlita_e_danno`, `experiments/toy_model/sim.py`, `e5`), derived in the kernel.
 *
 * Eight answers, the true one `y` uniform. A parametric signal `s` is `y` with probability `7/20`
 * and otherwise uniform on the other seven. An example of the frame, `g`, is `y` on a familiar task
 * and uniform on all eight on a new one, the two equally likely, so `g = y` has probability `9/16`
 * and each other value `1/16`. The reader is a well-specified Bayesian who never sees which kind of
 * task it is on, and is paid one for the right answer and nothing otherwise.
 *
 * The pair `(s, g)` is one signal `t = 8 s + g` of the sixty-four, read back by `NUM_DIV` and
 * `NUM_MOD`. Three values, each a theorem with no hypothesis:
 *
 *  - [[EssayCase.Empty]]: with `s` alone the value is `7/20`;
 *  - [[EssayCase.Average]]: with `s` and `g` it is `9/16`, at least `7/20` as Blackwell says, since
 *    dropping `g` is a garbling;
 *  - [[EssayCase.NewTask]]: the same reader's rule, which follows `g`, is right `1/8` of the time
 *    on new tasks, less than the `7/20` it had without `g`.
 *
 * So the monotonicity holds on average over the tasks and not conditioned on the task, which is the
 * point the essay prints. `docs/adr/0063` is why this is in the test scope and not in the library.
 *
 * The maximum at each signal is found by hand rather than computed: at `t = 8 s + g` the reader's
 * score for answer `a` is `1/8 * P(s | a) * P(g | a)`, largest at `a = g` and strictly, which three
 * case splits on `a = g`, `s = a` and `s = g` settle, the closest comparison being
 * `49/2240 < 117/2240` between the products `P(s | a) P(g | a)`, the common `1/8` left out. The
 * sums over the signals then close by `SUM_GROUPS`, `SUM_INDICATOR` and `SUM_COND_COUNT`.
 */
private[theories] object EssayCase {

  type R[A] = Either[LogicError, A]

  val Prior: String = "(\\y:num. (1:real) / 8)"
  val Signal: String = "(\\y:num. \\s:num. COND (s = y) ((7:real) / 20) (13 / 140))"
  val Utility: String = "(\\a:num. \\y:num. COND (y = a) (1:real) 0)"
  val Full: String =
    "(\\y:num. \\t:num. COND (NUM_DIV t 8 = y) ((7:real) / 20) (13 / 140) * COND (NUM_MOD t 8 = y) ((9:real) / 16) (1 / 16))"
  val Novel: String = "(\\y:num. \\t:num. COND (NUM_DIV t 8 = y) ((7:real) / 20) (13 / 140) * ((1:real) / 8))"

  /** `V(0)`: the signal alone. */
  val Empty: String = s"VALUE 8 8 7 $Prior $Signal $Utility = (7:real) / 20"

  /** `V(1; average)`: the signal and the frame, over both kinds of task. */
  val Average: String = s"VALUE 8 (8 * 8) 7 $Prior $Full $Utility = (9:real) / 16"

  /** `V(1; new task)`: the rule that is optimal on average, scored on new tasks only. */
  val NewTask: String =
    s"Sum (\\t:num. Sum (\\y:num. $Prior y * $Novel y t * $Utility (Argmax (\\a:num. " +
      s"Sum (\\z:num. $Prior z * $Full z t * $Utility a z) 8) 7) y) 8) (8 * 8) = (1:real) / 8"

  final case class Values(empty: Kernel.Thm, average: Kernel.Thm, newTask: Kernel.Thm)

  def derive(decision: Decision, successor: Successor): R[Values] = {
    val shared = new EssaySteps(decision, successor)
    import shared.*
    import shared.steps.*
    import shared.steps.kit.*

    /* ---------------------------------------------------------------- V(0) */

    val empty: R[Kernel.Thm] = {
      val a = Term.variable("a", TyApp(Natural.TypeName, Nil))
      for {
        value <- unfold(Decision.ValueName, "8:num", "8:num", "7:num", Prior, Signal, Utility)
        each <- prop(s"!s:num. s < 8 ==> Maximum (\\a:num. Sum (\\y:num. (1:real) / 8 * COND (s = y) $Q $Qr * " +
          s"COND (y = a) (1:real) 0) 8) 7 = (1:real) / 8 * $Q")
        perSignal <- every(each) { (ss, shs, goal) =>
          val S = num(ss(0))
          for {
            // the inner sum picks the term at a, for every a <= 7
            inner <- prop(s"!a:num. a <= 7 ==> Sum (\\y:num. (1:real) / 8 * COND ($S = y) $Q $Qr * COND (y = a) (1:real) 0) 8 = " +
              s"(\\a:num. (1:real) / 8 * COND ($S = a) $Q $Qr) a")
            picked <- every(inner) { (as, ahs, _) =>
              val A = num(as(0))
              for {
                lt <- belowEight(A, ahs(0))
                out <- at(k(Decision.SumIndicator),
                  s"$A < 8 ==> Sum (\\y:num. (1:real) / 8 * COND ($S = y) $Q $Qr * COND (y = $A) (1:real) 0) 8 = " +
                    s"(1:real) / 8 * COND ($S = $A) $Q $Qr").flatMap(mp(_, lt))
              } yield out
            }
            same <- at(k(Decision.MaximumCongruenceBelow),
              s"(!a:num. a <= 7 ==> (\\a:num. Sum (\\y:num. (1:real) / 8 * COND ($S = y) $Q $Qr * COND (y = a) (1:real) 0) 8) a = " +
                s"(\\a:num. (1:real) / 8 * COND ($S = a) $Q $Qr) a) ==> " +
                s"Maximum (\\a:num. Sum (\\y:num. (1:real) / 8 * COND ($S = y) $Q $Qr * COND (y = a) (1:real) 0) 8) 7 = " +
                s"Maximum (\\a:num. (1:real) / 8 * COND ($S = a) $Q $Qr) 7")
              .flatMap(mp(_, picked))
            // the maximum of 1/8 * P(s | a) is at a = s
            sLe <- atMostSeven(S, shs(0))
            fT <- prop0(s"\\a:num. (1:real) / 8 * COND ($S = a) $Q $Qr")
            sevenT <- nm("7")
            upper <- spec(k(Decision.MaximumUpper), fT, sevenT, ss(0)).flatMap(mp(_, sLe))
            onS <- condOn(s"$S = $S", Q, Qr, Kernel.refl(ss(0)))
            bound <- prop(s"!a:num. a <= 7 ==> (\\a:num. (1:real) / 8 * COND ($S = a) $Q $Qr) a <= (1:real) / 8 * $Q")
            bounded <- every(bound) { (as, _, g) =>
              val A = num(as(0))
              cases(s"$S = $A")(
                yes => condOn(s"$S = $A", Q, Qr, yes).flatMap(e => exact(Seq(e), Seq.empty, g)),
                no => condOff(s"$S = $A", Q, Qr, no).flatMap(e => exact(Seq(e), Seq.empty, g))
              )
            }
            cT <- prop0(s"(1:real) / 8 * $Q")
            least <- spec(k(Decision.MaximumLeast), fT, sevenT, cT).flatMap(mp(_, bounded))
            // the facts are not rewritten by `exact`, only the goal, so the bound at `s` is read first
            settled <- rw(onS, upper)
            out <- exact(Seq(same), Seq(settled, least), goal)
          } yield out
        }
        summed <- at(fact("SUM_CONGRUENCE_BELOW"),
          s"(!s:num. s < 8 ==> Maximum (\\a:num. Sum (\\y:num. (1:real) / 8 * COND (s = y) $Q $Qr * COND (y = a) (1:real) 0) 8) 7 = " +
            s"(\\s:num. (1:real) / 8 * $Q) s) ==> " +
            s"Sum (\\s:num. Maximum (\\a:num. Sum (\\y:num. (1:real) / 8 * COND (s = y) $Q $Qr * COND (y = a) (1:real) 0) 8) 7) 8 = " +
            s"Sum (\\s:num. (1:real) / 8 * $Q) 8")
          .flatMap(mp(_, perSignal))
        constant <- at(fact("SUM_CONSTANT"), s"Sum (\\s:num. (1:real) / 8 * $Q) 8 = real_of_num 8 * ((1:real) / 8 * $Q)")
        numerals <- realNumerals
        wanted <- prop(Empty)
        out <- rewriting(Seq(value, summed, constant), wanted)(g => exact(numerals, Seq.empty, g))
      } yield out
    }

    /* ------------------------------------------------- the pair (s, g) of one signal */
    /** The reader's score for answer `a` at the pair `(s, g)`, once the inner sum is collapsed. */
    def score(S: String, G: String, A: String): String =
      s"(1:real) / 8 * (COND ($S = $A) $Q $Qr * COND ($G = $A) $H $Hr)"

    /** The inner sum of the full experiment at the pair, before collapsing. */
    def inner(S: String, G: String, A: String): String =
      s"Sum (\\y:num. (1:real) / 8 * (COND ($S = y) $Q $Qr * COND ($G = y) $H $Hr) * COND (y = $A) (1:real) 0) 8"

    /** `inner a = score a` for every `a <= 7`. */
    def collapsed(S: String, G: String): R[Kernel.Thm] =
      for {
        each <- prop(s"!a:num. a <= 7 ==> ${inner(S, G, "a")} = ${score(S, G, "a")}")
        out <- every(each) { (as, ahs, _) =>
          val A = num(as(0))
          for {
            lt <- belowEight(A, ahs(0))
            out <- at(k(Decision.SumIndicator), s"$A < 8 ==> ${inner(S, G, A)} = ${score(S, G, A)}").flatMap(mp(_, lt))
          } yield out
        }
      } yield out

    /** Away from `g` the score is strictly below the score at `g`: `49/17920 < 117/17920` and the like. */
    def strictlyBelow(S: String, G: String, A: String, other: Kernel.Thm): R[Kernel.Thm] =
      for {
        goal <- prop(s"${score(S, G, A)} < ${score(S, G, G)}")
        gT <- prop0(G)
        turned <- flip(A, G)
        gOther <- rw(turned, other)
        frameOff <- condOff(s"$G = $A", H, Hr, gOther)
        frameOn <- condOn(s"$G = $G", H, Hr, Kernel.refl(gT))
        out <- cases(s"$S = $A")(
          hit =>
            for {
              signalOn <- condOn(s"$S = $A", Q, Qr, hit)
              // s = a and a <> g, so s <> g
              sg <- prop(s"$S = $G")
              assumed <- LogicError.lift(Kernel.assume(sg))
              back <- Conv.sym(hit)
              ag <- trans(back, assumed)
              absurd <- rules.notElim(other, ag)
              sOther <- rules.notIntro(sg, absurd)
              signalAtG <- condOff(s"$S = $G", Q, Qr, sOther)
              out <- exact(Seq(signalOn, frameOff, frameOn, signalAtG), Seq.empty, goal)
            } yield out,
          miss =>
            for {
              signalOff <- condOff(s"$S = $A", Q, Qr, miss)
              out <- cases(s"$S = $G")(
                same => condOn(s"$S = $G", Q, Qr, same).flatMap(e => exact(Seq(signalOff, frameOff, frameOn, e), Seq.empty, goal)),
                apart => condOff(s"$S = $G", Q, Qr, apart).flatMap(e => exact(Seq(signalOff, frameOff, frameOn, e), Seq.empty, goal))
              )
            } yield out
        )
      } yield out

    /** `Maximum (\a. inner a) 7 = score g`, at a pair with `g <= 7`. */
    def maximum(S: String, G: String, gLe: Kernel.Thm): R[Kernel.Thm] =
      for {
        pointwise <- collapsed(S, G)
        same <- at(k(Decision.MaximumCongruenceBelow),
          s"(!a:num. a <= 7 ==> (\\a:num. ${inner(S, G, "a")}) a = (\\a:num. ${score(S, G, "a")}) a) ==> " +
            s"Maximum (\\a:num. ${inner(S, G, "a")}) 7 = Maximum (\\a:num. ${score(S, G, "a")}) 7")
          .flatMap(mp(_, pointwise))
        fT <- prop0(s"\\a:num. ${score(S, G, "a")}")
        sevenT <- nm("7")
        gV <- numVar(G)
        upper <- spec(k(Decision.MaximumUpper), fT, sevenT, gV).flatMap(mp(_, gLe))
        bound <- prop(s"!a:num. a <= 7 ==> (\\a:num. ${score(S, G, "a")}) a <= ${score(S, G, G)}")
        bounded <- every(bound) { (as, _, g) =>
          val A = num(as(0))
          cases(s"$A = $G")(
            equal => exact(Seq(equal), Seq.empty, g),
            other => strictlyBelow(S, G, A, other).flatMap(lt => exact(Seq.empty, Seq(lt), g))
          )
        }
        cT <- prop0(score(S, G, G))
        least <- spec(k(Decision.MaximumLeast), fT, sevenT, cT).flatMap(mp(_, bounded))
        goal <- prop(s"Maximum (\\a:num. ${inner(S, G, "a")}) 7 = ${score(S, G, G)}")
        out <- exact(Seq(same), Seq(upper, least), goal)
      } yield out

    /**
     * A sum over the sixty-four signals whose term at `8 s + g` is `coefficient * P(s | y = g)`:
     * read in blocks of eight, each block a count of `SUM_COND_COUNT`, and the blocks summed.
     */
    def overPairs(
      at64: String => String,
      cell: (FVar, FVar, Kernel.Thm, Kernel.Thm) => R[Kernel.Thm],
      coefficient: String,
      whole: Seq[Kernel.Thm],
      total: String
    ): R[Kernel.Thm] = {
      val row = s"($coefficient) * ($Q + (real_of_num 8 - 1) * $Qr)"
      for {
        groups <- at(k(Decision.SumGroups),
          s"Sum (\\t:num. ${at64("t")}) (8 * 8) = Sum (\\s:num. Sum (\\g:num. ${at64("(8 * s + g)")}) 8) 8")
        perS <- prop(s"!s:num. s < 8 ==> Sum (\\g:num. ${at64("(8 * s + g)")}) 8 = $row")
        rows <- every(perS) { (ss, shs, rowGoal) =>
          val S = num(ss(0))
          val Cell = s"(\\g:num. ($coefficient) * COND (g = $S) $Q $Qr)"
          for {
            perG <- prop(s"!g:num. g < 8 ==> ${at64(s"(8 * $S + g)")} = $Cell g")
            cells <- every(perG) { (gs, ghs, _) => cell(ss(0), gs(0), shs(0), ghs(0)) }
            spread <- at(fact("SUM_CONGRUENCE_BELOW"),
              s"(!g:num. g < 8 ==> ${at64(s"(8 * $S + g)")} = $Cell g) ==> " +
                s"Sum (\\g:num. ${at64(s"(8 * $S + g)")}) 8 = Sum $Cell 8")
              .flatMap(mp(_, cells))
            scaled <- at(fact("SUM_SCALE"),
              s"Sum (\\g:num. ($coefficient) * COND (g = $S) $Q $Qr) 8 = ($coefficient) * Sum (\\g:num. COND (g = $S) $Q $Qr) 8")
            counted <- at(k(Decision.SumCondCount),
              s"$S < 8 ==> Sum (\\g:num. COND (g = $S) $Q $Qr) 8 = $Q + (real_of_num 8 - 1) * $Qr").flatMap(mp(_, shs(0)))
            out <- exact(Seq(spread, scaled, counted), Seq.empty, rowGoal)
          } yield out
        }
        outer <- at(fact("SUM_CONGRUENCE_BELOW"),
          s"(!s:num. s < 8 ==> Sum (\\g:num. ${at64("(8 * s + g)")}) 8 = (\\s:num. $row) s) ==> " +
            s"Sum (\\s:num. Sum (\\g:num. ${at64("(8 * s + g)")}) 8) 8 = Sum (\\s:num. $row) 8")
          .flatMap(mp(_, rows))
        flat <- at(fact("SUM_CONSTANT"), s"Sum (\\s:num. $row) 8 = real_of_num 8 * ($row)")
        numerals <- realNumerals
        goal <- prop(total)
        // the numerals last: rewriting `real_of_num 8` inside the row first would hide the row from `flat`
        out <- rewriting(whole ++ Seq(groups, outer, flat), goal)(g => exact(numerals, Seq.empty, g))
      } yield out
    }

    /* ---------------------------------------------------------------- V(1), on average */

    def fullAt(t: String): String =
      s"Maximum (\\a:num. Sum (\\y:num. (1:real) / 8 * (COND (NUM_DIV $t 8 = y) $Q $Qr * " +
        s"COND (NUM_MOD $t 8 = y) $H $Hr) * COND (y = a) (1:real) 0) 8) 7"

    val average: R[Kernel.Thm] =
      for {
        whole <- unfold(Decision.ValueName, "8:num", "(8:num) * 8", "7:num", Prior, Full, Utility)
        out <- overPairs(
          fullAt,
          (s, g, _, gBelow) => {
            val (sT, gT) = (num(s), num(g))
            for {
              coords <- coordinates(sT, gT, gBelow)
              moved <- rewritten(coords, fullAt(s"(8 * $sT + $gT)"))
              gLe <- atMostSeven(gT, gBelow)
              top <- maximum(sT, gT, gLe)
              turned <- flip(sT, gT)
              onG <- condOn(s"$gT = $gT", H, Hr, Kernel.refl(g))
              goal <- prop(s"${fullAt(s"(8 * $sT + $gT)")} = (\\g:num. ((1:real) / 8 * $H) * COND (g = $sT) $Q $Qr) $gT")
              out <- exact(Seq(moved, top, onG, turned), Seq.empty, goal)
            } yield out
          },
          s"(1:real) / 8 * $H",
          Seq(whole),
          Average
        )
      } yield out

    /* ---------------------------------------------------------------- V(1), on new tasks */

    def novelAt(t: String): String =
      s"Sum (\\y:num. (1:real) / 8 * (COND (NUM_DIV $t 8 = y) $Q $Qr * ((1:real) / 8)) * " +
        s"COND (y = Argmax (\\a:num. Sum (\\z:num. (1:real) / 8 * (COND (NUM_DIV $t 8 = z) $Q $Qr * " +
        s"COND (NUM_MOD $t 8 = z) $H $Hr) * COND (z = a) (1:real) 0) 8) 7) (1:real) 0) 8"

    val newTask: R[Kernel.Thm] =
      for {
        out <- overPairs(
          novelAt,
          (s, g, _, gBelow) => {
            val (sT, gT) = (num(s), num(g))
            for {
              coords <- coordinates(sT, gT, gBelow)
              moved <- rewritten(coords, novelAt(s"(8 * $sT + $gT)"))
              gLe <- atMostSeven(gT, gBelow)
              pointwise <- collapsed(sT, gT)
              strict <- prop(s"!i:num. i <= 7 ==> ~(i = $gT) ==> " +
                s"(\\a:num. ${inner(sT, gT, "a")}) i < (\\a:num. ${inner(sT, gT, "a")}) $gT")
              below <- every(strict) { (is, ihs, goal) =>
                val I = num(is(0))
                for {
                  atI <- at(pointwise, s"$I <= 7 ==> ${inner(sT, gT, I)} = ${score(sT, gT, I)}").flatMap(mp(_, ihs(0)))
                  atG <- at(pointwise, s"$gT <= 7 ==> ${inner(sT, gT, gT)} = ${score(sT, gT, gT)}").flatMap(mp(_, gLe))
                  lt <- strictlyBelow(sT, gT, I, ihs(1))
                  out <- exact(Seq(atI, atG), Seq(lt), goal)
                } yield out
              }
              fT <- prop0(s"\\a:num. ${inner(sT, gT, "a")}")
              sevenT <- nm("7")
              rule <- spec(k(Decision.ArgmaxUnique), fT, sevenT, g).flatMap(mp(_, gLe, below))
              picked <- at(k(Decision.SumIndicator),
                s"$gT < 8 ==> Sum (\\y:num. (1:real) / 8 * (COND ($sT = y) $Q $Qr * ((1:real) / 8)) * COND (y = $gT) (1:real) 0) 8 = " +
                  s"(1:real) / 8 * (COND ($sT = $gT) $Q $Qr * ((1:real) / 8))").flatMap(mp(_, gBelow))
              turned <- flip(sT, gT)
              goal <- prop(s"${novelAt(s"(8 * $sT + $gT)")} = (\\g:num. ((1:real) / 8 * ((1:real) / 8)) * COND (g = $sT) $Q $Qr) $gT")
              out <- exact(Seq(moved, rule, picked, turned), Seq.empty, goal)
            } yield out
          },
          "(1:real) / 8 * ((1:real) / 8)",
          Seq.empty,
          NewTask
        )
      } yield out

    for {
      e <- empty
      a <- average
      n <- newTask
    } yield Values(e, a, n)
  }
}

/**
 * The steps the essay's cases are written in, over `Decision`'s theory: the arithmetic of the
 * indices below eight, the conditionals settled by an equation, the coordinates of a signal read
 * back by `NUM_DIV` and `NUM_MOD`, and the closing step that keeps rational numerals as numbers.
 */
private[theories] final class EssaySteps(decision: Decision, successor: Successor) {
  type R[A] = Either[LogicError, A]

  val steps: Decision.Proofs = decision.steps
  import steps.*
  import steps.kit.*

  val Q = "((7:real) / 20)"
  val Qr = "((13:real) / 140)"
  val H = "((9:real) / 16)"
  val Hr = "((1:real) / 16)"

  def numeral(text: String): R[Term] = nm(text)

  // |- SUC 7 = 8, from the two spellings
  val sucSevenIsEight: R[Kernel.Thm] =
    for {
      seven <- numeral("7").flatMap(successor.spell)
      eight <- numeral("8").flatMap(successor.spell)
      suc <- term("SUC", Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Natural.TypeName, Nil)))
      lifted <- Conv.apTerm(suc, seven)
      back <- Conv.sym(eight)
      out <- trans(lifted, back)
    } yield out

  def belowEight(x: String, le: Kernel.Thm): R[Kernel.Thm] =
    for {
      eight <- sucSevenIsEight
      step <- at(fact("NUM_LT_SUC"), "(7:num) < SUC 7")
      both <- conj(le, step)
      lt <- at(fact("NUM_LE_LT_TRANS"), s"$x <= 7 /\\ 7 < SUC 7 ==> $x < SUC 7").flatMap(mp(_, both))
      out <- rw(eight, lt)
    } yield out

  def atMostSeven(x: String, lt: Kernel.Thm): R[Kernel.Thm] =
    for {
      eight <- sucSevenIsEight
      back <- Conv.sym(eight)
      moved <- rw(back, lt)
      out <- at(fact("NUM_LE_OF_LT_SUC"), s"$x < SUC 7 ==> $x <= 7").flatMap(mp(_, moved))
    } yield out

  val realNumerals: R[Seq[Kernel.Thm]] =
    for {
      b0 <- fact("NUM_REAL_BIT0")
      b1 <- fact("NUM_REAL_BIT1")
      one <- fact("NUM_REAL_ONE")
    } yield Seq(b0, b1, one)

  /**
   * The goal rewritten with `equations` and closed by `Linarith` from `facts`, with the rational
   * numerals kept as numbers: `linAfter` abstracts every quotient into a fresh atom, which is
   * right for `x / y` and turns `8 * (1 / 8) = 1` into `8 * q = 1`.
   */
  def exact(equations: Seq[Kernel.Thm], facts: Seq[Kernel.Thm], goal: Term): R[Kernel.Thm] =
    rewriting(equations, goal) { g =>
      Term.destEq(g) match {
        // a rewriting that has already met the other side wants no arithmetic at all
        case Some((l, r)) if facts.isEmpty && l == r => Right(Kernel.refl(l))
        // an equation from nothing is a ring identity, and `Ring` derives a ground one in half
        // of what `Linarith` spends on it, measured on E6a's six totals on 2026-10-23
        case Some(_) if facts.isEmpty => driver.identity(g)
        case _ =>
          for {
            implication <- facts.reverse.foldLeft[R[Term]](Right(g))((acc, f) => acc.flatMap(logic.mkImp(f.conclusion, _)))
            general <- linarith.prove(implication)
            out <- facts.foldLeft[R[Kernel.Thm]](Right(general))((acc, f) => acc.flatMap(rules.mp(_, f)))
          } yield out
      }
    }

  /** A COND on an equation, settled by whether the equation holds. */
  def condOn(eq: String, x: String, z: String, holds: Kernel.Thm): R[Kernel.Thm] =
    at(fact("COND_TRUE"), s"$eq ==> COND ($eq) $x $z = $x").flatMap(mp(_, holds))
  def condOff(eq: String, x: String, z: String, fails: Kernel.Thm): R[Kernel.Thm] =
    at(fact("COND_FALSE"), s"~($eq) ==> COND ($eq) $x $z = $z").flatMap(mp(_, fails))

  def num(x: FVar): String = v(x)


  def numVar(text: String): R[FVar] =
    prop0(text).flatMap {
      case x: FVar => Right(x)
      case other => Left(NotOfForm("a variable", other))
    }

  /** `|- (a = b) = (b = a)` at two numbers: either orientation makes the two spellings one. */
  def flip(a: String, b: String): R[Kernel.Thm] =
    for {
      ab <- prop(s"$a = $b")
      ba <- prop(s"$b = $a")
      one <- LogicError.lift(Kernel.assume(ab)).flatMap(Conv.sym)
      two <- LogicError.lift(Kernel.assume(ba)).flatMap(Conv.sym)
    } yield Kernel.deductAntisym(two, one)

  /** `NUM_DIV (8 * s + g) 8 = s` and `NUM_MOD (8 * s + g) 8 = g`, for `g < 8`. */
  def coordinates(S: String, G: String, gBelow: Kernel.Thm): R[Seq[Kernel.Thm]] =
    for {
      t <- nm(s"8 * $S + $G")
      both <- conj(Kernel.refl(t), gBelow)
      unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
        s"8 * $S + $G = 8 * $S + $G /\\ $G < 8 ==> $S = NUM_DIV (8 * $S + $G) 8 /\\ $G = NUM_MOD (8 * $S + $G) 8")
        .flatMap(mp(_, both))
      parts <- split(unique)
      div <- Conv.sym(parts(0))
      mod <- Conv.sym(parts(1))
    } yield Seq(div, mod)

  /** A term rewritten with `equations`, as an equation. */
  def rewritten(equations: Seq[Kernel.Thm], text: String): R[Kernel.Thm] =
    for {
      t <- prop0(text)
      set <- Rewrite.Rule.all(logic, equations.toVector)
      out <- Rewrite.rewrite(set, t)
    } yield out

}
