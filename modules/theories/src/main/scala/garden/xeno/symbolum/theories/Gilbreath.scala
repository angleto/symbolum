package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The table of Gilbreath's conjecture over any first row, and the form the conjecture takes on it.
 *
 * Row `k + 1` holds the absolute differences of neighbours in row `k`. The absolute value of a
 * difference of naturals is written with the truncated subtraction as `NUM_SUB a b + NUM_SUB b a`,
 * one of the two terms being 0, so no absolute value on the naturals is needed. The conjecture is
 * that over the primes every row after the first starts with 1. Nothing here is about the primes:
 * the library has no enumeration of them, so every statement is over any table satisfying the
 * equation, and `GILBREATH_EXISTS` shows there is one for every first row.
 *
 * Not a development: it declares nothing, and `Complex` publishes what it proves beside
 * `RuleThirty`, because the steps it is written in are the ones that link already has.
 * `docs/adr/0065` is the decision; Mycelium note 917b3939, section 5.2, is the account with the
 * measurements.
 *
 * == What the statements say ==
 *
 * `GILBREATH_FRONT`: a row starting with 1 passes a 1 to the next row exactly when its entry at
 * position 1 is 0 or 2, because `|e - 1| = 1` holds exactly there. `GILBREATH_EQUIVALENT` reads that
 * over every row: when the second row starts with 1, the conjecture holds exactly when position 1
 * holds 0 or 2 in every row after the first. `GILBREATH_EVEN`: even entries from position 1 on stay
 * even, which over the primes, where every gap after the first is even, turns "0 or 2" into "at
 * most 2". `GILBREATH_HEAD`: a row starting with 1 and followed by `n + 1` entries in `{0, 2}` passes
 * on a head of `n`. `GILBREATH_WINDOW`: a head of `n` guarantees the 1 for the next `n` rows.
 *
 * == The bound and the ladder ==
 *
 * Two abbreviations, written out in each statement by `bounded` and `runs`: `M k n D` says
 * positions 0 to `n` of row `k` are at most `D`, and `B k n D m` says every run of `m` consecutive
 * entries in `{0, D}` inside them is all zeros, which is Chase's "the longest block in `{0, D}`
 * containing a `D` has length `L`" at `m = L + 1`. `GILBREATH_BELOW`: `M k (SUC n) D` gives
 * `M (SUC k) n D`, and `GILBREATH_BELOW_ROWS` the same over `j` rows; at `D = 1` that is the
 * heredity of a row in `{0, 1}`. `GILBREATH_SHRINK` is Chase's inductive step, `B` at `SUC m` on
 * row `k` giving `B` at `m` on row `k + 1` inside a bounded window, and `GILBREATH_DROP` lowers the
 * bound by one when no entry equals it. `GILBREATH_RUNG` is Chase's Lemma 3.2 ("A random analogue of
 * Gilbreath's conjecture") in this form: `L` rows below a window with no block longer than `L`, the
 * bound is `D - 1`. `GILBREATH_LADDER` chains rungs, the bound lowered by one per rung, down to the
 * single entry the last window leaves, which is at most 1. `docs/adr/0065` has the dated record.
 *
 * == What they do not say ==
 *
 * That the head never runs out, which is the conjecture, and that the primes' table has blocks
 * short enough for the ladder at every depth, which is the same question asked of the bound. The
 * measurements in the note place it in the gaps modulo 4: a large value meeting the head is
 * absorbed when the head keeps producing 2s, and the kernel has nothing on how the gaps between
 * primes are distributed.
 */
private[theories] object Gilbreath {

  type R[A] = Either[LogicError, A]

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Rows: Type = Type.fun(Numbers, Numbers)
  private val Tables: Type = Type.fun(Numbers, Rows)

  private val D = "(d:num->num->num)"

  /** Row `k + 1` from row `k`: the equation that characterises the table. */
  private val Step: String =
    s"(!k:num. !i:num. $D (SUC k) i = NUM_SUB ($D k (i + 1)) ($D k i) + NUM_SUB ($D k i) ($D k (i + 1)))"

  private def over(claim: String): String = s"!d:num->num->num. $Step ==> $claim"

  /** The entry is 0 or 2. */
  private def good(e: String): String = s"($e = 0 \\/ $e = 2)"

  /** Every entry of row `row` from position 0 to position `width` is at most `bound`. */
  private def bounded(row: String, width: String, bound: String): String =
    s"(!i:num. i <= $width ==> $D ($row) i <= $bound)"

  /** The entry is 0 or `bound`. */
  private def member(e: String, bound: String): String = s"($e = 0 \\/ $e = $bound)"

  /**
   * The run of `length` entries of row `row` starting at `start`, when it lies in positions 0 to
   * `width`: if every entry of it is 0 or `bound`, every entry of it is 0. `start` and the other
   * arguments must not mention `t`, which is bound here.
   */
  private def runsFrom(row: String, width: String, bound: String, length: String, start: String): String =
    s"$start + $length <= SUC ($width) ==> (!t:num. t < $length ==> ${member(s"$D ($row) ($start + t)", bound)}) ==> " +
      s"(!t:num. t < $length ==> $D ($row) ($start + t) = 0)"

  /**
   * Every run of `length` consecutive entries in `{0, bound}` inside positions 0 to `width` of row
   * `row` is all zeros. Chase's "the longest block containing `bound` has length `L`" is this at
   * `length = L + 1`. The arguments must not mention `j` or `t`, which are bound here.
   */
  private def runs(row: String, width: String, bound: String, length: String): String =
    s"(!j:num. ${runsFrom(row, width, bound, length, "j")})"

  /**
   * The hypothesis of the ladder: row `r 0` bounded by `D` on positions 0 to `w 0`, and at each
   * stage `s < c` a rung of `l s` rows taking row `r s` with window `w s` to row `r (SUC s)` with a
   * window `l s` shorter, the runs of stage `s` bounded by `l s` at the bound `D - s`; and the bound
   * after `c` stages is at most 1.
   */
  private def staged(c: String, r: String, l: String, w: String, bound: String): String =
    s"${bounded(s"$r 0", s"$w 0", bound)} /\\ (!s:num. s < $c ==> ${stage(r, l, w, bound, "s")}) /\\ NUM_SUB $bound $c <= 1"

  /** Stage `s` of the ladder. */
  private def stage(r: String, l: String, w: String, bound: String, s: String): String =
    s"$r (SUC $s) = $r $s + $l $s /\\ $w $s = $w (SUC $s) + $l $s /\\ ${runs(s"$r $s", s"$w $s", s"NUM_SUB $bound $s", s"SUC ($l $s)")}"

  /** What `Complex` publishes from here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    "GILBREATH_EXISTS" -> s"!r:num->num. ?d:num->num->num. (!i:num. d 0 i = r i) /\\ $Step",
    "GILBREATH_FRONT" -> over(s"!k:num. $D k 0 = 1 ==> ($D (SUC k) 0 = 1 = ${good(s"$D k 1")})"),
    "GILBREATH_EVEN" -> over(
      s"!k:num. (!i:num. 0 < i ==> NUM_MOD ($D k i) 2 = 0) ==> (!i:num. 0 < i ==> NUM_MOD ($D (SUC k) i) 2 = 0)"),
    "GILBREATH_HEAD" -> over(
      s"!k:num. !n:num. $D k 0 = 1 /\\ (!i:num. 0 < i /\\ i <= SUC n ==> ${good(s"$D k i")}) ==> " +
        s"$D (SUC k) 0 = 1 /\\ (!i:num. 0 < i /\\ i <= n ==> ${good(s"$D (SUC k) i")})"),
    "GILBREATH_WINDOW" -> over(
      s"!n:num. !k:num. $D k 0 = 1 /\\ (!i:num. 0 < i /\\ i <= n ==> ${good(s"$D k i")}) ==> (!j:num. j <= n ==> $D (k + j) 0 = 1)"),
    "GILBREATH_EQUIVALENT" -> over(
      s"$D 1 0 = 1 ==> ((!k:num. 0 < k ==> $D k 0 = 1) = (!k:num. 0 < k ==> ${good(s"$D k 1")}))"),
    "GILBREATH_BELOW" -> over(s"!k:num. !n:num. !D:num. ${bounded("k", "SUC n", "D")} ==> ${bounded("SUC k", "n", "D")}"),
    "GILBREATH_BELOW_ROWS" -> over(s"!j:num. !k:num. !n:num. !D:num. ${bounded("k", "n + j", "D")} ==> ${bounded("k + j", "n", "D")}"),
    "GILBREATH_SHRINK" -> over(
      s"!k:num. !n:num. !D:num. !m:num. ${bounded("k", "SUC n", "D")} /\\ ${runs("k", "SUC n", "D", "SUC m")} ==> ${runs("SUC k", "n", "D", "m")}"),
    "GILBREATH_DROP" -> over(s"!k:num. !n:num. !D:num. ${bounded("k", "n", "D")} /\\ ${runs("k", "n", "D", "1")} ==> ${bounded("k", "n", "NUM_SUB D 1")}"),
    "GILBREATH_RUNG" -> over(
      s"!L:num. !k:num. !n:num. !D:num. ${bounded("k", "n + L", "D")} /\\ ${runs("k", "n + L", "D", "SUC L")} ==> ${bounded("k + L", "n", "NUM_SUB D 1")}"),
    "GILBREATH_LADDER" -> over(
      s"!c:num. !r:num->num. !l:num->num. !w:num->num. !D:num. ${staged("c", "r", "l", "w", "D")} ==> $D (r c + w c) 0 <= 1")
  )

  private val Order: Vector[(String, Proofs => R[Kernel.Thm])] = Vector(
    "GILBREATH_EXISTS" -> (_.exists),
    "GILBREATH_FRONT" -> (_.front),
    "GILBREATH_EVEN" -> (_.even),
    "GILBREATH_HEAD" -> (_.head),
    "GILBREATH_WINDOW" -> (_.window),
    "GILBREATH_EQUIVALENT" -> (_.equivalent),
    "GILBREATH_BELOW" -> (_.below),
    "GILBREATH_BELOW_ROWS" -> (_.belowRows),
    "GILBREATH_SHRINK" -> (_.shrink),
    "GILBREATH_DROP" -> (_.drop),
    "GILBREATH_RUNG" -> (_.rung),
    "GILBREATH_LADDER" -> (_.ladder)
  )

  /** The facts [[Statements]] names, derived with `kit`. */
  def prove(kit: ComplexKit, semiring: Semiring, recursion: Kernel.Thm, held: Map[String, Kernel.Thm]): R[Map[String, Kernel.Thm]] = {
    val steps = new NumberSteps(kit, semiring)
    ComplexKit.derive(Order, Statements, held)(known => new Proofs(kit, steps, recursion, known))
  }

  private final class Proofs(val kit: ComplexKit, val steps: NumberSteps, recursion: Kernel.Thm, known: Map[String, Kernel.Thm]) {
    import kit.*
    import steps.*

    private val dv = Term.variable("d", Tables)
    private val kv = Term.variable("k", Numbers)
    private val nv = Term.variable("n", Numbers)
    private val iv = Term.variable("i", Numbers)
    private val jv = Term.variable("j", Numbers)
    private val rv = Term.variable("r", Rows)
    private val lv = Term.variable("l", Rows)
    private val wv = Term.variable("w", Rows)
    private val boundv = Term.variable("D", Numbers)
    private val mv = Term.variable("m", Numbers)
    private val tv = Term.variable("t", Numbers)
    private val pv = Term.variable("p", Numbers)
    private val sv = Term.variable("s", Numbers)
    private val cv = Term.variable("c", Numbers)
    private val lengthv = Term.variable("L", Numbers)

    /** The equation assumed, and what `body` proves from it discharged. */
    private def table(body: Kernel.Thm => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        hT <- prop(Step)
        h <- LogicError.lift(Kernel.assume(hT))
        proved <- body(h)
        out <- rules.disch(hT, proved).flatMap(gen(_, dv))
      } yield out

    /** A fact published earlier from here, at the equation assumed. */
    private def under(name: String): R[Kernel.Thm] =
      for {
        h <- assume(Step)
        out <- spec(known(name), dv).flatMap(mp(_, h))
      } yield out

    /** The equation at the row and position written, as text. */
    private def stepAt(step: Kernel.Thm, row: String, pos: String): R[Kernel.Thm] =
      at(step, s"$D (SUC $row) $pos = NUM_SUB ($D $row ($pos + 1)) ($D $row $pos) + NUM_SUB ($D $row $pos) ($D $row ($pos + 1))")

    /** `hyp ==> claim`, the claim settled by `numLin` from `facts` and the hypothesis. */
    private def implication(facts: Seq[Kernel.Thm], hyp: String, claim: String): R[Kernel.Thm] =
      for {
        held <- assumed(hyp)
        proved <- numLinText(facts :+ held._2, claim)
        out <- rules.disch(held._1, proved)
      } yield out

    /** What `lo <= hi` gives about the two subtractions: `NUM_SUB lo hi = 0` and `NUM_SUB hi lo + lo = hi`. */
    private def ordered(le: Kernel.Thm, lo: String, hi: String): R[Vector[Kernel.Thm]] =
      for {
        zero <- at(fact("NUM_SUB_EQ_ZERO"), s"$lo <= $hi ==> NUM_SUB $lo $hi = 0").flatMap(mp(_, le))
        add <- at(fact("NUM_SUB_ADD"), s"$lo <= $hi ==> NUM_SUB $hi $lo + $lo = $hi").flatMap(mp(_, le))
      } yield Vector(le, zero, add)

    /** One conclusion from both orders of `a` and `b`: `close(lo, hi, le)` proves it under `lo <= hi`. */
    private def eitherOrder(a: String, b: String)(close: (String, String, Kernel.Thm) => R[Kernel.Thm]): R[Kernel.Thm] =
      for {
        total <- at(fact("NUM_LE_TOTAL"), s"$a <= $b \\/ $b <= $a")
        one <- assume(s"$a <= $b").flatMap(close(a, b, _))
        other <- assume(s"$b <= $a").flatMap(close(b, a, _))
        out <- rules.disjElim(total, one, other)
      } yield out

    /** A disjunction of two equations between numerals, by whichever side `numLin` settles. */
    private def eitherSide(goal: Term): R[Kernel.Thm] =
      for {
        sides <- logic.destDisj(goal).toRight(NotOfForm("a disjunction", goal))
        out <- numLin(Seq.empty, sides._1).flatMap(rules.disjIntro1(sides._2, _))
          .orElse(numLin(Seq.empty, sides._2).flatMap(rules.disjIntro2(sides._1, _)))
      } yield out

    /* ------------------------------------------------------------ the table */

    /** A table exists for every first row, by the recursion theorem at the type of a row. */
    def exists: R[Kernel.Thm] =
      for {
        recursive <- Right(Kernel.instType(Map("a" -> Rows), recursion))
        stepper <- term("\\f:num->num. \\k:num. \\i:num. NUM_SUB (f (i + 1)) (f i) + NUM_SUB (f i) (f (i + 1))", Type.fun(Rows, Type.fun(Numbers, Rows)))
        made <- spec(recursive, rv, stepper)
        out <- choose(made, "fn") { (fn, clauses) =>
          for {
            parts <- split(clauses)
            atZero <- Conv.apThm(parts(0), iv).flatMap(beta).flatMap(gen(_, iv))
            atSuc <- spec(parts(1), kv).flatMap(Conv.apThm(_, iv)).flatMap(beta).flatMap(gen(_, kv, iv))
            both <- conj(atZero, atSuc)
            predicate <- predicateOf(s"?d:num->num->num. (!i:num. d 0 i = (r:num->num) i) /\\ $Step")
            out <- introduce(predicate, fn, both)
          } yield out
        }
        general <- gen(out, rv)
      } yield general

    /**
     * A row that starts with 1 passes a 1 on exactly when position 1 holds 0 or 2. The next row
     * starts with `|e - 1|`, and in each order of `e` and 1 that is 1 at exactly one of the two values.
     */
    def front: R[Kernel.Thm] =
      table { step =>
        val K = v("k"); val E = s"$D $K 1"
        val S = s"NUM_SUB ($E) 1 + NUM_SUB 1 ($E)"
        for {
          held <- assumed(s"$D $K 0 = 1")
          (hT, h) = held
          opened <- stepAt(step, K, "0")
          plus <- num("(0:num) + 1 = 1")
          value <- rw(plus, opened).flatMap(rw(h, _))
          goal <- prop(s"$D (SUC $K) 0 = 1 = ${good(E)}")
          proved <- rewriting(Seq(value), goal) { g =>
            eitherOrder(s"($E)", "1") { (lo, hi, le) =>
              // below 1 the entry is 0 and the next row's 1 is 1 - e; above it, the entry is 2 and it is e - 1
              val (hits, misses) = if (hi == "1") (s"$E = 0", s"$E = 2") else (s"$E = 2", s"$E = 0")
              for {
                facts <- ordered(le, lo, hi)
                forward <- implication(facts, s"$S = 1", hits)
                backward <- implication(facts, hits, s"$S = 1")
                vacuous <- implication(facts, misses, s"$S = 1")
                out <- tauto(Seq(forward, backward, vacuous), g)
              } yield out
            }
          }
          out <- rules.disch(hT, proved).flatMap(gen(_, kv))
        } yield out
      }

    /**
     * Even entries from position 1 on stay even. Writing each as twice its half, the absolute
     * difference of two of them is twice the absolute difference of the halves.
     */
    def even: R[Kernel.Thm] =
      table { step =>
        val K = v("k"); val I = v("i")
        val A = s"$D $K ($I + 1)"; val B = s"$D $K $I"
        val Ha = s"NUM_DIV ($A) 2"; val Hb = s"NUM_DIV ($B) 2"
        val V = s"NUM_SUB ($A) ($B) + NUM_SUB ($B) ($A)"
        val T = s"NUM_SUB ($Ha) ($Hb) + NUM_SUB ($Hb) ($Ha)"
        for {
          held <- assumed(s"!i:num. 0 < i ==> NUM_MOD ($D $K i) 2 = 0")
          (hT, h) = held
          pos <- assumed(s"0 < $I")
          evenA <- numLinText(Seq.empty, s"0 < $I + 1").flatMap(p => at(h, s"0 < $I + 1 ==> NUM_MOD ($A) 2 = 0").flatMap(mp(_, p)))
          evenB <- at(h, s"0 < $I ==> NUM_MOD ($B) 2 = 0").flatMap(mp(_, pos._2))
          halfA <- at(fact("NUM_DIV_MOD"), s"2 * $Ha + NUM_MOD ($A) 2 = $A").flatMap(rw(evenA, _))
          halfB <- at(fact("NUM_DIV_MOD"), s"2 * $Hb + NUM_MOD ($B) 2 = $B").flatMap(rw(evenB, _))
          twice <- eitherOrder(s"($Ha)", s"($Hb)") { (lo, hi, le) =>
            val (low, high) = if (lo == s"($Ha)") (s"($A)", s"($B)") else (s"($B)", s"($A)")
            for {
              halves <- ordered(le, lo, hi)
              whole <- numLinText(Seq(halfA, halfB, le), s"$low <= $high")
              wholes <- ordered(whole, low, high)
              out <- numLinText(Seq(halfA, halfB) ++ halves ++ wholes, s"$V = 2 * ($T) + 0")
            } yield out
          }
          below <- two
          unique <- at(fact("NUM_DIV_MOD_UNIQUE"), s"$V = 2 * ($T) + 0 /\\ (0:num) < 2 ==> $T = NUM_DIV ($V) 2 /\\ 0 = NUM_MOD ($V) 2")
          modulus <- conj(twice, below).flatMap(mp(unique, _)).flatMap(rules.conjElim2).flatMap(Conv.sym)
          opened <- stepAt(step, K, I)
          goal <- prop(s"NUM_MOD ($D (SUC $K) $I) 2 = 0")
          proved <- rewriting(Seq(opened), goal)(landsOn(modulus))
          general <- rules.disch(pos._1, proved).flatMap(gen(_, iv))
          out <- rules.disch(hT, general).flatMap(gen(_, kv))
        } yield out
      }

    /**
     * A head of `n + 1` entries in `{0, 2}` passes on the 1 and a head of `n`: the 1 by
     * `GILBREATH_FRONT`, and each entry of the new head from the four pairs of values above it.
     */
    def head: R[Kernel.Thm] =
      table { step =>
        val K = v("k"); val N = v("n"); val I = v("i")
        for {
          frontHere <- under("GILBREATH_FRONT")
          held <- assumed(s"$D $K 0 = 1 /\\ (!i:num. 0 < i /\\ i <= SUC $N ==> ${good(s"$D $K i")})")
          (hT, h) = held
          parts <- split(h)
          wide = parts(1)
          atOne <- numLinText(Seq.empty, s"(0:num) < 1 /\\ 1 <= SUC $N")
            .flatMap(c => at(wide, s"(0:num) < 1 /\\ 1 <= SUC $N ==> ${good(s"$D $K 1")}").flatMap(mp(_, c)))
          iff <- at(frontHere, s"$D $K 0 = 1 ==> ($D (SUC $K) 0 = 1 = ${good(s"$D $K 1")})").flatMap(mp(_, parts(0)))
          passed <- Conv.sym(iff).flatMap(s => LogicError.lift(Kernel.eqMp(s, atOne)))
          numerals <- Seq(
            at(fact("NUM_ZERO_SUB"), "NUM_SUB 0 0 = 0"),
            at(fact("NUM_ZERO_SUB"), "NUM_SUB 0 2 = 0"),
            at(fact("NUM_SUB_ZERO"), "NUM_SUB 2 0 = 2"),
            at(fact("NUM_SUB_REFL"), "NUM_SUB 2 2 = 0")
          ).foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, e) => for { done <- acc; f <- e } yield done :+ f)
          range <- assumed(s"0 < $I /\\ $I <= $N")
          here <- numLinText(Seq(range._2), s"0 < $I /\\ $I <= SUC $N")
            .flatMap(c => at(wide, s"0 < $I /\\ $I <= SUC $N ==> ${good(s"$D $K $I")}").flatMap(mp(_, c)))
          next <- numLinText(Seq(range._2), s"0 < $I + 1 /\\ $I + 1 <= SUC $N")
            .flatMap(c => at(wide, s"0 < $I + 1 /\\ $I + 1 <= SUC $N ==> ${good(s"$D $K ($I + 1)")}").flatMap(mp(_, c)))
          opened <- stepAt(step, K, I)
          goal <- prop(good(s"$D (SUC $K) $I"))
          byValues = (right: String, left: String) =>
            for {
              r <- assume(s"$D $K ($I + 1) = $right")
              l <- assume(s"$D $K $I = $left")
              value <- rw(r, opened).flatMap(rw(l, _)).flatMap(o => numerals.foldLeft[R[Kernel.Thm]](Right(o))((acc, e) => acc.flatMap(rw(e, _))))
              out <- rewriting(Seq(value), goal)(eitherSide)
            } yield out
          whenZero <- for { a <- byValues("0", "0"); b <- byValues("0", "2"); out <- rules.disjElim(here, a, b) } yield out
          whenTwo <- for { a <- byValues("2", "0"); b <- byValues("2", "2"); out <- rules.disjElim(here, a, b) } yield out
          entry <- rules.disjElim(next, whenZero, whenTwo)
          rest <- rules.disch(range._1, entry).flatMap(gen(_, iv))
          both <- conj(passed, rest)
          out <- rules.disch(hT, both).flatMap(gen(_, kv, nv))
        } yield out
      }

    /** A head of `n` guarantees the 1 for the next `n` rows: by induction on `n`, `GILBREATH_HEAD` shortening the head by one per row. */
    def window: R[Kernel.Thm] =
      table { _ =>
        def hypothesis(row: String, length: String) =
          s"$D $row 0 = 1 /\\ (!i:num. 0 < i /\\ i <= $length ==> ${good(s"$D $row i")})"
        def claim(length: String) =
          s"!k:num. ${hypothesis("k", length)} ==> (!j:num. j <= $length ==> $D (k + j) 0 = 1)"
        val K = v("k"); val J = v("j")
        // `d (k + j) 0 = 1` at `j = 0`, from the row's own 1
        def first(start: Kernel.Thm, zero: Kernel.Thm): R[Kernel.Thm] =
          for {
            plus <- num(s"$K + 0 = $K")
            goal <- prop(s"$D ($K + $J) 0 = 1")
            out <- rewriting(Seq(zero, plus), goal)(landsOn(start))
          } yield out
        for {
          headHere <- under("GILBREATH_HEAD")
          body <- prop(claim("(n:num)"))
          proved <- induct(nv, body)(
            _ =>
              for {
                held <- assumed(hypothesis(K, "0"))
                start <- split(held._2).map(_(0))
                bound <- assumed(s"$J <= 0")
                zero <- numLinText(Seq(bound._2), s"$J = 0")
                reached <- first(start, zero)
                out <- rules.disch(bound._1, reached).flatMap(gen(_, jv)).flatMap(rules.disch(held._1, _)).flatMap(gen(_, kv))
              } yield out,
            (kk, hyp, _) => {
              val N = v(kk.name)
              for {
                held <- assumed(hypothesis(K, s"SUC $N"))
                (hT, h) = held
                start <- split(h).map(_(0))
                passed <- at(headHere, s"${hypothesis(K, s"SUC $N")} ==> $D (SUC $K) 0 = 1 /\\ (!i:num. 0 < i /\\ i <= $N ==> ${good(s"$D (SUC $K) i")})")
                  .flatMap(mp(_, h))
                later <- at(hyp, s"${hypothesis(s"(SUC $K)", N)} ==> (!j:num. j <= $N ==> $D (SUC $K + j) 0 = 1)").flatMap(mp(_, passed))
                bound <- assumed(s"$J <= SUC $N")
                reached <- cases(s"$J = 0")(
                  zero => first(start, zero),
                  nonzero =>
                    for {
                      positive <- positiveOf(nonzero, J)
                      one <- numLinText(Seq(positive), s"1 <= $J")
                      back <- at(fact("NUM_SUB_ADD"), s"1 <= $J ==> NUM_SUB $J 1 + 1 = $J").flatMap(mp(_, one))
                      within <- numLinText(Seq(back, bound._2), s"NUM_SUB $J 1 <= $N")
                      atRow <- at(later, s"NUM_SUB $J 1 <= $N ==> $D (SUC $K + NUM_SUB $J 1) 0 = 1").flatMap(mp(_, within))
                      shift <- numLinText(Seq(back), s"SUC $K + NUM_SUB $J 1 = $K + $J")
                      out <- rw(shift, atRow)
                    } yield out
                )
                out <- rules.disch(bound._1, reached).flatMap(gen(_, jv)).flatMap(rules.disch(hT, _)).flatMap(gen(_, kv))
              } yield out
            }
          )
        } yield proved
      }

    /**
     * When the second row starts with 1, the conjecture holds exactly when position 1 holds 0 or 2
     * in every row after the first: one direction is `GILBREATH_FRONT` read forwards at each row, the
     * other is induction on the row, reading it backwards.
     */
    def equivalent: R[Kernel.Thm] =
      table { _ =>
        val K = v("k")
        def iffAt(frontHere: Kernel.Thm, row: String, start: Kernel.Thm): R[Kernel.Thm] =
          at(frontHere, s"$D $row 0 = 1 ==> ($D (SUC $row) 0 = 1 = ${good(s"$D $row 1")})").flatMap(mp(_, start))
        for {
          frontHere <- under("GILBREATH_FRONT")
          held <- assumed(s"$D 1 0 = 1")
          (hT, second) = held
          everyOne <- prop(s"!k:num. 0 < k ==> $D k 0 = 1")
          everyGood <- prop(s"!k:num. 0 < k ==> ${good(s"$D k 1")}")
          forward <- for {
            all <- LogicError.lift(Kernel.assume(everyOne))
            pos <- assumed(s"0 < $K")
            here <- at(all, s"0 < $K ==> $D $K 0 = 1").flatMap(mp(_, pos._2))
            next <- numLinText(Seq(pos._2), s"0 < SUC $K").flatMap(p => at(all, s"0 < SUC $K ==> $D (SUC $K) 0 = 1").flatMap(mp(_, p)))
            iff <- iffAt(frontHere, K, here)
            reached <- LogicError.lift(Kernel.eqMp(iff, next))
            out <- rules.disch(pos._1, reached).flatMap(gen(_, kv))
          } yield out
          backward <- for {
            all <- LogicError.lift(Kernel.assume(everyGood))
            body <- prop(s"0 < (k:num) ==> $D k 0 = 1")
            out <- induct(kv, body)(
              _ =>
                for {
                  pos <- assumed("(0:num) < 0")
                  irreflexive <- at(fact("NUM_LT_IRREFL"), "~((0:num) < 0)")
                  absurd <- rules.notElim(irreflexive, pos._2)
                  reached <- prop(s"$D 0 0 = 1").flatMap(rules.falsityElim(_, absurd))
                  out <- rules.disch(pos._1, reached)
                } yield out,
              (kk, ih, _) => {
                val M = v(kk.name)
                for {
                  pos <- assumed(s"0 < SUC $M")
                  reached <- cases(s"$M = 0")(
                    zero =>
                      for {
                        one <- fact("NUM_ONE_SUC").flatMap(Conv.sym)
                        goal <- prop(s"$D (SUC $M) 0 = 1")
                        out <- rewriting(Seq(zero, one), goal)(landsOn(second))
                      } yield out,
                    nonzero =>
                      for {
                        positive <- positiveOf(nonzero, M)
                        here <- mp(ih, positive)
                        entry <- at(all, s"0 < $M ==> ${good(s"$D $M 1")}").flatMap(mp(_, positive))
                        iff <- iffAt(frontHere, M, here)
                        out <- Conv.sym(iff).flatMap(s => LogicError.lift(Kernel.eqMp(s, entry)))
                      } yield out
                  )
                  out <- rules.disch(pos._1, reached)
                } yield out
              }
            )
          } yield out
          both = Kernel.deductAntisym(backward, forward)
          out <- rules.disch(hT, both)
        } yield out
      }

    /* ------------------------------------------------------------ the bound and the ladder */

    /** `induct` with the step's variable named `variable` with a `0` after it: see `ComplexKit.induct` for why. */
    private def inductOn(variable: FVar, body: Term)(
      base: Term => R[Kernel.Thm],
      stepCase: (FVar, Kernel.Thm, Term) => R[Kernel.Thm]
    ): R[Kernel.Thm] =
      induct(variable, body, Some(Term.variable(s"${variable.name}0", Numbers)))(base, stepCase)

    /** `hyp1 ==> hyp2 ==> claim`, the claim settled by `numLin` from `facts` and both hypotheses. */
    private def implication2(facts: Seq[Kernel.Thm], hyp1: String, hyp2: String, claim: String): R[Kernel.Thm] =
      for {
        first <- assumed(hyp1)
        second <- assumed(hyp2)
        proved <- numLinText(facts ++ Seq(first._2, second._2), claim)
        out <- rules.disch(second._1, proved).flatMap(rules.disch(first._1, _))
      } yield out

    /**
     * What the difference at position `p` of row `SUC k` says about the two entries above it, when
     * both are at most `bound`: a difference equal to `bound` puts both in `{0, bound}`; a difference
     * in `{0, bound}` makes the two entries agree on membership of `{0, bound}`; two zeros above give
     * a zero below. The three are what `GILBREATH_SHRINK` walks a run with.
     */
    private def pairClaim(row: String, p: String, bound: String): String = {
      val x = s"$D $row $p"; val y = s"$D $row ($p + 1)"; val below = s"$D (SUC $row) $p"
      s"($below = $bound ==> ${member(x, bound)} /\\ ${member(y, bound)}) /\\ " +
        s"(${member(below, bound)} ==> (${member(x, bound)} = ${member(y, bound)})) /\\ " +
        s"($x = 0 /\\ $y = 0 ==> $below = 0)"
    }

    /** `!p. d k p <= D ==> d k (p + 1) <= D ==> pairClaim`, at the `k` and `D` free, from the equation. */
    private def pair(step: Kernel.Thm): R[Kernel.Thm] = {
      val K = v("k"); val P = v("p"); val Bd = v("D")
      val X = s"$D $K $P"; val Y = s"$D $K ($P + 1)"; val S = s"$D (SUC $K) $P"
      for {
        bx <- assumed(s"$X <= $Bd")
        by <- assumed(s"$Y <= $Bd")
        opened <- stepAt(step, K, P)
        claim <- prop(pairClaim(K, P, Bd))
        proved <- eitherOrder(s"($X)", s"($Y)") { (lo, hi, le) =>
          // in each order the difference is `hi - lo`, so it reaches the bound only from 0 to the bound
          for {
            ordering <- ordered(le, lo, hi)
            facts = ordering ++ Seq(bx._2, by._2, opened)
            low <- implication(facts, s"$S = $Bd", s"$lo = 0")
            high <- implication(facts, s"$S = $Bd", s"$hi = $Bd")
            same <- Seq((X, Y), (Y, X)).flatMap { case (a, b) => Seq("0", Bd).map(c => (a, b, c)) }
              .foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty)) { case (acc, (a, b, c)) =>
                for { done <- acc; f <- implication2(facts, s"$S = 0", s"$a = $c", s"$b = $c") } yield done :+ f
              }
            flat <- implication2(facts, s"$X = 0", s"$Y = 0", s"$S = 0")
            out <- tauto(Seq(low, high) ++ same :+ flat, claim)
          } yield out
        }
        out <- rules.disch(by._1, proved).flatMap(rules.disch(bx._1, _)).flatMap(gen(_, pv))
      } yield out
    }

    /** Entries at most `D` on positions 0 to `n + 1` give entries at most `D` on 0 to `n` one row down: `|x - y| <= D`. */
    def below: R[Kernel.Thm] =
      table { step =>
        val K = v("k"); val N = v("n"); val I = v("i"); val Bd = v("D")
        val X = s"$D $K $I"; val Y = s"$D $K ($I + 1)"
        for {
          held <- assumed(bounded(K, s"SUC $N", Bd))
          (hT, h) = held
          range <- assumed(s"$I <= $N")
          bx <- numLinText(Seq(range._2), s"$I <= SUC $N").flatMap(c => at(h, s"$I <= SUC $N ==> $X <= $Bd").flatMap(mp(_, c)))
          by <- numLinText(Seq(range._2), s"$I + 1 <= SUC $N").flatMap(c => at(h, s"$I + 1 <= SUC $N ==> $Y <= $Bd").flatMap(mp(_, c)))
          opened <- stepAt(step, K, I)
          goal <- prop(s"$D (SUC $K) $I <= $Bd")
          proved <- rewriting(Seq(opened), goal) { g =>
            eitherOrder(s"($X)", s"($Y)") { (lo, hi, le) => ordered(le, lo, hi).flatMap(f => numLin(f ++ Seq(bx, by), g)) }
          }
          out <- rules.disch(range._1, proved).flatMap(gen(_, iv)).flatMap(rules.disch(hT, _)).flatMap(gen(_, kv, nv, boundv))
        } yield out
      }

    /** `GILBREATH_BELOW` over `j` rows, the window one shorter per row: by induction on `j`. */
    def belowRows: R[Kernel.Thm] =
      table { _ =>
        val K = v("k"); val N = v("n"); val Bd = v("D")
        def claim(j: String) = s"!k:num. !n:num. !D:num. ${bounded("k", s"n + $j", "D")} ==> ${bounded(s"k + $j", "n", "D")}"
        for {
          belowHere <- under("GILBREATH_BELOW")
          body <- prop(claim("(j:num)"))
          proved <- inductOn(jv, body)(
            _ =>
              for {
                held <- assumed(bounded(K, s"$N + 0", Bd))
                widths <- num(s"$N + 0 = $N")
                rows <- num(s"$K + 0 = $K")
                here <- rw(widths, held._2)
                goal <- prop(bounded(s"$K + 0", N, Bd))
                reached <- rewriting(Seq(rows), goal)(landsOn(here))
                out <- rules.disch(held._1, reached).flatMap(gen(_, kv, nv, boundv))
              } yield out,
            (jj, hyp, _) => {
              val J = v(jj.name)
              for {
                held <- assumed(bounded(K, s"$N + SUC $J", Bd))
                widths <- numLinText(Seq.empty, s"$N + SUC $J = SUC ($N + $J)")
                wide <- rw(widths, held._2)
                next <- at(belowHere, s"${bounded(K, s"SUC ($N + $J)", Bd)} ==> ${bounded(s"SUC $K", s"$N + $J", Bd)}").flatMap(mp(_, wide))
                later <- at(hyp, s"${bounded(s"SUC $K", s"$N + $J", Bd)} ==> ${bounded(s"SUC $K + $J", N, Bd)}").flatMap(mp(_, next))
                rows <- numLinText(Seq.empty, s"SUC $K + $J = $K + SUC $J")
                reached <- rw(rows, later)
                out <- rules.disch(held._1, reached).flatMap(gen(_, kv, nv, boundv))
              } yield out
            }
          )
        } yield proved
      }

    /**
     * Chase's inductive step. Take a run `j .. j + m - 1` of row `k + 1` in `{0, D}`; row `k` at
     * `j .. j + m` lies in the window, and by `pair` every one of those entries has the membership of
     * `{0, D}` that entry `j` has, by induction along the run. If entry `j` is in, the run of `m + 1`
     * above is all zeros by the hypothesis on row `k`, and so is every difference. If it is not, no
     * difference can equal `D`, which would put both its ends in, so each is 0.
     */
    def shrink: R[Kernel.Thm] =
      table { step =>
        val K = v("k"); val N = v("n"); val Bd = v("D"); val Mm = v("m"); val J = v("j"); val T = v("t")
        def x(pos: String) = s"$D $K ($pos)"
        def in(e: String) = member(e, Bd)
        for {
          pairHere <- pair(step)
          held <- assumed(s"${bounded(K, s"SUC $N", Bd)} /\\ ${runs(K, s"SUC $N", Bd, s"SUC $Mm")}")
          (hT, h) = held
          parts <- split(h)
          (wide, blocks) = (parts(0), parts(1))
          range <- assumed(s"$J + $Mm <= SUC $N")
          run <- assumed(s"(!t:num. t < $Mm ==> ${in(s"$D (SUC $K) ($J + t)")})")
          // `pair` at position `j + u` of the run, for `u < m`: both entries above are in the window
          entries = (u: String, lt: Kernel.Thm) =>
            for {
              here <- numLinText(Seq(range._2, lt), s"$J + $u <= SUC $N")
              b0 <- at(wide, s"$J + $u <= SUC $N ==> ${x(s"$J + $u")} <= $Bd").flatMap(mp(_, here))
              next <- numLinText(Seq(range._2, lt), s"($J + $u) + 1 <= SUC $N")
              b1 <- at(wide, s"($J + $u) + 1 <= SUC $N ==> ${x(s"($J + $u) + 1")} <= $Bd").flatMap(mp(_, next))
              out <- at(pairHere, s"${x(s"$J + $u")} <= $Bd ==> ${x(s"($J + $u) + 1")} <= $Bd ==> ${pairClaim(K, s"($J + $u)", Bd)}")
                .flatMap(mp(_, b0, b1))
              claims <- split(out)
            } yield claims
          sameBody <- prop(s"$T <= $Mm ==> (${in(x(s"$J + $T"))} = ${in(x(J))})")
          same <- inductOn(tv, sameBody)(
            base =>
              for {
                zero <- num(s"$J + 0 = $J")
                out <- rewriting(Seq(zero), base)(tauto(Seq.empty, _))
              } yield out,
            (tt, ih, _) => {
              val U = v(tt.name)
              for {
                bound <- assumed(s"SUC $U <= $Mm")
                within <- numLinText(Seq(bound._2), s"$U <= $Mm")
                lt <- numLinText(Seq(bound._2), s"$U < $Mm")
                prior <- mp(ih, within)
                claims <- entries(U, lt)
                difference <- at(run._2, s"$U < $Mm ==> ${in(s"$D (SUC $K) ($J + $U)")}").flatMap(mp(_, lt))
                shift <- numLinText(Seq.empty, s"$J + SUC $U = ($J + $U) + 1")
                target <- prop(s"${in(x(s"$J + SUC $U"))} = ${in(x(J))}")
                reached <- rewriting(Seq(shift), target)(tauto(Seq(prior, difference, claims(1)), _))
                out <- rules.disch(bound._1, reached)
              } yield out
            }
          )
          // when entry `j` is in, the hypothesis on row `k` makes all `m + 1` entries above zero
          zeros <- for {
            yes <- assumed(in(x(J)))
            lt <- assumed(s"$T < SUC $Mm")
            within <- numLinText(Seq(lt._2), s"$T <= $Mm")
            agree <- at(same, s"$T <= $Mm ==> (${in(x(s"$J + $T"))} = ${in(x(J))})").flatMap(mp(_, within))
            inside <- Conv.sym(agree).flatMap(e => LogicError.lift(Kernel.eqMp(e, yes._2)))
            every <- rules.disch(lt._1, inside).flatMap(gen(_, tv))
            block <- numLinText(Seq(range._2), s"$J + SUC $Mm <= SUC (SUC $N)")
            out <- at(blocks, runsFrom(K, s"SUC $N", Bd, s"SUC $Mm", J)).flatMap(mp(_, block, every))
            imp <- rules.disch(yes._1, out)
          } yield imp
          lt <- assumed(s"$T < $Mm")
          claims <- entries(T, lt._2)
          difference <- at(run._2, s"$T < $Mm ==> ${in(s"$D (SUC $K) ($J + $T)")}").flatMap(mp(_, lt._2))
          within <- numLinText(Seq(lt._2), s"$T <= $Mm")
          agree <- at(same, s"$T <= $Mm ==> (${in(x(s"$J + $T"))} = ${in(x(J))})").flatMap(mp(_, within))
          goal <- prop(s"$D (SUC $K) ($J + $T) = 0")
          reached <- cases(in(x(J)))(
            yes =>
              for {
                all <- mp(zeros, yes)
                first <- numLinText(Seq(lt._2), s"$T < SUC $Mm")
                  .flatMap(c => at(all, s"$T < SUC $Mm ==> ${x(s"$J + $T")} = 0").flatMap(mp(_, c)))
                shift <- numLinText(Seq.empty, s"$J + SUC $T = ($J + $T) + 1")
                second <- numLinText(Seq(lt._2), s"SUC $T < SUC $Mm")
                  .flatMap(c => at(all, s"SUC $T < SUC $Mm ==> ${x(s"$J + SUC $T")} = 0").flatMap(mp(_, c)))
                  .flatMap(rw(shift, _))
                out <- conj(first, second).flatMap(mp(claims(2), _))
              } yield out,
            no => tauto(Seq(no, agree, difference, claims(0)), goal)
          )
          out <- rules.disch(lt._1, reached).flatMap(gen(_, tv))
            .flatMap(rules.disch(run._1, _)).flatMap(rules.disch(range._1, _)).flatMap(gen(_, jv))
            .flatMap(rules.disch(hT, _)).flatMap(gen(_, kv, nv, boundv, mv))
        } yield out
      }

    /**
     * No entry equals `D` once every run of one entry in `{0, D}` is all zeros, so every entry is
     * below `D`, or is 0 when `D` is: at most `D - 1` either way.
     */
    def drop: R[Kernel.Thm] =
      table { _ =>
        val K = v("k"); val N = v("n"); val Bd = v("D"); val I = v("i"); val T = v("t")
        val E = s"$D $K $I"
        for {
          held <- assumed(s"${bounded(K, N, Bd)} /\\ ${runs(K, N, Bd, "1")}")
          (hT, h) = held
          parts <- split(h)
          range <- assumed(s"$I <= $N")
          top <- at(parts(0), s"$I <= $N ==> $E <= $Bd").flatMap(mp(_, range._2))
          either <- at(fact("NUM_LE_CASES"), s"$E <= $Bd ==> $E < $Bd \\/ $E = $Bd").flatMap(mp(_, top))
          goal = s"$E <= NUM_SUB $Bd 1"
          lower <- for {
            lt <- assume(s"$E < $Bd")
            one <- numLinText(Seq(lt), s"1 <= $Bd")
            back <- at(fact("NUM_SUB_ADD"), s"1 <= $Bd ==> NUM_SUB $Bd 1 + 1 = $Bd").flatMap(mp(_, one))
            out <- numLinText(Seq(lt, back), goal)
          } yield out
          atTop <- for {
            equal <- assume(s"$E = $Bd")
            inside <- numLinText(Seq(range._2), s"$I + 1 <= SUC ($N)")
            single <- for {
              lt <- assumed(s"$T < 1")
              zero <- numLinText(Seq(lt._2), s"$I + $T = $I")
              left <- prop(s"$E = 0")
              hit <- rules.disjIntro2(left, equal)
              target <- prop(member(s"$D $K ($I + $T)", Bd))
              reached <- rewriting(Seq(zero), target)(landsOn(hit))
              out <- rules.disch(lt._1, reached).flatMap(gen(_, tv))
            } yield out
            zeros <- at(parts(1), runsFrom(K, N, Bd, "1", I)).flatMap(mp(_, inside, single))
            plus <- num(s"$I + 0 = $I")
            zero <- numLinText(Seq.empty, "(0:num) < 1")
              .flatMap(c => at(zeros, s"(0:num) < 1 ==> $D $K ($I + 0) = 0").flatMap(mp(_, c))).flatMap(rw(plus, _))
            out <- numLinText(Seq(zero), goal)
          } yield out
          proved <- rules.disjElim(either, lower, atTop)
          out <- rules.disch(range._1, proved).flatMap(gen(_, iv)).flatMap(rules.disch(hT, _)).flatMap(gen(_, kv, nv, boundv))
        } yield out
      }

    /**
     * Chase's Lemma 3.2: by induction on `L` for every row, window and bound. `L = 0` is
     * `GILBREATH_DROP`; a rung of `L + 1` is `GILBREATH_SHRINK` and `GILBREATH_BELOW` at row `k`,
     * which leave a rung of `L` at row `k + 1`.
     */
    def rung: R[Kernel.Thm] =
      table { _ =>
        val K = v("k"); val N = v("n"); val Bd = v("D")
        def claim(l: String) =
          s"!k:num. !n:num. !D:num. ${bounded("k", s"n + $l", "D")} /\\ ${runs("k", s"n + $l", "D", s"SUC $l")} ==> ${bounded(s"k + $l", "n", "NUM_SUB D 1")}"
        for {
          dropHere <- under("GILBREATH_DROP")
          shrinkHere <- under("GILBREATH_SHRINK")
          belowHere <- under("GILBREATH_BELOW")
          body <- prop(claim("(L:num)"))
          proved <- inductOn(lengthv, body)(
            _ =>
              for {
                held <- assumed(s"${bounded(K, s"$N + 0", Bd)} /\\ ${runs(K, s"$N + 0", Bd, "SUC 0")}")
                widths <- num(s"$N + 0 = $N")
                one <- fact("NUM_ONE_SUC").flatMap(Conv.sym)
                here <- rw(widths, held._2).flatMap(rw(one, _))
                dropped <- at(dropHere, s"${bounded(K, N, Bd)} /\\ ${runs(K, N, Bd, "1")} ==> ${bounded(K, N, s"NUM_SUB $Bd 1")}")
                  .flatMap(mp(_, here))
                rows <- num(s"$K + 0 = $K")
                goal <- prop(bounded(s"$K + 0", N, s"NUM_SUB $Bd 1"))
                reached <- rewriting(Seq(rows), goal)(landsOn(dropped))
                out <- rules.disch(held._1, reached).flatMap(gen(_, kv, nv, boundv))
              } yield out,
            (ll, hyp, _) => {
              val L = v(ll.name)
              val inner = s"$N + $L"
              for {
                held <- assumed(s"${bounded(K, s"$N + SUC $L", Bd)} /\\ ${runs(K, s"$N + SUC $L", Bd, s"SUC (SUC $L)")}")
                widths <- numLinText(Seq.empty, s"$N + SUC $L = SUC ($inner)")
                here <- rw(widths, held._2)
                parts <- split(here)
                shrunk <- at(shrinkHere,
                  s"${bounded(K, s"SUC ($inner)", Bd)} /\\ ${runs(K, s"SUC ($inner)", Bd, s"SUC (SUC $L)")} ==> ${runs(s"SUC $K", inner, Bd, s"SUC $L")}")
                  .flatMap(mp(_, here))
                lowered <- at(belowHere, s"${bounded(K, s"SUC ($inner)", Bd)} ==> ${bounded(s"SUC $K", inner, Bd)}").flatMap(mp(_, parts(0)))
                both <- conj(lowered, shrunk)
                later <- at(hyp,
                  s"${bounded(s"SUC $K", inner, Bd)} /\\ ${runs(s"SUC $K", inner, Bd, s"SUC $L")} ==> ${bounded(s"SUC $K + $L", N, s"NUM_SUB $Bd 1")}")
                  .flatMap(mp(_, both))
                rows <- numLinText(Seq.empty, s"SUC $K + $L = $K + SUC $L")
                reached <- rw(rows, later)
                out <- rules.disch(held._1, reached).flatMap(gen(_, kv, nv, boundv))
              } yield out
            }
          )
        } yield proved
      }

    /**
     * The counted ladder: `c` rungs, the bound lowered by one per rung, take row `r 0` bounded by `D`
     * on `w 0 + 1` positions to row `r c` bounded by `D - c` on `w c + 1` positions, by induction on
     * the stage with `GILBREATH_RUNG`; then `GILBREATH_BELOW_ROWS` takes that window down `w c` rows
     * to the single entry it bounds, once `D - c` is at most 1.
     */
    def ladder: R[Kernel.Thm] =
      table { _ =>
        val C = v("c"); val R0 = "(r:num->num)"; val Ln = "(l:num->num)"; val W = "(w:num->num)"
        val Bd = v("D"); val S = v("s"); val I = v("i")
        for {
          rungHere <- under("GILBREATH_RUNG")
          rowsHere <- under("GILBREATH_BELOW_ROWS")
          held <- assumed(staged(C, R0, Ln, W, Bd))
          (hT, h) = held
          parts <- split(h)
          body <- prop(s"$S <= $C ==> ${bounded(s"$R0 $S", s"$W $S", s"NUM_SUB $Bd $S")}")
          reach <- inductOn(sv, body)(
            base =>
              for {
                zero <- at(fact("NUM_SUB_ZERO"), s"NUM_SUB $Bd 0 = $Bd")
                first <- prop(bounded(s"$R0 0", s"$W 0", s"NUM_SUB $Bd 0"))
                reached <- rewriting(Seq(zero), first)(landsOn(parts(0)))
                start <- prop(s"0 <= $C")
                out <- rules.disch(start, reached)
              } yield out,
            (ss, ih, _) => {
              val U = v(ss.name)
              val narrow = s"$W (SUC $U) + $Ln $U"
              for {
                bound <- assumed(s"SUC $U <= $C")
                within <- numLinText(Seq(bound._2), s"$U <= $C")
                lt <- numLinText(Seq(bound._2), s"$U < $C")
                prior <- mp(ih, within)
                here <- at(parts(1), s"$U < $C ==> ${stage(R0, Ln, W, Bd, U)}").flatMap(mp(_, lt)).flatMap(split)
                bounds <- rw(here(1), prior)
                blocks <- rw(here(1), here(2))
                rung <- at(rungHere,
                  s"${bounded(s"$R0 $U", narrow, s"NUM_SUB $Bd $U")} /\\ ${runs(s"$R0 $U", narrow, s"NUM_SUB $Bd $U", s"SUC ($Ln $U)")} ==> " +
                    bounded(s"$R0 $U + $Ln $U", s"$W (SUC $U)", s"NUM_SUB (NUM_SUB $Bd $U) 1"))
                lowered <- conj(bounds, blocks).flatMap(mp(rung, _))
                rows <- Conv.sym(here(0))
                sub <- at(fact("NUM_SUB_SUB"), s"NUM_SUB (NUM_SUB $Bd $U) 1 = NUM_SUB $Bd ($U + 1)")
                suc <- numLinText(Seq.empty, s"$U + 1 = SUC $U")
                reached <- rw(rows, lowered).flatMap(rw(sub, _)).flatMap(rw(suc, _))
                out <- rules.disch(bound._1, reached)
              } yield out
            }
          )
          last <- numLinText(Seq.empty, s"$C <= $C")
            .flatMap(c => at(reach, s"$C <= $C ==> ${bounded(s"$R0 $C", s"$W $C", s"NUM_SUB $Bd $C")}").flatMap(mp(_, c)))
          weak <- for {
            range <- assumed(s"$I <= 0 + $W $C")
            within <- numLinText(Seq(range._2), s"$I <= $W $C")
            entry <- at(last, s"$I <= $W $C ==> $D ($R0 $C) $I <= NUM_SUB $Bd $C").flatMap(mp(_, within))
            out <- numLinText(Seq(entry, parts(2)), s"$D ($R0 $C) $I <= 1")
            general <- rules.disch(range._1, out).flatMap(gen(_, iv))
          } yield general
          down <- at(rowsHere, s"${bounded(s"$R0 $C", s"0 + $W $C", "1")} ==> ${bounded(s"$R0 $C + $W $C", "0", "1")}").flatMap(mp(_, weak))
          end <- numLinText(Seq.empty, "(0:num) <= 0")
            .flatMap(c => at(down, s"(0:num) <= 0 ==> $D ($R0 $C + $W $C) 0 <= 1").flatMap(mp(_, c)))
          out <- rules.disch(hT, end).flatMap(gen(_, cv, rv, lv, wv, boundv))
        } yield out
      }
  }
}
