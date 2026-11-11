package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The table of Gilbreath's conjecture over any first row, the list of the primes, and the form the
 * conjecture takes on the table over them.
 *
 * Row `k + 1` holds the absolute differences of neighbours in row `k`. The absolute value of a
 * difference of naturals is written with the truncated subtraction as `NUM_SUB a b + NUM_SUB b a`,
 * one of the two terms being 0, so no absolute value on the naturals is needed. The conjecture is
 * that over the primes every row after the first starts with 1. Most statements here are over any
 * table satisfying the equation, and `GILBREATH_EXISTS` shows there is one for every first row. The
 * primes enter as a hypothesis on a function `p` rather than as a constant: `p` lists them when
 * `p 0 = 2` and each entry is the least prime above the one before, and `GILBREATH_PRIMES_EXIST` and
 * `GILBREATH_PRIMES_ALL` show that such a `p` exists and that it misses no prime.
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
 * == Over the primes ==
 *
 * `GILBREATH_PRIMES_START`: the list begins 2, 3, 5. `GILBREATH_PRIMES_GAPS`: every gap after the
 * first is even and at least 2, a prime above 2 being odd. `GILBREATH_NORMALISED` is over any table
 * whose second row is even and at least 2 from position 1 on: halving every row after the first,
 * taking 1 from the halved second row, and reading each row from position 1, gives a table with the
 * same equation, and `GILBREATH_NORMALISED_EXISTS` that every table has one. The shift is what
 * makes it hold, since the first gap, 3 - 2, is odd. Over the primes the normalised table's row
 * `n`, from 1 on, starts with half the entry at position 1 of row `n + 1` of the table, so
 * `GILBREATH_PRIMES_CONE` turns a ladder over it, from row 0 with window `n`, into that entry being
 * 0 or 2. `GILBREATH_PRIMES_FRONT` collects the ladders for every window up to `R` into the 1 at
 * the front of every row up to `R + 2`, and `GILBREATH_PRIMES_CONJECTURE` all of them into the
 * conjecture.
 *
 * == What they do not say ==
 *
 * That the ladder certifies every window over the primes, which is what the conjecture has become
 * here: `GILBREATH_PRIMES_CONJECTURE` assumes it rather than proving it. It is the same question
 * asked of the bound, whether the primes' table has blocks short enough at every depth. The
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
  private val F = "(f:num->num->num)"
  private val P = "(p:num->num)"

  /** Row `k + 1` of `table` from row `k`: the equation that characterises a table. */
  private def stepOf(table: String): String =
    s"(!k:num. !i:num. $table (SUC k) i = NUM_SUB ($table k (i + 1)) ($table k i) + NUM_SUB ($table k i) ($table k (i + 1)))"

  /** The equation of the table `d`. */
  private val Step: String = stepOf(D)

  private def over(claim: String): String = s"!d:num->num->num. $Step ==> $claim"

  /** The entry is 0 or 2. */
  private def good(e: String): String = s"($e = 0 \\/ $e = 2)"

  /** Every entry of row `row` of `table` from position 0 to position `width` is at most `bound`. */
  private def bounded(row: String, width: String, bound: String, table: String = D): String =
    s"(!i:num. i <= $width ==> $table ($row) i <= $bound)"

  /** The entry is 0 or `bound`. */
  private def member(e: String, bound: String): String = s"($e = 0 \\/ $e = $bound)"

  /**
   * The run of `length` entries of row `row` of `table` starting at `start`, when it lies in
   * positions 0 to `width`: if every entry of it is 0 or `bound`, every entry of it is 0. `start`
   * and the other arguments must not mention `t`, which is bound here.
   */
  private def runsFrom(row: String, width: String, bound: String, length: String, start: String, table: String = D): String =
    s"$start + $length <= SUC ($width) ==> (!t:num. t < $length ==> ${member(s"$table ($row) ($start + t)", bound)}) ==> " +
      s"(!t:num. t < $length ==> $table ($row) ($start + t) = 0)"

  /**
   * Every run of `length` consecutive entries in `{0, bound}` inside positions 0 to `width` of row
   * `row` of `table` is all zeros. Chase's "the longest block containing `bound` has length `L`" is
   * this at `length = L + 1`. The arguments must not mention `j` or `t`, which are bound here.
   */
  private def runs(row: String, width: String, bound: String, length: String, table: String = D): String =
    s"(!j:num. ${runsFrom(row, width, bound, length, "j", table)})"

  /**
   * The hypothesis of the ladder over `table`: row `r 0` bounded by `D` on positions 0 to `w 0`,
   * and at each stage `s < c` a rung of `l s` rows taking row `r s` with window `w s` to row
   * `r (SUC s)` with a window `l s` shorter, the runs of stage `s` bounded by `l s` at the bound
   * `D - s`; and the bound after `c` stages is at most 1.
   */
  private def staged(c: String, r: String, l: String, w: String, bound: String, table: String = D): String =
    s"${bounded(s"$r 0", s"$w 0", bound, table)} /\\ (!s:num. s < $c ==> ${stage(r, l, w, bound, "s", table)}) /\\ NUM_SUB $bound $c <= 1"

  /** Stage `s` of the ladder over `table`. */
  private def stage(r: String, l: String, w: String, bound: String, s: String, table: String = D): String =
    s"$r (SUC $s) = $r $s + $l $s /\\ $w $s = $w (SUC $s) + $l $s /\\ ${runs(s"$r $s", s"$w $s", s"NUM_SUB $bound $s", s"SUC ($l $s)", table)}"

  /**
   * `y` is the least prime above `x`. The arguments must not mention `m`, which is bound here.
   */
  private def nextPrime(x: String, y: String): String =
    s"(NUM_PRIME ($y) /\\ $x < $y /\\ (!m:num. $x < m /\\ m < $y ==> ~(NUM_PRIME m)))"

  /**
   * `p` lists the primes in increasing order from `p 0 = 2`: each entry after the first is the
   * least prime above the one before it. `GILBREATH_PRIMES_EXIST` shows such a `p` exists and
   * `GILBREATH_PRIMES_ALL` that it misses no prime.
   */
  private def enumerates(p: String): String =
    s"($p 0 = 2 /\\ (!n:num. ${nextPrime(s"$p n", s"$p (SUC n)")}))"

  /** The gap after the `n + 1`-st prime, counting `p 0 = 2` as the 0-th. */
  private def gap(n: String): String = s"NUM_SUB ($P (SUC (SUC $n))) ($P (SUC $n))"

  /** Every entry of row 1 of `d` from position 1 on is even and at least 2. */
  private val EvenGaps: String = s"(!j:num. NUM_MOD ($D 1 (SUC j)) 2 = 0 /\\ 2 <= $D 1 (SUC j))"

  /**
   * `f` is the normalised table of `d`, shifted one position to the right: row 0 is the halved
   * second row of `d` less one, row `k + 1` the halved row `k + 2`, both read from position 1.
   */
  private def normalised(f: String): String =
    s"((!i:num. $f 0 i = NUM_SUB (NUM_DIV ($D 1 (SUC i)) 2) 1) /\\ (!k:num. !i:num. $f (SUC k) i = NUM_DIV ($D (SUC (SUC k)) (SUC i)) 2))"

  /** `d` is Gilbreath's table over the primes listed by `p`, and `f` its normalised table. */
  private val Setting: String = s"${enumerates(P)} /\\ (!i:num. $D 0 i = $P i) /\\ ${normalised(F)}"

  /** Ladder data for `f`, starting at row 0 with window `n`, exist. `n` must not mention the names bound here. */
  private def certified(n: String): String =
    s"(?c:num. ?r:num->num. ?l:num->num. ?w:num->num. ?D:num. r 0 = 0 /\\ w 0 = $n /\\ ${staged("c", "r", "l", "w", "D", F)})"

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
      s"!c:num. !r:num->num. !l:num->num. !w:num->num. !D:num. ${staged("c", "r", "l", "w", "D")} ==> $D (r c + w c) 0 <= 1"),
    "GILBREATH_PRIMES_EXIST" -> s"?p:num->num. ${enumerates(P)}",
    "GILBREATH_PRIMES_ALL" -> s"!p:num->num. !q:num. ${enumerates(P)} ==> NUM_PRIME q ==> (?n:num. $P n = q)",
    "GILBREATH_PRIMES_START" -> s"!p:num->num. ${enumerates(P)} ==> $P 1 = 3 /\\ $P 2 = 5",
    "GILBREATH_PRIMES_GAPS" -> s"!p:num->num. ${enumerates(P)} ==> (!n:num. NUM_MOD (${gap("n")}) 2 = 0 /\\ 2 <= ${gap("n")})",
    "GILBREATH_NORMALISED" -> over(s"$EvenGaps ==> (!f:num->num->num. ${normalised(F)} ==> ${stepOf(F)})"),
    "GILBREATH_NORMALISED_EXISTS" -> s"!d:num->num->num. ?f:num->num->num. ${normalised(F)}",
    "GILBREATH_PRIMES_CONE" -> over(
      s"!p:num->num. !f:num->num->num. !c:num. !r:num->num. !l:num->num. !w:num->num. !D:num. !n:num. " +
        s"$Setting /\\ ${staged("c", "r", "l", "w", "D", F)} /\\ r 0 = 0 /\\ w 0 = n /\\ 1 <= n ==> ${good(s"$D (SUC n) 1")}"),
    "GILBREATH_PRIMES_FRONT" -> over(
      s"!p:num->num. !f:num->num->num. !R:num. $Setting /\\ (!n:num. 1 <= n /\\ n <= R ==> ${certified("n")}) ==> " +
        s"(!k:num. 1 <= k /\\ k <= R + 2 ==> $D k 0 = 1)"),
    "GILBREATH_PRIMES_CONJECTURE" -> over(
      s"!p:num->num. !f:num->num->num. $Setting /\\ (!n:num. 1 <= n ==> ${certified("n")}) ==> (!k:num. 0 < k ==> $D k 0 = 1)")
  )

  /**
   * Proved on the way and not published, each named here so that a later step reads it rather
   * than proving it again: every prime in the list is at least its index plus 2, and every row
   * after the first of a table whose second row is even from position 1 on is even from there too.
   */
  private val Lemmas: Vector[(String, String)] = Vector(
    "GILBREATH_PRIMES_CLIMB" -> s"!p:num->num. ${enumerates(P)} ==> (!n:num. n + 2 <= $P n)",
    "GILBREATH_EVEN_ROWS" -> over(s"$EvenGaps ==> (!k:num. !i:num. NUM_MOD ($D (SUC k) (SUC i)) 2 = 0)")
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
    "GILBREATH_LADDER" -> (_.ladder),
    "GILBREATH_PRIMES_EXIST" -> (_.primesExist),
    "GILBREATH_PRIMES_CLIMB" -> (_.primesClimb),
    "GILBREATH_PRIMES_ALL" -> (_.primesAll),
    "GILBREATH_PRIMES_START" -> (_.primesStart),
    "GILBREATH_PRIMES_GAPS" -> (_.primesGaps),
    "GILBREATH_EVEN_ROWS" -> (_.evenRows),
    "GILBREATH_NORMALISED" -> (_.normalisedStep),
    "GILBREATH_NORMALISED_EXISTS" -> (_.normalisedExists),
    "GILBREATH_PRIMES_CONE" -> (_.primesCone),
    "GILBREATH_PRIMES_FRONT" -> (_.primesFront),
    "GILBREATH_PRIMES_CONJECTURE" -> (_.primesConjecture)
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
     * Half the absolute difference of two even numbers `a` and `b`, from `NUM_MOD a 2 = 0` and
     * `NUM_MOD b 2 = 0`: `T = NUM_DIV V 2 /\\ 0 = NUM_MOD V 2`, with `V` the absolute difference of
     * `a` and `b` and `T` that of their halves, both written with the truncated subtraction. Writing
     * each as twice its half, `V` is twice `T`.
     */
    private def halved(A: String, B: String, evenA: Kernel.Thm, evenB: Kernel.Thm): R[Kernel.Thm] = {
      val Ha = s"NUM_DIV ($A) 2"; val Hb = s"NUM_DIV ($B) 2"
      val V = s"NUM_SUB ($A) ($B) + NUM_SUB ($B) ($A)"
      val T = s"NUM_SUB ($Ha) ($Hb) + NUM_SUB ($Hb) ($Ha)"
      for {
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
        out <- conj(twice, below).flatMap(mp(unique, _))
      } yield out
    }

    /** Even entries from position 1 on stay even: the difference of two of them is twice that of their halves, by `halved`. */
    def even: R[Kernel.Thm] =
      table { step =>
        val K = v("k"); val I = v("i")
        val A = s"$D $K ($I + 1)"; val B = s"$D $K $I"
        for {
          held <- assumed(s"!i:num. 0 < i ==> NUM_MOD ($D $K i) 2 = 0")
          (hT, h) = held
          pos <- assumed(s"0 < $I")
          evenA <- numLinText(Seq.empty, s"0 < $I + 1").flatMap(p => at(h, s"0 < $I + 1 ==> NUM_MOD ($A) 2 = 0").flatMap(mp(_, p)))
          evenB <- at(h, s"0 < $I ==> NUM_MOD ($B) 2 = 0").flatMap(mp(_, pos._2))
          modulus <- halved(A, B, evenA, evenB).flatMap(rules.conjElim2).flatMap(Conv.sym)
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

    /* ------------------------------------------------------------ the primes in order */

    private val primesv = Term.variable("p", Rows)
    private val fv = Term.variable("f", Tables)
    private val qv = Term.variable("q", Numbers)
    private val xv = Term.variable("x", Numbers)
    private val ceilingv = Term.variable("R", Numbers)

    /** A lemma of `Lemmas` proved earlier, checked against its text before it is spent. */
    private def lemma(name: String): R[Kernel.Thm] =
      for {
        thm <- known.get(name).toRight(MissingDefinition(name))
        text <- Lemmas.toMap.get(name).toRight(MissingDefinition(name))
        expected <- prop(text)
        out <- if (thm.conclusion == expected && thm.hypotheses.isEmpty) Right(thm)
          else Left(NotOfForm("the statement Gilbreath.Lemmas writes for it, with no hypothesis", thm.conclusion))
      } yield out

    /** A lemma of `Lemmas` over the table, at the equation assumed. */
    private def underLemma(name: String): R[Kernel.Thm] =
      for {
        h <- assume(Step)
        out <- lemma(name).flatMap(spec(_, dv)).flatMap(mp(_, h))
      } yield out

    /** Falsity from comparisons of naturals that cannot all hold, which `numLin` sees as `SUC 0 = 0`. */
    private def absurd(facts: Seq[Kernel.Thm]): R[Kernel.Thm] =
      for {
        zero <- numLinText(facts, "SUC 0 = 0")
        never <- at(fact("NUM_SUC_NOT_ZERO"), "~(SUC 0 = 0)")
        out <- rules.notElim(never, zero)
      } yield out

    /** `goal` from falsity. */
    private def anyway(falsity: Kernel.Thm, goal: String): R[Kernel.Thm] = prop(goal).flatMap(rules.falsityElim(_, falsity))

    /** `SUC 0 = 1`, which carries a row or a position written by a recurrence to the numeral. */
    private def oneOfSuc: R[Kernel.Thm] = fact("NUM_ONE_SUC").flatMap(Conv.sym)

    /** `SUC (NUM_SUB x 1) = x` from `1 <= x`, and `NUM_SUB x 1 + 1 = x` beside it. */
    private def predecessor(one: Kernel.Thm, x: String): R[(Kernel.Thm, Kernel.Thm)] =
      for {
        back <- at(fact("NUM_SUB_ADD"), s"1 <= $x ==> NUM_SUB $x 1 + 1 = $x").flatMap(mp(_, one))
        suc <- numLinText(Seq(back), s"SUC (NUM_SUB $x 1) = $x")
      } yield (suc, back)

    /** `!i. 0 < i ==> P i` from `!i. P (SUC i)`, with `entry` writing `P` at a position. */
    private def fromSuccessor(thm: Kernel.Thm, entry: String => String): R[Kernel.Thm] = {
      val I = v("i")
      for {
        pos <- assumed(s"0 < $I")
        one <- numLinText(Seq(pos._2), s"1 <= $I")
        suc <- predecessor(one, I).map(_._1)
        there <- at(thm, entry(s"(SUC (NUM_SUB $I 1))")).flatMap(rw(suc, _))
        out <- rules.disch(pos._1, there).flatMap(gen(_, iv))
      } yield out
    }

    /** Every existential of `existential` opened in turn, under the names given, and `use` on the body. */
    private def chooseAll(existential: Kernel.Thm, names: Seq[String])(use: Kernel.Thm => R[Kernel.Thm]): R[Kernel.Thm] =
      names match {
        case Seq() => use(existential)
        case name +: rest => choose(existential, name)((_, inner) => chooseAll(inner, rest)(use))
      }

    /** The clause of the list at `index`, split: `p (SUC index)` is prime, above `p index`, and no prime lies between. */
    private def clause(clauses: Kernel.Thm, index: String): R[Vector[Kernel.Thm]] =
      at(clauses, nextPrime(s"$P ($index)", s"$P (SUC ($index))")).flatMap(split)

    /**
     * `m = N` for the numeral `N`, from `N = m * k`, `SUC 0 < m` and `m <= c`: each candidate from
     * `c` down to 2 other than `N` is refused because `N` is not a multiple of it, which `numLin`
     * sees once `k` is placed either side of `N / c`.
     */
    private def onlyDivisor(n: Int, c: Int, product: Kernel.Thm, low: Kernel.Thm, le: Kernel.Thm): R[Kernel.Thm] = {
      val M = v("m"); val K = v("k"); val goal = s"$M = $n"
      if (c <= 1) numLinText(Seq(low, le), goal)
      else
        for {
          sides <- at(fact("NUM_LE_CASES"), s"$M <= $c ==> $M < $c \\/ $M = $c").flatMap(mp(_, le))
          below <- assume(s"$M < $c").flatMap(lt => numLinText(Seq(lt), s"$M <= ${c - 1}")).flatMap(onlyDivisor(n, c - 1, product, low, _))
          here <- assume(s"$M = $c").flatMap { equal =>
            if (c == n) Right(equal)
            else
              for {
                multiple <- rw(equal, product)
                quotient = n / c
                out <- cases(s"$K <= $quotient")(
                  small => numLinText(Seq(multiple, small), goal),
                  large =>
                    notLeTheorem.flatMap(at(_, s"~($K <= $quotient) ==> $quotient < $K")).flatMap(mp(_, large))
                      .flatMap(gt => numLinText(Seq(multiple, gt), goal))
                )
              } yield out
          }
          out <- rules.disjElim(sides, below, here)
        } yield out
    }

    /** `NUM_PRIME N` for a numeral `N`: the prime factor `NUM_PRIME_FACTOR` gives it is `N` itself. */
    private def primeNumeral(n: Int): R[Kernel.Thm] = {
      val M = v("m")
      for {
        above <- numLinText(Seq.empty, s"SUC 0 < $n")
        factor <- at(fact("NUM_PRIME_FACTOR"), s"SUC 0 < $n ==> (?m:num. NUM_PRIME m /\\ NUM_DIVIDES m $n)").flatMap(mp(_, above))
        out <- choose(factor, "m") { (_, held) =>
          for {
            parts <- split(held)
            low <- at(fact("NUM_PRIME_ABOVE_ONE"), s"NUM_PRIME $M ==> SUC 0 < $M").flatMap(mp(_, parts(0)))
            sizes <- at(fact("NUM_DIVIDES_LE"), s"NUM_DIVIDES $M $n ==> $M <= $n \\/ ($n:num) = 0").flatMap(mp(_, parts(1)))
            fits <- assume(s"$M <= $n")
            empty <- assume(s"($n:num) = 0").flatMap(z => numLinText(Seq(z), s"$M <= $n"))
            high <- rules.disjElim(sizes, fits, empty)
            quotient <- at(fact("NUM_DIVIDES_ELIM"), s"NUM_DIVIDES $M $n ==> (?k:num. $n = $M * k)").flatMap(mp(_, parts(1)))
            equal <- choose(quotient, "k")((_, product) => onlyDivisor(n, n, product, low, high))
            out <- rw(equal, parts(0))
          } yield out
        }
      } yield out
    }

    /** `~(NUM_PRIME 4)`: 2 divides it. */
    private def fourNotPrime: R[Kernel.Thm] =
      for {
        held <- assumed("NUM_PRIME 4")
        twice <- num("(4:num) = 2 * 2")
        divides <- at(fact("NUM_DIVIDES_INTRO"), "(4:num) = 2 * 2 ==> NUM_DIVIDES 2 4").flatMap(mp(_, twice))
        only <- at(fact("NUM_PRIME_DIVISOR"), "NUM_PRIME 4 ==> NUM_DIVIDES 2 4 ==> 2 = SUC 0 \\/ (2:num) = 4").flatMap(mp(_, held._2, divides))
        one <- assume("(2:num) = SUC 0").flatMap(e => absurd(Seq(e)))
        other <- assume("(2:num) = 4").flatMap(e => absurd(Seq(e)))
        falsity <- rules.disjElim(only, one, other)
        out <- rules.notIntro(held._1, falsity)
      } yield out

    /** `NUM_MOD q 2 = 1` for a prime `q` above 2: were it even, 2 would be a divisor other than 1 and `q`. */
    private def oddPrime(prime: Kernel.Thm, above: Kernel.Thm, Q: String): R[Kernel.Thm] = {
      val goal = s"NUM_MOD ($Q) 2 = 1"
      for {
        below <- two.flatMap(t => at(fact("NUM_MOD_LT"), s"(0:num) < 2 ==> NUM_MOD ($Q) 2 < 2").flatMap(mp(_, t)))
        whole <- at(fact("NUM_DIV_MOD"), s"2 * NUM_DIV ($Q) 2 + NUM_MOD ($Q) 2 = $Q")
        out <- cases(s"NUM_MOD ($Q) 2 = 0")(
          zero =>
            for {
              halves <- rw(zero, whole)
              flat <- numLinText(Seq(halves), s"$Q = 2 * NUM_DIV ($Q) 2")
              divides <- at(fact("NUM_DIVIDES_INTRO"), s"$Q = 2 * NUM_DIV ($Q) 2 ==> NUM_DIVIDES 2 ($Q)").flatMap(mp(_, flat))
              only <- at(fact("NUM_PRIME_DIVISOR"), s"NUM_PRIME ($Q) ==> NUM_DIVIDES 2 ($Q) ==> 2 = SUC 0 \\/ 2 = $Q").flatMap(mp(_, prime, divides))
              one <- assume("(2:num) = SUC 0").flatMap(e => absurd(Seq(e))).flatMap(anyway(_, goal))
              other <- assume(s"2 = $Q").flatMap(e => absurd(Seq(e, above))).flatMap(anyway(_, goal))
              out <- rules.disjElim(only, one, other)
            } yield out,
          nonzero => positiveOf(nonzero, s"NUM_MOD ($Q) 2").flatMap(pos => numLinText(Seq(pos, below), goal))
        )
      } yield out
    }

    /**
     * `x <= N` from `lo < N`, `NUM_PRIME N` and the clause that no prime lies strictly between `lo`
     * and `x`: otherwise `N` would be one.
     */
    private def atMost(x: String, lo: Int, n: Int, gaps: Kernel.Thm, prime: Kernel.Thm): R[Kernel.Thm] =
      for {
        total <- at(fact("NUM_LE_TOTAL"), s"$x <= $n \\/ $n <= $x")
        fits <- assume(s"$x <= $n")
        beyond <- for {
          le <- assume(s"$n <= $x")
          sides <- at(fact("NUM_LE_CASES"), s"$n <= $x ==> $n < $x \\/ $n = $x").flatMap(mp(_, le))
          strict <- for {
            lt <- assume(s"$n < $x")
            inside <- numLinText(Seq.empty, s"($lo:num) < $n").flatMap(conj(_, lt))
            never <- at(gaps, s"($lo:num) < $n /\\ $n < $x ==> ~(NUM_PRIME $n)").flatMap(mp(_, inside))
            falsity <- rules.notElim(never, prime)
            out <- anyway(falsity, s"$x <= $n")
          } yield out
          equal <- assume(s"$n = $x").flatMap(e => numLinText(Seq(e), s"$x <= $n"))
          out <- rules.disjElim(sides, strict, equal)
        } yield out
        out <- rules.disjElim(total, fits, beyond)
      } yield out

    /** `!x. ?y. y is the least prime above x`: Euclid's primes above `x`, and the least of them. */
    private def nextExists: R[Kernel.Thm] = {
      val X = v("x"); val M = v("m")
      for {
        some <- at(fact("NUM_PRIME_UNBOUNDED"), s"?m:num. NUM_PRIME m /\\ $X < m")
        property <- term(s"\\m:num. NUM_PRIME m /\\ $X < m", Type.fun(Numbers, Type.Bool))
        least <- fact("NUM_LEAST").flatMap(spec(_, property)).flatMap(mp(_, some))
        predicate <- predicateOf(s"?y:num. ${nextPrime(X, "y")}")
        out <- choose(least, "y") { (y, held) =>
          val Y = v(y.name)
          for {
            parts <- split(held)
            pair <- split(parts(0))
            between <- for {
              range <- assumed(s"$X < $M /\\ $M < $Y")
              ends <- split(range._2)
              minimal <- at(parts(1), s"$M < $Y ==> ~(NUM_PRIME $M /\\ $X < $M)").flatMap(mp(_, ends(1)))
              wanted <- prop(s"~(NUM_PRIME $M)")
              never <- tauto(Seq(minimal, ends(0)), wanted)
              out <- rules.disch(range._1, never).flatMap(gen(_, mv))
            } yield out
            holds <- conjs(pair(0), pair(1), between)
            out <- introduce(predicate, y, holds)
          } yield out
        }
        general <- gen(out, xv)
      } yield general
    }

    /**
     * A list of the primes exists: by the recursion theorem, from 2, each entry the chosen least
     * prime above the one before it, which `nextExists` and choice make the least prime above it.
     */
    def primesExist: R[Kernel.Thm] =
      for {
        nexts <- nextExists
        choice <- classical.axiom(Classical.Choice).map(Kernel.instType(Map(Classical.TypeVariable -> Numbers), _))
        recursive <- Right(Kernel.instType(Map("a" -> Numbers), recursion))
        start <- nm("2")
        stepper <- term(s"\\x:num. \\n:num. select (\\y:num. ${nextPrime("x", "y")})", Type.fun(Numbers, Type.fun(Numbers, Numbers)))
        made <- spec(recursive, start, stepper)
        predicate <- predicateOf(s"?p:num->num. ${enumerates(P)}")
        out <- choose(made, "fn") { (fn, clauses) =>
          for {
            parts <- split(clauses)
            atSuc <- spec(parts(1), nv)
            chosen <- Term.destEq(atSuc.conclusion) match {
              case Some((_, App(_, predicateTerm))) => Right(predicateTerm)
              case _ => Left(NotOfForm("an entry chosen by select", atSuc.conclusion))
            }
            before <- LogicError.lift(Term.app(fn, nv))
            exists <- spec(nexts, before)
            reached <- choose(exists, "y")((y, holds) => spec(choice, chosen, y).flatMap(mp(_, holds)))
            back <- Conv.sym(atSuc)
            here <- rw(back, reached)
            every <- gen(here, nv)
            both <- conj(parts(0), every)
            out <- introduce(predicate, fn, both)
          } yield out
        }
      } yield out

    /** Every entry is at least its index plus 2: by induction, each entry above the one before. */
    def primesClimb: R[Kernel.Thm] =
      for {
        held <- assumed(enumerates(P))
        (hT, h) = held
        parts <- split(h)
        body <- prop(s"(n:num) + 2 <= $P n")
        proved <- inductOn(nv, body)(
          base => numLin(Seq(parts(0)), base),
          (nn, ih, goal) => clause(parts(1), v(nn.name)).flatMap(c => numLin(Seq(ih, c(1)), goal))
        )
        out <- rules.disch(hT, proved).flatMap(gen(_, primesv))
      } yield out

    /**
     * The list misses no prime. The least index whose entry reaches `q` exists, since entry `q`
     * does; at index 0 the entry is 2 and `q` is above 1, and at any later index the entry before
     * is below `q`, so `q` below the entry would be a prime between two consecutive ones.
     */
    def primesAll: R[Kernel.Thm] = {
      val Q = v("q"); val N = v("n")
      val goal = s"?n:num. $P n = $Q"
      for {
        climb <- lemma("GILBREATH_PRIMES_CLIMB").flatMap(spec(_, primesv))
        held <- assumed(enumerates(P))
        (hT, h) = held
        parts <- split(h)
        prime <- assumed(s"NUM_PRIME $Q")
        (qT, hq) = prime
        far <- mp(climb, h).flatMap(at(_, s"$Q + 2 <= $P $Q"))
        reach <- numLinText(Seq(far), s"$Q <= $P $Q")
        some <- existsIntro(s"?n:num. $Q <= $P n", qv, reach)
        property <- term(s"\\n:num. $Q <= $P n", Type.fun(Numbers, Type.Bool))
        least <- fact("NUM_LEAST").flatMap(spec(_, property)).flatMap(mp(_, some))
        above <- at(fact("NUM_PRIME_ABOVE_ONE"), s"NUM_PRIME $Q ==> SUC 0 < $Q").flatMap(mp(_, hq))
        found <- choose(least, "n") { (n, both) =>
          for {
            bs <- split(both)
            out <- cases(s"$N = 0")(
              zero =>
                for {
                  low <- rw(zero, bs(0))
                  equal <- numLinText(Seq(low, parts(0), above), s"$P 0 = $Q")
                  witness <- nm("0")
                  out <- existsIntro(goal, witness, equal)
                } yield out,
              nonzero =>
                for {
                  one <- positiveOf(nonzero, N).flatMap(pos => numLinText(Seq(pos), s"1 <= $N"))
                  pred <- predecessor(one, N)
                  (suc, back) = pred
                  prior = s"(NUM_SUB $N 1)"
                  earlier <- numLinText(Seq(back), s"$prior < $N")
                  short <- at(bs(1), s"$prior < $N ==> ~($Q <= $P $prior)").flatMap(mp(_, earlier))
                  lower <- notLeTheorem.flatMap(at(_, s"~($Q <= $P $prior) ==> $P $prior < $Q")).flatMap(mp(_, short))
                  gaps <- clause(parts(1), prior).flatMap(c => rw(suc, c(2)))
                  sides <- at(fact("NUM_LE_CASES"), s"$Q <= $P $N ==> $Q < $P $N \\/ $Q = $P $N").flatMap(mp(_, bs(0)))
                  strict <- for {
                    lt <- assume(s"$Q < $P $N")
                    between <- conj(lower, lt)
                    never <- at(gaps, s"$P $prior < $Q /\\ $Q < $P $N ==> ~(NUM_PRIME $Q)").flatMap(mp(_, between))
                    falsity <- rules.notElim(never, hq)
                    out <- anyway(falsity, goal)
                  } yield out
                  equal <- for {
                    e <- assume(s"$Q = $P $N")
                    s <- Conv.sym(e)
                    out <- existsIntro(goal, n, s)
                  } yield out
                  out <- rules.disjElim(sides, strict, equal)
                } yield out
            )
          } yield out
        }
        out <- rules.disch(qT, found).flatMap(rules.disch(hT, _)).flatMap(gen(_, primesv, qv))
      } yield out
    }

    /** `p 1 = 3` and `p 2 = 5`: 3 and 5 are prime, 4 is not, and the list skips no prime. */
    def primesStart: R[Kernel.Thm] = {
      val P1 = s"$P 1"; val P2 = s"$P 2"
      for {
        held <- assumed(enumerates(P))
        (hT, h) = held
        parts <- split(h)
        one <- oneOfSuc
        twoOfSuc <- numLinText(Seq.empty, "SUC 1 = 2")
        three <- primeNumeral(3)
        five <- primeNumeral(5)
        four <- fourNotPrime
        first <- clause(parts(1), "0").flatMap(cs =>
          cs.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, c) => for { done <- acc; t <- rw(one, c).flatMap(rw(parts(0), _)) } yield done :+ t))
        upper1 <- atMost(P1, 2, 3, first(2), three)
        p1 <- numLinText(Seq(first(1), upper1), s"$P1 = 3")
        second <- clause(parts(1), "1").flatMap(cs =>
          cs.foldLeft[R[Vector[Kernel.Thm]]](Right(Vector.empty))((acc, c) => for { done <- acc; t <- rw(twoOfSuc, c).flatMap(rw(p1, _)) } yield done :+ t))
        upper2 <- atMost(P2, 3, 5, second(2), five)
        sides <- at(fact("NUM_LE_CASES"), s"$P2 <= 5 ==> $P2 < 5 \\/ $P2 = 5").flatMap(mp(_, upper2))
        notFour <- for {
          lt <- assume(s"$P2 < 5")
          isFour <- numLinText(Seq(lt, second(1)), s"$P2 = 4")
          primeFour <- rw(isFour, second(0))
          falsity <- rules.notElim(four, primeFour)
          out <- anyway(falsity, s"$P2 = 5")
        } yield out
        p2 <- assume(s"$P2 = 5").flatMap(rules.disjElim(sides, notFour, _))
        both <- conj(p1, p2)
        out <- rules.disch(hT, both).flatMap(gen(_, primesv))
      } yield out
    }

    /**
     * Every gap after the first is even and at least 2: the primes either side are odd, so their
     * difference is twice the difference of their halves, which is not 0 because they differ.
     */
    def primesGaps: R[Kernel.Thm] = {
      val N = v("n"); val A = s"$P (SUC (SUC $N))"; val B = s"$P (SUC $N)"
      val Ha = s"NUM_DIV ($A) 2"; val Hb = s"NUM_DIV ($B) 2"
      val S = s"NUM_SUB ($Ha) ($Hb)"; val G = gap(N)
      for {
        climb <- lemma("GILBREATH_PRIMES_CLIMB").flatMap(spec(_, primesv))
        held <- assumed(enumerates(P))
        (hT, h) = held
        parts <- split(h)
        here <- clause(parts(1), N)
        next <- clause(parts(1), s"SUC $N")
        farB <- mp(climb, h).flatMap(at(_, s"SUC $N + 2 <= $B"))
        aboveB <- numLinText(Seq(farB), s"2 < $B")
        aboveA <- numLinText(Seq(farB, next(1)), s"2 < $A")
        oddB <- oddPrime(here(0), aboveB, B)
        oddA <- oddPrime(next(0), aboveA, A)
        halfA <- at(fact("NUM_DIV_MOD"), s"2 * $Ha + NUM_MOD ($A) 2 = $A").flatMap(rw(oddA, _))
        halfB <- at(fact("NUM_DIV_MOD"), s"2 * $Hb + NUM_MOD ($B) 2 = $B").flatMap(rw(oddB, _))
        le <- numLinText(Seq(next(1)), s"$B <= $A")
        whole <- at(fact("NUM_SUB_ADD"), s"$B <= $A ==> $G + $B = $A").flatMap(mp(_, le))
        halfLe <- numLinText(Seq(halfA, halfB, next(1)), s"$Hb <= $Ha")
        half <- at(fact("NUM_SUB_ADD"), s"$Hb <= $Ha ==> $S + $Hb = $Ha").flatMap(mp(_, halfLe))
        twice <- numLinText(Seq(halfA, halfB, whole, half), s"$G = 2 * ($S) + 0")
        below <- two
        unique <- at(fact("NUM_DIV_MOD_UNIQUE"), s"$G = 2 * ($S) + 0 /\\ (0:num) < 2 ==> $S = NUM_DIV ($G) 2 /\\ 0 = NUM_MOD ($G) 2")
        even <- conj(twice, below).flatMap(mp(unique, _)).flatMap(rules.conjElim2).flatMap(Conv.sym)
        wide <- cases(s"$S = 0")(
          zero => numLinText(Seq(zero, twice, whole, next(1)), s"2 <= $G"),
          nonzero => positiveOf(nonzero, S).flatMap(pos => numLinText(Seq(pos, twice), s"2 <= $G"))
        )
        both <- conj(even, wide)
        out <- gen(both, nv).flatMap(rules.disch(hT, _)).flatMap(gen(_, primesv))
      } yield out
    }

    /** Every row after the first is even from position 1 on, when the second row is: by induction with `GILBREATH_EVEN`. */
    def evenRows: R[Kernel.Thm] =
      table { _ =>
        val I = v("i")
        for {
          evenHere <- under("GILBREATH_EVEN")
          held <- assumed(EvenGaps)
          (hT, h) = held
          one <- oneOfSuc
          body <- prop(s"!i:num. NUM_MOD ($D (SUC (k:num)) (SUC i)) 2 = 0")
          proved <- inductOn(kv, body)(
            base =>
              rewriting(Seq(one), base) { g =>
                at(h, s"NUM_MOD ($D 1 (SUC $I)) 2 = 0 /\\ 2 <= $D 1 (SUC $I)").flatMap(rules.conjElim1).flatMap(gen(_, iv)).flatMap(landsOn(_)(g))
              },
            (kk, ih, _) => {
              val K = v(kk.name)
              for {
                positive <- fromSuccessor(ih, i => s"NUM_MOD ($D (SUC $K) $i) 2 = 0")
                next <- at(evenHere,
                  s"(!i:num. 0 < i ==> NUM_MOD ($D (SUC $K) i) 2 = 0) ==> (!i:num. 0 < i ==> NUM_MOD ($D (SUC (SUC $K)) i) 2 = 0)")
                  .flatMap(mp(_, positive))
                lt <- numLinText(Seq.empty, s"0 < SUC $I")
                entry <- at(next, s"0 < SUC $I ==> NUM_MOD ($D (SUC (SUC $K)) (SUC $I)) 2 = 0").flatMap(mp(_, lt))
                out <- gen(entry, iv)
              } yield out
            }
          )
          out <- rules.disch(hT, proved)
        } yield out
      }

    /**
     * The normalised table satisfies the table's equation. Below row 1 each entry is half an
     * absolute difference of two even entries, which is the absolute difference of their halves by
     * `halved`; at row 1 the halves are of the second row, and taking 1 from both, each at least
     * 1, leaves their difference as it was.
     */
    def normalisedStep: R[Kernel.Thm] =
      table { step =>
        val K = v("k"); val I = v("i")
        val A = s"$D 1 (SUC $I + 1)"; val B = s"$D 1 (SUC $I)"
        val Ha = s"NUM_DIV ($A) 2"; val Hb = s"NUM_DIV ($B) 2"
        def stepText(row: String, pos: String): String =
          s"$F (SUC $row) $pos = NUM_SUB ($F $row ($pos + 1)) ($F $row $pos) + NUM_SUB ($F $row $pos) ($F $row ($pos + 1))"
        for {
          rowsHere <- underLemma("GILBREATH_EVEN_ROWS")
          held <- assumed(EvenGaps)
          (gT, gaps) = held
          evens <- mp(rowsHere, gaps)
          described <- assumed(normalised(F))
          (fT, fh) = described
          fs <- split(fh)
          one <- oneOfSuc
          shift <- numLinText(Seq.empty, s"SUC ($I + 1) = SUC $I + 1")
          later <- for {
            top <- at(fs(1), s"$F (SUC (SUC $K)) $I = NUM_DIV ($D (SUC (SUC (SUC $K))) (SUC $I)) 2")
            right <- at(fs(1), s"$F (SUC $K) ($I + 1) = NUM_DIV ($D (SUC (SUC $K)) (SUC ($I + 1))) 2").flatMap(rw(shift, _))
            left <- at(fs(1), s"$F (SUC $K) $I = NUM_DIV ($D (SUC (SUC $K)) (SUC $I)) 2")
            opened <- stepAt(step, s"(SUC (SUC $K))", s"(SUC $I)")
            twoShift <- numLinText(Seq.empty, s"SUC (SUC $I) = SUC $I + 1")
            evenA <- at(evens, s"NUM_MOD ($D (SUC (SUC $K)) (SUC (SUC $I))) 2 = 0").flatMap(rw(twoShift, _))
            evenB <- at(evens, s"NUM_MOD ($D (SUC (SUC $K)) (SUC $I)) 2 = 0")
            halves <- halved(s"$D (SUC (SUC $K)) (SUC $I + 1)", s"$D (SUC (SUC $K)) (SUC $I)", evenA, evenB)
              .flatMap(rules.conjElim1).flatMap(Conv.sym)
            goal <- prop(stepText(s"(SUC $K)", I))
            proved <- rewriting(Seq(top, opened, right, left), goal)(landsOn(halves))
            out <- gen(proved, kv, iv)
          } yield out
          first <- for {
            top <- at(fs(1), s"$F (SUC 0) $I = NUM_DIV ($D (SUC (SUC 0)) (SUC $I)) 2").flatMap(rw(one, _))
            opened <- stepAt(step, "1", s"(SUC $I)")
            right <- at(fs(0), s"$F 0 ($I + 1) = NUM_SUB (NUM_DIV ($D 1 (SUC ($I + 1))) 2) 1").flatMap(rw(shift, _))
            left <- at(fs(0), s"$F 0 $I = NUM_SUB (NUM_DIV ($D 1 (SUC $I)) 2) 1")
            gapA <- at(gaps, s"NUM_MOD ($D 1 (SUC ($I + 1))) 2 = 0 /\\ 2 <= $D 1 (SUC ($I + 1))").flatMap(rw(shift, _)).flatMap(split)
            gapB <- at(gaps, s"NUM_MOD ($B) 2 = 0 /\\ 2 <= $B").flatMap(split)
            halves <- halved(A, B, gapA(0), gapB(0)).flatMap(rules.conjElim1)
            wholeA <- at(fact("NUM_DIV_MOD"), s"2 * $Ha + NUM_MOD ($A) 2 = $A").flatMap(rw(gapA(0), _))
            wholeB <- at(fact("NUM_DIV_MOD"), s"2 * $Hb + NUM_MOD ($B) 2 = $B").flatMap(rw(gapB(0), _))
            backA <- numLinText(Seq(wholeA, gapA(1)), s"1 <= $Ha").flatMap(predecessor(_, s"($Ha)")).map(_._2)
            backB <- numLinText(Seq(wholeB, gapB(1)), s"1 <= $Hb").flatMap(predecessor(_, s"($Hb)")).map(_._2)
            goal <- prop(stepText("0", I))
            proved <- rewriting(Seq(one, top, opened, right, left), goal) { g =>
              eitherOrder(s"($Ha)", s"($Hb)") { (lo, hi, le) =>
                val (lo1, hi1) = (s"(NUM_SUB $lo 1)", s"(NUM_SUB $hi 1)")
                for {
                  outer <- ordered(le, lo, hi)
                  le1 <- numLinText(Seq(le, backA, backB), s"$lo1 <= $hi1")
                  inner <- ordered(le1, lo1, hi1)
                  out <- numLin(outer ++ inner ++ Seq(halves, backA, backB), g)
                } yield out
              }
            }
            out <- gen(proved, iv)
          } yield out
          goal <- prop(stepText(K, I))
          entry <- cases(s"$K = 0")(
            zero => spec(first, iv).flatMap(atI => rewriting(Seq(zero), goal)(landsOn(atI))),
            nonzero =>
              for {
                one1 <- positiveOf(nonzero, K).flatMap(pos => numLinText(Seq(pos), s"1 <= $K"))
                suc <- predecessor(one1, K).map(_._1)
                out <- at(later, stepText(s"(SUC (NUM_SUB $K 1))", I)).flatMap(rw(suc, _))
              } yield out
          )
          general <- gen(entry, kv, iv)
          out <- rules.disch(fT, general).flatMap(gen(_, fv)).flatMap(rules.disch(gT, _))
        } yield out
      }

    /**
     * Every table has a normalised table: `\k i. NUM_SUB (NUM_DIV (d (SUC k) (SUC i)) 2) (NUM_SUB 1 k)`,
     * which takes 1 at row 0 and nothing after it, so no case split is written. It is what keeps the
     * hypothesis on `f` in `GILBREATH_PRIMES_CONE` and the two after it from being one nothing
     * satisfies.
     */
    def normalisedExists: R[Kernel.Thm] = {
      val K = v("k"); val I = v("i")
      val later = s"NUM_DIV ($D (SUC (SUC $K)) (SUC $I)) 2"
      for {
        witness <- term(s"\\k:num. \\i:num. NUM_SUB (NUM_DIV ($D (SUC k) (SUC i)) 2) (NUM_SUB 1 k)", Tables)
        predicate <- predicateOf(s"?f:num->num->num. ${normalised(F)}")
        one <- oneOfSuc
        first <- for {
          goal <- prop(s"NUM_SUB (NUM_DIV ($D (SUC 0) (SUC $I)) 2) (NUM_SUB 1 0) = NUM_SUB (NUM_DIV ($D 1 (SUC $I)) 2) 1")
          zero <- at(fact("NUM_SUB_ZERO"), "NUM_SUB 1 0 = 1")
          out <- rewriting(Seq(one, zero), goal)(byBeta).flatMap(gen(_, iv))
        } yield out
        rest <- for {
          goal <- prop(s"NUM_SUB ($later) (NUM_SUB 1 (SUC $K)) = $later")
          le <- numLinText(Seq.empty, s"1 <= SUC $K")
          none <- at(fact("NUM_SUB_EQ_ZERO"), s"1 <= SUC $K ==> NUM_SUB 1 (SUC $K) = 0").flatMap(mp(_, le))
          same <- at(fact("NUM_SUB_ZERO"), s"NUM_SUB ($later) 0 = $later")
          out <- rewriting(Seq(none, same), goal)(byBeta).flatMap(gen(_, kv, iv))
        } yield out
        both <- conj(first, rest)
        out <- introduce(predicate, witness, both).flatMap(gen(_, dv))
      } yield out
    }

    /** Row 1 of the table over the list: `!j. d 1 j = NUM_SUB (p (SUC j)) (p j)`, the list being increasing. */
    private def rowOne(step: Kernel.Thm, list: Kernel.Thm, first: Kernel.Thm): R[Kernel.Thm] = {
      val J = v("j")
      for {
        parts <- split(list)
        c <- clause(parts(1), J)
        one <- oneOfSuc
        opened <- stepAt(step, "0", J)
        succ <- numLinText(Seq.empty, s"$J + 1 = SUC $J")
        here <- at(first, s"$D 0 $J = $P $J")
        there <- at(first, s"$D 0 (SUC $J) = $P (SUC $J)")
        values <- rw(succ, opened).flatMap(rw(there, _)).flatMap(rw(here, _))
        le <- numLinText(Seq(c(1)), s"$P $J <= $P (SUC $J)")
        zero <- at(fact("NUM_SUB_EQ_ZERO"), s"$P $J <= $P (SUC $J) ==> NUM_SUB ($P $J) ($P (SUC $J)) = 0").flatMap(mp(_, le))
        equal <- numLinText(Seq(values, zero), s"$D (SUC 0) $J = NUM_SUB ($P (SUC $J)) ($P $J)").flatMap(rw(one, _))
        out <- gen(equal, jv)
      } yield out
    }

    /** `EvenGaps` for the table over the list, from `GILBREATH_PRIMES_GAPS` read through row 1. */
    private def evenGapsOf(rows: Kernel.Thm, gaps: Kernel.Thm): R[Kernel.Thm] = {
      val J = v("j"); val G = s"NUM_SUB ($P (SUC (SUC $J))) ($P (SUC $J))"
      for {
        row <- at(rows, s"$D 1 (SUC $J) = $G")
        here <- at(gaps, s"NUM_MOD ($G) 2 = 0 /\\ 2 <= $G")
        back <- Conv.sym(row)
        out <- rw(back, here).flatMap(gen(_, jv))
      } yield out
    }

    /** `r c + w c = r 0 + w 0` from the ladder's hypothesis: each stage moves `l s` from the window to the row. */
    private def sumOfStages(ladder: Kernel.Thm, C: String, R0: String, Ln: String, W: String, Bd: String): R[Kernel.Thm] =
      for {
        parts <- split(ladder)
        body <- prop(s"(s:num) <= $C ==> $R0 s + $W s = $R0 0 + $W 0")
        reach <- inductOn(sv, body)(
          base =>
            for {
              sides <- logic.destImp(base).toRight(NotOfForm("an implication", base))
              same <- numLin(Seq.empty, sides._2)
              out <- rules.disch(sides._1, same)
            } yield out,
          (ss, ih, _) => {
            val U = v(ss.name)
            for {
              bound <- assumed(s"SUC $U <= $C")
              within <- numLinText(Seq(bound._2), s"$U <= $C")
              lt <- numLinText(Seq(bound._2), s"$U < $C")
              prior <- mp(ih, within)
              here <- at(parts(1), s"$U < $C ==> ${stage(R0, Ln, W, Bd, U, F)}").flatMap(mp(_, lt)).flatMap(split)
              moved <- numLinText(Seq(prior, here(0), here(1)), s"$R0 (SUC $U) + $W (SUC $U) = $R0 0 + $W 0")
              out <- rules.disch(bound._1, moved)
            } yield out
          }
        )
        out <- numLinText(Seq.empty, s"$C <= $C").flatMap(c => at(reach, s"$C <= $C ==> $R0 $C + $W $C = $R0 0 + $W 0").flatMap(mp(_, c)))
      } yield out

    /**
     * The cone over the primes: a ladder for the normalised table from row 0 with window `n` puts
     * its entry `n` rows down, at most 1, which is half the entry at position 1 of row `n + 1` of
     * the table; that entry is even, so it is 0 or 2.
     */
    def primesCone: R[Kernel.Thm] =
      table { step =>
        val N = v("n"); val C = v("c"); val R0 = "(r:num->num)"; val Ln = "(l:num->num)"; val W = "(w:num->num)"; val Bd = v("D")
        val X = s"$D (SUC $N) 1"; val H = s"NUM_DIV ($X) 2"
        for {
          normalisedHere <- under("GILBREATH_NORMALISED")
          rowsHere <- underLemma("GILBREATH_EVEN_ROWS")
          held <- assumed(s"$Setting /\\ ${staged(C, R0, Ln, W, Bd, F)} /\\ $R0 0 = 0 /\\ $W 0 = $N /\\ 1 <= $N")
          (hT, h) = held
          parts <- split(h)
          gapsHere <- spec(known("GILBREATH_PRIMES_GAPS"), primesv).flatMap(mp(_, parts(0)))
          rows <- rowOne(step, parts(0), parts(1))
          evenGaps <- evenGapsOf(rows, gapsHere)
          stepF <- mp(normalisedHere, evenGaps).flatMap(spec(_, fv)).flatMap(mp(_, parts(2)))
          ladderF <- spec(known("GILBREATH_LADDER"), fv).flatMap(mp(_, stepF))
          // the ladder's three conjuncts are not parenthesised in the statement, so they come apart with the rest
          ladder <- conjs(parts(3), parts(4), parts(5))
          bound <- at(ladderF, s"${staged(C, R0, Ln, W, Bd, F)} ==> $F ($R0 $C + $W $C) 0 <= 1").flatMap(mp(_, ladder))
          total <- sumOfStages(ladder, C, R0, Ln, W, Bd)
          landed <- numLinText(Seq(total, parts(6), parts(7)), s"$R0 $C + $W $C = $N")
          atN <- rw(landed, bound)
          suc <- predecessor(parts(8), N).map(_._1)
          one <- oneOfSuc
          fs <- split(parts(2))
          value <- at(fs(1), s"$F (SUC (NUM_SUB $N 1)) 0 = NUM_DIV ($D (SUC (SUC (NUM_SUB $N 1))) (SUC 0)) 2")
            .flatMap(rw(suc, _)).flatMap(rw(one, _))
          half <- rw(value, atN)
          even <- mp(rowsHere, evenGaps).flatMap(at(_, s"NUM_MOD ($D (SUC $N) (SUC 0)) 2 = 0")).flatMap(rw(one, _))
          whole <- at(fact("NUM_DIV_MOD"), s"2 * $H + NUM_MOD ($X) 2 = $X").flatMap(rw(even, _))
          sides <- at(fact("NUM_LE_CASES"), s"$H <= 1 ==> $H < 1 \\/ $H = 1").flatMap(mp(_, half))
          goal <- prop(good(X))
          ends <- logic.destDisj(goal).toRight(NotOfForm("a disjunction", goal))
          zero <- for {
            lt <- assume(s"$H < 1")
            z <- numLinText(Seq(lt, whole), s"$X = 0")
            out <- rules.disjIntro1(ends._2, z)
          } yield out
          two_ <- for {
            e <- assume(s"$H = 1")
            t <- numLinText(Seq(e, whole), s"$X = 2")
            out <- rules.disjIntro2(ends._1, t)
          } yield out
          reached <- rules.disjElim(sides, zero, two_)
          out <- rules.disch(hT, reached).flatMap(gen(_, primesv, fv, cv, rv, lv, wv, boundv, nv))
        } yield out
      }

    /**
     * Every row from 1 to `R + 2` starts with 1 when the ladder certifies every window from 1 to
     * `R`: row 1 starts with `3 - 2`, row 2 because `d 1 1 = 5 - 3 = 2`, and each later row by
     * `GILBREATH_FRONT` and `GILBREATH_PRIMES_CONE`, by induction on the row.
     */
    def primesFront: R[Kernel.Thm] =
      table { step =>
        val Top = v("R"); val R0 = "(r:num->num)"; val Ln = "(l:num->num)"; val W = "(w:num->num)"; val C = v("c"); val Bd = v("D")
        for {
          coneHere <- under("GILBREATH_PRIMES_CONE")
          frontHere <- under("GILBREATH_FRONT")
          held <- assumed(s"$Setting /\\ (!n:num. 1 <= n /\\ n <= $Top ==> ${certified("n")})")
          (hT, h) = held
          parts <- split(h)
          list <- split(parts(0))
          start <- spec(known("GILBREATH_PRIMES_START"), primesv).flatMap(mp(_, parts(0))).flatMap(split)
          rows <- rowOne(step, parts(0), parts(1))
          one <- oneOfSuc
          twoOfSuc <- numLinText(Seq.empty, "SUC 1 = 2")
          firstEntry <- for {
            r <- at(rows, s"$D 1 0 = NUM_SUB ($P (SUC 0)) ($P 0)").flatMap(rw(one, _))
            le <- numLinText(Seq(start(0), list(0)), s"$P 0 <= $P 1")
            sub <- at(fact("NUM_SUB_ADD"), s"$P 0 <= $P 1 ==> NUM_SUB ($P 1) ($P 0) + $P 0 = $P 1").flatMap(mp(_, le))
            out <- numLinText(Seq(r, sub, start(0), list(0)), s"$D 1 0 = 1")
          } yield out
          secondEntry <- for {
            r <- at(rows, s"$D 1 1 = NUM_SUB ($P (SUC 1)) ($P 1)").flatMap(rw(twoOfSuc, _))
            le <- numLinText(Seq(start(0), start(1)), s"$P 1 <= $P 2")
            sub <- at(fact("NUM_SUB_ADD"), s"$P 1 <= $P 2 ==> NUM_SUB ($P 2) ($P 1) + $P 1 = $P 2").flatMap(mp(_, le))
            two_ <- numLinText(Seq(r, sub, start(0), start(1)), s"$D 1 1 = 2")
            zero <- prop(s"$D 1 1 = 0")
            out <- rules.disjIntro2(zero, two_)
          } yield out
          body <- prop(s"1 <= (k:num) /\\ k <= $Top + 2 ==> $D k 0 = 1")
          proved <- inductOn(kv, body)(
            base =>
              for {
                sides <- logic.destImp(base).toRight(NotOfForm("an implication", base))
                pre <- LogicError.lift(Kernel.assume(sides._1))
                reached <- numLin(Seq(pre), sides._2)
                out <- rules.disch(sides._1, reached)
              } yield out,
            (kk, ih, _) => {
              val K = v(kk.name)
              for {
                pre <- assumed(s"1 <= SUC $K /\\ SUC $K <= $Top + 2")
                target <- prop(s"$D (SUC $K) 0 = 1")
                reached <- cases(s"$K = 0")(
                  zero => rewriting(Seq(zero, one), target)(landsOn(firstEntry)),
                  nonzero =>
                    for {
                      positive <- positiveOf(nonzero, K)
                      inRange <- numLinText(Seq(positive, pre._2), s"1 <= $K /\\ $K <= $Top + 2")
                      here <- mp(ih, inRange)
                      iff <- at(frontHere, s"$D $K 0 = 1 ==> ($D (SUC $K) 0 = 1 = ${good(s"$D $K 1")})").flatMap(mp(_, here))
                      atLeastOne <- numLinText(Seq(positive), s"1 <= $K")
                      sides <- at(fact("NUM_LE_CASES"), s"1 <= $K ==> 1 < $K \\/ 1 = $K").flatMap(mp(_, atLeastOne))
                      wanted <- prop(good(s"$D $K 1"))
                      later <- for {
                        gt <- assume(s"1 < $K")
                        pred <- predecessor(atLeastOne, K)
                        (suc, back) = pred
                        prior = s"(NUM_SUB $K 1)"
                        range <- numLinText(Seq(gt, back, pre._2), s"1 <= $prior /\\ $prior <= $Top")
                        low <- rules.conjElim1(range)
                        certificate <- at(parts(3), s"1 <= $prior /\\ $prior <= $Top ==> ${certified(prior)}").flatMap(mp(_, range))
                        out <- chooseAll(certificate, Seq("c", "r", "l", "w", "D")) { body =>
                          for {
                            bs <- split(body)
                            hyp <- conjs(parts(0), parts(1), parts(2), bs(2), bs(3), bs(4), bs(0), bs(1), low)
                            cone <- at(coneHere,
                              s"$Setting /\\ ${staged(C, R0, Ln, W, Bd, F)} /\\ $R0 0 = 0 /\\ $W 0 = $prior /\\ 1 <= $prior ==> ${good(s"$D (SUC $prior) 1")}")
                              .flatMap(mp(_, hyp))
                            out <- rw(suc, cone)
                          } yield out
                        }
                      } yield out
                      atOne <- assume(s"1 = $K").flatMap(Conv.sym).flatMap(e => rewriting(Seq(e), wanted)(landsOn(secondEntry)))
                      entry <- rules.disjElim(sides, later, atOne)
                      out <- Conv.sym(iff).flatMap(s => LogicError.lift(Kernel.eqMp(s, entry)))
                    } yield out
                )
                out <- rules.disch(pre._1, reached)
              } yield out
            }
          )
          out <- rules.disch(hT, proved).flatMap(gen(_, primesv, fv, ceilingv))
        } yield out
      }

    /** The conjecture over the primes when the ladder certifies every window: `GILBREATH_PRIMES_FRONT` at `R = k`. */
    def primesConjecture: R[Kernel.Thm] =
      table { _ =>
        val X = v("x"); val N = v("n")
        for {
          frontHere <- under("GILBREATH_PRIMES_FRONT")
          held <- assumed(s"$Setting /\\ (!n:num. 1 <= n ==> ${certified("n")})")
          (hT, h) = held
          parts <- split(h)
          narrowed <- for {
            range <- assumed(s"1 <= $N /\\ $N <= $X")
            low <- rules.conjElim1(range._2)
            out <- at(parts(3), s"1 <= $N ==> ${certified(N)}").flatMap(mp(_, low))
            general <- rules.disch(range._1, out).flatMap(gen(_, nv))
          } yield general
          hyp <- conjs(parts(0), parts(1), parts(2), narrowed)
          front <- at(frontHere,
            s"$Setting /\\ (!n:num. 1 <= n /\\ n <= $X ==> ${certified("n")}) ==> (!k:num. 1 <= k /\\ k <= $X + 2 ==> $D k 0 = 1)")
            .flatMap(mp(_, hyp))
          positive <- assumed(s"0 < $X")
          range <- numLinText(Seq(positive._2), s"1 <= $X /\\ $X <= $X + 2")
          reached <- at(front, s"1 <= $X /\\ $X <= $X + 2 ==> $D $X 0 = 1").flatMap(mp(_, range))
          out <- rules.disch(positive._1, reached).flatMap(gen(_, xv)).flatMap(rules.disch(hT, _)).flatMap(gen(_, primesv, fv))
        } yield out
      }
  }
}
