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
 * `docs/adr/0065` is the decision; Mycelium note 917b3939, section 12, is the account with the
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
 * == What they do not say ==
 *
 * That the head never runs out, which is the conjecture. The measurements in the note place that
 * question in the gaps modulo 4: a large value meeting the head is absorbed when the head keeps
 * producing 2s, and the kernel has nothing on how the gaps between primes are distributed.
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
      s"$D 1 0 = 1 ==> ((!k:num. 0 < k ==> $D k 0 = 1) = (!k:num. 0 < k ==> ${good(s"$D k 1")}))")
  )

  private val Order: Vector[(String, Proofs => R[Kernel.Thm])] = Vector(
    "GILBREATH_EXISTS" -> (_.exists),
    "GILBREATH_FRONT" -> (_.front),
    "GILBREATH_EVEN" -> (_.even),
    "GILBREATH_HEAD" -> (_.head),
    "GILBREATH_WINDOW" -> (_.window),
    "GILBREATH_EQUIVALENT" -> (_.equivalent)
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
  }
}
