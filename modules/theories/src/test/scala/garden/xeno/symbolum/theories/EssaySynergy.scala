package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Synergy, for the essay on the use and harm of history for language models
 * (`thinktank/utitlita_e_danno`), derived in the kernel: two pieces of information each worth
 * nothing alone and everything together.
 *
 * Two bits `a` and `b`, uniform and independent, are the state `y = 2 a + b` of four, read back as
 * `a = NUM_DIV y 2` and `b = NUM_MOD y 2`, each with probability `1/4`. The reader has two actions
 * and is paid one for naming `a XOR b`, which is `NUM_MOD (a + b) 2`, and nothing otherwise. Four
 * experiments, each value a theorem with no hypothesis:
 *
 *  - [[EssaySynergy.Nothing]], one signal that says nothing: `1/2`;
 *  - [[EssaySynergy.OnlyA]], the signal `a`: `1/2`;
 *  - [[EssaySynergy.OnlyB]], the signal `b`: `1/2`;
 *  - [[EssaySynergy.Both]], the signal `y`, so both bits: `1`.
 *
 * And `XOR_SYNERGY` puts the point in one statement: each bit alone is worth what no signal is
 * worth, and the two together are worth more. Blackwell's order says nothing here, because `a`
 * alone is not a garbling of `b` alone nor the other way round; it is the case where information
 * is not a quantity that adds.
 *
 * Every value is computed rather than argued: the sums over four states and at most four signals
 * are opened by their recurrence, the maximum over the two actions by its own, and what is left is
 * ground. The quotients and remainders by two of the four states and of the four sums of two bits
 * are `NUM_DIV_MOD_UNIQUE` at an identity of numerals `NaturalLinear` settles, and each conditional
 * on two numerals is decided by reflexivity or by `Successor.distinct`.
 */
private[theories] object EssaySynergy {

  type R[A] = Either[LogicError, A]

  val Prior: String = "(\\y:num. (1:real) / 4)"
  val Utility: String = "(\\a:num. \\y:num. COND (a = NUM_MOD (NUM_DIV y 2 + NUM_MOD y 2) 2) (1:real) 0)"

  /**
   * An experiment on the four states: how many signals, the channel as a term, its row at a state
   * and a signal written as text, and the same row as a number, which only chooses which side of a
   * maximum to prove and is checked by the kernel like everything else.
   */
  final case class Experiment(name: String, signals: Int, channel: String, row: (String, String) => String, weight: (Int, Int) => Int)

  val Nothing: Experiment = Experiment("XOR_NOTHING", 1, "(\\y:num. \\s:num. (1:real))", (_, _) => "(1:real)", (_, _) => 1)
  val OnlyA: Experiment = Experiment("XOR_ONLY_A", 2, "(\\y:num. \\s:num. COND (s = NUM_DIV y 2) (1:real) 0)",
    (y, s) => s"COND ($s = NUM_DIV $y 2) (1:real) 0", (y, s) => if (s == y / 2) 1 else 0)
  val OnlyB: Experiment = Experiment("XOR_ONLY_B", 2, "(\\y:num. \\s:num. COND (s = NUM_MOD y 2) (1:real) 0)",
    (y, s) => s"COND ($s = NUM_MOD $y 2) (1:real) 0", (y, s) => if (s == y % 2) 1 else 0)
  val Both: Experiment = Experiment("XOR_BOTH", 4, "(\\y:num. \\s:num. COND (s = y) (1:real) 0)",
    (y, s) => s"COND ($s = $y) (1:real) 0", (y, s) => if (s == y) 1 else 0)

  def value(e: Experiment): String = s"VALUE 4 ${e.signals} 1 $Prior ${e.channel} $Utility"

  /** Each experiment with the value the statement prints. */
  val Values: Vector[(Experiment, String)] =
    Vector(Nothing -> "(1:real) / 2", OnlyA -> "(1:real) / 2", OnlyB -> "(1:real) / 2", Both -> "(1:real)")

  /** Each bit alone is worth what nothing is worth, and both are worth more: three claims, derived as written. */
  val Apart: Vector[String] =
    Vector(s"${value(OnlyA)} = ${value(Nothing)}", s"${value(OnlyB)} = ${value(Nothing)}", s"${value(Nothing)} < ${value(Both)}")
  val Synergy: String = Apart.mkString(" /\\ ")

  val Statements: Vector[(String, String)] =
    Values.map { case (e, v) => e.name -> s"${value(e)} = $v" } :+ ("XOR_SYNERGY" -> Synergy)

  def derive(decision: Decision, successor: Successor, natural: NaturalLinear): R[Map[String, Kernel.Thm]] = {
    val shared = new EssaySteps(decision, successor)
    import shared.*
    import shared.steps.*
    import shared.steps.kit.*

    def n(i: Int): String = s"($i:num)"
    def suc(k: Int): String = if (k == 0) "(0:num)" else s"(SUC ${suc(k - 1)})"
    def all[A](items: Seq[R[A]]): R[Vector[A]] =
      items.foldLeft[R[Vector[A]]](Right(Vector.empty))((acc, x) => acc.flatMap(done => x.map(done :+ _)))

    /** `|- SUC i = i + 1` for `i < 3`, which puts the successor forms the recurrences leave back into numerals. */
    val numerals: R[Vector[Kernel.Thm]] = all((0 until 3).map { i =>
      for {
        here <- nm(i.toString).flatMap(successor.spell)
        next <- nm((i + 1).toString).flatMap(successor.spell)
        sucT <- term("SUC", Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Natural.TypeName, Nil)))
        lifted <- Conv.apTerm(sucT, here)
        back <- Conv.sym(next)
        out <- trans(lifted, back)
      } yield out
    })

    /** `|- Sum (\i. body i) count = 0 + body 0 + ... + body (count - 1)`, with the indices as numerals. */
    def unrolled(binder: String, body: String => String, count: Int): R[Kernel.Thm] = {
      val f = s"(\\$binder:num. ${body(binder)})"
      for {
        sumF <- prop0(s"Sum $f")
        spelled <- nm(count.toString).flatMap(successor.spell)
        lifted <- Conv.apTerm(sumF, spelled)
        recurrences <- all((1 to count).map(k => at(fact("SUM_SUC"), s"Sum $f ${suc(k)} = Sum $f ${suc(k - 1)} + ${body(suc(k - 1))}")))
        empty <- at(fact("SUM_ZERO"), s"Sum $f 0 = 0")
        opened <- (recurrences.reverse :+ empty).foldLeft[R[Kernel.Thm]](Right(lifted))((acc, e) => acc.flatMap(rw(e, _)))
        back <- numerals
        out <- back.foldLeft[R[Kernel.Thm]](Right(opened))((acc, e) => acc.flatMap(rw(e, _)))
      } yield out
    }

    /** `NUM_DIV sum 2 = q` and `NUM_MOD sum 2 = r`, at a term `sum` of numerals whose value is `total`. */
    def byTwo(sum: String, total: Int): R[Seq[Kernel.Thm]] = {
      val (q, r) = (n(total / 2), n(total % 2))
      for {
        eq <- prop(s"$sum = 2 * $q + $r").flatMap(natural(Seq.empty, _))
        lt <- prop(s"$r < 2").flatMap(natural(Seq.empty, _))
        both <- conj(eq, lt)
        unique <- at(fact("NUM_DIV_MOD_UNIQUE"),
          s"$sum = 2 * $q + $r /\\ $r < 2 ==> $q = NUM_DIV ($sum) 2 /\\ $r = NUM_MOD ($sum) 2").flatMap(mp(_, both))
        parts <- split(unique)
        div <- Conv.sym(parts(0))
        mod <- Conv.sym(parts(1))
      } yield Seq(div, mod)
    }

    /** `|- !x z. COND (i = j) x z = x`, or `= z`, at two numerals below four. */
    def decided(i: Int, j: Int): R[Kernel.Thm] =
      for {
        x <- prop0("x:real").flatMap { case v: FVar => Right(v); case o => Left(NotOfForm("a variable", o)) }
        z <- prop0("z:real").flatMap { case v: FVar => Right(v); case o => Left(NotOfForm("a variable", o)) }
        left <- nm(i.toString)
        right <- nm(j.toString)
        at <- if (i == j) condOn(s"${n(i)} = ${n(j)}", "(x:real)", "(z:real)", Kernel.refl(left))
              else successor.distinct(left, right).flatMap(condOff(s"${n(i)} = ${n(j)}", "(x:real)", "(z:real)", _))
        out <- rules.genAll(at, List(x, z))
      } yield out

    /** Every ground fact a term of the four experiments meets once its indices are numerals. */
    val ground: R[Vector[Kernel.Thm]] =
      for {
        states <- all((0 until 4).map(y => byTwo(n(y), y)))
        parities <- all(for { p <- 0 until 2; q <- 0 until 2 } yield byTwo(s"${n(p)} + ${n(q)}", p + q))
        conds <- all(for { i <- 0 until 4; j <- 0 until 4 } yield decided(i, j))
      } yield states.flatten ++ parities.flatten ++ conds

    def u(a: String, y: String): String = s"COND ($a = NUM_MOD (NUM_DIV $y 2 + NUM_MOD $y 2) 2) (1:real) 0"
    def body(e: Experiment, a: String, s: String)(y: String): String = s"(1:real) / 4 * ${e.row(y, s)} * ${u(a, y)}"
    def inner(e: Experiment, a: String, s: String): String = s"Sum (\\y:num. ${body(e, a, s)("y")}) 4"
    def rowOf(e: Experiment, s: String): String = s"(\\a:num. ${inner(e, "a", s)})"
    def best(e: Experiment, s: String): String = s"Maximum ${rowOf(e, s)} 1"

    def count(e: Experiment, a: Int, s: Int): Int =
      (0 until 4).map(y => e.weight(y, s) * (if (a == (y / 2 + y % 2) % 2) 1 else 0)).sum
    def quarters(c: Int): String = s"(($c:real) / 4)"

    /** `|- inner a s = c / 4`, the sum over the four states opened and every conditional in it decided. */
    def innerValue(e: Experiment, a: Int, s: Int): R[Kernel.Thm] =
      for {
        opened <- unrolled("y", body(e, n(a), n(s)), 4)
        facts <- ground
        goal <- prop(s"${inner(e, n(a), n(s))} = ${quarters(count(e, a, s))}")
        out <- exact(opened +: facts, Seq.empty, goal)
      } yield out

    /** `|- Maximum (\a. inner a s) 1 = c / 4`: the larger of the two actions, by the recurrence at `SUC 0`. */
    def bestValue(e: Experiment, s: Int): R[Kernel.Thm] = {
      val f = rowOf(e, n(s))
      val (c0, c1) = (count(e, 0, s), count(e, 1, s))
      for {
        maxF <- prop0(s"Maximum $f")
        one <- fact("NUM_ONE_SUC")
        lifted <- Conv.apTerm(maxF, one)
        step <- at(k(Decision.MaximumAtSuccessor), s"Maximum $f (SUC 0) = max (Maximum $f 0) (${inner(e, "(SUC 0)", n(s))})")
        base <- at(k(Decision.MaximumAtZero), s"Maximum $f 0 = ${inner(e, n(0), n(s))}")
        top <- trans(lifted, step).flatMap(rw(base, _))
        back <- numerals
        read <- back.foldLeft[R[Kernel.Thm]](Right(top))((acc, eq) => acc.flatMap(rw(eq, _)))
        x0 <- innerValue(e, 0, s)
        x1 <- innerValue(e, 1, s)
        larger <-
          if (c1 <= c0) prop(s"${quarters(c1)} <= ${quarters(c0)}").flatMap(exact(Seq.empty, Seq.empty, _)).flatMap(maxLeft(quarters(c0), quarters(c1), _))
          else prop(s"${quarters(c0)} <= ${quarters(c1)}").flatMap(exact(Seq.empty, Seq.empty, _)).flatMap(maxRight(quarters(c0), quarters(c1), _))
        goal <- prop(s"${best(e, n(s))} = ${quarters(c0 max c1)}")
        out <- exact(Seq(read, x0, x1, larger), Seq.empty, goal)
      } yield out
    }

    /** `|- VALUE ... = total`: the sum over the signals opened and each maximum put in. */
    def valueOf(e: Experiment, total: String): R[Kernel.Thm] =
      for {
        whole <- unfold(Decision.ValueName, "4:num", s"${e.signals}:num", "1:num", Prior, e.channel, Utility)
        outer <- unrolled("s", s => best(e, s), e.signals)
        bests <- all((0 until e.signals).map(bestValue(e, _)))
        // composed before anything is rewritten: where the row does not read the signal, a maximum's
        // value would otherwise rewrite under the sum's binder and the unrolling would no longer match
        opened <- trans(whole, outer)
        goal <- prop(s"${value(e)} = $total")
        out <- exact(opened +: bests, Seq.empty, goal)
      } yield out

    for {
      values <- all(Values.map { case (e, v) => valueOf(e, v).map(e.name -> _) })
      named = values.toMap
      // each claim is closed from the four values alone, so a claim the numbers do not make is refused
      claims <- all(Apart.map(text => prop(text).flatMap(exact(values.map(_._2), Seq.empty, _))))
      synergy <- claims.init.foldRight[R[Kernel.Thm]](Right(claims.last))((c, acc) => acc.flatMap(conj(c, _)))
    } yield named + ("XOR_SYNERGY" -> synergy)
  }
}
