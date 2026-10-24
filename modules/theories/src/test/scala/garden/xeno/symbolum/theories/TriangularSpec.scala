package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Triangular maps as `Complex` publishes them, checked where `ComplexSpec` does not reach.
 *
 * `ComplexSpec` compares every published fact with its text and counts the axioms. What it cannot
 * say is that the hypothesis the theorems assume is a property some maps have and others lack: a
 * hypothesis that held of nothing would make every theorem here vacuous, and one that held of
 * everything would make the instances say nothing. So the hypothesis is read off the published
 * `TRIANGULAR_INJECTIVE` and evaluated, as the term it is, on maps computed in `Long`: it has to
 * hold of `3 n + 1`, `n + 1`, Rule 30's map and `n XOR 2 n`, the last of which the kernel proves
 * triangular as `PASCAL_MAP_TRIANGULAR`, and fail of `n * n`, `n / 2` and `2 n`. The evaluation is
 * over the ranges named, which is a reading and not a theorem.
 */
class TriangularSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private lazy val complex = Chain.standard.complex
  private lazy val logic = complex.logic

  private def fact(name: String): Kernel.Thm = force(complex.fact(name))

  /** The value of a closed arithmetic term under `env`, with `map` the value of the one function variable. */
  private def value(t: Term, env: Map[FVar, Long], map: Long => Long): Long = t match {
    case v: FVar => env.getOrElse(v, fail(s"unbound $v"))
    case Const(Natural.NumberZero, _) => 0L
    case Const(Peano.NumeralOne, _) => 1L
    case App(Const("SUC", _), x) => value(x, env, map) + 1
    case App(Const(Peano.NumeralBit0, _), x) => 2 * value(x, env, map)
    case App(Const(Peano.NumeralBit1, _), x) => 2 * value(x, env, map) + 1
    case App(App(Const(Peano.Addition, _), x), y) => value(x, env, map) + value(y, env, map)
    case App(App(Const(Peano.Multiplication, _), x), y) => value(x, env, map) * value(y, env, map)
    case App(App(Const(Peano.Exponentiation, _), x), y) => math.pow(value(x, env, map).toDouble, value(y, env, map).toDouble).toLong
    case App(App(Const(Modular.ModName, _), x), y) => value(x, env, map) % value(y, env, map)
    case App(_: FVar, x) => map(value(x, env, map))
    case other => fail(s"not arithmetic the test reads: $other")
  }

  /** The truth of a proposition without quantifiers under `env`. */
  private def holds(t: Term, env: Map[FVar, Long], map: Long => Long): Boolean =
    logic.destConj(t).map { case (a, b) => holds(a, env, map) && holds(b, env, map) }
      .orElse(logic.destImp(t).map { case (a, b) => !holds(a, env, map) || holds(b, env, map) })
      .orElse(logic.destNot(t).map(a => !holds(a, env, map)))
      .orElse(Term.destEq(t).map { case (a, b) => value(a, env, map) == value(b, env, map) })
      .getOrElse(fail(s"not a proposition the test reads: $t"))

  /** A clause `!k m n. body`, checked for `k` up to `bound` and `m`, `n` below `2^(k + 2)`. */
  private def clauseHolds(clause: Term, map: Long => Long, env: Map[FVar, Long], bound: Int): Boolean = {
    val (vars, body) = force(Logic.stripForall(clause))
    vars.size shouldBe 3
    val Vector(k, m, n) = vars: @unchecked
    (0 to bound).forall { kk =>
      val below = 1L << (kk + 2)
      (0L until below).forall(mm => (0L until below).forall(nn => holds(body, env ++ Map(k -> kk.toLong, m -> mm, n -> nn), map)))
    }
  }

  /** The hypothesis `TRIANGULAR_INJECTIVE` assumes, as its two clauses. */
  private lazy val hypothesis: (FVar, Term, Term) = {
    val (vars, body) = force(Logic.stripForall(fact("TRIANGULAR_INJECTIVE").conclusion))
    val assumed = logic.destImp(body).map(_._1).getOrElse(fail("not an implication"))
    val (first, second) = logic.destConj(assumed).getOrElse(fail("not two clauses"))
    (vars.head, first, second)
  }

  private def triangular(map: Long => Long): (Boolean, Boolean) = {
    val (_, first, second) = hypothesis
    (clauseHolds(first, map, Map.empty, 4), clauseHolds(second, map, Map.empty, 4))
  }

  private val ruleThirty: Long => Long = n => n ^ ((2 * n) | (4 * n))

  "The hypothesis the theorems assume" should "hold of 3n + 1, n + 1, Rule 30's map and n XOR 2n" in {
    Seq[(String, Long => Long)]("3n + 1" -> (n => 3 * n + 1), "n + 1" -> (n => n + 1), "Rule 30" -> ruleThirty, "n XOR 2n" -> (n => n ^ (2 * n)))
      .foreach { case (name, map) => withClue(s"$name: ")(triangular(map) shouldBe ((true, true))) }
  }

  /**
   * The controls, one failing each clause and one failing the second only: halving reads bit `k + 1`
   * into bit `k`, which is where Collatz's own map leaves the class; doubling keeps agreement but
   * moves the flipped bit up; squaring keeps agreement and never flips bit 1.
   */
  it should "fail of n / 2, of 2n and of n * n, each at the clause it breaks" in {
    triangular(n => n / 2)._1 shouldBe false
    triangular(n => 2 * n) shouldBe ((true, false))
    triangular(n => n * n) shouldBe ((true, false))
  }

  /** `TRIANGULAR_AFFINE` at `a = 3, b = 1` is the hypothesis at `3 n + 1`, and at `a = 2` its premise fails and so does the map. */
  "TRIANGULAR_AFFINE" should "be about a n + b, and need a odd" in {
    val (vars, body) = force(Logic.stripForall(fact("TRIANGULAR_AFFINE").conclusion))
    val Vector(a, b) = vars: @unchecked
    val (odd, claim) = logic.destImp(body).getOrElse(fail("not an implication"))
    val (first, second) = logic.destConj(claim).getOrElse(fail("not two clauses"))
    val none: Long => Long = _ => fail("no function variable here")
    holds(odd, Map(a -> 3L, b -> 1L), none) shouldBe true
    clauseHolds(first, none, Map(a -> 3L, b -> 1L), 5) shouldBe true
    clauseHolds(second, none, Map(a -> 3L, b -> 1L), 5) shouldBe true
    holds(odd, Map(a -> 2L, b -> 1L), none) shouldBe false
    clauseHolds(second, none, Map(a -> 2L, b -> 1L), 5) shouldBe false
  }

  /**
   * `TRIANGULAR_PERIOD` read over the maps the hypothesis was evaluated on: the period of the orbit
   * of 1 modulo `2^k` is, from one `k` to the next, the same or twice. Over these ranges `3 n + 1`
   * doubles from `k = 2` on and the two others stall for long stretches, so both cases occur.
   */
  "The period of an orbit" should "stay or double from one power of two to the next" in {
    def period(map: Long => Long, k: Int): Int = {
      val m = 1L << k
      Iterator.iterate(map(1) % m)(x => map(x) % m).indexWhere(_ == 1 % m) + 1
    }
    Seq[(String, Long => Long)]("3n + 1" -> (n => 3 * n + 1), "Rule 30" -> ruleThirty, "n XOR 2n" -> (n => n ^ (2 * n))).foreach { case (name, map) =>
      val periods = (1 to 16).map(period(map, _))
      withClue(s"$name, $periods: ") {
        periods.zip(periods.tail).foreach { case (p, q) => Set(p, 2 * p) should contain(q) }
      }
    }
  }
}
