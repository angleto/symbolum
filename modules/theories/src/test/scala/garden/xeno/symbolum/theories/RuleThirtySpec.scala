package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Rule 30 as `Complex` publishes it, checked where `ComplexSpec` does not reach.
 *
 * `ComplexSpec` compares every published fact with its text and counts the axioms. What it cannot
 * say is that the theorems are about Rule 30: each is an implication from equations, and an
 * implication says nothing about the automaton if the equations are not the automaton's, or if
 * nothing satisfies them. So two things are checked here. The existence theorems exhibit exactly the
 * equations the other theorems assume. And those equations, read in `Long`, are Rule 30: the frame
 * that moves one cell per step reproduces the centre column of a direct simulation, and the halving
 * equations hold of `n ^ ((n << 1) | (n << 2))`, whose orbit from 1 is the rows read as numbers.
 * The second half compares a transcription with the automaton, which is a reading and not a
 * theorem, over the ranges named.
 */
class RuleThirtySpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private lazy val complex = Chain.standard.complex
  private lazy val rules = complex.logic.rules
  private val Numbers = TyApp(Natural.TypeName, Nil)
  private val Rows = Type.fun(Numbers, Type.Bool)

  private def fact(name: String): Kernel.Thm = force(complex.fact(name))

  /** The body of `?v. P v` at `witness`. */
  private def opened(existential: Term, witness: Term): Term = force(for {
    predicate <- complex.logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
    applied <- LogicError.lift(Term.app(predicate, witness))
    root <- Conv.betaRoot(applied)
    body <- Term.destEq(root.conclusion).map(_._2).toRight(NotOfForm("an equation", root.conclusion))
  } yield body)

  "The theorems over rows" should "assume exactly the equations an evolution that exists satisfies" in {
    val run = Term.variable("run", Type.fun(Rows, Type.fun(Numbers, Type.fun(Numbers, Type.Bool))))
    val exhibited = opened(fact("RULE_THIRTY_EXISTS").conclusion, run)
    Seq("RULE_THIRTY_SHIFT", "RULE_THIRTY_CONE", "RULE_THIRTY_LEFT_PERMUTIVE", "RULE_THIRTY_WALSH_FORM", "RULE_THIRTY_BALANCED")
      .foreach { name =>
        withClue(s"$name: ") {
          val assumed = force(rules.specAll(fact(name), List(run)))
          complex.logic.destImp(assumed.conclusion).map(_._1) shouldBe Some(exhibited)
        }
      }
  }

  "The theorems over the naturals" should "assume exactly the equations a map and iterate that exist satisfy" in {
    val g = Term.variable("g", Type.fun(Type.Bool, Type.fun(Type.Bool, Type.fun(Numbers, Numbers))))
    val iterate = Term.variable("iterate", Type.fun(Numbers, Type.fun(Numbers, Numbers)))
    val exhibited = opened(opened(fact("RULE_THIRTY_MAP_EXISTS").conclusion, g), iterate)
    Seq("RULE_THIRTY_MAP_RESIDUES", "RULE_THIRTY_MAP_INJECTIVE", "RULE_THIRTY_MAP_ROW_LENGTH", "RULE_THIRTY_MAP_BALANCED",
      "RULE_THIRTY_MAP_WALSH_FORM").foreach { name =>
      withClue(s"$name: ") {
        val assumed = force(rules.specAll(fact(name), List(g, iterate)))
        complex.logic.destImp(assumed.conclusion).map(_._1) shouldBe Some(exhibited)
      }
    }
  }

  "The bridge" should "assume both, the rows' equations first" in {
    val run = Term.variable("run", Type.fun(Rows, Type.fun(Numbers, Type.fun(Numbers, Type.Bool))))
    val g = Term.variable("g", Type.fun(Type.Bool, Type.fun(Type.Bool, Type.fun(Numbers, Numbers))))
    val iterate = Term.variable("iterate", Type.fun(Numbers, Type.fun(Numbers, Numbers)))
    val rows = opened(fact("RULE_THIRTY_EXISTS").conclusion, run)
    val map = opened(opened(fact("RULE_THIRTY_MAP_EXISTS").conclusion, g), iterate)
    val assumed = force(rules.specAll(fact("RULE_THIRTY_BRIDGE"), List(run, g, iterate))).conclusion
    val (first, rest) = complex.logic.destImp(assumed).get
    first shouldBe rows
    complex.logic.destImp(rest).map(_._1) shouldBe Some(map)
  }

  private def rule(l: Boolean, c: Boolean, r: Boolean): Boolean = l ^ (c || r)

  /** The centre column of a direct simulation from one cell, in the automaton's own coordinates. */
  private def centre(steps: Int): Vector[Boolean] = {
    var row = Map(0 -> true)
    (0 until steps).map { t =>
      val cell = row.getOrElse(0, false)
      row = (-t - 1 to t + 1).map(x => x -> rule(row.getOrElse(x - 1, false), row.getOrElse(x, false), row.getOrElse(x + 1, false))).toMap
      cell
    }.toVector
  }

  "The rows' equations" should "be Rule 30 in a frame that moves one cell per step" in {
    val steps = 60
    val start = 2 * steps + 1
    // run x (SUC t) i = ~(run x t i = (run x t (i + 1) \/ run x t (i + 2))), from one cell at `steps`
    val frames = Iterator.iterate(Vector.tabulate(start)(_ == steps)) { r =>
      Vector.tabulate(r.length - 2)(i => r(i) != (r(i + 1) || r(i + 2)))
    }.take(steps).toVector
    (0 until steps).map(t => frames(t)(steps - t)) shouldBe centre(steps)
  }

  /** `g p q n` read off its two equations, by recursion on `n`; `g F F 0` is what they force. */
  private def g(p: Boolean, q: Boolean, n: Long): Long =
    if (n == 0) (if (p || q) 1L else 0L) + 2 * (if (p) 1L else 0L)
    else {
      val (m, odd) = (n / 2, n % 2 == 1)
      (if ((p || q) != odd) 1L else 0L) + 2 * g(odd, p, m)
    }

  "The map's equations" should "be n ^ ((n << 1) | (n << 2)), whose orbit from 1 is the rows" in {
    def f(n: Long): Long = n ^ ((n << 1) | (n << 2))
    for (p <- Seq(false, true); q <- Seq(false, true); m <- 0L until 2000L) {
      g(p, q, 2 * m) shouldBe (if (p || q) 1L else 0L) + 2 * g(false, p, m)
      g(p, q, 2 * m + 1) shouldBe (if (p || q) 0L else 1L) + 2 * g(true, p, m)
    }
    (0L until 5000L).foreach(n => g(false, false, n) shouldBe f(n))
    // bit t of F^t(1) is the centre column
    val orbit = Iterator.iterate(1L)(f).take(30).toVector
    orbit.indices.map(t => ((orbit(t) >> t) & 1L) == 1L) shouldBe centre(30)
  }
}
