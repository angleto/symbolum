package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Gilbreath's table as `Complex` publishes it, checked where `ComplexSpec` does not reach.
 *
 * `ComplexSpec` compares every published fact with its text and counts the axioms. What it cannot
 * say is that the theorems are about Gilbreath's table: each is an implication from one equation,
 * and it says nothing about the table if the equation is not the table's, or if nothing satisfies
 * it. So the existence theorem is checked to exhibit exactly the equation the other five assume, and
 * that equation, read off the published statement and evaluated in `Long`, is checked to be the
 * absolute difference of neighbours and to reproduce the table over the primes, where the
 * conjecture is known to hold for the rows computed. The second half compares a transcription with
 * the table, which is a reading and not a theorem, over the ranges named.
 */
class GilbreathSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private lazy val complex = Chain.standard.complex
  private lazy val rules = complex.logic.rules
  private val Numbers = TyApp(Natural.TypeName, Nil)
  private val Tables = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  private def fact(name: String): Kernel.Thm = force(complex.fact(name))
  private def term(text: String, ty: Type): Term = force(complex.term(text, ty))

  /** The body of `?v. P v` at `witness`. */
  private def opened(existential: Term, witness: Term): Term = force(for {
    predicate <- complex.logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
    applied <- LogicError.lift(Term.app(predicate, witness))
    root <- Conv.betaRoot(applied)
    body <- Term.destEq(root.conclusion).map(_._2).toRight(NotOfForm("an equation", root.conclusion))
  } yield body)

  private val d = Term.variable("d", Tables)

  /** The step equation `GILBREATH_EXISTS` exhibits, at a table `d` and a first row `r`. */
  private lazy val exhibited: Term = {
    val r = Term.variable("r", Type.fun(Numbers, Numbers))
    val atRow = force(rules.specAll(fact("GILBREATH_EXISTS"), List(r))).conclusion
    complex.logic.destConj(opened(atRow, d)).map(_._2).getOrElse(fail("not two clauses"))
  }

  "The theorems about the table" should "assume exactly the equation a table that exists satisfies" in {
    Seq("GILBREATH_FRONT", "GILBREATH_EVEN", "GILBREATH_HEAD", "GILBREATH_WINDOW", "GILBREATH_EQUIVALENT").foreach { name =>
      withClue(s"$name: ") {
        val assumed = force(rules.specAll(fact(name), List(d)))
        complex.logic.destImp(assumed.conclusion).map(_._1) shouldBe Some(exhibited)
      }
    }
  }

  /**
   * The step the published equation says, read off `GILBREATH_EXISTS` rather than transcribed: the
   * right side of `d (SUC k) i = ...` as a function of the entries at `i + 1` and `i`, with `+` and
   * the truncated subtraction evaluated. Anything else in it is refused.
   */
  private lazy val publishedStep: (Long, Long) => Long = {
    val (k, i) = (Term.variable("k", Numbers), Term.variable("i", Numbers))
    val atStep = force(rules.specAll(force(LogicError.lift(Kernel.assume(exhibited))), List(k, i))).conclusion
    val (lhs, rhs) = Term.destEq(atStep).getOrElse(fail("not an equation"))
    lhs shouldBe term("(d:num->num->num) (SUC (k:num)) (i:num)", Numbers)
    val right = term("(d:num->num->num) (k:num) ((i:num) + 1)", Numbers)
    val left = term("(d:num->num->num) (k:num) (i:num)", Numbers)
    (a: Long, b: Long) => {
      def value(t: Term): Long = t match {
        case _ if t == right => a
        case _ if t == left => b
        case App(App(Const(Peano.Addition, _), x), y) => value(x) + value(y)
        case App(App(Const(Peano.Subtraction, _), x), y) => math.max(0L, value(x) - value(y))
        case other => fail(s"not arithmetic the test reads: $other")
      }
      value(rhs)
    }
  }

  "The table's equation" should "be the absolute difference of the two entries above" in {
    val random = new scala.util.Random(65)
    val pairs = Seq((0L, 0L), (0L, 2L), (2L, 0L), (2L, 2L), (1L, 4L), (4L, 1L)) ++
      Seq.fill(200)((random.nextInt(1000).toLong, random.nextInt(1000).toLong))
    pairs.foreach { case (a, b) => withClue(s"($a, $b): ")(publishedStep(a, b) shouldBe math.abs(a - b)) }
  }

  private def primes(count: Int): Vector[Long] =
    Iterator.from(2).filter(n => (2 to math.sqrt(n.toDouble).toInt).forall(n % _ != 0)).map(_.toLong).take(count).toVector

  private def table(first: Vector[Long], rows: Int): Vector[Vector[Long]] =
    Iterator.iterate(first)(row => Vector.tabulate(row.length - 1)(i => publishedStep(row(i + 1), row(i)))).take(rows).toVector

  /**
   * Over the first 400 primes the published step gives Gilbreath's table, whose rows after the first
   * all start with 1 as far as computed, and position 1 holds 0 or 2 in each of them, which is what
   * `GILBREATH_EQUIVALENT` says the first fact amounts to. A first row whose second entry is 4 is the
   * control: the condition fails at row 1 and so does the 1 at row 2, so the reading can come out red.
   */
  "Over the primes" should "start every row after the first with 1, with 0 or 2 behind it" in {
    val rows = table(primes(400), 200)
    (1 until rows.length).foreach { k =>
      withClue(s"row $k: ") {
        rows(k)(0) shouldBe 1L
        Set(0L, 2L) should contain(rows(k)(1))
      }
    }
    val control = table(Vector(2L, 3L, 7L, 9L, 11L), 3)
    control(1)(0) shouldBe 1L
    control(1)(1) shouldBe 4L
    control(2)(0) should not be 1L
  }

  /**
   * `GILBREATH_HEAD` read over the primes: a head of 0s and 2s after the 1 shortens by at most one
   * per row. Measured as the length of the longest such head in each row, which over these rows is
   * never zero, so the comparison has something to compare.
   */
  it should "keep a head of 0s and 2s that shortens by at most one per row" in {
    val rows = table(primes(400), 200)
    def head(row: Vector[Long]): Int = row.drop(1).takeWhile(e => e == 0L || e == 2L).length
    val heads = rows.drop(1).map(head)
    heads.min should be > 0
    heads.indices.drop(1).foreach(k => withClue(s"row ${k + 1}: ")(heads(k) should be >= heads(k - 1) - 1))
  }
}
