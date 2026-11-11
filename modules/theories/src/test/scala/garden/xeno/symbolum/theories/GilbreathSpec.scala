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
    Gilbreath.Statements.map(_._1).filterNot(_ == "GILBREATH_EXISTS").foreach { name =>
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

  /* ------------------------------------------------------------ the bound and the ladder */

  private val Ladder = Vector("GILBREATH_BELOW", "GILBREATH_BELOW_ROWS", "GILBREATH_SHRINK", "GILBREATH_DROP", "GILBREATH_RUNG", "GILBREATH_LADDER")

  /**
   * Choice, eta and infinity, measured on 2026-11-11 for each of the six: the naturals are built on
   * infinity, and every comparison is settled by `Linarith` over the reals, which are cuts and rest
   * on choice and eta. Nothing is asserted on the way, so the chain's own list of axioms is the
   * comparison too.
   */
  "The bound and the ladder" should "rest on choice, eta and infinity, and add no axiom" in {
    val chain = Chain.standard
    val expected = Set(
      force(chain.classical.axiom(Classical.Choice)).conclusion,
      force(chain.classical.axiom(Classical.Eta)).conclusion,
      force(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    Ladder.foreach { name =>
      val theorem = fact(name)
      withClue(s"$name: ")(Derivation.axiomsOf(theorem) shouldBe expected)
      info(s"$name: ${Derivation.size(theorem)} inferences")
    }
    complex.theory.axioms.toSet shouldBe expected
  }

  /**
   * The published statements read by an evaluator rather than by their text: every quantifier in
   * them is `!x. x <= e ==> ...`, `!x. x < e ==> ...` or `!j. j + m <= e ==> ...`, so it ranges over
   * `0 .. e`, and the rest is `+`, the truncated subtraction, `SUC`, the table and the three
   * functions of the ladder. Anything else is refused, so a statement that grew a shape the reading
   * does not know comes out red rather than read wrongly.
   */
  private final case class Reading(table: Vector[Vector[Long]], numbers: Map[Term, Long], functions: Map[Term, Long => Long], depth: Int = 0) {

    def value(t: Term): Long = t match {
      case _ if numbers.contains(t) => numbers(t)
      case Const(Natural.NumberZero, _) => 0L
      case Const(Peano.NumeralOne, _) => 1L
      case App(Const(Natural.NumberSuccessor, _), x) => value(x) + 1
      case App(App(Const(Peano.Addition, _), x), y) => value(x) + value(y)
      case App(App(Const(Peano.Subtraction, _), x), y) => math.max(0L, value(x) - value(y))
      case App(App(f, row), position) if f == d =>
        val (k, i) = (value(row).toInt, value(position).toInt)
        if (k < table.length && i < table(k).length) table(k)(i) else fail(s"outside the table: row $k, position $i")
      case App(f, x) if functions.contains(f) => functions(f)(value(x))
      case other => fail(s"not a number the reading knows: $other")
    }

    def holds(t: Term): Boolean = {
      val logic = complex.logic
      logic.destConj(t).map { case (a, b) => holds(a) && holds(b) }
        .orElse(logic.destDisj(t).map { case (a, b) => holds(a) || holds(b) })
        .orElse(logic.destImp(t).map { case (a, b) => !holds(a) || holds(b) })
        .orElse(logic.destForallPredicate(t).map(forall))
        .getOrElse(t match {
          case App(App(Const(Peano.NonStrictOrder, _), x), y) => value(x) <= value(y)
          case App(App(Const(Peano.StrictOrder, _), x), y) => value(x) < value(y)
          case _ if Term.destEq(t).isDefined =>
            val (x, y) = Term.destEq(t).get
            value(x) == value(y)
          case other => fail(s"not a proposition the reading knows: $other")
        })
    }

    private def forall(predicate: Term): Boolean = {
      // one name per depth, so a quantifier inside another never reuses the name of the one outside
      val x = Term.variable(s"x$depth", Numbers)
      val body = force(LogicError.lift(Term.app(predicate, x)).flatMap(a => Term.betaReduce(a).toRight(NotOfForm("a redex", a))))
      val (range, rest) = complex.logic.destImp(body).getOrElse(fail(s"not a bounded quantifier: $body"))
      val bound = range match {
        case App(App(Const(Peano.NonStrictOrder | Peano.StrictOrder, _), _), e) if !Term.freeVariables(e).contains(x) => value(e)
        case other => fail(s"not a bound the reading knows: $other")
      }
      (0L to bound).forall(v => { val inner = copy(numbers = numbers + (x -> v), depth = depth + 1); !inner.holds(range) || inner.holds(rest) })
    }
  }

  /** The body of a published fact after the table's equation, opened at the variables named. */
  private def openedFact(name: String, variables: FVar*): Term = {
    val afterTable = complex.logic.destImp(force(rules.specAll(fact(name), List(d))).conclusion).map(_._2).getOrElse(fail("no equation"))
    force(rules.specAll(force(LogicError.lift(Kernel.assume(afterTable))), variables.toList)).conclusion
  }

  private val (lv, kv, nv, bv) = (Term.variable("L", Numbers), Term.variable("k", Numbers), Term.variable("n", Numbers), Term.variable("D", Numbers))

  private def randomTable(random: scala.util.Random, length: Int, top: Int): Vector[Vector[Long]] = {
    val first = Vector.fill(length)(random.nextInt(4) match {
      case 0 => 0L
      case 1 => top.toLong
      case _ => random.nextInt(top + 1).toLong
    })
    table(first, length)
  }

  /** The longest run of entries in `{0, bound}` that holds `bound`, inside positions 0 to `n`: Chase's `L`. */
  private def longestBlock(row: Vector[Long], n: Int, bound: Long): Int =
    if (bound == 0L) 0
    else
      row.take(n + 1).foldLeft((0, 0, false)) { case ((best, length, top), e) =>
        if (e == 0L || e == bound) {
          val (l, t) = (length + 1, top || e == bound)
          (if (t) math.max(best, l) else best, l, t)
        } else (best, 0, false)
      }._1

  /**
   * `GILBREATH_RUNG`'s hypothesis and conclusion against the informal ones, each written here
   * without the statement: the window holds no entry above `D`, the longest run in `{0, D}` holding
   * a `D` is at most `L`, and `L` rows down the window `L` shorter holds nothing above `D - 1`. The
   * other end is the control: "one row too few", the conclusion read at row `k + L - 1` over a
   * window one longer, which is false, and must come out false somewhere or the reading is not
   * reading the row.
   *
   * 3000 tables of 2 to 13 entries with bounds 0 to 5, every `L` and the `k = 0` row: measured on
   * 2026-11-11 at 22 623 cases in 1.5 seconds, the hypothesis holding in 5558 and the control false
   * in 213. The count is chosen against the suite's wall clock rather than for power: the random
   * check run before the proof, in Python over the same shapes, put 271 901 cases to the statement
   * and found the same control false in 20 734, and the kernel's proof is what settles the claim.
   */
  it should "read GILBREATH_RUNG as Chase's Lemma 3.2, and the row it names as the one that holds" in {
    val statement = openedFact("GILBREATH_RUNG", lv, kv, nv, bv)
    val (hypothesis, conclusion) = complex.logic.destImp(statement).getOrElse(fail("not an implication"))
    val (window, blocks) = complex.logic.destConj(hypothesis).getOrElse(fail("not two hypotheses"))
    val random = new scala.util.Random(538)
    var cases = 0
    var held = 0
    var control = 0
    (1 to 3000).foreach { _ =>
      val length = 2 + random.nextInt(12)
      val top = random.nextInt(6)
      val rows = randomTable(random, length, top)
      (0 until length).foreach { l =>
        val n = length - 1 - l
        val bound = random.nextInt(top + 1).toLong
        val reading = Reading(rows, Map(lv -> l.toLong, kv -> 0L, nv -> n.toLong, bv -> bound), Map.empty)
        val (inWindow, inBlocks) = (reading.holds(window), reading.holds(blocks))
        withClue(s"row ${rows(0)}, L = $l, D = $bound: ") {
          inWindow shouldBe rows(0).take(n + l + 1).forall(_ <= bound)
          inBlocks shouldBe (longestBlock(rows(0), n + l, bound) <= l)
          if (inWindow && inBlocks) {
            held += 1
            reading.holds(conclusion) shouldBe true
            rows(l).take(n + 1).forall(_ <= math.max(0L, bound - 1)) shouldBe true
            if (l >= 1 && !reading.copy(numbers = reading.numbers ++ Map(lv -> (l - 1).toLong, nv -> (n + 1).toLong)).holds(conclusion)) control += 1
          }
        }
        cases += 1
      }
    }
    info(s"$cases cases, the hypothesis holding in $held, one row too few false in $control")
    held should be > cases / 10
    control should be > 0
  }

  /**
   * `GILBREATH_LADDER` read the same way, at ladders built here from Chase's `L` at each stage, the
   * bound lowered by one per stage until it is at most 1, and the window shortened by `L`. Its
   * hypothesis must hold on every ladder built so, and the entry it names must be at most 1. The
   * control stops one stage early, at a bound of 2: there the last hypothesis fails, and the entry
   * is above 1 somewhere, so that hypothesis is not idle.
   *
   * 1500 first rows of 2 to 25 entries with bounds 1 to 5, measured on 2026-11-11 at 1263 ladders
   * built and 1406 stopped early, 96 of those with the entry above 1, in half a second.
   */
  it should "read GILBREATH_LADDER as the counted ladder, the last bound doing work" in {
    val (cv, rv, lfv, wv) = (Term.variable("c", Numbers), Term.variable("r", Type.fun(Numbers, Numbers)),
      Term.variable("l", Type.fun(Numbers, Numbers)), Term.variable("w", Type.fun(Numbers, Numbers)))
    val statement = openedFact("GILBREATH_LADDER", cv, rv, lfv, wv, bv)
    val (hypothesis, conclusion) = complex.logic.destImp(statement).getOrElse(fail("not an implication"))
    val random = new scala.util.Random(917)
    var built = 0
    var controls = 0
    var above = 0
    (1 to 1500).foreach { _ =>
      val length = 2 + random.nextInt(24)
      val top = 1 + random.nextInt(5)
      val rows = randomTable(random, length, top)
      Seq(1L, 2L).foreach { stop =>
        // stages while the bound is above `stop`, each of Chase's L, as long as the window allows
        val (rs, ws, ls) = (scala.collection.mutable.ArrayBuffer(0), scala.collection.mutable.ArrayBuffer(length - 1), scala.collection.mutable.ArrayBuffer.empty[Int])
        var fits = true
        while (fits && math.max(0L, top - ls.length) > stop) {
          val s = ls.length
          val l = longestBlock(rows(rs(s)), ws(s), top - s.toLong)
          if (l > ws(s)) fits = false else { ls += l; rs += rs(s) + l; ws += ws(s) - l }
        }
        if (fits) {
          val c = ls.length
          val pad = (f: scala.collection.mutable.ArrayBuffer[Int]) => (x: Long) => f.lift(x.toInt).getOrElse(0).toLong
          val reading = Reading(rows, Map(cv -> c.toLong, bv -> top.toLong), Map(rv -> pad(rs), lfv -> pad(ls), wv -> pad(ws)))
          val entry = rows(rs(c) + ws(c))(0)
          withClue(s"row ${rows(0)}, stages $ls, stopping at $stop: ") {
            if (stop == 1L) {
              built += 1
              reading.holds(hypothesis) shouldBe true
              reading.holds(conclusion) shouldBe true
              entry should be <= 1L
            } else {
              controls += 1
              if (math.max(0L, top - c.toLong) > 1L) reading.holds(hypothesis) shouldBe false
              if (entry > 1L) above += 1
            }
          }
        }
      }
    }
    info(s"$built ladders built, $controls stopped one stage early, the entry above 1 in $above")
    built should be > 100
    above should be > 0
  }
}
