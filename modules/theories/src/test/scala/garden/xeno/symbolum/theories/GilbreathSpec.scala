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

  /**
   * The six statements that assume no table's equation: the existence of a table and of its
   * normalised table, and the list of the primes.
   */
  private val NotOverATable = Set("GILBREATH_EXISTS", "GILBREATH_NORMALISED_EXISTS", "GILBREATH_PRIMES_EXIST", "GILBREATH_PRIMES_ALL",
    "GILBREATH_PRIMES_START", "GILBREATH_PRIMES_GAPS")

  "The theorems about the table" should "assume exactly the equation a table that exists satisfies" in {
    Gilbreath.Statements.map(_._1).filterNot(NotOverATable).foreach { name =>
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
   * them is `!x. x <= e ==> ...`, `!x. x < e ==> ...`, `!j. j + m <= e ==> ...`, or the same with
   * the bound as the last conjunct of the range, so it ranges over `0 .. e`; and the rest is `+`,
   * `*`, the truncated subtraction, the quotient and the remainder, `SUC`, the numerals, the table,
   * the tables and functions named, `NUM_PRIME` read by trial division, and the connectives.
   * Anything else is refused, so a statement that grew a shape the reading does not know comes out
   * red rather than read wrongly. A quantifier with no bound is read over `0 .. horizon` when a
   * horizon is given and refused otherwise: such a reading is of a finite piece of the statement,
   * and the comments where one is used say which piece.
   */
  private final case class Reading(
    table: Vector[Vector[Long]],
    numbers: Map[Term, Long],
    functions: Map[Term, Long => Long],
    depth: Int = 0,
    tables: Map[Term, (Long, Long) => Long] = Map.empty,
    horizon: Option[Long] = None
  ) {

    def value(t: Term): Long = t match {
      case _ if numbers.contains(t) => numbers(t)
      case Const(Natural.NumberZero, _) => 0L
      case Const(Peano.NumeralOne, _) => 1L
      case App(Const(Peano.NumeralBit0, _), x) => 2 * value(x)
      case App(Const(Peano.NumeralBit1, _), x) => 2 * value(x) + 1
      case App(Const(Natural.NumberSuccessor, _), x) => value(x) + 1
      case App(App(Const(Peano.Addition, _), x), y) => value(x) + value(y)
      case App(App(Const(Peano.Multiplication, _), x), y) => value(x) * value(y)
      case App(App(Const(Peano.Subtraction, _), x), y) => math.max(0L, value(x) - value(y))
      case App(App(Const(Modular.DivName, _), x), y) if value(y) > 0 => value(x) / value(y)
      case App(App(Const(Modular.ModName, _), x), y) if value(y) > 0 => value(x) % value(y)
      case App(App(f, row), position) if f == d =>
        val (k, i) = (value(row).toInt, value(position).toInt)
        if (k < table.length && i < table(k).length) table(k)(i) else fail(s"outside the table: row $k, position $i")
      case App(App(f, row), position) if tables.contains(f) => tables(f)(value(row), value(position))
      case App(f, x) if functions.contains(f) => functions(f)(value(x))
      case other => fail(s"not a number the reading knows: $other")
    }

    def holds(t: Term): Boolean = {
      val logic = complex.logic
      logic.destConj(t).map { case (a, b) => holds(a) && holds(b) }
        .orElse(logic.destDisj(t).map { case (a, b) => holds(a) || holds(b) })
        .orElse(logic.destImp(t).map { case (a, b) => !holds(a) || holds(b) })
        .orElse(logic.destNot(t).map(a => !holds(a)))
        .orElse(logic.destForallPredicate(t).map(forall))
        .getOrElse(t match {
          case App(App(Const(Peano.NonStrictOrder, _), x), y) => value(x) <= value(y)
          case App(App(Const(Peano.StrictOrder, _), x), y) => value(x) < value(y)
          case App(Const(Modular.PrimeName, _), x) => prime(value(x))
          case _ if Term.destEq(t).isDefined =>
            val (x, y) = Term.destEq(t).get
            value(x) == value(y)
          case other => fail(s"not a proposition the reading knows: $other")
        })
    }

    /**
     * The upper end of a range: the right side of its comparison, or of its last conjunct's, when
     * the left side mentions `x` and the right side does not.
     */
    private def upper(range: Term, x: FVar): Option[Long] = range match {
      case App(App(Const(Peano.NonStrictOrder | Peano.StrictOrder, _), l), e)
          if Term.freeVariables(l).contains(x) && !Term.freeVariables(e).contains(x) => Some(value(e))
      case _ => complex.logic.destConj(range).flatMap { case (_, last) => upper(last, x) }
    }

    private def forall(predicate: Term): Boolean = {
      // one name per depth, so a quantifier inside another never reuses the name of the one outside
      val x = Term.variable(s"x$depth", Numbers)
      val body = force(LogicError.lift(Term.app(predicate, x)).flatMap(a => Term.betaReduce(a).toRight(NotOfForm("a redex", a))))
      val inner = (v: Long) => copy(numbers = numbers + (x -> v), depth = depth + 1)
      complex.logic.destImp(body).flatMap { case (range, rest) => upper(range, x).map((range, rest, _)) } match {
        case Some((range, rest, bound)) => (0L to bound).forall(v => !inner(v).holds(range) || inner(v).holds(rest))
        case None =>
          val top = horizon.getOrElse(fail(s"not a bounded quantifier, and no horizon: $body"))
          (0L to top).forall(v => inner(v).holds(body))
      }
    }
  }

  /** Primality by trial division, written here and not read off the library. */
  private def prime(n: Long): Boolean = n >= 2 && (2L to math.sqrt(n.toDouble).toLong).forall(n % _ != 0)

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

  /* ------------------------------------------------------------ the primes */

  private val PrimesFacts = Vector(
    "GILBREATH_PRIMES_EXIST", "GILBREATH_PRIMES_ALL", "GILBREATH_PRIMES_START", "GILBREATH_PRIMES_GAPS",
    "GILBREATH_NORMALISED", "GILBREATH_NORMALISED_EXISTS", "GILBREATH_PRIMES_CONE", "GILBREATH_PRIMES_FRONT", "GILBREATH_PRIMES_CONJECTURE"
  )

  /**
   * The same three axioms, measured on 2026-11-11 for each of the nine but one: the list of the
   * primes is built by the recursion theorem with each entry chosen by `select`, which is the
   * choice axiom spent directly, from Euclid's theorem, the least number principle and a
   * propositional step, and no comparison in it is settled over the reals; so
   * `GILBREATH_PRIMES_EXIST` rests on choice and infinity alone. The other eight settle comparisons
   * with `Linarith` over the reals, which are cuts, as the six above do. Fewer axioms is a stronger
   * statement, and the assertion is the measured set rather than a bound, so a change that makes the
   * existence spend eta goes red here. `GILBREATH_NORMALISED_EXISTS` settles `1 <= SUC k` with
   * `Linarith`, so it is among the eight on all three.
   */
  "The table over the primes" should "rest on choice, eta and infinity, the list of the primes on choice and infinity alone" in {
    val chain = Chain.standard
    val (choice, eta, infinity) = (
      force(chain.classical.axiom(Classical.Choice)).conclusion,
      force(chain.classical.axiom(Classical.Eta)).conclusion,
      force(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    PrimesFacts.foreach { name =>
      val theorem = fact(name)
      val expected = if (name == "GILBREATH_PRIMES_EXIST") Set(choice, infinity) else Set(choice, eta, infinity)
      withClue(s"$name: ")(Derivation.axiomsOf(theorem) shouldBe expected)
      info(s"$name: ${Derivation.size(theorem)} inferences")
    }
  }

  private val Rows = Type.fun(Numbers, Numbers)
  private val (pv, fv, cv, rv, lfv, wv) = (Term.variable("p", Rows), Term.variable("f", Tables), Term.variable("c", Numbers),
    Term.variable("r", Rows), Term.variable("l", Rows), Term.variable("w", Rows))

  /** The first 400 primes, 0-indexed from `p 0 = 2`, and Gilbreath's table over them, 200 rows. */
  private lazy val listed: Vector[Long] = primes(400)
  private lazy val overPrimes: Vector[Vector[Long]] = table(listed, 200)

  /**
   * The normalised table written from the informal account rather than from the statement: with
   * the primes 1-indexed, `b_0(j) = (p_(j+2) - p_(j+1)) / 2 - 1` and `b_r(j) = d_(r+1)(j) / 2`,
   * where `d_1` is the first row of differences, and `f(k, i) = b_k(i + 1)`. `unshifted` is
   * `b_k(i)` itself.
   */
  private def normalisedOf(rows: Vector[Vector[Long]], first: Vector[Long], shift: Int): (Long, Long) => Long = {
    def b(r: Int, j: Int): Long =
      if (r == 0) math.max(0L, (first(j + 1) - first(j)) / 2 - 1)
      else rows(r + 1)(j) / 2
    (k: Long, i: Long) => b(k.toInt, i.toInt + shift)
  }

  /**
   * `GILBREATH_NORMALISED` read over the primes: its hypothesis on row 1, the two equations that
   * describe the normalised table, and the table's equation on it, each against the table written
   * from the account. Read over rows and positions 0 to 60, the horizon, which keeps every entry it
   * touches inside the 200 rows computed. The controls: the unshifted table satisfies the equations
   * of `f` nowhere it differs, and fails the table's equation, every failure at position 0, which
   * is the first gap, 3 - 2, being odd; and a first row with an odd gap after the first fails the
   * hypothesis.
   */
  "The normalised table" should "satisfy the table's equation over the primes, and the unshifted one should not" in {
    val statement = openedFact("GILBREATH_NORMALISED")
    val (gaps, rest) = complex.logic.destImp(statement).getOrElse(fail("not an implication"))
    val opened = force(rules.specAll(force(LogicError.lift(Kernel.assume(rest))), List(fv))).conclusion
    val (described, equation) = complex.logic.destImp(opened).getOrElse(fail("not an implication"))
    val shifted = normalisedOf(overPrimes, listed, 1)
    val unshifted = normalisedOf(overPrimes, listed, 0)
    val horizon = Some(60L)
    val reading = Reading(overPrimes, Map.empty, Map.empty, tables = Map(fv -> shifted), horizon = horizon)
    reading.holds(gaps) shouldBe true
    reading.holds(described) shouldBe true
    reading.holds(equation) shouldBe true
    val control = reading.copy(tables = Map(fv -> unshifted))
    control.holds(equation) shouldBe false
    val failures = for {
      k <- 0 until 60; i <- 0 until 60
      if unshifted(k + 1, i) != math.abs(unshifted(k, i + 1) - unshifted(k, i))
    } yield (k, i)
    failures should not be empty
    failures.map(_._2).distinct shouldBe Vector(0)
    info(s"the unshifted table fails the equation at ${failures.size} of 3600 entries, rows and positions 0 to 59, all at position 0")
    val odd = listed.updated(3, 8L)
    reading.copy(table = table(odd, 200)).holds(gaps) shouldBe false
  }

  /** The ladder for `f` from row 0 with window `n`, each stage of Chase's `L` at the bound it has reached, or nothing if one does not fit. */
  private def ladderFor(f: (Long, Long) => Long, n: Int): Option[(Long, Vector[Int], Vector[Int], Vector[Int])] = {
    def row(k: Int): Vector[Long] = Vector.tabulate(n + 1)(i => f(k.toLong, i.toLong))
    val top = row(0).max
    val (rs, ws, ls) = (scala.collection.mutable.ArrayBuffer(0), scala.collection.mutable.ArrayBuffer(n), scala.collection.mutable.ArrayBuffer.empty[Int])
    var fits = true
    while (fits && math.max(0L, top - ls.length) > 1) {
      val s = ls.length
      val l = longestBlock(row(rs(s)), ws(s), top - s.toLong)
      if (l > ws(s)) fits = false else { ls += l; rs += rs(s) + l; ws += ws(s) - l }
    }
    if (fits) Some((top, rs.toVector, ls.toVector, ws.toVector)) else None
  }

  /**
   * `GILBREATH_PRIMES_CONE` read over the primes, at the ladders built here for the table written
   * from the account, from row 0 with each window `n` from 1 to 40: the hypothesis must hold and so
   * must the conclusion, which names the entry at position 1 of row `n + 1`. The unbounded
   * quantifiers of the list and of the two equations of `f` are read over 0 to 60. The controls are
   * the ladders one row short, the last stage with a positive `L` given `L - 1` rows and the window
   * the row it saves, which must not certify; and the unshifted table in place of `f`, which must
   * not be the normalised table.
   *
   * Measured on 2026-11-11: a ladder fits every window from 1 to 119 over these primes, checked in
   * Python before the proof; the first windows need no stage, the bound being at most 1 already.
   */
  "Over the primes" should "read GILBREATH_PRIMES_CONE at the ladders that fit, and refuse a ladder one row short" in {
    val statement = openedFact("GILBREATH_PRIMES_CONE", pv, fv, cv, rv, lfv, wv, bv, nv)
    val (hypothesis, conclusion) = complex.logic.destImp(statement).getOrElse(fail("not an implication"))
    val shifted = normalisedOf(overPrimes, listed, 1)
    val unshifted = normalisedOf(overPrimes, listed, 0)
    val atPrimes = (x: Long) => listed(x.toInt)
    var read = 0
    var short = 0
    (1 to 40).foreach { n =>
      val (top, rs, ls, ws) = ladderFor(shifted, n).getOrElse(fail(s"no ladder at window $n"))
      val pad = (f: Vector[Int]) => (x: Long) => f.lift(x.toInt).getOrElse(0).toLong
      val reading = Reading(overPrimes, Map(cv -> ls.length.toLong, bv -> top, nv -> n.toLong),
        Map(pv -> atPrimes, rv -> pad(rs), lfv -> pad(ls), wv -> pad(ws)), tables = Map(fv -> shifted), horizon = Some(60L))
      withClue(s"window $n, stages $ls: ") {
        reading.holds(hypothesis) shouldBe true
        reading.holds(conclusion) shouldBe true
        Set(0L, 2L) should contain(overPrimes(n + 1)(1))
        reading.copy(tables = Map(fv -> unshifted)).holds(hypothesis) shouldBe false
        val last = ls.lastIndexWhere(_ > 0)
        if (last >= 0) {
          val fewer = ls.updated(last, ls(last) - 1)
          val rows = rs.indices.map(s => if (s > last) rs(s) - 1 else rs(s)).toVector
          val windows = ws.indices.map(s => if (s > last) ws(s) + 1 else ws(s)).toVector
          reading.copy(functions = Map(pv -> atPrimes, rv -> pad(rows), lfv -> pad(fewer), wv -> pad(windows))).holds(hypothesis) shouldBe false
          short += 1
        }
      }
      read += 1
    }
    info(s"$read windows read, $short ladders one row short refused")
    short should be > 10
  }
}
