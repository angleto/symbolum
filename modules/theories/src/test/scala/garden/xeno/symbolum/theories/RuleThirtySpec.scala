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

  private def term(text: String, ty: Type): Term = force(complex.term(text, ty))
  private val Runs = Type.fun(Rows, Type.fun(Numbers, Type.fun(Numbers, Type.Bool)))
  private val Steps = Type.fun(Type.Bool, Type.fun(Type.Bool, Type.fun(Numbers, Numbers)))
  private val Iterates = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  /**
   * A proposition built from atoms by `~`, `\\/` and `=` between propositions, evaluated where every
   * atom has a value. Anything else is refused, so a statement written with another connective
   * fails here rather than being read as something it is not.
   */
  private def truth(t: Term, atoms: Map[Term, Boolean]): Boolean =
    atoms.get(t) match {
      case Some(b) => b
      case None =>
        complex.logic.destNot(t).map(a => !truth(a, atoms))
          .orElse(complex.logic.destDisj(t).map { case (a, b) => truth(a, atoms) || truth(b, atoms) })
          .orElse(Term.destEq(t).collect { case (a, b) if Term.typeOf(a) == Type.Bool => truth(a, atoms) == truth(b, atoms) })
          .getOrElse(fail(s"not a connective over the atoms: $t"))
    }

  /**
   * The step the published equations say, read off `RULE_THIRTY_EXISTS` rather than transcribed:
   * the right side of `run x (SUC t) i = ...` as a function of the cells at `i`, `i + 1`, `i + 2`.
   */
  private lazy val publishedStep: (Boolean, Boolean, Boolean) => Boolean = {
    val run = Term.variable("run", Runs)
    val equations = opened(fact("RULE_THIRTY_EXISTS").conclusion, run)
    val step = complex.logic.destConj(equations).map(_._2).getOrElse(fail("not two equations"))
    val (x, t, i) = (Term.variable("x", Rows), Term.variable("t", Numbers), Term.variable("i", Numbers))
    val atStep = force(rules.specAll(force(LogicError.lift(Kernel.assume(step))), List(x, t, i))).conclusion
    val rhs = Term.destEq(atStep).map(_._2).getOrElse(fail("not an equation"))
    def cell(offset: String) = term(s"(run:(num->bool)->num->num->bool) (x:num->bool) (t:num) ($offset)", Type.Bool)
    val (l, c, r) = (cell("i:num"), cell("(i:num) + 1"), cell("(i:num) + 2"))
    (a: Boolean, b: Boolean, d: Boolean) => truth(rhs, Map(l -> a, c -> b, r -> d))
  }

  "The rows' equations" should "say Rule 30 in all eight cases, with the cell itself on the left" in {
    for (l <- Seq(false, true); c <- Seq(false, true); r <- Seq(false, true))
      withClue(s"($l, $c, $r): ")(publishedStep(l, c, r) shouldBe rule(l, c, r))
  }

  /**
   * The published step, in its frame, against a direct simulation of Rule 30 from a row that is not
   * symmetric: cell `(t, i)` of the frame is cell `i + t` of the automaton. The centre column of a
   * single cell would not do, because it is the same for Rule 30 and for its mirror Rule 86.
   */
  it should "be Rule 30 in a frame that moves one cell per step, row for row" in {
    val width = 200
    val steps = 60
    val random = new scala.util.Random(30)
    val start = Vector.fill(width)(random.nextBoolean())
    val frames = Iterator.iterate(start)(r => Vector.tabulate(r.length - 2)(i => publishedStep(r(i), r(i + 1), r(i + 2)))).take(steps).toVector
    val direct = Iterator.iterate(start)(r => Vector.tabulate(width)(x =>
      rule(r.lift(x - 1).getOrElse(false), r(x), r.lift(x + 1).getOrElse(false)))).take(steps).toVector
    for (t <- 0 until steps; i <- 0 until width - 2 * t) withClue(s"cell ($t, $i): ")(frames(t)(i) shouldBe direct(t)(i + t))
    def mirror(l: Boolean, c: Boolean, r: Boolean): Boolean = rule(r, c, l)
    val mirrored = Iterator.iterate(start)(r => Vector.tabulate(r.length - 2)(i => mirror(r(i), r(i + 1), r(i + 2)))).take(steps).toVector
    (0 until steps).exists(t => (0 until width - 2 * t).exists(i => mirrored(t)(i) != direct(t)(i + t))) shouldBe true
  }

  /**
   * The map's two equations read off `RULE_THIRTY_MAP_EXISTS` and interpreted: a numeral, `+`, `*`,
   * `COND` and the connectives evaluated, and an application of `g` evaluated by the equations
   * again. At `m = 0` the even equation reads `g F F 0 = c + 2 * g F F 0`, which has the one
   * natural solution `0` exactly when `c` is `0`, and that is checked rather than assumed.
   */
  private lazy val publishedMap: (Boolean, Boolean, Long) => Long = {
    val (g, iterate) = (Term.variable("g", Steps), Term.variable("iterate", Iterates))
    val equations = opened(opened(fact("RULE_THIRTY_MAP_EXISTS").conclusion, g), iterate)
    val clauses = Iterator.unfold(Option(equations))(_.map(e => complex.logic.destConj(e) match {
      case Some((a, b)) => (a, Some(b))
      case None => (e, None)
    })).toVector
    val (p, q, m) = (Term.variable("p", Type.Bool), Term.variable("q", Type.Bool), Term.variable("m", Numbers))
    def rhs(clause: Term) = Term.destEq(force(rules.specAll(force(LogicError.lift(Kernel.assume(clause))), List(p, q, m))).conclusion)
      .getOrElse(fail("not an equation"))
    val (evenLhs, evenRhs) = rhs(clauses(0))
    val (oddLhs, oddRhs) = rhs(clauses(1))
    evenLhs shouldBe term("(g:bool->bool->num->num) (p:bool) (q:bool) (2 * (m:num))", Numbers)
    oddLhs shouldBe term("(g:bool->bool->num->num) (p:bool) (q:bool) (2 * (m:num) + 1)", Numbers)
    val (zero, one, two) = (term("0:num", Numbers), term("1:num", Numbers), term("2:num", Numbers))
    val (truthT, falseT) = (term("T", Type.Bool), term("F", Type.Bool))
    lazy val self: (Boolean, Boolean, Long) => Long = (pv, qv, n) => {
      val bools: Map[Term, Boolean] = Map(p -> pv, q -> qv, truthT -> true, falseT -> false)
      def num(t: Term): Long = t match {
        case _ if t == zero => 0L
        case _ if t == one => 1L
        case _ if t == two => 2L
        case _ if t == m => n / 2
        case App(App(App(Const(Classical.Conditional, _), b), y), z) => if (truth(b, bools)) num(y) else num(z)
        case App(App(Const(Peano.Addition, _), a), b) => num(a) + num(b)
        case App(App(Const(Peano.Multiplication, _), a), b) => num(a) * num(b)
        case App(App(App(f, b1), b2), arg) if f == g =>
          val (x1, x2, x3) = (truth(b1, bools), truth(b2, bools), num(arg))
          if (x3 == 0 && n == 0 && !x1 && !x2) 0L else self(x1, x2, x3)
        case other => fail(s"not arithmetic the test reads: $other")
      }
      if (n == 0 && !pv && !qv) {
        // The right side at m = 0 with g F F 0 read as 0 must give back 0: the fixed point holds.
        num(evenRhs) shouldBe 0L
        0L
      } else num(if (n % 2 == 0) evenRhs else oddRhs)
    }
    self
  }

  "The map's equations" should "be n ^ ((n << 1) | (n << 2)), whose orbit from 1 is the rows" in {
    def f(n: Long): Long = n ^ ((n << 1) | (n << 2))
    (0L until 5000L).foreach(n => withClue(s"F($n): ")(publishedMap(false, false, n) shouldBe f(n)))
    val orbit = Iterator.iterate(1L)(f).take(30).toVector
    orbit.indices.map(t => ((orbit(t) >> t) & 1L) == 1L) shouldBe centre(30)
  }
}
