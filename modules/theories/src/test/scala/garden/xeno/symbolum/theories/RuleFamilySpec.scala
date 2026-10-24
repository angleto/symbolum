package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The family of rules `l XOR h(c, r)` as `Complex` publishes it, checked where `ComplexSpec` does not
 * reach.
 *
 * `ComplexSpec` compares every published fact with its text and counts the axioms. What it cannot say
 * is that the theorems are about the family: each is an implication from equations, and it says
 * nothing about a rule if the equations are not that rule's, or if nothing satisfies them. So the
 * equations are read off the published existence theorems and interpreted in `Long`, for all sixteen
 * rules `h`: where `h F F` is false they are the map whose bit `j` is bit `j` of `n` XOR `h` of the two
 * bits below, and where it is true the even equation at 0 has no natural solution, which is why
 * `RULE_FAMILY_EXISTS` asks for it. Then the two instances are shown to be the family's equations at
 * their rule, term for term, and `PASCAL_MAP_BITS` is read on `n XOR 2 n`, where it holds, and on Rule
 * 30's map, where it must not. The readings are over the ranges named, which is a reading and not a
 * theorem.
 */
class RuleFamilySpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private lazy val complex = Chain.standard.complex
  private lazy val logic = complex.logic
  private lazy val rules = logic.rules
  private val Numbers = TyApp(Natural.TypeName, Nil)
  private val Rules = Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool))
  private val Steps = Type.fun(Type.Bool, Type.fun(Type.Bool, Type.fun(Numbers, Numbers)))
  private val Iterates = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  private val h = Term.variable("h", Rules)
  private val g = Term.variable("g", Steps)

  private def fact(name: String): Kernel.Thm = force(complex.fact(name))
  private def term(text: String, ty: Type): Term = force(complex.term(text, ty))

  /** The body of `?v. P v` at `witness`. */
  private def opened(existential: Term, witness: Term): Term = force(for {
    predicate <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
    applied <- LogicError.lift(Term.app(predicate, witness))
    root <- Conv.betaRoot(applied)
    body <- Term.destEq(root.conclusion).map(_._2).toRight(NotOfForm("an equation", root.conclusion))
  } yield body)

  /** The antecedent of `name` at `args`, beta-normal. */
  private def assumedBy(name: String, args: Term*): Term = {
    val inst = force(rules.specAll(fact(name), args.toList))
    val normal = force(Conv.betaNormalise(inst.conclusion)).conclusion
    val body = Term.destEq(normal).map(_._2).getOrElse(fail("not an equation"))
    logic.destImp(body).map(_._1).getOrElse(fail(s"$name is not an implication"))
  }

  /** The family's equations, as `RULE_FAMILY_EXISTS` exhibits them at `h` and `g`. */
  private lazy val family: Term = {
    val atH = force(rules.specAll(fact("RULE_FAMILY_EXISTS"), List(h))).conclusion
    val existential = logic.destImp(atH).map(_._2).getOrElse(fail("not an implication"))
    opened(existential, g)
  }

  "The theorems over the family" should "assume exactly the equations a member that exists satisfies" in {
    Seq("RULE_FAMILY_STEP", "RULE_FAMILY_TRIANGULAR", "RULE_FAMILY_BIT_ZERO", "RULE_FAMILY_BIT_SUC", "RULE_FAMILY_BIT_RULE")
      .foreach(name => withClue(s"$name: ")(assumedBy(name, h, g) shouldBe family))
  }

  "The theorems over the Pascal map" should "assume exactly the equations a Pascal map that exists satisfies" in {
    val exhibited = opened(fact("PASCAL_MAP_EXISTS").conclusion, g)
    Seq("PASCAL_MAP_TRIANGULAR", "PASCAL_MAP_BITS").foreach(name => withClue(s"$name: ")(assumedBy(name, g) shouldBe exhibited))
  }

  /**
   * Both instances are the family at their rule, term for term: the family's equations with `h`
   * instantiated and beta-reduced are the Pascal map's, and they are the first two of Rule 30's.
   */
  "The two instances" should "be the family's equations at their rule" in {
    val first = term("\\p:bool. \\q:bool. p", Rules)
    val or = term("\\p:bool. \\q:bool. p \\/ q", Rules)
    assumedBy("RULE_FAMILY_TRIANGULAR", first, g) shouldBe opened(fact("PASCAL_MAP_EXISTS").conclusion, g)
    val iterate = Term.variable("iterate", Iterates)
    val ruleThirty = opened(opened(fact("RULE_THIRTY_MAP_EXISTS").conclusion, g), iterate)
    val (evenOdd, _) = logic.destConj(ruleThirty).flatMap { case (a, rest) => logic.destConj(rest).map { case (b, more) => (force(logic.mkConj(a, b)), more) } }
      .getOrElse(fail("not four equations"))
    assumedBy("RULE_FAMILY_TRIANGULAR", or, g) shouldBe evenOdd
  }

  /**
   * A proposition built from atoms by `~`, `\\/` and `=` between propositions, and from `rule`
   * applied as `h a b`, evaluated where every atom has a value. Anything else is refused.
   */
  private def truth(t: Term, atoms: Map[Term, Boolean], rule: (Boolean, Boolean) => Boolean): Boolean =
    atoms.get(t) match {
      case Some(b) => b
      case None => t match {
        case App(App(f, a), b) if f == h => rule(truth(a, atoms, rule), truth(b, atoms, rule))
        case _ =>
          logic.destNot(t).map(a => !truth(a, atoms, rule))
            .orElse(logic.destDisj(t).map { case (a, b) => truth(a, atoms, rule) || truth(b, atoms, rule) })
            .orElse(Term.destEq(t).collect { case (a, b) if Term.typeOf(a) == Type.Bool => truth(a, atoms, rule) == truth(b, atoms, rule) })
            .getOrElse(fail(s"not a connective over the atoms: $t"))
      }
    }

  private val (p, q, m) = (Term.variable("p", Type.Bool), Term.variable("q", Type.Bool), Term.variable("m", Numbers))

  /** The right sides of the even and the odd equation in `equations`, whose left sides are checked. */
  private def sides(equations: Term): (Term, Term) = {
    val (even, odd) = logic.destConj(equations).getOrElse(fail("not two equations"))
    def rhs(clause: Term) = Term.destEq(force(rules.specAll(force(LogicError.lift(Kernel.assume(clause))), List(p, q, m))).conclusion)
      .getOrElse(fail("not an equation"))
    val (evenLhs, evenRhs) = rhs(even)
    val (oddLhs, oddRhs) = rhs(odd)
    evenLhs shouldBe term("(g:bool->bool->num->num) (p:bool) (q:bool) (2 * (m:num))", Numbers)
    oddLhs shouldBe term("(g:bool->bool->num->num) (p:bool) (q:bool) (2 * (m:num) + 1)", Numbers)
    (evenRhs, oddRhs)
  }

  /**
   * A right side evaluated at `p`, `q` and `n` (so `m` is `n / 2`), with `g` applied evaluated by
   * `recurse`: a numeral, `+`, `*`, `COND` and the connectives, nothing else.
   */
  private def evaluate(rhs: Term, pv: Boolean, qv: Boolean, n: Long, rule: (Boolean, Boolean) => Boolean,
                       recurse: (Boolean, Boolean, Long) => Long): Long = {
    val (zero, one, two) = (term("0:num", Numbers), term("1:num", Numbers), term("2:num", Numbers))
    val bools: Map[Term, Boolean] = Map(p -> pv, q -> qv, term("T", Type.Bool) -> true, term("F", Type.Bool) -> false)
    def num(t: Term): Long = t match {
      case _ if t == zero => 0L
      case _ if t == one => 1L
      case _ if t == two => 2L
      case _ if t == m => n / 2
      case App(App(App(Const(Classical.Conditional, _), b), y), z) => if (truth(b, bools, rule)) num(y) else num(z)
      case App(App(Const(Peano.Addition, _), a), b) => num(a) + num(b)
      case App(App(Const(Peano.Multiplication, _), a), b) => num(a) * num(b)
      case App(App(App(f, b1), b2), arg) if f == g => recurse(truth(b1, bools, rule), truth(b2, bools, rule), num(arg))
      case other => fail(s"not arithmetic the test reads: $other")
    }
    num(rhs)
  }

  /**
   * The map the equations define, where they define one: `g F F 0` is the fixed point of
   * `x = c + 2 x`, which is 0 when `c` is and does not exist otherwise.
   */
  private def mapOf(equations: Term, rule: (Boolean, Boolean) => Boolean): Long => Long = {
    val (evenRhs, oddRhs) = sides(equations)
    lazy val self: (Boolean, Boolean, Long) => Long = (pv, qv, n) =>
      if (n == 0 && !pv && !qv) {
        evaluate(evenRhs, false, false, 0, rule, (a, b, x) => if (!a && !b && x == 0) 0L else self(a, b, x)) shouldBe 0L
        0L
      } else evaluate(if (n % 2 == 0) evenRhs else oddRhs, pv, qv, n, rule, self)
    n => self(false, false, n)
  }

  /** Bit `j` of the value is bit `j` of `n` XOR `rule` of bits `j - 1` and `j - 2`. */
  private def expected(rule: (Boolean, Boolean) => Boolean)(n: Long): Long = {
    def b(j: Int): Boolean = j >= 0 && ((n >> j) & 1L) == 1L
    (0 until 64 - java.lang.Long.numberOfLeadingZeros(n) + 3).foldLeft(0L) { (acc, j) =>
      if (b(j) ^ rule(b(j - 1), b(j - 2))) acc | (1L << j) else acc
    }
  }

  private val allRules: Seq[(Int, (Boolean, Boolean) => Boolean)] =
    (0 until 16).map(code => code -> ((c: Boolean, r: Boolean) => ((code >> ((if (c) 2 else 0) + (if (r) 1 else 0))) & 1) == 1))

  "The family's equations" should "be, for each of the eight rules keeping white white, n with each bit XORed with the rule below" in {
    val keeping = allRules.filterNot { case (_, rule) => rule(false, false) }
    keeping.size shouldBe 8
    keeping.foreach { case (code, rule) =>
      val map = mapOf(family, rule)
      (0L until 2048L).foreach(n => withClue(s"rule $code at $n: ")(map(n) shouldBe expected(rule)(n)))
    }
  }

  /**
   * Where `h F F` holds, `g F F 0 = 1 + 2 * g F F 0`, which no natural satisfies: the theorems over
   * the family are vacuous for those rules, and `RULE_FAMILY_EXISTS` is right to exclude them.
   */
  it should "have no map at all for the eight rules that turn white black" in {
    val (evenRhs, _) = sides(family)
    val turning = allRules.filter { case (_, rule) => rule(false, false) }
    turning.size shouldBe 8
    turning.foreach { case (code, rule) =>
      (0L to 64L).foreach { x =>
        withClue(s"rule $code with g F F 0 = $x: ")(evaluate(evenRhs, false, false, 0, rule, (a, b, y) => if (!a && !b && y == 0) x else fail("only g F F 0 occurs")) should not be x)
      }
    }
  }

  "The Pascal map's equations" should "be n XOR 2n, and not Rule 30's map" in {
    val map = mapOf(opened(fact("PASCAL_MAP_EXISTS").conclusion, g), (_, _) => fail("the Pascal map's equations name no rule"))
    (0L until 5000L).foreach(n => withClue(s"D($n): ")(map(n) shouldBe (n ^ (n << 1))))
    (0L until 64L).exists(n => map(n) != (n ^ ((n << 1) | (n << 2)))) shouldBe true
  }

  /** The value of an arithmetic term under `env`, with `map` the value of `g F F`. */
  private def value(t: Term, env: Map[FVar, Long], map: Long => Long): Long = t match {
    case v: FVar => env.getOrElse(v, fail(s"unbound $v"))
    case Const(Natural.NumberZero, _) => 0L
    case Const(Peano.NumeralOne, _) => 1L
    case App(Const("SUC", _), x) => value(x, env, map) + 1
    case App(Const(Peano.NumeralBit0, _), x) => 2 * value(x, env, map)
    case App(Const(Peano.NumeralBit1, _), x) => 2 * value(x, env, map) + 1
    case App(App(Const(Peano.Exponentiation, _), x), y) => if (value(x, env, map) == 2) 1L << value(y, env, map) else fail("only powers of 2")
    case App(App(Const(Modular.ModName, _), x), y) => value(x, env, map) % value(y, env, map)
    case App(App(Const(Modular.DivName, _), x), y) => value(x, env, map) / value(y, env, map)
    case App(App(App(f, _), _), x) if f == g => map(value(x, env, map))
    case other => fail(s"not arithmetic the test reads: $other")
  }

  /** The truth of a proposition without quantifiers, `/\\`, `~`, `=` between numbers or propositions. */
  private def holds(t: Term, env: Map[FVar, Long], map: Long => Long): Boolean =
    logic.destConj(t).map { case (a, b) => holds(a, env, map) && holds(b, env, map) }
      .orElse(logic.destNot(t).map(a => !holds(a, env, map)))
      .orElse(Term.destEq(t).map { case (a, b) =>
        if (Term.typeOf(a) == Type.Bool) holds(a, env, map) == holds(b, env, map) else value(a, env, map) == value(b, env, map)
      })
      .getOrElse(fail(s"not a proposition the test reads: $t"))

  /** `PASCAL_MAP_BITS`, its claim for each `x` below 512 and `j` below 10, with `g F F` read as `map`. */
  private def bitsHold(map: Long => Long): Boolean = {
    val claim = force(rules.specAll(fact("PASCAL_MAP_BITS"), List(g))).conclusion
    val (xs, body) = force(Logic.stripForall(logic.destImp(claim).map(_._2).getOrElse(fail("not an implication"))))
    val (low, rest) = logic.destConj(body).getOrElse(fail("not two parts"))
    val (js, upper) = force(Logic.stripForall(rest))
    (0L until 512L).forall { xv =>
      val env = Map(xs.head -> xv)
      holds(low, env, map) && (0L until 10L).forall(jv => holds(upper, env + (js.head -> jv), map))
    }
  }

  "PASCAL_MAP_BITS" should "hold of n XOR 2n and fail of Rule 30's map" in {
    bitsHold(n => n ^ (n << 1)) shouldBe true
    bitsHold(n => n ^ ((n << 1) | (n << 2))) shouldBe false
  }
}
