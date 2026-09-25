package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Euclid's algorithm as a definition, and a computation with it.
 *
 * What distinguishes this from `NUM_GCD` is that its equations run: `NUM_EUCLID_GCD 4 6` is taken to
 * `2` below by the step and the base case alone, with `Value` supplying each remainder and
 * `Successor.distinct` each `~(b = 0)`. A definition whose equations nobody computes with reads
 * exactly like one whose equations are wrong, so the computation is the assertion that matters.
 */
class EuclidAlgorithmSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private lazy val euclid = force(EuclidAlgorithm.construct(chain))
  private lazy val rules = euclid.logic.rules
  private lazy val evaluator = force(Value.construct(chain))
  private val Num = TyApp(Natural.TypeName, Nil)

  private def fact(name: String): Kernel.Thm = force(euclid.fact(name))
  private def numeral(n: Int): Term = force(euclid.term(n.toString, Num))

  "Every fact of the development" should "prove the statement it is published as" in {
    EuclidAlgorithm.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe force(euclid.proposition(text))
        fact(name).hypotheses shouldBe empty
      }
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    euclid.facts.keySet shouldBe EuclidAlgorithm.Statements.map(_._1).toSet
  }

  it should "cost choice and infinity, which is what the recursion under it costs" in {
    val expected = Set(
      force(chain.classical.axiom(Classical.Choice)).conclusion,
      force(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    EuclidAlgorithm.Statements.foreach { case (name, _) =>
      withClue(s"$name: ")(Derivation.axiomsOf(fact(name)) shouldBe expected)
    }
  }

  /** `|- NUM_EUCLID_GCD a b = g`, by the step until the second argument is zero. */
  private def evaluate(a: Int, b: Int): Kernel.Thm =
    if (b == 0) force(rules.spec(numeral(a), fact(EuclidAlgorithm.AtZero)))
    else {
      val next = force(
        for {
          atAB <- rules.specAll(fact(EuclidAlgorithm.Step), List(numeral(a), numeral(b)))
          apart <- chain.successor.distinct(numeral(b), numeral(0))
          stepped <- rules.mp(atAB, apart)
          remainder <- evaluator.of("NUM_MOD", Vector(BigInt(a), BigInt(b)))
          name <- euclid.term(s"${EuclidAlgorithm.Name} ${b}")
          carried <- Conv.apTerm(name, remainder)
          result <- Conv.trans(stepped, carried)
        } yield result
      )
      force(Conv.trans(next, evaluate(b, a % b)))
    }

  "The algorithm" should "compute a greatest common divisor by its equations" in {
    val computed = evaluate(4, 6)
    computed.hypotheses shouldBe empty
    computed.conclusion shouldBe force(euclid.proposition("NUM_EUCLID_GCD 4 6 = 2"))
  }

  /**
   * The computation above, carried to the chosen constant: `NUM_GCD 4 6 = 2` with nothing assumed,
   * which nothing in this repository could say before `NUM_EUCLID_GCD_IS_GCD`. `NUM_GCD` is defined
   * by choice and no equation of its own runs.
   */
  it should "say what NUM_GCD is at a pair, through the theorem that it computes it" in {
    val four = numeral(4)
    val six = numeral(6)
    val notBoth = force(
      for {
        apart <- chain.successor.distinct(four, numeral(0))
        both <- euclid.proposition("(4:num) = 0 /\\ (6:num) = 0")
        assumed <- LogicError.lift(Kernel.assume(both))
        fourZero <- rules.conjElim1(assumed)
        absurd <- rules.notElim(apart, fourZero)
        result <- rules.notIntro(both, absurd)
      } yield result)
    val chosen = force(
      rules
        .specAll(fact(EuclidAlgorithm.IsGcd), List(four, six))
        .flatMap(rules.mp(_, notBoth))
        .flatMap(Conv.sym)
        .flatMap(Conv.trans(_, evaluate(4, 6))))

    chosen.hypotheses shouldBe empty
    chosen.conclusion shouldBe force(euclid.proposition("NUM_GCD 4 6 = 2"))
  }

  /**
   * The division's equations run too: `NUM_EUCLID_DIV 3 2` is one by the recursion alone, in
   * successor form so that the subtraction is `NUM_SUB_SUC_SUC` and the order is `NUM_LT_SUC`.
   * Then `NUM_EUCLID_DIV_IS_DIV` carries it to `NUM_DIV`, which gives the quotient of the chosen
   * constant without `Value`, as a check that the two agree at a point rather than only in a
   * statement.
   */
  "The division" should "compute a quotient by its equations and agree with NUM_DIV there" in {
    val lemma = (name: String) =>
      force(chain.peano.fact(name).orElse(chain.peano.naturals.fact(name)).orElse(chain.classical.fact(name)))
    def term(text: String): Term = force(euclid.term(text, Num))
    val one = term("SUC 0")
    val two = term("SUC (SUC 0)")
    val three = term("SUC (SUC (SUC 0))")
    val condTrue = Kernel.instType(Map(Classical.TypeVariable -> Num), lemma(Classical.CondTrue))
    val condFalse = Kernel.instType(Map(Classical.TypeVariable -> Num), lemma(Classical.CondFalse))
    def pieces(t: Term): (Term, Term, Term) = t match {
      case App(App(App(_, test), yes), no) => (test, yes, no)
      case other => fail(s"a conditional was expected: $other")
    }
    def rightOf(th: Kernel.Thm): Term = Term.destEq(th.conclusion).map(_._2).getOrElse(fail("an equation"))
    val twoNonZero = force(rules.spec(one, lemma("NUM_SUC_NOT_ZERO")))

    // At (1, 2): 1 < 2, so zero.
    val atOne = force(rules.specAll(fact(EuclidAlgorithm.DivRecursion), List(one, two)))
    val (t1, z1, inner1) = pieces(rightOf(atOne))
    val skip1 = force(rules.specAll(condFalse, List(t1, z1, inner1)).flatMap(rules.mp(_, twoNonZero)))
    val (t2, z2, s2) = pieces(inner1)
    val oneBelowTwo = force(rules.spec(one, lemma("NUM_LT_SUC")))
    val take2 = force(rules.specAll(condTrue, List(t2, z2, s2)).flatMap(rules.mp(_, oneBelowTwo)))
    val divOne = force(Conv.trans(atOne, skip1).flatMap(Conv.trans(_, take2)))

    // At (3, 2): not 3 < 2, so one more than at (3 - 2, 2), and 3 - 2 is 1.
    val atThree = force(rules.specAll(fact(EuclidAlgorithm.DivRecursion), List(three, two)))
    val (u1, y1, innerThree) = pieces(rightOf(atThree))
    val skip3 = force(rules.specAll(condFalse, List(u1, y1, innerThree)).flatMap(rules.mp(_, twoNonZero)))
    val (u2, y2, sucTerm) = pieces(innerThree)
    val notBelow = force(
      for {
        assumed <- LogicError.lift(Kernel.assume(u2))
        twoBelowThree <- rules.spec(two, lemma("NUM_LT_SUC"))
        both <- rules.conjIntro(assumed, twoBelowThree)
        threeThree <- rules.specAll(lemma("NUM_LT_TRANS"), List(three, two, three)).flatMap(rules.mp(_, both))
        absurd <- rules.spec(three, lemma("NUM_LT_IRREFL")).flatMap(rules.notElim(_, threeThree))
        result <- rules.notIntro(u2, absurd)
      } yield result)
    val take3 = force(rules.specAll(condFalse, List(u2, y2, sucTerm)).flatMap(rules.mp(_, notBelow)))
    val minus = force(
      Rewrite.Rule.all(euclid.logic, Vector(lemma("NUM_SUB_SUC_SUC"), lemma("NUM_SUB_ZERO")))
        .flatMap(Rewrite.rewrite(_, term("NUM_SUB (SUC (SUC (SUC 0))) (SUC (SUC 0))"))))
    val carried = force(
      for {
        name <- euclid.term(s"\\x:num. SUC (${EuclidAlgorithm.DivName} x (SUC (SUC 0)))")
        moved <- Conv.apTerm(name, minus).flatMap(Conv.betaSides)
        succ <- euclid.term("SUC")
        down <- Conv.apTerm(succ, divOne)
        result <- Conv.trans(moved, down)
      } yield result)
    val computed = force(
      Conv.trans(atThree, skip3).flatMap(Conv.trans(_, take3)).flatMap(Conv.trans(_, carried)))

    computed.hypotheses shouldBe empty
    computed.conclusion shouldBe force(euclid.proposition("NUM_EUCLID_DIV (SUC (SUC (SUC 0))) (SUC (SUC 0)) = SUC 0"))

    val chosen = force(
      rules
        .specAll(fact(EuclidAlgorithm.DivIsDiv), List(three, two))
        .flatMap(rules.mp(_, twoNonZero))
        .flatMap(Conv.sym)
        .flatMap(Conv.trans(_, computed)))
    chosen.hypotheses shouldBe empty
    chosen.conclusion shouldBe force(euclid.proposition("NUM_DIV (SUC (SUC (SUC 0))) (SUC (SUC 0)) = SUC 0"))
  }
}
