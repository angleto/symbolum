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
   * At two zeros the theorem claims nothing, and that is the half which says its hypothesis is
   * meant. `NUM_GCD 0 0` is a choice with nothing provable about it, so `NUM_EUCLID_GCD 0 0 =
   * NUM_GCD 0 0` is a claim nothing here could either prove or refute, and a statement making it
   * would be one nobody could check. So three things are asserted at the pair: the algorithm's own
   * equations still run there and answer `0`; the published theorem, specialised there, has an
   * antecedent whose negation is derived with nothing assumed, so it cannot be detached; and
   * `Value`, which reaches `NUM_GCD` by the characterisation, refuses the pair where it answers
   * `4 6`. The last is the control on the refusal: an evaluator that refused everything would pass
   * the first half of it.
   */
  it should "claim nothing at two zeros, where NUM_GCD is a choice" in {
    val zero = numeral(0)

    val computed = evaluate(0, 0)
    computed.hypotheses shouldBe empty
    computed.conclusion shouldBe force(euclid.proposition("NUM_EUCLID_GCD 0 0 = 0"))

    val instance = force(rules.specAll(fact(EuclidAlgorithm.IsGcd), List(zero, zero)))
    val (antecedent, _) = euclid.logic.destImp(instance.conclusion).getOrElse(
      fail(s"not an implication at 0 0: ${instance.conclusion}"))
    val bothZero = force(rules.conjIntro(Kernel.refl(zero), Kernel.refl(zero)))
    bothZero.hypotheses shouldBe empty
    antecedent shouldBe force(euclid.logic.mkNot(bothZero.conclusion))

    evaluator.of(Modular.GcdName, Vector(BigInt(0), BigInt(0))).isLeft shouldBe true
    force(evaluator.of(Modular.GcdName, Vector(BigInt(4), BigInt(6)))).conclusion shouldBe
      force(euclid.proposition("NUM_GCD 4 6 = 2"))
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

  /**
   * The gcd equality over a grid rather than at one pair, because one pair is where a statement
   * about a different function could still agree. Every pair up to six except the double zero,
   * which includes the pairs with one zero, the equal pairs and both orders: the algorithm's
   * equations are run, carried to `NUM_GCD` by `NUM_EUCLID_GCD_IS_GCD`, and compared with the gcd
   * computed in Scala and with `Value`'s answer, which reaches `NUM_GCD` through its
   * characterisation and a Bezout combination and so shares no step with the algorithm. Added by
   * the verification of the cards that asked for the theorem.
   */
  it should "agree with NUM_GCD, and with Value, at every pair up to six but the double zero" in {
    val zero = numeral(0)
    val pairs = for { a <- 0 to 6; b <- 0 to 6 if !(a == 0 && b == 0) } yield (a, b)
    pairs.size shouldBe 48
    pairs.foreach { case (a, b) =>
      withClue(s"at ($a, $b): ") {
        val g = BigInt(a).gcd(BigInt(b))
        val computed = evaluate(a, b)
        computed.hypotheses shouldBe empty
        computed.conclusion shouldBe force(euclid.proposition(s"NUM_EUCLID_GCD $a $b = $g"))
        val notBoth = force(
          for {
            apart <- chain.successor.distinct(numeral(if (a != 0) a else b), zero)
            both <- euclid.proposition(s"($a:num) = 0 /\\ ($b:num) = 0")
            assumed <- LogicError.lift(Kernel.assume(both))
            half <- if (a != 0) rules.conjElim1(assumed) else rules.conjElim2(assumed)
            absurd <- rules.notElim(apart, half)
            result <- rules.notIntro(both, absurd)
          } yield result)
        val chosen = force(
          rules
            .specAll(fact(EuclidAlgorithm.IsGcd), List(numeral(a), numeral(b)))
            .flatMap(rules.mp(_, notBoth))
            .flatMap(Conv.sym)
            .flatMap(Conv.trans(_, computed)))
        chosen.hypotheses shouldBe empty
        chosen.conclusion shouldBe force(euclid.proposition(s"NUM_GCD $a $b = $g"))
        force(evaluator.of(Modular.GcdName, Vector(BigInt(a), BigInt(b)))).conclusion shouldBe chosen.conclusion
      }
    }
  }

  /**
   * The quotient over a grid too: every dividend up to seven by every divisor up to three, by the
   * recursion alone in successor form, carried to `NUM_DIV` by `NUM_EUCLID_DIV_IS_DIV`, and compared
   * with the quotient computed in Scala and with `Value`'s, which reads it off
   * `NUM_DIV_MOD_UNIQUE`. The orders the recursion needs are chains of `NUM_LT_SUC`, and `a < b` for
   * `a >= b` is refused by irreflexivity after a chain back.
   */
  it should "compute NUM_DIV by its equations at every dividend up to seven and divisor up to three" in {
    val lemma = (name: String) =>
      force(chain.peano.fact(name).orElse(chain.peano.naturals.fact(name)).orElse(chain.classical.fact(name)))
    def term(text: String): Term = force(euclid.term(text, Num))
    def spelled(n: Int): Term = term(("SUC (" * n) + "0" + (")" * n))
    val condTrue = Kernel.instType(Map(Classical.TypeVariable -> Num), lemma(Classical.CondTrue))
    val condFalse = Kernel.instType(Map(Classical.TypeVariable -> Num), lemma(Classical.CondFalse))
    def pieces(t: Term): (Term, Term, Term) = t match {
      case App(App(App(_, test), yes), no) => (test, yes, no)
      case other => fail(s"a conditional was expected: $other")
    }
    def rightOf(th: Kernel.Thm): Term = Term.destEq(th.conclusion).map(_._2).getOrElse(fail("an equation"))
    val subtraction =
      force(Rewrite.Rule.all(euclid.logic, Vector(lemma("NUM_SUB_SUC_SUC"), lemma("NUM_SUB_ZERO"))))

    // `x < y` for x < y, by NUM_LT_SUC and NUM_LT_TRANS.
    def below(x: Int, y: Int): Kernel.Thm =
      if (y == x + 1) force(rules.spec(spelled(x), lemma("NUM_LT_SUC")))
      else
        force(
          rules
            .conjIntro(below(x, y - 1), force(rules.spec(spelled(y - 1), lemma("NUM_LT_SUC"))))
            .flatMap(both =>
              rules
                .specAll(lemma("NUM_LT_TRANS"), List(spelled(x), spelled(y - 1), spelled(y)))
                .flatMap(rules.mp(_, both))))

    // `~(x < y)` for x >= y.
    def notBelow(x: Int, y: Int): Kernel.Thm = force(
      for {
        claim <- euclid.proposition(s"NUM_LT (${spelled(x)}) (${spelled(y)})")
        assumed <- LogicError.lift(Kernel.assume(claim))
        loop <-
          if (x == y) Right(assumed)
          else
            rules
              .conjIntro(assumed, below(y, x))
              .flatMap(both =>
                rules
                  .specAll(lemma("NUM_LT_TRANS"), List(spelled(x), spelled(y), spelled(x)))
                  .flatMap(rules.mp(_, both)))
        absurd <- rules.spec(spelled(x), lemma("NUM_LT_IRREFL")).flatMap(rules.notElim(_, loop))
        result <- rules.notIntro(claim, absurd)
      } yield result)

    def quotient(a: Int, b: Int): Kernel.Thm = {
      val nonZero = force(rules.spec(spelled(b - 1), lemma("NUM_SUC_NOT_ZERO")))
      val at = force(rules.specAll(fact(EuclidAlgorithm.DivRecursion), List(spelled(a), spelled(b))))
      val (t1, z1, inner) = pieces(rightOf(at))
      val skip = force(rules.specAll(condFalse, List(t1, z1, inner)).flatMap(rules.mp(_, nonZero)))
      val (t2, z2, again) = pieces(inner)
      if (a < b) {
        val take = force(rules.specAll(condTrue, List(t2, z2, again)).flatMap(rules.mp(_, below(a, b))))
        force(Conv.trans(at, skip).flatMap(Conv.trans(_, take)))
      } else {
        val take = force(rules.specAll(condFalse, List(t2, z2, again)).flatMap(rules.mp(_, notBelow(a, b))))
        val minus = force(Rewrite.rewrite(subtraction, term(s"NUM_SUB (${spelled(a)}) (${spelled(b)})")))
        val carried = force(
          for {
            name <- euclid.term(s"\\x:num. SUC (${EuclidAlgorithm.DivName} x (${spelled(b)}))")
            moved <- Conv.apTerm(name, minus).flatMap(Conv.betaSides)
            succ <- euclid.term("SUC")
            down <- Conv.apTerm(succ, quotient(a - b, b))
            result <- Conv.trans(moved, down)
          } yield result)
        force(Conv.trans(at, skip).flatMap(Conv.trans(_, take)).flatMap(Conv.trans(_, carried)))
      }
    }

    val pairs = for { a <- 0 to 7; b <- 1 to 3 } yield (a, b)
    pairs.size shouldBe 24
    pairs.foreach { case (a, b) =>
      withClue(s"at ($a, $b): ") {
        val q = a / b
        val computed = quotient(a, b)
        computed.hypotheses shouldBe empty
        computed.conclusion shouldBe
          force(euclid.proposition(s"${EuclidAlgorithm.DivName} (${spelled(a)}) (${spelled(b)}) = ${spelled(q)}"))
        val chosen = force(
          rules
            .specAll(fact(EuclidAlgorithm.DivIsDiv), List(spelled(a), spelled(b)))
            .flatMap(rules.mp(_, force(rules.spec(spelled(b - 1), lemma("NUM_SUC_NOT_ZERO")))))
            .flatMap(Conv.sym)
            .flatMap(Conv.trans(_, computed)))
        chosen.hypotheses shouldBe empty
        chosen.conclusion shouldBe
          force(euclid.proposition(s"NUM_DIV (${spelled(a)}) (${spelled(b)}) = ${spelled(q)}"))
        force(evaluator.of("NUM_DIV", Vector(BigInt(a), BigInt(b)))).conclusion shouldBe
          force(euclid.proposition(s"NUM_DIV $a $b = $q"))
      }
    }
  }
}
