package garden.xeno.symbolum.theories

import org.scalacheck.Gen
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.scalacheck.ScalaCheckDrivenPropertyChecks
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The inequalities between numerals this development can prove.
 *
 * The order axioms are all relational: each says how `<` survives an operation, and none asserts
 * that any number is below any other. So the interesting assertions here are not that `0 < 1` came
 * out, but that it came out of the sixteen axioms with nothing assumed and nothing added, and that
 * every other numeral fact is reached from it by unfolding the binary encoding rather than by
 * assuming a second thing.
 */
class OrderSpec extends AnyFlatSpec with Matchers with ScalaCheckDrivenPropertyChecks {

  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(minSuccessful = 200)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val order = Order.standard
  private val reals = order.reals

  "The order" should "prove that zero is below one" in {
    val theorem = force(order.zeroLessOne)

    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe force(reals.proposition("0 < 1"))
    reals.show(theorem.conclusion) shouldBe "0 < 1"
  }

  it should "add two positive quantities" in {
    // Written in `Linarith` and moved here when the recursion on the bits of a numeral turned out
    // to need it once per bit. One home, for every consumer.
    reals.show(force(order.addPositive).conclusion) shouldBe
      "!x:real. !y:real. 0 < x ==> 0 < y ==> 0 < x + y"
  }

  it should "add nothing to what has to be believed" in {
    // The whole point of deriving it rather than asserting it. If this number moves, something
    // reached for `assertAxiom` and the derivation stopped being one.
    order.reals.theory.axioms.toSet shouldBe (Classical.standard.theory.axioms ++ Natural.standard.theory.axioms).toSet
    Real.Axioms should have length 16
  }

  it should "build from the ring rather than from a fixed instance" in {
    // `construct` takes the ring it is built over, so a later theory that extends the reals can
    // have these facts too. `standard` is the instance over `Ring.standard`, not the only one.
    val built = force(Order.construct(Ring.standard))

    force(built.zeroLessOne).conclusion shouldBe force(order.zeroLessOne).conclusion
  }

  it should "refuse a fact it does not have" in {
    order.fact("LT_ANYTHING").left.map(_.getClass) shouldBe Left(classOf[MissingDefinition])
  }

  "The pieces the derivation rests on" should "each be provable on their own" in {
    // Written out because the derivation is long enough that a failure in it is hard to place, and
    // these are the three steps that could plausibly stop working: two ring identities and the
    // trichotomy instance. If `zeroLessOne` fails and these pass, the fault is in the case
    // analysis rather than in what it is made of.
    val ring = order.ring
    val rules = reals.logic.rules

    force(ring.prove("1 + -1 = 0")).hypotheses shouldBe empty
    force(ring.prove("-1 * -1 = 1")).hypotheses shouldBe empty

    val trichotomy = force(
      reals
        .axiom("LT_TOTAL")
        .flatMap(rules.spec(force(reals.term("0")), _))
        .flatMap(rules.spec(force(reals.term("1")), _))
    )
    reals.show(trichotomy.conclusion) shouldBe "0 < 1 \\/ 0 = 1 \\/ 1 < 0"
  }

  "A theory with domain constants" should "keep every tactic that was built on it" in {
    // The point of extension: a development about something other than numbers declares its own
    // constants and does not leave the arithmetic behind. Everything from the numerals up takes
    // what it is built on as an argument, so the whole chain rebuilds over the extended theory.
    val extended = force(
      Real.standard.extended(
        Vector("agent" -> 0),
        Vector(
          "selectivity" -> TyApp(Real.TypeName, Nil),
          "payoff" -> Type.fun(TyApp("agent", Nil), TyApp(Real.TypeName, Nil))
        )
      )
    )

    val overThere = force(
      for {
        arithmetic <- Arithmetic.construct(extended)
        ring <- Ring.construct(arithmetic)
        order <- Order.construct(ring)
        linarith <- Linarith.construct(order)
      } yield linarith
    )

    // A goal about a declared constant, proved by the same procedure, with the constant carried
    // through as an atom the search knows nothing about and does not need to.
    val theorem = force(overThere.prove("!x:real. selectivity < x ==> selectivity < x + 1"))
    theorem.hypotheses shouldBe empty
    extended.show(theorem.conclusion) shouldBe
      "!x:real. selectivity < x ==> selectivity < x + 1"

    // And declaring cost nothing: the trusted base is what it was.
    extended.theory.axioms.toSet shouldBe (Classical.standard.theory.axioms ++ Natural.standard.theory.axioms).toSet
  }

  it should "not let a declared type be said to be inhabited" in {
    // The price of that conservativity, and worth stating because it is easy to assume otherwise:
    // a declared type may have one element as far as the theory knows. Nothing here proves
    // `?x:agent. T`, and asserting it would be an axiom.
    val extended = force(Real.standard.extended(Vector("agent" -> 0), Vector.empty))
    val statement = force(extended.proposition("?x:agent. T"))

    Linarith.standard.prove(statement).isLeft shouldBe true
    extended.theory.axioms.toSet shouldBe (Classical.standard.theory.axioms ++ Natural.standard.theory.axioms).toSet
  }

  "The ordered field lemmas" should "each state what they claim" in {
    // Printed rather than compared as terms, because what a reader of the guide checks against the
    // paper is the printed statement: an inequality multiplied on the wrong side, or a premise in
    // the wrong order, is invisible in a comparison with a term this file built the same way.
    //
    // The letters are the printer's and not the source's. The kernel is locally nameless, so a
    // bound variable has no name in the term at all and `Printer` invents `x, y, z` by depth: the
    // factor `Order` calls `c` prints as `x` wherever it is bound outermost.
    reals.show(force(order.moveToZero).conclusion) shouldBe
      "!x:real. !y:real. x < y ==> 0 < y - x"
    reals.show(force(order.moveFromZero).conclusion) shouldBe
      "!x:real. !y:real. 0 < y - x ==> x < y"
    reals.show(force(order.nonZero).conclusion) shouldBe
      "!x:real. 0 < x ==> ~(x = 0)"
    reals.show(force(order.cancelPositive).conclusion) shouldBe
      "!x:real. !y:real. 0 < x ==> 0 < x * y ==> 0 < y"
    reals.show(force(order.multiplyBoth).conclusion) shouldBe
      "!x:real. !y:real. !z:real. 0 < x ==> y < z ==> y * x < z * x"
    reals.show(force(order.inversePositive).conclusion) shouldBe
      "!x:real. 0 < x ==> 0 < inv x"

    // The two non-strict multiplications, printed side by side, because the whole difference
    // between them is one character and it is the difference between a lemma the order axioms
    // give and one that needs a case analysis.
    reals.show(force(order.multiplyNonNegative).conclusion) shouldBe
      "!x:real. !y:real. 0 < x ==> 0 <= y ==> 0 <= x * y"
    reals.show(force(order.multiplyNonNegatives).conclusion) shouldBe
      "!x:real. !y:real. 0 <= x ==> 0 <= y ==> 0 <= x * y"

    reals.show(force(order.squareNonNegative).conclusion) shouldBe "!x:real. 0 <= x * x"
    reals.show(force(order.addLe).conclusion) shouldBe
      "!x:real. !y:real. !z:real. !u:real. x <= y ==> z <= u ==> x + z <= y + u"

    // The two that landed on 2026-09-18, printed beside the strict multiplication they extend, for
    // the reason the pair above is printed together: `LT_MUL_BOTH` and `LE_MUL_BOTH` differ by one
    // character in two places and by a case analysis underneath.
    reals.show(force(order.multiplyLe).conclusion) shouldBe
      "!x:real. !y:real. !z:real. 0 <= x ==> y <= z ==> y * x <= z * x"
    reals.show(force(order.inverseAntitone).conclusion) shouldBe
      "!x:real. !y:real. 0 < x ==> x <= y ==> inv y <= inv x"
  }

  "The reciprocal reversing the order" should "carry the positivity hypothesis it cannot drop" in {
    // The attack, and it is the only form one can take against a theorem: the kernel says the
    // statement holds, so what is left to check is that it is the statement worth having. Drop
    // `0 < x` and it is false, and the witness is derived here rather than argued: at `x = 0 - 1`
    // and `y = 1` the premise `x <= y` holds, and the conclusion `inv y <= inv x` would say
    // `1 <= inv (0 - 1)`, which is `1 <= 0 - 1` and contradicts what the order proves.
    //
    // So the hypothesis is not decoration and the lemma is not the unguarded one with a condition
    // left on by habit. `PrimesSpec` makes the same move about `NUM_SQUARE_NOT_DOUBLE`, and for
    // the same reason: a theorem cannot refuse, so a negative control has to be a derivation of
    // the instance that would break.
    val rules = reals.logic.rules
    val theorem = force(order.inverseAntitone)

    theorem.hypotheses shouldBe empty

    // The guarded instance, which is the lemma doing its job: 1 <= 2 gives inv 2 <= inv 1.
    val guarded = force(
      rules
        .specAll(theorem, List(force(reals.term("1")), force(reals.term("2"))))
        .flatMap(rules.mp(_, force(order.positive(1))))
    )
    reals.show(guarded.conclusion) shouldBe "1 <= 2 ==> inv 2 <= inv 1"

    // And the premise the unguarded version would have to be given, which the order refutes: the
    // negative witness is below zero, so `0 < x` is not available at it and no instance is reached.
    val negative = force(reals.term("0 - 1"))
    val instance = force(rules.specAll(theorem, List(negative, force(reals.term("1")))))
    reals.show(instance.conclusion) shouldBe
      "0 < 0 - 1 ==> 0 - 1 <= 1 ==> inv 1 <= inv (0 - 1)"
  }

  "The two lemmas the geometric series wanted" should "rest on the axioms and on nothing assumed" in {
    // What they cost, reported rather than asserted as a budget: the count moves on an improvement
    // to any of the lemmas underneath and a number pinned here would go red on one.
    //
    // What IS asserted is the split, because that is the claim: nothing is assumed, and the
    // reciprocal one reaches `MUL_INVERSE` where the multiplication one does not, which is the
    // whole difference between an order fact and a field fact.
    val times = force(order.multiplyLe)
    val reciprocal = force(order.inverseAntitone)

    times.hypotheses shouldBe empty
    reciprocal.hypotheses shouldBe empty

    val timesAxioms = Real.spent(times)
    val reciprocalAxioms = Real.spent(reciprocal)
    val inverseAxiom = force(reals.axiom("MUL_INVERSE")).conclusion

    timesAxioms should not contain inverseAxiom
    reciprocalAxioms should contain(inverseAxiom)
    timesAxioms.subsetOf(reciprocalAxioms) shouldBe true

    info(s"LE_MUL_BOTH reaches ${timesAxioms.size} axioms in ${Derivation.size(times)} inferences, " +
      s"INV_ANTITONE ${reciprocalAxioms.size} in ${Derivation.size(reciprocal)}")
  }

  "Two bounds added together" should "be the move the order axioms leave out" in {
    // The invariant: `LT_ADD` adds the same term to both sides of one inequality, so a bound
    // assembled from two separate bounds is not an instance of it. This asserts the shape that is
    // not derivable from one axiom step: four independent terms, two premises, one conclusion.
    val rules = reals.logic.rules
    val theorem = force(order.addLe)

    theorem.hypotheses shouldBe empty

    // Used the way a caller uses it: two bounds on unrelated quantities give a bound on the sum.
    val applied = force(
      for {
        instance <- rules.specAll(
          theorem,
          List(
            force(reals.term("a:real")),
            force(reals.term("2")),
            force(reals.term("b:real")),
            force(reals.term("3"))
          )
        )
      } yield instance
    )
    reals.show(applied.conclusion) shouldBe "a <= 2 ==> b <= 3 ==> a + b <= 2 + 3"
  }

  "The sign of a square" should "hold for every real and not only for the positive ones" in {
    // The invariant, which is what makes this fact worth its own name rather than an instance of
    // `LT_MUL`: the axiom gives a positive product from two positive factors and is silent about a
    // factor that is negative or zero, so a claim about `x * x` for **every** `x` is a case
    // analysis on trichotomy and cannot be an instance of anything the axioms state. What is
    // asserted here is that the theorem quantifies over the whole line, with nothing assumed.
    val theorem = force(order.squareNonNegative)

    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe force(reals.proposition("!x:real. 0 <= x * x"))
  }

  it should "be the non-strict claim and not the strict one, because zero is on the line" in {
    // Why the statement is `<=` rather than `<`, said as a refusal rather than as prose: the strict
    // form is false at zero, so nothing here proves it and `Linarith` cannot either. A reader who
    // wants `0 < x * x` owes a hypothesis that `x` is not zero, and this records that the weaker
    // statement is the one that holds rather than the one that was easier to reach.
    val strict = force(reals.proposition("!x:real. 0 < x * x"))

    Linarith.standard.prove(strict).isLeft shouldBe true

    // And the fact does apply at zero, which is the point of the non-strict form: at `0` the
    // product is `0 * 0`, and the theorem says that is at least zero.
    val rules = reals.logic.rules
    val atZero = force(rules.spec(force(reals.term("0")), force(order.squareNonNegative)))
    reals.show(atZero.conclusion) shouldBe "0 <= 0 * 0"
  }

  it should "be usable on a term that is not a variable, which is what an extremal argument has" in {
    // Specialising it at a compound term, because that is how every use of it looks: what is
    // squared in an extremal argument is a difference, not an unknown. The theorem is one
    // quantifier over the reals, so this is `spec` and not a second derivation.
    val rules = reals.logic.rules
    val difference = force(reals.term("x:real - y:real"))
    val instance = force(rules.spec(difference, force(order.squareNonNegative)))

    instance.hypotheses shouldBe empty
    reals.show(instance.conclusion) shouldBe "0 <= (x - y) * (x - y)"
  }

  it should "have no hypotheses, every one of them" in {
    order.facts.foreach { case (name, theorem) =>
      withClue(s"$name: ") { theorem.hypotheses shouldBe empty }
    }
  }

  "A positive numeral and a lemma" should "compose into the step a ratio needs" in {
    // The three uses these lemmas exist for, each written the way a caller writes it: a numeral is
    // proved positive, and that discharges the first premise of the lemma.
    val rules = reals.logic.rules
    val x = force(reals.term("x:real"))
    val y = force(reals.term("y:real"))
    val two = force(reals.term("2"))
    val three = force(reals.term("3"))

    val scaled = force(
      rules
        .spec(three, force(order.multiplyBoth))
        .flatMap(rules.spec(x, _))
        .flatMap(rules.spec(y, _))
        .flatMap(rules.mp(_, force(order.positive(3))))
    )
    reals.show(scaled.conclusion) shouldBe "x < y ==> x * 3 < y * 3"

    val cancelled = force(
      rules
        .spec(two, force(order.cancelPositive))
        .flatMap(rules.spec(x, _))
        .flatMap(rules.mp(_, force(order.positive(2))))
    )
    reals.show(cancelled.conclusion) shouldBe "0 < 2 * x ==> 0 < x"

    val inverted = force(
      rules
        .spec(two, force(order.inversePositive))
        .flatMap(rules.mp(_, force(order.positive(2))))
    )
    reals.show(inverted.conclusion) shouldBe "0 < inv 2"
  }

  "A numeral above zero" should "be proved positive, whatever its bits" in {
    // Both bit cases, both from the base and from a longer numeral: 2 and 4 are `BIT0`, 3 is
    // `BIT1` of the base, 12 is `BIT0 (BIT0 (BIT1 1))` and exercises all three.
    Vector(1, 2, 3, 4, 5, 12, 1000).foreach { value =>
      val theorem = force(order.positive(value))

      withClue(s"0 < $value: ") {
        theorem.hypotheses shouldBe empty
        reals.show(theorem.conclusion) shouldBe s"0 < $value"
      }
    }
  }

  it should "state the goal about the numeral as it is written" in {
    // The recursion builds the right-hand side by unfolding `BIT0` and `BIT1`, so what it ends on
    // is a term rather than a rendering: this asserts it is the same term the parser produces for
    // `12`, not merely something that prints the same way.
    force(order.positive(12)).conclusion shouldBe force(reals.proposition("0 < 12"))
  }

  it should "cost what its digits cost, not what its value costs" in {
    // A derivation that counted up to the numeral could not do this one: it is a million million.
    // The recursion is one step per bit, so it is forty. Measured on 2026-09-05 outside the suite,
    // one JVM and single runs, so soft by a factor of a few: 9 ms at ten bits (`1000`), 77 ms at
    // forty (this one), 225 ms at eighty (`10^24`), 319 ms at a hundred and sixty. The values in
    // that row differ by a factor of `10^45` and the times by a factor of thirty-five. No time is
    // asserted, because a time is a machine on a day; what is asserted is that it finishes.
    val large = BigInt(10).pow(12)
    val theorem = force(order.positive(large))

    theorem.hypotheses shouldBe empty
    reals.show(theorem.conclusion) shouldBe s"0 < $large"
  }

  it should "be refused at zero and below" in {
    // `0 < 0` is false and there is no numeral below zero, so both are refusals rather than
    // attempts that fail somewhere inside the recursion.
    order.positive(0).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
    order.positive(-1).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
  }

  "Two numerals" should "be compared by proving their difference positive" in {
    Vector((0, 1), (0, 5), (1, 2), (2, 3), (53, 60), (999, 1000)).foreach { case (left, right) =>
      val theorem = force(order.less(left, right))

      withClue(s"$left < $right: ") {
        theorem.hypotheses shouldBe empty
        reals.show(theorem.conclusion) shouldBe s"$left < $right"
      }
    }
  }

  it should "be refused when the claim is false or not about numerals" in {
    order.less(5, 5).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
    order.less(7, 3).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
    order.less(-1, 3).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
  }

  "Positivity" should "hold for any numeral, not for the ones chosen here" in {
    // Two hundred samples, each one derivation per bit over numerals of up to seventeen bits. The
    // property took 943 ms in one run on 2026-09-05 and 302 ms in another on the same machine the
    // same morning, which is the spread the whole file's timings should be read with. The range is
    // deliberately not the range of the examples above: those are small and hand-picked, and a
    // recursion that is wrong on a long run of ones would pass them.
    forAll(Gen.chooseNum(1L, 100000L)) { value =>
      val theorem = force(order.positive(BigInt(value)))

      theorem.hypotheses shouldBe empty
      reals.show(theorem.conclusion) shouldBe s"0 < $value"
    }
  }

  "Comparison" should "hold for any pair, in the order the numerals are" in {
    // Two hundred samples again, which the measurement allows: 449 ms on 2026-09-05, the same
    // order as the property above even though each sample also costs two ring steps on numerals.
    // The pair is generated as a base and a gap rather than as two numbers, because a generator
    // that drew both and sorted them would almost never produce a small difference, and a small
    // difference is where a subtraction done on the numerals could go wrong.
    val pairs = for {
      left <- Gen.chooseNum(0L, 5000L)
      gap <- Gen.chooseNum(1L, 5000L)
    } yield (left, left + gap)

    forAll(pairs) { case (left, right) =>
      val theorem = force(order.less(BigInt(left), BigInt(right)))

      theorem.hypotheses shouldBe empty
      reals.show(theorem.conclusion) shouldBe s"$left < $right"
    }
  }

  /**
   * A negated comparison becomes a positive one here, and it costs nothing classical.
   *
   * The obvious reading of `~(x < y) ==> y <= x` is that turning a negation round is where the
   * excluded middle is spent. On a total order it is not, and this is the assertion that says so:
   * both derivations rest on `LT_TOTAL` and on nothing else, so `Order` stays over the axiom-free
   * logic it is deliberately built on. A derivation that started reaching for `Classical` would
   * still prove these two and would show here.
   */
  "Turning a negated comparison round" should "rest on trichotomy and on nothing else" in {
    val trichotomy = force(order.ring.arithmetic.reals.axiom("LT_TOTAL")).conclusion

    List(Order.LeOfNotLt, Order.LtOfNotLe).foreach { name =>
      val proved = force(order.fact(name))
      withClue(s"$name: ") {
        Real.spent(proved).toSet shouldBe Set(trichotomy)
        proved.hypotheses shouldBe empty
      }
    }
  }
}
