package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Add, Cos, Div, Dsl, Expr, Mul, Num, Pow, Sin, Var}
import garden.xeno.symbolum.kernel.{Term, TyApp}
import garden.xeno.symbolum.logic.{NotNormalised, NotOfForm}
import garden.xeno.symbolum.theories.Real

/**
 * Screening then proving.
 *
 * Three outcomes, and each has a test: an identity that is proved, one that is disproved with the
 * point that kills it, and one that survives every point tried and is not turned into a theorem.
 *
 * The third is where the attention goes, and it is four situations rather than one. Only the last
 * of them is a lead; the other three are the machinery saying the fragment was too narrow, the
 * numerals too large, or the rewriting unfinished. There is a test per case, and the case that
 * cannot be produced end to end says so rather than being tested through something it is not.
 */
class DiscoverySpec extends AnyFlatSpec with Matchers {

  private val discovery = Discovery.standard

  private val x = Var("x")
  private val y = Var("y")

  private def samplesFor(expressions: Expr*): Vector[Map[String, Double]] =
    Discovery.grid(expressions.toVector, 12)

  "A true identity in the fragment" should "come out proved" in {
    val left = Mul(Vector(Add(Vector(x, Num(1))), Add(Vector(x, Num(1)))))
    val right = Add(Vector(Pow(x, Num(2)), Mul(Vector(Num(2), x)), Num(1)))

    discovery.settle(left, right, samplesFor(left, right)) should matchPattern {
      case Discovery.Proved(_, _, _) =>
    }
  }

  "A false identity" should "come out disproved, with the point that shows it" in {
    val left = Mul(Vector(Add(Vector(x, Num(1))), Add(Vector(x, Num(1)))))
    val right = Add(Vector(Pow(x, Num(2)), Num(1)))

    discovery.settle(left, right, samplesFor(left, right)) match {
      case Discovery.Disproved(_, _, witness, difference) =>
        // The witness is a real counterexample: the two sides differ there by what is reported.
        math.abs(left.eval(witness) - right.eval(witness)) shouldBe math.abs(difference) +- 1e-9
        difference should not be 0.0

      case other => fail(s"expected a disproof, got $other")
    }
  }

  "An identity that holds but is outside the fragment" should "say that is why" in {
    // A cosine: the theory has no constant for it, so the reader refuses by name and the pair is
    // outside the fragment. Nothing is wrong here, and nothing is a lead either: the fragment is
    // narrow, which is a fact about this system rather than about the candidate.
    //
    // This used to be `2 * x / 2 = x`, which stopped being a witness on 2026-09-09 when the
    // reader learned to read a quotient. That identity is now *read* and still not proved, which
    // is a different bucket and a more useful one; it is pinned as such below.
    val left = Add(Vector(Pow(Sin(x), Num(2)), Pow(Cos(x), Num(2))))
    val right = Num(1)

    discovery.settle(left, right, samplesFor(left, right)) match {
      case Discovery.Unsettled(_, _, why, reason, pointsTried) =>
        why shouldBe Discovery.Why.OutsideTheFragment
        reason shouldBe a[OutsideFragment]
        pointsTried shouldBe 12

      case other => fail(s"expected an unsettled pair, got $other")
    }
  }

  "A candidate carrying a numeral too large to be worth the wait" should "be declined before it is attempted" in {
    // This test used to use `1000 * x`, and on 2026-09-04 that had become a two-millisecond goal:
    // RING collects coefficients instead of expanding them, so the wall the budget was set against
    // moved by ten orders of magnitude. What is left is the numeral arithmetic, which grows with
    // the number of digits, and `Oracle.NumeralBudget` carries the measurement that placed it. The
    // loop still declines rather than starting, and this test still returns at once, which is the
    // point of it.
    val large = Mul(Vector(Num(1e13), x))

    discovery.settle(large, large, samplesFor(large)) match {
      case Discovery.Unsettled(_, _, why, reason, _) =>
        why shouldBe Discovery.Why.BeyondTheBudget
        reason shouldBe a[BeyondBudget]
        reason.message should include("10000000000000")

      case other => fail(s"expected the budget to decline it, got $other")
    }
  }

  "A candidate that the budget used to decline" should "now be certified" in {
    // The other half of the change above, and the reason it is a test rather than a comment: a
    // budget that was merely raised would leave this passing by accident.
    val large = Mul(Vector(Num(1000), x))

    discovery.settle(large, large, samplesFor(large)) should matchPattern {
      case Discovery.Proved(_, _, _) =>
    }
  }

  "A candidate that agrees over the sample and is false" should "be the one worth reading" in {
    // The lead, and the reason `pointsTried` is carried. `x * x = x` holds at 1 and nowhere else
    // that matters, so a sample of one point lets it through the screening; RING then reaches a
    // normal form on both sides, they differ, and that difference is a statement about the
    // candidate rather than about the machinery. Agreement at one point is nothing, which the
    // count says out loud.
    val left = Mul(Vector(x, x))

    discovery.settle(left, x, Vector(Map("x" -> 1.0))) match {
      case Discovery.Unsettled(_, _, why, _, pointsTried) =>
        why shouldBe Discovery.Why.NotProvableHere
        pointsTried shouldBe 1

      case other => fail(s"expected the lead, got $other")
    }
  }

  "The rewriter running out" should "be classified apart from a candidate that is not provable" in {
    // The fourth case, and the only one without an end-to-end test, because no input was found
    // that exhausts the standard normalisation: on 2026-09-04 reversed sums up to thirty-two terms
    // and two hundred and fifty nested cancellations all certified, and the numerals that would be
    // slow enough are declined by the budget above before they are tried. It is reachable through
    // `Rewrite` with a rule set of one's own, which `RewriteSpec` demonstrates, so the
    // classification is tested here where the classifying happens and the error is tested there
    // where it arises.
    val stuck = Term.variable("t", TyApp(Real.TypeName, Nil))

    Discovery.why(NotCertified("a = b", NotNormalised(stuck))) shouldBe
      Discovery.Why.RewriterRanOut
    Discovery.why(OutsideFragment(x, "the theory has no constant for this")) shouldBe
      Discovery.Why.OutsideTheFragment
    Discovery.why(NotCertified("a = b", NotOfForm("a term equal to it", stuck))) shouldBe
      Discovery.Why.NotProvableHere
  }

  "Screening a bag of candidates" should "sort them into the three outcomes" in {
    val square = Mul(Vector(Add(Vector(x, Num(1))), Add(Vector(x, Num(1)))))
    val expanded = Add(Vector(Pow(x, Num(2)), Mul(Vector(Num(2), x)), Num(1)))
    val different = Add(Vector(Pow(x, Num(2)), Num(1)))

    val candidates = Vector(square, expanded, different)
    val outcomes = discovery.identities(candidates, Discovery.grid(candidates, 12))

    outcomes should have length 3
    outcomes.count(_.isInstanceOf[Discovery.Proved]) shouldBe 1
    outcomes.count(_.isInstanceOf[Discovery.Disproved]) shouldBe 2
  }

  "The sample grid" should "be the same every time it is built" in {
    val first = Discovery.grid(Vector(Add(Vector(x, y))), 5)
    val second = Discovery.grid(Vector(Add(Vector(x, y))), 5)

    first shouldBe second
    first should have length 5
    first.head.keySet shouldBe Set("x", "y")
  }

  it should "not put every variable at the same value" in {
    // Sampling several variables at one point makes distinct expressions agree by accident.
    val point = Discovery.grid(Vector(Add(Vector(x, y))), 3).head

    point("x") should not be point("y")
  }

  it should "not put its points on a line" in {
    // The first grid set every coordinate to an affine function of the point's index, which is a
    // line in any number of dimensions, and a polynomial vanishing on that line agreed at every
    // point. Twelve points over three variables must span the whole space: affine rank four.
    val z = Var("z")
    val points = Discovery.grid(Vector(Add(Vector(x, y, z))), 12)

    affineRank(points.map(point => Vector(point("x"), point("y"), point("z")))) shouldBe 4
  }

  it should "give a named constant its value rather than sampling it" in {
    val points = Discovery.grid(Vector(Add(Vector(x, Dsl.pi))), 5)

    points.map(_("pi")).distinct shouldBe Vector(math.Pi)
    points.map(_("x")).distinct should have length 5
  }

  "A trigonometric candidate" should "be judged at the real pi" in {
    // `sin(pi) = 0` is true and outside the fragment, so the right answer is unsettled. A grid
    // that sampled `pi` disproved it at a made-up value.
    val left = Sin(Dsl.pi)
    val right = Num(0)

    discovery.settle(left, right, samplesFor(left, right)) should matchPattern {
      case Discovery.Unsettled(_, _, Discovery.Why.OutsideTheFragment, _, _) =>
    }
  }

  /** The rank of the points as affine combinations: `n + 1` when they span `n` dimensions. */
  private def affineRank(points: Vector[Vector[Double]]): Int = {
    val rows = points.map(point => 1.0 +: point).map(_.toArray).toArray
    val columns = rows.head.length
    var rank = 0

    for (column <- 0 until columns) {
      val pivot = (rank until rows.length).maxByOption(row => math.abs(rows(row)(column)))
      pivot.filter(row => math.abs(rows(row)(column)) > 1e-9).foreach { row =>
        val swap = rows(rank); rows(rank) = rows(row); rows(row) = swap
        for (other <- rank + 1 until rows.length) {
          val factor = rows(other)(column) / rows(rank)(column)
          for (k <- column until columns) rows(other)(k) -= factor * rows(rank)(k)
        }
        rank += 1
      }
    }

    rank
  }
}
