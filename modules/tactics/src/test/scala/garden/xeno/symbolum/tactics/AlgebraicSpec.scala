package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import garden.xeno.symbolum.{Arbitrary, Relation}
import garden.xeno.symbolum.kernel.Derivation
import garden.xeno.symbolum.tactics.Algebraic.{Outcome, Root}
import garden.xeno.symbolum.theories.Chain

/**
 * The first source: a polynomial nobody supplied, found in the numbers and proved by the kernel.
 *
 * `RelationSpec` already pinned the numeric half: the minimal polynomial of `sqrt2 + sqrt3 + sqrt5`
 * comes back as `x^8 - 40x^6 + 352x^4 - 960x^2 + 576` at the top of its ladder of precisions and as
 * random-looking numbers at the bottom. What it could not do was say anything a kernel would sign.
 * This asks the whole thing: does the polynomial that the lattice reduction found become a theorem.
 *
 * == What makes the positive rows worth anything, which is the negative ones ==
 *
 * Every assertion here that something was **proved** is empty unless something comparable is
 * **refused**, and this file carries three refusals of three different kinds:
 *
 *  - a polynomial the caller chose that is simply wrong (`x^2 - 3` for a square root of two);
 *  - a polynomial the numeric half got **right** and that is still not a theorem, because the claim
 *    quantifies over every choice of sign and the numbers only ever saw one (`sqrt2 + sqrt8`);
 *  - a request that cannot be put at all.
 *
 * The second is the one to read. It is the architecture's own claim run as an experiment: the
 * untrusted search agreed with itself to more digits than `Relation.Confirmation` asks for and the
 * certification stopped it, which is exactly what `docs/adr/0005` says the two halves are for.
 */
class AlgebraicSpec extends AnyFlatSpec with Matchers {

  private val algebraic = Algebraic.standard
  private val show = Chain.standard.widest.show

  private def found(outcome: Outcome): Outcome.Found = outcome match {
    case f: Outcome.Found => f
    case other => fail(s"expected a certified polynomial and got $other")
  }

  /**
   * The largest case, run once and read twice.
   *
   * A `lazy val` rather than a call in each test: the degree-eight certification was two and a
   * half seconds of the suite when this was written on 2026-09-13, and asking for it a second time
   * to print its cost would double that without asking a second question.
   */
  private lazy val threeRoots = found(algebraic.of(Vector(Root(2, 2), Root(2, 3), Root(2, 5))))

  "The source" should "prove the polynomial of a single square root" in {
    val outcome = found(algebraic.of(Vector(Root(2, 2))))

    outcome.coefficients shouldBe Vector(BigInt(-2), BigInt(0), BigInt(1))
    show(outcome.theorem.conclusion) shouldBe "!x:real. x * x = 2 ==> Power x 2 - 2 = 0"
    outcome.theorem.hypotheses shouldBe empty
  }

  it should "prove the quartic a sum of two square roots satisfies" in {
    val outcome = found(algebraic.of(Vector(Root(2, 2), Root(2, 3))))

    // x^4 - 10x^2 + 1, which a reader checks by squaring twice: (sqrt2 + sqrt3)^2 is 5 + 2 sqrt6,
    // and (5 + 2 sqrt6)^2 is 49 + 20 sqrt6, which is 10 * (5 + 2 sqrt6) - 1.
    outcome.coefficients shouldBe Vector(BigInt(1), BigInt(0), BigInt(-10), BigInt(0), BigInt(1))
    show(outcome.theorem.conclusion) shouldBe
      "!x:real. !y:real. x * x = 2 ==> y * y = 3 ==> " +
      "Power (x + y) 4 - 10 * Power (x + y) 2 + 1 = 0"
    outcome.theorem.hypotheses shouldBe empty
  }

  it should "prove the degree-eight polynomial `RelationSpec` could only measure" in {
    val outcome = threeRoots

    outcome.coefficients shouldBe
      Vector(576, 0, -960, 0, 352, 0, -40, 0, 1).map(BigInt.apply)
    outcome.theorem.hypotheses shouldBe empty
    outcome.confirmed.getOrElse(0) should be >= Relation.Confirmation

    // The statement as a reader meets it, which is the half this source is for and which it did
    // not have until 2026-09-13: the same claim written with the multiplication spelled out
    // carried twenty copies of `(x + y + z)`, and a reader comparing it with "the minimal
    // polynomial is x^8 - 40x^6 + ..." was counting copies rather than reading.
    show(outcome.theorem.conclusion) shouldBe
      "!x:real. !y:real. !z:real. x * x = 2 ==> y * y = 3 ==> z * z = 5 ==> " +
      "Power (x + y + z) 8 - 40 * Power (x + y + z) 6 + 352 * Power (x + y + z) 4 - " +
      "960 * Power (x + y + z) 2 + 576 = 0"
  }

  it should "reach a degree the two-element case cannot, with cube roots" in {
    val outcome = found(algebraic.of(Vector(Root(3, 2), Root(3, 3))))

    // x^9 - 15x^6 - 87x^3 - 125, and the derivation a reader can follow: with a^3 = 2 and b^3 = 3,
    // (a+b)^3 = 5 + 3ab(a+b), so (t^3 - 5)^3 = 27 (ab)^3 t^3 = 162 t^3 since (ab)^3 = 6.
    outcome.coefficients shouldBe
      Vector(-125, 0, 0, -87, 0, 0, -15, 0, 0, 1).map(BigInt.apply)
    outcome.theorem.hypotheses shouldBe empty

    // The defining equations stay written as products and only the polynomial is a power, which is
    // not an oversight: `x * x * x = 2` is what says a reader is looking at a cube root, and
    // `Power x 3 = 2` says the same thing with one more thing to unfold.
    show(outcome.theorem.conclusion) shouldBe
      "!x:real. !y:real. x * x * x = 2 ==> y * y * y = 3 ==> " +
      "Power (x + y) 9 - 15 * Power (x + y) 6 - 87 * Power (x + y) 3 - 125 = 0"
  }

  it should "mix the degrees of its roots, where the polynomial stops being even" in {
    // Every case above is a sum of roots of one degree, and every polynomial they produce has zero
    // odd coefficients: `x^8 - 40x^6 + ...` has no `x^7` and no `x`. That is a property of the
    // symmetry, not of the search, and it is why the coverage report found the degree-one spelling
    // had never been exercised by anything the source actually produced.
    //
    // `sqrt2 + cbrt2` breaks the symmetry and the odd coefficients appear, found by the search
    // rather than constructed to make a branch run. The polynomial is also checkable from outside
    // this repository: it is the known minimal polynomial of that value, and it was recomputed
    // independently from the six conjugates before this test was written rather than read off what
    // the search reported.
    val outcome = found(algebraic.of(Vector(Root(2, 2), Root(3, 2))))

    outcome.coefficients shouldBe Vector(-4, -24, 12, -4, -6, 0, 1).map(BigInt.apply)
    outcome.coefficients.zipWithIndex.exists { case (c, k) => k % 2 == 1 && c != 0 } shouldBe true
    outcome.theorem.hypotheses shouldBe empty

    // The two defining equations carry different degrees, which no other case here does, and the
    // linear term is written bare.
    show(outcome.theorem.conclusion) shouldBe
      "!x:real. !y:real. x * x = 2 ==> y * y * y = 2 ==> " +
      "Power (x + y) 6 - 6 * Power (x + y) 4 - 4 * Power (x + y) 3 + 12 * Power (x + y) 2 - " +
      "24 * (x + y) - 4 = 0"
  }

  it should "certify a multiple of the minimal polynomial, which is what it says it does not exclude" in {
    // The docstring is explicit that a certified polynomial need not be the minimal one, and
    // nothing asserted it. `(x^2 - 2)(x + 1)` annihilates every real whose square is two, for the
    // same reason and by the same certificate.
    //
    // It was written to cover the degree-one spelling, which the coverage report found had never
    // run, and it is no longer the only case here that reaches it: the mixed-degree row above has a
    // linear term the search produced rather than one chosen to make a branch execute. Both stay,
    // because they demonstrate different things. That one says the source finds odd coefficients
    // when the symmetry allows them; this one says a certificate does not require minimality, which
    // is a property of the method and not of any particular value.
    val outcome = found(
      algebraic.certifying(Vector(Root(2, 2)), Vector(-2, -2, 1, 1).map(BigInt.apply))
    )

    show(outcome.theorem.conclusion) shouldBe
      "!x:real. x * x = 2 ==> Power x 3 + Power x 2 - 2 * x - 2 = 0"
    outcome.theorem.hypotheses shouldBe empty

    // The first degree written bare and not as `Power x 1`, which is the whole of that branch:
    // `x^1` is `x` to a reader and the two expand to the same thing.
    show(outcome.theorem.conclusion) should not include "Power x 1"
  }

  /* ------------------------------------------------------------- the refusals */

  it should "refuse a polynomial that does not annihilate the roots" in {
    // Pointed at a case whose answer is known before it runs: a square root of two does not satisfy
    // x^2 - 3, the reduction leaves -1, and no certificate exists to offer `Ring`. Without this row
    // every positive row above is a procedure agreeing with itself.
    algebraic.certifying(Vector(Root(2, 2)), Vector(BigInt(-3), BigInt(0), BigInt(1))) match {
      case Outcome.NotInTheIdeal(remainder, _) => remainder shouldBe "(neg 1)"
      case other => fail(s"expected a refusal and got $other")
    }
  }

  it should "refuse a polynomial the numbers got right, where the claim quantifies wider" in {
    // `sqrt2 + sqrt8` is `3 sqrt2`, so the numeric half is correct that the value satisfies
    // x^2 - 18. The claim is about **every** pair whose squares are 2 and 8, and the pair
    // (sqrt2, -2 sqrt2) sums to -sqrt2, whose square is 2. So the claim is false and the
    // certification says so, leaving `2xy - 8` behind.
    algebraic.of(Vector(Root(2, 2), Root(2, 8))) match {
      case Outcome.NotInTheIdeal(remainder, coefficients) =>
        remainder shouldBe "2 * x * y - 8"
        coefficients shouldBe Vector(BigInt(-18), BigInt(0), BigInt(1))
      case other => fail(s"expected a refusal and got $other")
    }
  }

  it should "have got that value right in the numbers, so the refusal is the kernel's and not the screen's" in {
    // The other half of the row above, and what stops it reading as "the numeric search failed".
    // The search did not fail: it found x^2 - 18 and was confirmed by digits to spare.
    val arithmetic = Arbitrary.to(Algebraic.Digits)
    val alpha = arithmetic.sum(
      Vector(2, 8).map(n =>
        arithmetic.power(BigDecimal(n), arithmetic.over(Vector(BigDecimal(1), BigDecimal(2))).get).get
      )
    )
    val powers = (0 to 2).toVector.map(k => arithmetic.power(alpha, BigDecimal(k)).get)

    Relation.among(powers, Algebraic.Digits) match {
      case Relation.Found(coefficients, confirmed, _) =>
        coefficients.map(_.abs) shouldBe Vector(BigInt(18), BigInt(0), BigInt(1))
        confirmed should be >= Relation.Confirmation
      case other => fail(s"the numeric half was supposed to succeed here and gave $other")
    }
  }

  it should "say it found nothing the digits support, which is not the same as no relation" in {
    // The row that keeps `NotCredible` from being a synonym for `NotInTheIdeal`. `RelationSpec`
    // measures the same value along a ladder of precisions and shows it coming back as noise at the
    // low end of it; here the whole source is run at twenty, walks every degree up to the bound,
    // and reports that nothing it found was confirmed by enough digits to be worth reporting.
    //
    // A reader acting on this raises the precision. A reader acting on `NotInTheIdeal` does not,
    // because no number of digits changes it, and `Remedy` sends the two to different places.
    Algebraic(Chain.standard, 20).of(Vector(Root(2, 2), Root(2, 3), Root(2, 5))) match {
      case Outcome.NotCredible(_, confirmed, bound) =>
        confirmed should be < Relation.Confirmation
        bound shouldBe 8
      case other => fail(s"expected an unconfirmed search and got $other")
    }
  }

  it should "refuse a precision too small to scale by at all" in {
    // One step further down, where the question cannot be put rather than answered badly: at four
    // digits there are fewer than two decimal places left to scale the lattice by once the size of
    // the values is paid for, and `Relation` says so instead of reducing a lattice of noise.
    Algebraic(Chain.standard, 4).of(Vector(Root(2, 2), Root(2, 3))) shouldBe a[Outcome.Unusable]
  }

  it should "refuse a request it cannot put, by which half of it is missing" in {
    algebraic.of(Vector.empty) shouldBe a[Outcome.Unusable]
    algebraic.of(Vector(Root(0, 2))) shouldBe a[Outcome.Unusable]
    algebraic.of(Vector(Root(2, 0))) shouldBe a[Outcome.Unusable]
    algebraic.of(Vector(Root(2, -3))) shouldBe a[Outcome.Unusable]
    algebraic.certifying(Vector(Root(2, 2)), Vector(BigInt(0), BigInt(0))) shouldBe a[Outcome.Unusable]
    algebraic.certifying(Vector.empty, Vector(BigInt(1))) shouldBe a[Outcome.Unusable]
  }

  it should "name a fourth root and beyond, which three letters cannot" in {
    // Read directly rather than by running a four-radical search, which would walk to degree
    // sixteen to answer a question about a string.
    Vector(0, 1, 2, 3, 4).map(Algebraic.nameOf) shouldBe Vector("x", "y", "z", "x4", "x5")
  }

  it should "print the zero polynomial as a zero, and not as nothing" in {
    // The empty `Map` is the zero polynomial, and an empty string in the middle of a claim is not
    // a term. Both halves are asserted, because the second is what the first would silently
    // become: `constant(0, n)` has to give back the empty map rather than a monomial with a zero
    // coefficient, or every later comparison against `zero` stops working.
    import Algebraic.Polynomial as Q
    Q.show(Q.zero, Vector("x")) shouldBe "0"
    Q.constant(BigInt(0), 2) shouldBe Q.zero
    Q.show(Q.constant(BigInt(-1), 1), Vector("x")) shouldBe "(neg 1)"
  }

  /* ------------------------------------------------------------- the machinery */

  it should "walk the degrees upward rather than take the bound it was given" in {
    // A square root of nine is 3, whose polynomial is x - 3 at degree one, and the bound the roots
    // give is two. If the search took the bound it would report a multiple of the answer, so this
    // asserts the degree and not only the coefficients. It is also refused at the certification for
    // the sign reason above, which is why the assertion is on what the search produced.
    val arithmetic = Arbitrary.to(Algebraic.Digits)
    val three = arithmetic.power(BigDecimal(9), arithmetic.over(Vector(BigDecimal(1), BigDecimal(2))).get).get
    Relation.among(Vector(BigDecimal(1), three), Algebraic.Digits) match {
      case Relation.Found(coefficients, _, _) => coefficients.length shouldBe 2
      case other => fail(s"a relation at degree one was expected and got $other")
    }
    algebraic.of(Vector(Root(2, 9))) match {
      case Outcome.NotInTheIdeal(_, coefficients) => coefficients shouldBe Vector(BigInt(-3), BigInt(1))
      case other => fail(s"expected the degree-one candidate and got $other")
    }
  }

  it should "reduce a polynomial to a remainder and cofactors that reconstruct it" in {
    // The untrusted arithmetic on its own, checked against the identity it claims rather than
    // against its own output: for `p` with `x^2 = 2` and `y^2 = 3`, the cofactors and the remainder
    // must add back up to `p` as polynomials. A reduction that lost a term would pass every test
    // above by producing a certificate `Ring` happens to accept only if the loss were also in the
    // claim, and this is the row that says it is not.
    import Algebraic.Polynomial as Q

    val x = Q.variable(0, 2)
    val y = Q.variable(1, 2)
    val p = Q.add(Q.power(Q.add(x, y), 5, 2), Q.scale(Q.multiply(x, Q.power(y, 4, 2)), BigInt(7)))
    val degrees = Vector(2, 2)
    val radicands = Vector(BigInt(2), BigInt(3))
    val (remainder, cofactors) = Q.reduce(p, degrees, radicands)

    remainder.keys.foreach(monomial => monomial.foreach(_ should be < 2))

    val rebuilt = cofactors.indices.foldLeft(remainder) { (acc, i) =>
      val defining = Q.add(Q.power(Q.variable(i, 2), degrees(i), 2), Q.constant(-radicands(i), 2))
      Q.add(acc, Q.multiply(cofactors(i), defining))
    }
    rebuilt shouldBe p
  }

  it should "cost what it costs, reported and not asserted" in {
    // A count rather than a clock: the inferences the largest case here takes. It is printed so a
    // later reader can see whether it moved, and asserted only loosely, because an exact figure
    // would break on any improvement to the shared lemmas underneath and tell nobody anything.
    val outcome = threeRoots
    info(s"sqrt2 + sqrt3 + sqrt5: ${outcome.inferences} inferences, " +
      s"confirmed to ${outcome.confirmed.getOrElse(0)} digits")
    outcome.inferences should be > 0
    Derivation.size(outcome.theorem) shouldBe outcome.inferences

    // The class docstring's example shows this outcome, and the digits it is confirmed to are a
    // function of `Algebraic.Digits` and the coefficients rather than of the machine, so they are
    // held to what the procedure returns: a digit there was compared with nothing until 2026-09-24.
    val confirmed = outcome.confirmed.getOrElse(fail("the three roots came back unconfirmed"))
    val source = new String(
      java.nio.file.Files.readAllBytes(
        java.nio.file.Paths.get("modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Algebraic.scala")
      ),
      "UTF-8"
    )
    source should include(s"1 0 -40 0 352 0 -960 0 576, confirmed to $confirmed digits)")
  }
}
