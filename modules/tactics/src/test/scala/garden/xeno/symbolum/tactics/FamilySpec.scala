package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.theories.*

/**
 * A closed form guessed from numbers and then proved, which is the loop this repository is for.
 *
 * The conjecture card lists four sources for a generator in order of how much each has actually
 * discovered, and this is the fourth: compute a family's first few values, fit the polynomial
 * through them, and put the claim that they agree everywhere to the induction driver. It is the
 * only one of the four whose proposal step is arithmetic on numbers and whose check is a theorem,
 * which is the architecture the anchor note calls the honest one.
 *
 * What is asserted here is mostly that the four outcomes are not each other. A family with no
 * polynomial closed form, a family whose values cannot be computed, and a fit the prover refuses
 * are three different things, and a generator that reported them as one would be telling a reader
 * that the mathematics is absent when the reader is absent instead.
 */
class FamilySpec extends AnyFlatSpec with Matchers {

  private val family = Family.standard
  private val chain = Chain.standard
  private val signature: Signature = chain.widest

  private def found(text: String): Family.Outcome.Found =
    family.of(text) match {
      case outcome: Family.Outcome.Found => outcome
      case other => fail(s"$text: expected a closed form, got $other")
    }

  /* --------------------------------------------------------- what it finds */

  "The sum of the first n numbers" should "come back as a theorem, from its values alone" in {
    // Nothing was told what the answer is. The samples are 0, 0, 1, 3, 6, 10 and the second
    // difference is constant, so the fit is quadratic, and the claim that comes out is put to
    // `Induct` and either is a theorem or is not.
    val outcome = found("\\i:num. real_of_num i")

    outcome.degree shouldBe 2
    outcome.samples.take(6).map(_.toString) shouldBe Vector("0", "0", "1", "3", "6", "10")
    signature.show(outcome.claim) shouldBe
      "!x:num. Sum (\\y:num. real_of_num y) x = real_of_num x * (real_of_num x - 1) / 2"

    outcome.theorem.conclusion shouldBe outcome.claim
    outcome.theorem.hypotheses shouldBe empty

    info(s"${Derivation.size(outcome.theorem)} inferences over ${Derivation.axiomsOf(outcome.theorem).size} axioms")
  }

  it should "reach the degrees a person would want, which is where the source stops being a toy" in {
    // Faulhaber's first four, found rather than stated. The last of them is a quartic and is the
    // reason the sampling budget is ten rather than four: a polynomial of degree d wants d + 1
    // points and this keeps two in hand.
    Vector(
      ("\\i:num. 1", 1),
      ("\\i:num. real_of_num i", 2),
      ("\\i:num. real_of_num i * real_of_num i", 3),
      ("\\i:num. real_of_num i * real_of_num i * real_of_num i", 4)
    ).foreach { case (summand, degree) =>
      val outcome = found(summand)

      withClue(s"$summand: ") { outcome.degree shouldBe degree }
      outcome.theorem.hypotheses shouldBe empty
      info(s"$summand: degree ${outcome.degree}, ${Derivation.size(outcome.theorem)} inferences")

      // The quartic's cost is quoted in `docs/evaluation.md`, and until 2026-09-24 that digit was
      // compared with nothing: it said 37859 while this printed 29456. Spelled from the proof now.
      if (degree == 4) {
        val cost = Derivation.size(outcome.theorem)
        val evaluation = new String(
          java.nio.file.Files.readAllBytes(java.nio.file.Paths.get("docs/evaluation.md")),
          "UTF-8"
        ).replaceAll("\\s+", " ")
        withClue(s"the quartic is $cost inferences: ") {
          evaluation should include(
            s"found from the values 0, 0, 1, 9, 36, 100 and proved in $cost inferences"
          )
        }
      }
    }
  }

  it should "be the same polynomial as the form a book prints, which `Ring` decides" in {
    // The Newton basis is what the interpolation is done in and nothing rearranges it afterwards,
    // because rearranging is the untrusted simplifier deciding what the claim says. So the sum of
    // squares comes back as `x(x-1)/2 + x(x-1)(x-2)/3` and not as `x(x-1)(2x-1)/6`, and a reader
    // who wants the familiar one asks for a theorem rather than trusting a printer.
    val agree = chain.ring.prove(
      "!x:real. x * (x - 1) / 2 + x * (x - 1) * (x - 2) / 3 = x * (x - 1) * (2 * x - 1) / 6"
    )

    agree.fold(error => fail(error.message), _.hypotheses shouldBe empty)
  }

  /* ------------------------------------------------- what it declines, in three ways */

  "A family with no polynomial closed form" should "say that, and show what it computed" in {
    // A geometric sum has a closed form and it is not a polynomial, so no number of differences
    // will find it. The samples come back so that a reader can see the family rather than only
    // being told the fit failed: 0, 1, 3, 7, 15 is a recognisable sequence and "not polynomial" is
    // not the same as "nothing is known about it".
    family.of("\\i:num. Power 2 i") match {
      case Family.Outcome.NotPolynomial(samples, sampled) =>
        samples.take(5).map(_.toString) shouldBe Vector("0", "1", "3", "7", "15")
        sampled shouldBe Family.Points
      case other => fail(s"expected a refusal to fit, got $other")
    }
  }

  it should "have been unreadable before the power's recurrences were in the sampler, which is a worse answer" in {
    // Kept as a case rather than as a note: with only the sum's two recurrences the sampling stops
    // at `0 + Power 2 ZERO`, which is not a number, and the outcome is `Unreadable` — "the reader
    // failed" — for a family about which something perfectly definite is true. The two are told
    // apart by which equations the sampler holds, and the fix was to hold more of them.
    val narrow =
      Family.construct(chain).fold(error => fail(error.message), identity)

    narrow.of("\\i:num. Power 2 i") shouldBe a[Family.Outcome.NotPolynomial]
  }

  "A summand the recurrences cannot reduce" should "be unreadable, not an empty fit" in {
    // A summand naming something with no value leaves a term this cannot evaluate, and there is
    // nothing to fit. The message names where the reduction stopped, because that is what a caller
    // acts on: here it is `inv 0`, which this theory leaves an atom rather than a number, so the
    // first sample already has no value and the family is not one this can be asked about.
    family.of("\\i:num. inv (real_of_num i)") match {
      case Family.Outcome.Unreadable(why) =>
        // The message says which of the two things happened, and here it is the first: the
        // recurrences have nothing left to do and what is left is not a number. `Rewrite.rewrite`
        // hands back the theorem it had when the step limit ran out, so a rule set that does not
        // settle looks exactly like a term that is irreducible, and reporting both the same way
        // would say something false about the family in one of the two cases.
        why should include("nothing left to do")
        why should include("inv 0")
      case other => fail(s"expected an unreadable summand, got $other")
    }
  }

  "A summand that is not a function from the naturals" should "be refused rather than fitted" in {
    family.of("\\x:real. x") shouldBe a[Family.Outcome.Unreadable]
  }

  /* ------------------------------------------------------ what it guarantees */

  "Every closed form it reports" should "be a theorem of exactly the claim it fitted" in {
    // The guarantee, and the whole reason the fit is allowed to be a guess. The screen is ten
    // points of agreement, which is evidence and not a proof; what makes a `Found` worth anything
    // is that the theorem inside it is a theorem of the claim beside it, with nothing on its left.
    //
    // `NotCertified` is the bucket for a fit that agreed at every sampled point and did not hold:
    // it is reachable and no witness for it is known in this fragment, because a summand that
    // agrees with a polynomial for ten values and then diverges needs a case split, and until
    // 2026-09-12 the reader had no conditional to write one with. `COND` is in the signature now,
    // so such a summand can be **written**; what there is still no way to get is a fit that
    // produces one, since the Newton form this interpolates in has no branch in it. Stated rather
    // than tested, because a test that cannot be written is better admitted than faked.
    Vector(
      "\\i:num. 1",
      "\\i:num. real_of_num i",
      "\\i:num. 2 * real_of_num i + 1",
      "\\i:num. real_of_num i * real_of_num i",
      "\\i:num. 3 * real_of_num i * real_of_num i - real_of_num i + 7"
    ).foreach { summand =>
      val outcome = found(summand)

      withClue(s"$summand: ") {
        outcome.theorem.conclusion shouldBe outcome.claim
        outcome.theorem.hypotheses shouldBe empty
      }
    }
  }
}
