package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The shape nothing here could settle, settled without a theorem.
 *
 * Every assertion below is about a decision and none is about a proof. `Quantified` eliminates
 * quantifiers over untrusted linear forms and says whether a claim holds over the reals; it builds
 * no `Kernel.Thm` and nothing in this file should be read as certifying anything.
 */
class QuantifiedSpec extends AnyFlatSpec with Matchers {

  private val quantified = Quantified.standard

  private def decide(text: String): Quantified.Verdict =
    quantified.decide(text).fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  "The quantifier swap" should "come out differently each way round" in {
    // The reason this exists. `docs/evaluation.md` called it the failure autoformalisation is most
    // known for and the one thing this system had nothing to say about, and track T reported it as
    // the one trap of nine it could not separate.
    decide("!x:real. ?y:real. x < y") shouldBe Quantified.Holds
    decide("?y:real. !x:real. x < y") shouldBe Quantified.Fails

    // And downwards, since an order unbounded above and one unbounded below are two facts.
    decide("!x:real. ?y:real. y < x") shouldBe Quantified.Holds
    decide("?y:real. !x:real. y < x") shouldBe Quantified.Fails
  }

  "The order's own facts" should "come out as they should, which is the control on the elimination" in {
    // A procedure that answered `Holds` to everything would pass the pair above. These are the
    // statements whose truth is not in doubt, in both directions.
    decide("!x:real. x < x + 1") shouldBe Quantified.Holds
    decide("!x:real. x <= x") shouldBe Quantified.Holds
    decide("!x:real. ~(x < x)") shouldBe Quantified.Holds
    decide("!x:real y:real. x < y ==> ~(y < x)") shouldBe Quantified.Holds

    decide("!x:real. 0 < x") shouldBe Quantified.Fails
    decide("!x:real. ?y:real. x < y /\\ y < x") shouldBe Quantified.Fails
    decide("?x:real. x < x") shouldBe Quantified.Fails
  }

  "Density and betweenness" should "be decided, which is the shape an analysis claim has" in {
    // The two nested alternations a limit argument is written with, and the first thing anyone
    // formalising an epsilon-delta statement asks about.
    decide("!x:real y:real. x < y ==> ?z:real. x < z /\\ z < y") shouldBe Quantified.Holds
    decide("!e:real. 0 < e ==> ?d:real. 0 < d /\\ d < e") shouldBe Quantified.Holds
    decide("?d:real. !e:real. 0 < e ==> 0 < d /\\ d < e") shouldBe Quantified.Fails
  }

  "A free variable" should "be read as universally quantified, since that is what asking means" in {
    // `0 < x` with `x` free is not a question about some `x`: it is the claim, and the claim is
    // false. Deciding the instance instead would answer a question nobody asked.
    decide("x:real < x:real + 1") shouldBe Quantified.Holds
    decide("0 < x:real") shouldBe Quantified.Fails
  }

  "A statement that is not linear" should "be refused by name, not eliminated as far as it goes" in {
    // `LinearForm.of` holds a product of two unknowns as an opaque atom, so the elimination has
    // nothing to range over and would otherwise report an answer about a statement it had not read.
    decide("?x:real. !y:real. x * y = 0") match {
      case Quantified.Refused(why) => why should include("atom")
      case other => fail(s"expected a refusal about the atom, got $other")
    }

    decide("!x:real. 0 < x ==> 0 < inv x") match {
      case Quantified.Refused(why) => why should include("atom")
      case other => fail(s"expected a refusal about the atom, got $other")
    }
  }

  "A leaf that is not a relation between reals" should "be refused, and never decided" in {
    // The invariant: this procedure answers only about statements it has read as linear forms over
    // the reals, and a proposition it cannot read is a refusal rather than an atom to range over.
    //
    // What makes it worth a test of its own is what the other reading would have said. Until
    // 2026-09-10 this read a leaf through `LinearFact.of`, whose documented fallthrough turns a
    // proposition it cannot take apart into the strict fact `0 < p` over an atom nobody else
    // mentions. That is right for a procedure that ends in a theorem or in nothing, and it made
    // this one report that `p \/ ~p` HOLDS over the reals, because `0 < p \/ ~(0 < p)` is a
    // tautology over an ordered field. This logic has no excluded middle and cannot prove that
    // formula, and the claim is not about the reals at all: it is the shape of answer
    // `docs/adr/0005` exists to keep out, an answer to a question nobody asked wearing the form a
    // reader is invited to check. `LinearFact.relation` is `factOf` without the fallthrough and is
    // what this reads through now.
    val excludedMiddle = quantified.decide("p:bool \\/ ~ p:bool")

    excludedMiddle match {
      case Right(Quantified.Refused(why)) => why should include("relation")
      case other => fail(s"expected a refusal naming the leaf, got $other")
    }

    // And the same for a bare proposition, so that neither half of the disjunction is what carried
    // it. A boolean variable is not a quantity this procedure can range over in either polarity.
    quantified.decide("!x:real. p:bool \\/ x < x + 1") match {
      case Right(Quantified.Refused(why)) => why should include("relation")
      case other => fail(s"expected a refusal naming the leaf, got $other")
    }

    // The control, and it is the half that says the repair was a narrowing and not a mutilation:
    // a body built only from relations between reals is still decided, in both directions.
    decide("!x:real. x < x + 1 \\/ x + 1 < x") shouldBe Quantified.Holds
    decide("!x:real. x < x + 1 /\\ x + 1 < x") shouldBe Quantified.Fails
  }

  "The elimination" should "stop and say so rather than run on" in {
    // Negation turns a disjunction into a product of choices, so an alternating prefix over a wide
    // body grows as the product. The budget is what keeps a caller from waiting without being told
    // why, and this is the assertion that it is reached rather than merely written down.
    val wide = (1 to 14).map(index => s"$index < x:real \\/ x:real < -$index").mkString(" /\\ ")

    quantified.decide(s"!x:real. $wide") match {
      case Right(Quantified.Refused(why)) => why should include("cases")
      case other => fail(s"expected the budget to stop it, got $other")
    }
  }

  "The source" should "never reach for an inference rule, which is what keeps it untrusted" in {
    // The whole placement of this file rests on it producing no theorem, and a type signature says
    // so only until somebody adds a second entry point. A scan says it for the file. Written this
    // way rather than as a runtime check on the verdict, because `Kernel.Thm` is opaque and erases
    // to a pair, so `should not be a[Kernel.Thm]` would pass whatever the file did: that is the
    // vacuous assertion this repository has already been caught writing once.
    val source = java.nio.file.Files.readString(
      java.nio.file.Paths.get("modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Quantified.scala")
    )

    val rules = Vector(
      "Kernel.refl", "Kernel.trans", "Kernel.mkComb", "Kernel.abs", "Kernel.beta", "Kernel.assume",
      "Kernel.eqMp", "Kernel.deductAntisym", "Kernel.inst", "Kernel.instType",
      "Kernel.defineConstant", "Kernel.assertAxiom", "Kernel.defineType"
    )

    val reached = rules.filter(source.contains)
    withClue(s"names an inference rule: ${reached.mkString(", ")}\n") { reached shouldBe empty }

    // And it does prove the thing it is named for, so the scan is not passing because the file is
    // empty.
    source should include("Fourier-Motzkin")
    decide("!x:real. x < x + 1") shouldBe Quantified.Holds
  }
}
