package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Whether a derivation that records itself comes out at the size of an essay.
 *
 * The spike of 2026-09-13, and the question it exists to settle is a measurement rather than a
 * design preference. A theorem's `Derivation` is at the kernel's size: over the library the median
 * lemma is 4651 inferences, 70% of the nodes are congruence, equality elimination, transitivity and
 * reflexivity, and collapsing the graph at every node that is a named lemma leaves 791 anonymous
 * steps in the median. The claim being tested is that the account a reader wants is one the
 * **author** has and the record does not, so capturing it where it exists costs a receiver at each
 * call site and gives a derivation of twenty lines instead of seven thousand.
 *
 * Three of `Magnitude`'s fourteen derivations are converted. Three rather than one because one
 * proves nothing about the shape of the others, and three rather than fourteen because the point of
 * a spike is to be cheap enough to throw away.
 *
 * == What is asserted, and why each assertion is not vacuous ==
 *
 * The compression is a **reading**, printed with its ratio, because a bound on it would be a bound
 * on how the underlying lemmas happen to be proved and would go red on a change that improved them.
 * What is asserted instead are the two properties that make an account worth printing at all:
 *
 *  - **the account ends where the theorem does.** A script whose last step is not the fact it is
 *    filed under is describing another derivation, which is the failure mode that would make every
 *    generated document quietly wrong. An empty script passes every other check here and fails this
 *    one, which is what makes the others non-trivial.
 *  - **every premise of every step is nameable**: a lemma some development holds, or the result of
 *    an earlier step of the same account. A premise that is neither renders as a bare sequent, and a
 *    document full of bare sequents is the thing this is supposed to replace. This is the assertion
 *    that fails first if a derivation takes an operation from `rules` directly instead of from the
 *    recorder, since the theorem it produced then belongs to no step.
 */
class MagnitudeScriptSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val magnitude = chain.magnitude
  private val library = Library.of(chain)

  /**
   * Every lemma of the chain, and this development's definitions beside them.
   *
   * The definitions are not decoration and their absence is what the first run of this spike found:
   * a rewriting step whose rule comes from the definition of `min` cites a theorem that is in no
   * library, so it printed as a bare sequent in the middle of an otherwise named account.
   * `Library.of` collects a development's `facts` and not its `definitions`, which is right for a
   * document listing what has been proved and wrong for an account of how something was derived.
   */
  private val names: Map[Kernel.Thm, String] =
    Script.names(
      Vector(
        library.entries.map(entry => (entry.name, entry.theorem)).toMap,
        magnitude.definitions.map { case (constant, theorem) =>
          (s"the definition of $constant", theorem)
        }
      )
    )

  /**
   * The one account that is longer than the cap, with the reason and the measurement.
   *
   * **A script is self-contained: it replays every account it rests on**, which is the property
   * the four `max` facts are written to have and the reason a reader can be handed one without
   * being handed a library first. So a fact three layers up carries the length of everything under
   * it, and `ABS_MUL` is the first one here that is: measured on 2026-09-20 its 182 steps are the
   * 87 of `ABS_OF_NONNEG`, the 83 of `ABS_OF_NONPOS` and its own four cases, with the shared
   * opening counted once.
   *
   * The cap is **raised for it and not removed**, and the ratio assertion below is untouched:
   * that one is what the sentence about two orders of magnitude means, and `ABS_MUL` reads 1:75
   * against it. What a bound of 120 would buy here is a derivation restructured to make an account
   * shorter by hiding steps, which is the opposite of what these scripts are for.
   */
  private val Ceiling: Map[String, Int] = Map(Magnitude.Multiplicative -> 200)

  "A recorded derivation" should "exist for every fact, and end at the theorem it is filed under" in {
    // Every fact and no more: a script filed under a name that is not a fact would pass the check
    // below vacuously, since there would be nothing to compare it against.
    magnitude.scripts.keySet shouldBe magnitude.facts.keySet

    magnitude.scripts.foreach { case (name, script) =>
      script.steps should not be empty
      script.steps.last.result shouldBe magnitude.facts(name)
    }
  }

  it should "cite only lemmas, its own earlier steps, and what it names itself" in {
    magnitude.scripts.foreach { case (name, script) =>
      script.steps.zipWithIndex.foreach { case (step, position) =>
        val reachable = script.steps.take(position).map(_.result).toSet
        val nameable = names ++ script.localNames

        step.premises.foreach { premise =>
          withClue(s"$name step ${position + 1} (${step.rule}) cites an unnameable premise: ") {
            (nameable.contains(premise) || reachable.contains(premise)) shouldBe true
          }
        }
      }
    }
  }

  it should "be shorter than the proof it describes by two orders of magnitude" in {
    val readings = magnitude.scripts.toVector.sortBy(_._1).map { case (name, script) =>
      val inferences = Derivation.size(magnitude.facts(name))
      (name, script.size, inferences)
    }

    // Printed rather than asserted, for the reason the class comment gives.
    readings.foreach { case (name, steps, inferences) =>
      info(f"$name%-16s $steps%3d recorded steps, $inferences%6d kernel inferences, 1 : ${inferences.toDouble / steps}%.0f")
    }

    readings.foreach { case (name, steps, inferences) =>
      withClue(s"$name: ")(steps should be < Ceiling.getOrElse(name, 120))
      withClue(s"$name: ")(steps should be < inferences / 20)
    }
  }

  it should "open the triangle inequality at the foundation and reach it through the named lemmas" in {
    val script = magnitude.scripts(Magnitude.Triangle)

    // Self-containedness, stated as what it is: the first line rests on nothing this account has
    // not shown, so it cites nothing. Until the whole file was converted this account opened on
    // `ABS_ABOVE` as a citation, and the assertion here said so; it opens on the trichotomy of the
    // order now, because the derivation of `ABS_ABOVE` is part of it.
    script.steps.head.premises shouldBe empty

    // On the theorems and not on the rendering, which is the discipline this whole exercise is
    // most exposed to: the product here IS text, so a check that read the text would be checking
    // the thing it is supposed to be evidence about. `names` is keyed by the sequent, so these say
    // the derivation leant on the lemmas held under those names, whatever gets printed.
    val cited = script.steps.flatMap(_.premises).flatMap(names.get)
    cited should contain(Order.AddLe)
    cited should contain(Magnitude.AbsAbove)
    cited should contain(Magnitude.AbsCases)

    // One check of the rendering itself, and only of what the rendering adds: a premise that is
    // not a named lemma is referred to by the step that produced it.
    script.render(magnitude.notation, names) should include("step 1")
  }
}
