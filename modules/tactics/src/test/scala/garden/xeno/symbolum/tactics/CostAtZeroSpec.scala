package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * What the whole tactic surface answers about `inv 0`, now that the constructed reals fix it.
 *
 * `inv 0 = 0` is a theorem of the chain since `docs/adr/0053` (`theories.InverseAtZeroSpec`
 * derives it), and before that it was independent of the sixteen. So two answers here would be
 * wrong rather than weak: `Fails` on the claim, which files a theorem as false, and `Proved` or
 * `Holds` on a denial of it, which would be an inconsistency or a false decision. What else each
 * claim gets is printed, because it says how far the surface reaches and nothing here pins it.
 *
 * Written by the verification of the card that constructed the reals.
 */
class CostAtZeroSpec extends AnyFlatSpec with Matchers {

  private val cost = Cost.standard

  private def outcome(text: String): Cost.Outcome =
    cost.of(text).fold(error => fail(s"$text: ${error.message}"), report => {
      info(s"$text: ${report.outcome}${report.refusal.map(r => s", ${TacticError.standing(r)}: ${r.message}").getOrElse("")}")
      report.outcome
    })

  "A claim true of inv 0 in the constructed reals" should "never be filed as failing" in {
    Vector("inv (0:real) = 0", "!x:real. x / 0 = 0", "!x:real. x * inv 0 = 0").foreach { text =>
      withClue(s"$text: ") { outcome(text) should not be Cost.Outcome.Fails }
    }
  }

  "A claim false of inv 0 in the constructed reals" should "never be proved or decided to hold" in {
    Vector("inv (0:real) = 1", "~(inv (0:real) = 0)", "?x:real. ~(x / 0 = 0)").foreach { text =>
      withClue(s"$text: ") {
        val answer = outcome(text)
        answer should not be Cost.Outcome.Proved
        answer should not be Cost.Outcome.Holds
      }
    }
  }
}
