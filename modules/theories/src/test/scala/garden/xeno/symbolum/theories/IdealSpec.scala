package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * [[Ideal]] end to end: a goal in, a theorem resting on nothing out, or a refusal that says which of
 * its causes it is.
 *
 * The three goals that open this file are miniF2F statements, written here as `ReachSpec`'s reader
 * renders them (powers expanded into products, quotients by numerals kept), and they are the ones
 * `docs/adr/0029` sorts under "deciding a system" and that only an ideal reaches. The rest are the
 * refusals, and the one that matters most is the first: a true claim the ideal does not reach must
 * come back unread, never decided.
 */
class IdealSpec extends AnyFlatSpec with Matchers {

  private val ideal = Ideal.standard

  private def proved(text: String): Kernel.Thm = {
    val goal = ideal.reals.proposition(text).fold(error => fail(s"could not read $text: ${error.message}"), identity)
    ideal.prove(goal) match {
      case Right(theorem) =>
        theorem.hypotheses shouldBe empty
        theorem.conclusion shouldBe goal
        info(s"${Derivation.size(theorem)} inferences, search spent ${ideal.search(goal).map(spent)}")
        theorem
      case Left(error) => fail(s"$text was refused: ${error.message}")
    }
  }

  private def spent(membership: Groebner.Membership): Long = membership match {
    case Groebner.Membership.Member(_, spent) => spent
    case Groebner.Membership.NotMember(_, spent) => spent
    case Groebner.Membership.Exhausted(spent, _) => spent
  }

  private def refused(text: String): LogicError =
    ideal.prove(text) match {
      case Right(theorem) => fail(s"$text was proved: ${theorem.conclusion}")
      case Left(error) => info(error.message); error
    }

  "aime_1990_p15" should "follow from its four power sums" in {
    proved(
      "!a b x y:real. a * x + b * y = 3 /\\ a * (x * x) + b * (y * y) = 7 /\\ " +
        "a * (x * x * x) + b * (y * y * y) = 16 /\\ a * (x * x * x * x) + b * (y * y * y * y) = 42 ==> " +
        "a * (x * x * x * x * x) + b * (y * y * y * y * y) = 20"
    )
  }

  "mathd_algebra_338" should "follow from its linear system" in {
    proved(
      "!a b c:real. 3 * a + b + c = neg 3 /\\ a + 3 * b + c = 9 /\\ a + b + 3 * c = 19 ==> a * b * c = neg 56"
    )
  }

  "mathd_algebra_478" should "follow by substitution, with the order hypotheses assumed and unused" in {
    proved(
      "!b h v:real. (0 < b /\\ 0 < h /\\ 0 < v) /\\ v = 1 / 3 * (b * h) /\\ b = 30 /\\ h = 13 / 2 ==> v = 65"
    )
  }

  "A hypothesis that rewrites another's variable" should "not stop the certificate, since nothing is rewritten" in {
    // `b = a + 1` and `c = b + 1` both mention `b`: the case rewriting with the assumptions gets wrong.
    proved("!a b c:real. b = a + 1 ==> c = b + 1 ==> c = a + 2")
  }

  "x * x = 0 ==> x = 0" should "be refused as outside the ideal, and never as decided, because it is true" in {
    val error = refused("!x:real. x * x = 0 ==> x = 0")
    error shouldBe a[OutsideTheIdeal]
    error.standing shouldBe LogicError.Standing.Unread
  }

  "A claim needing the order" should "be refused as outside the ideal" in {
    // True of the reals, a = 2 being the positive root, and out of reach of any ideal.
    refused("!a:real. 0 < a ==> a * a = 4 ==> a = 2") shouldBe a[OutsideTheIdeal]
  }

  "A search that runs out of budget" should "say so, and not that the goal is outside the ideal" in {
    // The same goal `mathd_algebra_338` proves above, at a budget its search spends eighty times over.
    val starved = Ideal.at(Ring.standard, 1)
    starved.prove("!a b c:real. 3 * a + b + c = neg 3 /\\ a + 3 * b + c = 9 /\\ a + b + 3 * c = 19 ==> a * b * c = neg 56") match {
      case Left(error: BoundReached) => error.standing shouldBe LogicError.Standing.Exhausted
      case other => fail(s"came back $other")
    }
  }

  "A goal with no equation among its hypotheses" should "be refused by its shape" in {
    refused("!x:real. 0 < x ==> x = x + 0") shouldBe a[NotOfForm]
  }

  "A conclusion that is not an equation between reals" should "be refused by its shape" in {
    refused("!x:real. x = 1 ==> 0 < x") shouldBe a[NotOfForm]
  }
}
