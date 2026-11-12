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

  "amc12_2000_p20" should "follow once its denominators are cleared and its difference squared" in {
    // The three positivity hypotheses are what clears `1 / x`, `1 / y` and `1 / z`, and then
    // `(x * y * z - 1)^2` is in the ideal while `x * y * z - 1` is not.
    proved(
      "!x y z:real. 0 < x /\\ 0 < y /\\ 0 < z ==> x + 1 / y = 4 ==> y + 1 / z = 1 ==> z + 1 / x = 7 / 3 ==> " +
        "x * y * z = 1"
    )
  }

  "amc12b_2002_p19" should "follow once the order says which root of its difference's polynomial is meant" in {
    // `x * y * z - 720` is outside the ideal and so are its squares; what the ideal holds is the
    // difference times a cofactor, and the cofactor is positive under the three hypotheses.
    proved(
      "!x y z:real. 0 < x /\\ 0 < y /\\ 0 < z ==> x * (y + z) = 152 ==> y * (z + x) = 162 ==> " +
        "z * (x + y) = 170 ==> x * y * z = 720"
    )
  }

  "amc12b_2002_p7" should "follow once the order rules out the roots below zero" in {
    // Over the reals here, where `ReachSpec` reads it over `real_of_num` atoms: the cubic has the
    // roots `-6`, `-1` and `4`, and only the last is positive.
    proved(
      "!a b c:real. 0 < a /\\ 0 < b /\\ 0 < c ==> b = a + 1 ==> c = b + 1 ==> " +
        "a * b * c = 8 * (a + b + c) ==> a * a + (b * b + c * c) = 77"
    )
  }

  "A root the order picks from below" should "be proved through the cofactor's negation" in {
    // The ideal holds `(x + 1) * (x - 1)`, and `x - 1` is negative here, so its sign is proved as
    // `0 < -(x - 1)`: the second of the two the search asks.
    proved("!x:real. x < 0 ==> x * x = 1 ==> x = neg 1")
  }

  "A root the order does not pick" should "be refused as outside the ideal and never as decided" in {
    // `x * x = x` has the roots `0` and `1`, and nothing says which: the cofactor `x` has no sign
    // under the hypotheses, so the order adds nothing and the refusal is the ideal's.
    val error = refused("!x:real. x * x = x ==> x = 1")
    error shouldBe a[OutsideTheIdeal]
    error.standing shouldBe LogicError.Standing.Unread
  }

  "x * x = 0 ==> x = 0" should "be proved through the radical, being outside the ideal itself" in {
    proved("!x:real. x * x = 0 ==> x = 0")
  }

  "A cube that vanishes" should "need two squarings, its square not being in the ideal either" in {
    proved("!x:real. x * x * x = 0 ==> x = 0")
  }

  "A fifth power that vanishes" should "be refused, since x^8 is past the squarings asked and x^4 is not a member" in {
    // The bound Ideal.Squarings drawn where it is, as a refusal and not a decision: the claim is true.
    val error = refused("!x:real. x * x * x * x * x = 0 ==> x = 0")
    error shouldBe a[OutsideTheIdeal]
    error.standing shouldBe LogicError.Standing.Unread
  }

  "x * x + y * y = 0 ==> x = 0" should "be refused as outside the ideal, and never as decided, because it is true" in {
    // True of the reals and of no power of x: the real radical is larger than any power reaches.
    val error = refused("!x y:real. x * x + y * y = 0 ==> x = 0")
    error shouldBe a[OutsideTheIdeal]
    error.standing shouldBe LogicError.Standing.Unread
  }

  "A denominator the hypotheses say is positive" should "be cleared" in {
    proved("!x y:real. 0 < y ==> x = 1 / y ==> x * y = 1")
  }

  "A denominator stated not to be zero" should "be cleared" in {
    proved("!x y:real. ~(y = 0) ==> x = 1 / y ==> x * y = 1")
  }

  "A denominator nobody said anything about" should "stay an unknown, the claim being false at zero" in {
    // At y = 0 the reals give inv 0 = 0, so x = 0 and x * y = 0: assuming y * inv y = 1 here would
    // prove something false.
    refused("!x y:real. x = 1 / y ==> x * y = 1") shouldBe a[OutsideTheIdeal]
  }

  "A claim needing the order" should "be proved, the order saying which root is meant" in {
    // This was the line drawn under the ideal alone, and was refused as outside it until the order
    // joined: `a * a - 4` is `(a - 2) * (a + 2)`, and `a + 2` is positive under `0 < a`. The refusal
    // the line now rests on is `x * x = x ==> x = 1` above, where neither root is excluded.
    proved("!a:real. 0 < a ==> a * a = 4 ==> a = 2")
  }

  "A search that runs out of budget" should "say so, and not that the goal is outside the ideal" in {
    // The same goal `mathd_algebra_338` proves above, at a budget its search spends eighty times over.
    val starved = Ideal.at(Order.standard, 1)
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
