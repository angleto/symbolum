package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What the field tactic proves, and what it owes for it.
 *
 * Every assertion here is about the hypotheses as much as about the conclusion, because a theorem
 * from this tactic is only worth what its side conditions say. A test that checked the conclusion
 * alone would pass against a tactic that assumed anything it liked.
 */
class FieldSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val field = Field.standard
  private val reals = field.reals
  private val real: Type = TyApp(Real.TypeName, Nil)

  private def shown(theorem: Kernel.Thm): (List[String], String) =
    (theorem.hypotheses.map(reals.show), reals.show(theorem.conclusion))

  "The field tactic" should "build over the standard arithmetic" in {
    Field.construct(Arithmetic.standard) should matchPattern { case Right(_) => }
  }

  it should "cancel a denominator and say what it assumed to do it" in {
    // The statement `Ring` refuses, and the reason it refuses is here in the hypothesis rather
    // than gone. `y` stays free because `~(y = 0)` names it: quantifying a variable that a
    // hypothesis mentions is unsound and the kernel does not allow it, so the goal comes back one
    // quantifier short with the reason beside it.
    shown(force(field.prove("!x:real y:real. (x * y) / y = x"))) shouldBe
      (List("~(y = 0)"), "!x:real. x * y / y = x")

    shown(force(field.prove("!x:real. x * inv x = 1"))) shouldBe
      (List("~(x = 0)"), "x * inv x = 1")
  }

  it should "assume nothing when nothing had to be cancelled" in {
    // The property that keeps this tactic honest, and it holds by construction rather than by a
    // check: a side condition reaches the theorem only through the rewrite rule that carries it,
    // so a rule that never fired leaves nothing behind. Both of these mention a denominator and
    // neither needs it to be non-zero, because moving a quotient about is the definition of `div`
    // and not the axiom for `inv`.
    //
    // The first is also what decides the ORDER of the two attempts, since 2026-09-09. Splitting
    // `inv (2 * y)` is an inference like any other, so a rule that fires puts its conditions on
    // the theorem whether the proof needed them or not, and splitting first proved this one while
    // assuming `~(y = 0)` — a debt it does not owe, since it holds at `y = 0` too. So the split is
    // the second attempt, and this assertion is what would catch it moving back to being the
    // first.
    shown(force(field.prove("!x:real y:real z:real. (z * x) / (2 * y) = z * (x / (2 * y))"))) shouldBe
      (Nil, "!x:real. !y:real. !z:real. z * x / (2 * y) = z * (x / (2 * y))")

    shown(force(field.prove("!x:real y:real. x / y + x / y = 2 * (x / y)"))) shouldBe
      (Nil, "!x:real. !y:real. x / y + x / y = 2 * (x / y)")
  }

  it should "still decide the ring fragment, with nothing owed" in {
    shown(force(field.prove("!x:real y:real. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y"))) shouldBe
      (Nil, "!x:real. !y:real. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y")
  }

  it should "cancel more than one copy of a denominator" in {
    shown(force(field.prove("!x:real. inv x * x * inv x = inv x"))) shouldBe
      (List("~(x = 0)"), "inv x * x * inv x = inv x")
  }

  it should "refuse an equation that is not an identity even where the denominator is not zero" in {
    // Assuming `~(x = 0)` and `~(y = 0)` does not make this true, and the tactic does not pretend
    // otherwise: what it assumes buys cancellation and nothing else.
    field.prove("!x:real y:real. x / y = y / x").left.map(_.getClass) shouldBe
      Left(classOf[NotEqualTo])
  }

  it should "take an inverse of a product apart, and charge only for the factors in doubt" in {
    // Pinned here as a refusal until 2026-09-09: `inv (2 * y)` was one atom and stayed one, so a
    // common factor inside a denominator did not cancel against one outside it.
    //
    // What settles it is `Field.reciprocal`, which takes `2 * y` apart by recursion and builds
    // `(2 * y) * (inv 2 * inv y) = 1` out of the unit lemmas, `Coefficient.unitOfProduct` for the
    // product and `Coefficient.inverseOf` for the numeral; `Coefficient.inverseOfUnit` then turns
    // that into `inv (2 * y) = inv 2 * inv y` in one step. There is no lemma here about the inverse
    // of a symbolic product, and what such a lemma would have needed is the reason this arrived
    // when it did: `~(a = 0) ==> ~(b = 0) ==> ~(a * b = 0)`, the absence of zero divisors, is the
    // obvious premise and is a theorem with a case analysis behind it. `inverseOfUnit` makes it
    // unnecessary, because `inv a * inv b` multiplies `a * b` to one by rearranging, and a factor
    // of one is an inverse.
    //
    // Read the hypothesis list rather than only that it proved. The `2` costs nothing, because a
    // numeral's condition is settled rather than assumed, so what a caller carries is the one
    // factor the theory genuinely cannot rule out.
    val theorem = force(field.prove("!x:real y:real. (2 * x) / (2 * y) = x / y"))

    theorem.hypotheses.map(reals.show) shouldBe List("~(y = 0)")
  }

  it should "take a negated denominator apart, which the product case does not cover" in {
    // `Field.reciprocal` recurses over the shape of a denominator and has a case per shape. The
    // product case is the test above; these two are the other two recursive ones, and until
    // 2026-09-17 nothing in this file drove either. A case in that recursion that nothing exercises
    // is a case that can be wrong in a way no reader would see: what it builds is a theorem, so a
    // mistake is not a crash but a hypothesis about the wrong term.
    //
    // The negation case rests on `unitOfNegation`, that `(-d) * (-(inv d)) = 1`, so the reciprocal
    // of a negated denominator is the negation of the reciprocal. What the caller owes is still
    // about `x` and not about `-x`, which is the part worth asserting: a condition naming a term
    // the goal does not contain is useless to whoever has to discharge it.
    val theorem = force(field.prove("!x:real y:real. (y * (-x)) / (-x) = y"))

    theorem.hypotheses.map(reals.show) shouldBe List("~(x = 0)")
  }

  it should "charge for the inverse itself where the denominator is one, not for what is under it" in {
    // The asymmetry with the case above, and it was written the other way round first: the
    // negation recurses and this does not. `-x` as a denominator comes back with `~(x = 0)`, and
    // `inv x` comes back with **`~(inv x = 0)`**, which is the condition a caller has to discharge
    // and is not the same sentence.
    //
    // It is sound rather than a defect, and knowing why is the reason to pin it: this theory gives
    // `inv 0` no axiom at all, so `inv x = 0` is not provably equivalent to `x = 0` and the tactic
    // cannot trade one for the other. What it could do instead is recurse, since `unitReversed`
    // says `inv d * d = 1`, and then the condition would be about `x`. Nothing here needs that
    // today, and a caller meeting this hypothesis should know it is asking about the inverse.
    val theorem = force(field.prove("!x:real y:real. (y * inv x) / inv x = y"))

    theorem.hypotheses.map(reals.show) shouldBe List("~(inv x = 0)")
  }

  it should "settle a numeral denominator with nothing assumed, which it could not until now" in {
    // These three were pinned here as refusals until 2026-09-09, and the reason written beside them
    // is the reason they have gone: a numeral was a monomial's coefficient and never one of its
    // atoms, so `2 * (x * inv 2)` kept the two halves of the cancellation on opposite sides of that
    // split. A coefficient can now be `1 / 2`, so the numeral case stopped being a case.
    //
    // Read what comes back rather than only that it did: the hypothesis list is empty. `~(2 = 0)`
    // is a theorem, not an assumption, so this does not go through the field fragment at all and
    // `Ring` settles it without `Field` in the picture.
    force(field.prove("!x:real. x / 2 + x / 2 = x")).hypotheses shouldBe empty
    force(field.prove("!x:real. (100 * x) / 100 = x")).hypotheses shouldBe empty
    force(field.prove("!x:real. 2 * ((3 * x + 1) / 2) = 3 * x + 1")).hypotheses shouldBe empty

    force(Ring.standard.prove("!x:real. x / 2 + x / 3 = 5 * x / 6")).hypotheses shouldBe empty
  }

  it should "settle a denominator that is a constant but not a numeral, and still assume nothing" in {
    // The rest of the same idea, from 2026-09-09 an hour later. `Positivity` proves `~(d = 0)` for
    // a numeral and for nothing else, so a negated numeral and a ratio of two of them were atoms
    // although both are constants the theory can name. `Coefficient.inverseOfUnit` asks instead for
    // a factor of one, which the reciprocal already is, so the condition is discharged by the
    // arithmetic and the order stays where it belongs, above the ring.
    //
    // They are put to `Ring` rather than to `Field`, which is the assertion: none of them costs a
    // hypothesis, so none of them is this tactic's business.
    val ring = Ring.standard

    force(ring.prove("!x:real. x / (-1) = -x")).hypotheses shouldBe empty
    force(ring.prove("!x:real. x / (-2) = -(x / 2)")).hypotheses shouldBe empty
    force(ring.prove("!x:real. x / (2 / 3) = 3 * x / 2")).hypotheses shouldBe empty
    force(ring.prove("!x:real. x / (-4 / 5) = -(5 * x / 4)")).hypotheses shouldBe empty
  }

  it should "leave a zero denominator alone, because inv 0 is an atom and not a denominator" in {
    // The line that separates this from inventing an answer. `x / 0 + x / 0 = 2 * (x / 0)` holds
    // whatever `inv 0` is, and it says nothing about what that is; `x / 0 = 0` does not hold and
    // is refused. The pair is what makes the atom an atom rather than a gap.
    force(Ring.standard.prove("!x:real. x / 0 + x / 0 = 2 * (x / 0)")).hypotheses shouldBe empty
    Ring.standard.prove("!x:real. x / 0 = 0").isLeft shouldBe true
  }

  "A denominator that can be shown positive" should "discharge the condition it left" in {
    // The sentence the task card ends on, run rather than asserted: `Positivity.nonZero` turns
    // `0 < y` into `~(y = 0)`, and discharging replaces one hypothesis by the other. What the
    // caller is left holding is a theorem about a positive denominator, which is the ordinary
    // case in a paper made of rates.
    val theorem = force(field.prove("!x:real y:real. (x * y) / y = x"))
    val condition = theorem.hypotheses.head

    val y = Term.variable("y", real)
    val nonZero = force(Positivity.nonZero(reals))
    val atY = force(reals.logic.rules.spec(y, nonZero))
    val positive = force(reals.proposition("0 < y:real"))
    val assumed = force(LogicError.lift(Kernel.assume(positive)))
    val derived = force(reals.logic.rules.mp(atY, assumed))

    val discharged = force(reals.logic.rules.disch(condition, theorem))
    val result = force(reals.logic.rules.mp(discharged, derived))

    shown(result) shouldBe (List("0 < y"), "!x:real. x * y / y = x")
  }

  "The theory it proves in" should "still assert only the reals' axioms" in {
    // The constraint the task was written under: a tactic that reached for a new axiom would have
    // solved a different problem.
    // Since `docs/adr/0053` the reals assert only the foundation they are built on.
    reals.theory.axioms.toSet shouldBe (Classical.standard.theory.axioms ++ Natural.standard.theory.axioms).toSet
  }

  /* ------------------------------------- what it charges is exact, not an upper bound */

  "The conditions" should "name only the cancellations that actually fired" in {
    // An audit on 2026-09-10 recorded `Field.conditions` as "literally `theorem.hypotheses`, an
    // upper bound of exactly the kind `Linarith.support` was written to replace", and said in the
    // same breath to check whether the no-split-then-split ordering already makes it tight. It
    // does, and these are the measurements that say so.
    //
    // The structural reason, which is why it will stay true: a condition reaches a theorem only
    // through the inference that used it. `Linarith` needs `support` because it ASSUMES every
    // hypothesis up front and then picks; `Field` assumes nothing up front, so a rule that never
    // fires contributes nothing and the hypothesis list is the support already.
    def charges(text: String): Vector[String] = {
      val theorem = force(field.prove(text))
      field.conditions(theorem).map(reals.show).toVector
    }

    // `y` is a denominator and is charged for, because the cancellation is what proves it.
    charges("!x:real y:real. (x * y) / y = x") shouldBe Vector("~(y = 0)")

    // `y` is a denominator and is charged nothing: the ring normalisation kills the quotient before
    // the field step is reached, so no cancellation fires and no condition is owed. An upper bound
    // would have named `y` here.
    charges("!x:real y:real. x / y * 0 = 0") shouldBe empty
    charges("!x:real y:real. x / y - x / y = 0") shouldBe empty
    charges("!x:real y:real z:real. (x / y) * 0 + z = z") shouldBe empty

    // The mixed case, which is the sharpest of the four and was added on 2026-09-11: two
    // denominators in one goal, one cancelled and one carried through untouched. An upper bound
    // would name both. Everything above is all-or-nothing and could in principle have been
    // explained by a coarser rule; this one cannot.
    charges("!x:real y:real z:real. x / y + z / z = x / y + 1") shouldBe Vector("~(z = 0)")
    charges("!x:real y:real z:real. x / y - x / y + z / z = 1") shouldBe Vector("~(z = 0)")
  }
}
