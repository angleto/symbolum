package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A written number opened into successors, which is what every recurrence over `num` was waiting for.
 *
 * `num` has had numerals since 2026-09-12 and no lemma could reach one: every recurrence is stated
 * at `SUC n` and `2:num` is `NUM_BIT0 NUM_ONE`. So `Power x 2 = x * x` was not provable, and
 * `Algebraic` stated a degree-eight polynomial with twenty copies of its base written out.
 *
 * What is asserted here, in order: the spelling is what it says it is; the aim is an aim, which is
 * asserted by pairing each "left alone" with the change that shows the conversion fires at all; two
 * consumers are proved end to end; a false claim is refused as **decided** and not merely as
 * unproved; and the line is measured in both directions, the way `Bounded` measures its own.
 */
class SuccessorSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val widest = chain.widest
  private val successor = chain.successor

  private def term(text: String): Term = force(widest.term(text))
  private def proposition(text: String): Term = force(widest.proposition(text))
  private def show(theorem: Kernel.Thm): String = widest.show(theorem.conclusion)

  /* --------------------------------------------------------------------- the spelling */

  "A numeral of num" should "spell as the successors it denotes" in {
    show(force(successor.spell(term("2:num")))) shouldBe "2 = SUC (SUC 0)"
    show(force(successor.spell(term("3:num")))) shouldBe "3 = SUC (SUC (SUC 0))"
  }

  it should "spell zero as itself, because ZERO is the encoding's zero" in {
    // Not a missing answer and not a special case. `0:num` and `ZERO` are the same term, so the
    // successor form of zero is zero and reflexivity is the whole theorem.
    val spelled = force(successor.spell(term("0:num")))

    show(spelled) shouldBe "0 = 0"
    spelled.hypotheses shouldBe empty
  }

  it should "rest on nothing, since the five facts it uses are all derived" in {
    force(successor.spell(term("8:num"))).hypotheses shouldBe empty
  }

  it should "refuse a term that is not a numeral of num, naming the type it wanted" in {
    successor.spell(term("n:num")) should matchPattern { case Left(NotOfForm(_, _)) => }

    // And a numeral of the WRONG type, which is the confusion this system can actually produce:
    // a digit string reads at two types and the caller is the one that decided which.
    successor.spell(term("2:real")) should matchPattern { case Left(NotOfForm(_, _)) => }
  }

  /* -------------------------------------------------------------------------- the aim */

  "The expansion" should "open a power at a written exponent" in {
    show(force(successor.expand(term("Power (x:real) (2:num)")))) shouldBe
      "Power x 2 = x * (x * 1)"
  }

  it should "leave a power at a variable exponent alone, and not because it fires on nothing" in {
    // The paired half is the point. "Unchanged" read on its own is what a conversion that never
    // fires also produces, so the same assertion is made against a term that must change.
    val variable = term("Power (x:real) (n:num)")
    val written = term("Power (x:real) (2:num)")

    Rewrite.changed(force(successor.expand(variable))) shouldBe false
    Rewrite.changed(force(successor.expand(written))) shouldBe true
  }

  it should "leave a numeral that is not an exponent alone, and not because it fires on nothing" in {
    // The reason the conversion is aimed rather than a rule set turned loose: the five rules
    // applied to a whole goal would open every numeral of `num` in it, and a modulus of ten
    // thousand would become a term with ten thousand nodes.
    val modulus = proposition("NUM_CONG (7:num) (a:num) (b:num)")
    val exponent = proposition("Power (x:real) (7:num) = x")

    Rewrite.changed(force(successor.expand(modulus))) shouldBe false
    Rewrite.changed(force(successor.expand(exponent))) shouldBe true
  }

  it should "leave a numeral inside the base alone, which aiming at the power does not give" in {
    // The case that says aiming at `Power b k` is not enough on its own. The rules that open the
    // exponent open a numeral wherever they find one, so run over the whole of this term they
    // would turn the `7` in the base into seven successors as well. The expansion is derived over
    // a variable base for that reason, and this is the assertion that says so.
    val expanded = force(successor.expand(term("Power (real_of_num (7:num)) (2:num)")))

    show(expanded) shouldBe "Power (real_of_num 7) 2 = real_of_num 7 * (real_of_num 7 * 1)"
    show(expanded) should not include "SUC"
  }

  /* ------------------------------------------------------------------- two consumers */

  "A power at a written exponent" should "be provable, which is what the card said it was not" in {
    val theorem = force(successor.prove(proposition("Power (x:real) (2:num) = x * x")))

    show(theorem) shouldBe "Power x 2 = x * x"
    theorem.hypotheses shouldBe empty
  }

  it should "carry a binomial, where the whole polynomial is the caller's" in {
    val theorem = force(
      successor.prove(proposition("Power ((x:real) + y) (2:num) = x * x + 2 * (x * y) + y * y"))
    )

    show(theorem) shouldBe "Power (x + y) 2 = x * x + 2 * (x * y) + y * y"
    theorem.hypotheses shouldBe empty
  }

  it should "refuse a false one as decided, and not merely as unproved" in {
    // The expansion is an equation, so what `Ring` decides about the opened claim it decides about
    // the claim as written. Paired with the two above, because a procedure that refused everything
    // would pass this line on its own.
    successor.prove(proposition("Power (x:real) (2:num) = x")) match {
      case Left(error) => error.standing shouldBe LogicError.Standing.Decided
      case other => fail(s"expected a decided refusal, got $other")
    }
  }

  /* ------------------------------------------------ a consumer this file does not know about */

  "A bound written as a numeral" should "reach Bounded, which only takes successors" in {
    // `Bounded.prove` refuses a bound written as `4` and takes `SUC (SUC (SUC (SUC ZERO)))`, and
    // its refusal says so in those words. Nothing in `Bounded` changes for this: the caller proves
    // the claim in the form that driver reads and carries the result across [[Successor.spell]],
    // which is two lines and is the whole reason the spelling is published as an equation rather
    // than as a term.
    //
    // It is here rather than in `BoundedSpec` because what it demonstrates is about this file: the
    // spelling has a consumer that is not the powers it was built for, which is the measurement
    // that says the driver is not one caller's helper.
    val bounded = Bounded.standard
    val numbers = TyApp(Natural.TypeName, Nil)
    val index = Term.variable("i", numbers)
    val zero = force(LogicError.lift(chain.peano.theory.constant(Natural.NumberZero, numbers)))
    val suc = force(
      LogicError.lift(
        chain.peano.theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
      )
    )
    val lessThan = force(
      LogicError.lift(
        chain.peano.theory
          .constant(Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
      )
    )

    val four = force(Bounded.numeral(zero, suc, 4))
    val guard = force(LogicError.lift(Term.appAll(lessThan, List(index, four))))
    val trivial = force(LogicError.lift(Term.eq(index, index)))
    val body = force(chain.logic.mkImp(guard, trivial))
    val claim = force(chain.logic.mkForall(index, body))

    val inSuccessors = force(bounded.prove(claim)(instance => Right(Conv.refl(instance.index))))

    val spelled = force(successor.spell(term("4:num")))
    val backwards = force(Rewrite.Rule.of(chain.logic, force(Conv.sym(spelled))))
    val asWritten = force(Rewrite.inTheorem(Vector(backwards), inSuccessors))

    // The whole conclusion rather than a fragment of it, because the bound is the only thing that
    // moved and a fragment would pass on a statement about something else. The binder prints as
    // `x` and not as `i`: this logic has no names for bound variables and the printer coins one
    // from the binder's position, which is the same fact `Rules.specTo` exists because of.
    widest.show(asWritten.conclusion) shouldBe "!x:num. NUM_LT x 4 ==> x = x"
    widest.show(inSuccessors.conclusion) shouldBe
      "!x:num. NUM_LT x (SUC (SUC (SUC (SUC 0)))) ==> x = x"
    asWritten.hypotheses shouldBe empty
  }

  /* ---------------------------------------------------------------------- the line */

  "The line on a written exponent" should "cut something that is otherwise provable" in {
    // Measured in both directions, the way `Bounded` measures its own: what the line cuts has to be
    // something the driver would otherwise do, or the refusal is about nothing.
    val narrow = force(Successor.construct(chain.peano, chain.series, 4))
    val goal = proposition("Power (x:real) (8:num) = x * (x * (x * (x * (x * (x * (x * x))))))")

    narrow.prove(goal) match {
      case Left(BoundReached(limit, reached, allowed, _)) =>
        limit shouldBe Successor.LimitName
        reached shouldBe 8
        allowed shouldBe 4

      case other => fail(s"expected the bound to be named, got $other")
    }

    show(force(successor.prove(goal))) should startWith("Power x 8 =")
  }

  it should "refuse an exponent nobody intended, naming the limit rather than walking it" in {
    successor.prove(proposition("Power (x:real) (100000:num) = x")) match {
      case Left(BoundReached(limit, reached, allowed, _)) =>
        limit shouldBe Successor.LimitName
        reached shouldBe 100000
        allowed shouldBe Successor.Exponent

      case other => fail(s"expected the bound to be named, got $other")
    }
  }

  "The rewriter's own ceiling" should "refuse a walk it could not finish, in both places" in {
    // The second line, and the two refusals it makes reachable. At the slack this ships with, the
    // longer walk costs `k + 2` and is allowed `k + 16`, so neither of these can fire and neither
    // would ever have been seen to work: a guard nothing can be pointed at is a guard nobody has
    // watched.
    //
    // Below zero, and that is the measurement rather than a flourish: the two walks do not cost the
    // same. Opening `Power b k` takes `k + 2` steps and opening the numeral alone takes about half
    // that, because `depthConv` makes a whole pass per step and the encoding's digits open several
    // successors in one. A ceiling that cuts both has to be under the cheaper one.
    val tight = force(Successor.construct(chain.peano, chain.series, Successor.Exponent, -20))

    tight.spell(term(s"${Successor.Exponent}:num")) should matchPattern {
      case Left(NotNormalised(_)) =>
    }
    tight.expand(term(s"Power (x:real) (${Successor.Exponent}:num)")) should matchPattern {
      case Left(NotNormalised(_)) =>
    }

    // And it is not refusing everything: the same driver settles a smaller one, so what the line
    // cuts is a walk that is too long and not a claim it cannot read.
    show(force(tight.spell(term("4:num")))) shouldBe "4 = SUC (SUC (SUC (SUC 0)))"
  }

  it should "stand where the reading put it" in {
    // The number is pinned because the docstring's table is what chose it, and a floor that moved
    // without the table moving would leave the argument describing a different line.
    successor.limit shouldBe Successor.Exponent
    Successor.Exponent shouldBe 32
  }

  /* ------------------------------------------------------------------- what it costs */

  "The cost" should "be reported as a function of the exponent, not asserted" in {
    // Reported rather than asserted, because what this repository has learned about stopwatches
    // applies to inference counts as soon as somebody pins one: the number that matters to a
    // reader is the shape, and the shape is that the driver is flat and the caller's polynomial is
    // not. `Power x k` against `x * ... * x` is the one that isolates the driver.
    val readings = Vector(2, 4, 8, 16, 32).map { k =>
      val product = Vector.fill(k)("x").mkString(" * ")
      val theorem = force(successor.prove(proposition(s"Power (x:real) ($k:num) = $product")))
      k -> Derivation.size(theorem)
    }

    info(readings.map { case (k, size) => s"k=$k: $size" }.mkString("   "))

    // The only thing asserted is that every one of them was proved, which the `force` above
    // already did, and that the largest permitted exponent is among them.
    readings.map(_._1) should contain(Successor.Exponent)
  }
}
