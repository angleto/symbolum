package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Divisibility over the reals, and the two theorems that say what it is worth.
 *
 * The statements are pinned as the theory prints them, because a lemma named `DIVIDES_LINEAR` that
 * quietly became a lemma about something else would fail no other test here.
 *
 * The assertions that carry the design are the last two, and they are a pair. `|- Divides 2 3` and
 * `|- ~(Divides 0 1)` are both theorems of this development, with nothing assumed. The first is
 * false of the integers and the second is the only place this relation has content at all, so
 * between them they say the thing a consumer has to know before building on this file: over a field
 * the relation is trivial wherever the divisor is non-zero, and coprimality is therefore something
 * the consumer carries as a hypothesis rather than something it can ask for here. Proving that
 * limit is the honest way to state it; a comment saying it would be read once and forgotten.
 */
class DivisibilitySpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val ring = Ring.standard
  private val reals = ring.reals
  private val logic = reals.logic
  private val rules = logic.rules
  private val divisibility = Divisibility.standard

  private def fact(name: String): Kernel.Thm = force(divisibility.fact(name))

  private def statement(name: String): String = divisibility.show(fact(name).conclusion)

  /** Every fact this development names, so that a new one is covered by the sweeps below. */
  private val Names: Vector[String] = Vector(
    Divisibility.Intro,
    Divisibility.Elim,
    Divisibility.Reflexive,
    Divisibility.Transitive,
    Divisibility.MultiplyLeft,
    Divisibility.MultiplyRight,
    Divisibility.LinearCombination,
    Divisibility.DividesZero,
    Divisibility.ZeroDivides,
    Divisibility.NonZeroDivides
  )

  // Named `divisor` and not `a` because `a` is one of ScalaTest's own matcher words, and the
  // collision is a type error rather than a shadowing warning. The terms are still `a`, `b` and
  // `c`, which is what the statements below print.
  private val divisor = Term.variable("a", TyApp(Real.TypeName, Nil))
  private val dividendLeft = Term.variable("b", TyApp(Real.TypeName, Nil))
  private val dividendRight = Term.variable("c", TyApp(Real.TypeName, Nil))

  /* ------------------------------------------------------- the definition itself */

  "The relation" should "be defined rather than assumed, so the trusted base does not move" in {
    // The count is taken from the theory it extended rather than written out here: a hand-written
    // number would have to be edited when the base moves for an unrelated reason, and editing it
    // is exactly the moment this assertion exists to interrupt.
    divisibility.theory.axioms.size shouldBe reals.theory.axioms.size
    divisibility.theory.axioms shouldBe reals.theory.axioms
    divisibility.theory.definitions.keySet should contain(Divisibility.DividesName)

    divisibility.show(divisibility.definition.conclusion) shouldBe
      "Divides = (\\x:real. \\y:real. ?z:real. y = x * z)"
  }

  it should "need only the reals, and none of what the naturals are built from" in {
    // The reason this item came first. `Divides` is stated over the type the theory already has, so
    // a consumer gets it without asking anyone to believe the choice operator or infinity. Measured
    // by walking each proof to its axioms rather than by reading the imports.
    val axiomsOfTheReals = reals.theory.axioms.toSet

    Names.foreach { name =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(fact(name)).diff(axiomsOfTheReals) shouldBe empty
      }
    }
  }

  it should "cost no axiom at all where it is only the definition being used" in {
    // Measured rather than argued, and it is the point of the encoding. The definition and both of
    // its directions are pure logic, so a consumer that only introduces and eliminates the relation
    // has added nothing to what it asks anyone to believe; the field axioms enter exactly where
    // arithmetic does, which is every other fact here.
    Derivation.axiomsOf(divisibility.definition) shouldBe empty
    Derivation.axiomsOf(fact(Divisibility.Intro)) shouldBe empty
    Derivation.axiomsOf(fact(Divisibility.Elim)) shouldBe empty

    Derivation.axiomsOf(fact(Divisibility.LinearCombination)) should not be empty
  }

  "Both directions of the definition" should "be theorems, not steps a caller repeats" in {
    // The elimination is the one that matters and the one that is easy to get wrong. Taking the
    // witness out of the existential carries side conditions, and doing it once here is what lets
    // every derivation below read as arithmetic.
    statement(Divisibility.Intro) shouldBe
      "!x:real. !y:real. !z:real. y = x * z ==> Divides x y"
    statement(Divisibility.Elim) shouldBe
      "!x:real. !y:real. Divides x y ==> (?z:real. y = x * z)"
  }

  it should "take a witness in and give a relation out, at numerals" in {
    // End to end rather than by inspection: `12 = 3 * 4` is proved by the ring, handed to the
    // introduction, and what comes back mentions no witness.
    val theorem = force(
      for {
        three <- reals.term("3")
        twelve <- reals.term("12")
        four <- reals.term("4")
        product <- reals.proposition("12 = 3 * 4")
        equation <- ring.prove(product)
        introduction <- divisibility.intro
        instance <- rules.specAll(introduction, List(three, twelve, four))
        related <- rules.mp(instance, equation)
      } yield related
    )

    divisibility.show(theorem.conclusion) shouldBe "Divides 3 12"
    theorem.hypotheses shouldBe empty
  }

  /* ------------------------------------------------------------------ the lemmas */

  "Reflexivity" should "hold at every real, zero included" in {
    statement(Divisibility.Reflexive) shouldBe "!x:real. Divides x x"
  }

  "Transitivity" should "compose two witnesses into their product" in {
    statement(Divisibility.Transitive) shouldBe
      "!x:real. !y:real. !z:real. Divides x y ==> Divides y z ==> Divides x z"
  }

  "A divisor of a factor" should "divide the product, on either side of it" in {
    // Two theorems and not one. Commutativity makes them equivalent as statements and does nothing
    // for a caller whose product is spelled one way rather than the other.
    statement(Divisibility.MultiplyLeft) shouldBe
      "!x:real. !y:real. !z:real. Divides x y ==> Divides x (z * y)"
    statement(Divisibility.MultiplyRight) shouldBe
      "!x:real. !y:real. !z:real. Divides x y ==> Divides x (y * z)"
  }

  "The linear combination" should "hold for every pair of scalars a consumer might choose" in {
    // The one the whole file is for. An invariant that survives a step survives because the new
    // value is a combination of old ones, and the scalars are unconstrained: a step that subtracts,
    // or that scales by a fraction, is still an instance of this.
    statement(Divisibility.LinearCombination) shouldBe
      "!x:real. !y:real. !z:real. !u:real. !v:real. " +
        "Divides x y ==> Divides x z ==> Divides x (u * y + v * z)"
  }

  it should "specialise into the sum and the difference a step is actually written with" in {
    // End to end, because this is the shape a consumer writes rather than the general lemma: the
    // scalars are chosen, the arithmetic is closed by the ring, and what comes back is about
    // `b + c` and `b - c` with no coefficient left in it.
    divisibility.show(combined("1", "1", "b:real + c").conclusion) shouldBe
      "Divides a b ==> Divides a c ==> Divides a (b + c)"
    divisibility.show(combined("1", "-1", "b:real - c").conclusion) shouldBe
      "Divides a b ==> Divides a c ==> Divides a (b - c)"

    combined("1", "-1", "b:real - c").hypotheses shouldBe empty
  }

  "Zero" should "be divided by everything, and divide only itself" in {
    statement(Divisibility.DividesZero) shouldBe "!x:real. Divides x 0"

    // An equality of propositions rather than a pair of implications, so it can be used as a
    // rewrite rule where two implications would each need a detachment. The test below uses it that
    // way, which is the check that the form is the usable one.
    statement(Divisibility.ZeroDivides) shouldBe "!x:real. Divides 0 x = (x = 0)"
  }

  /* ------------------------------------------------- what the whole thing rests on */

  "Every fact here" should "hold with nothing assumed" in {
    Names.foreach { name =>
      withClue(s"$name: ") { fact(name).hypotheses shouldBe empty }
    }
  }

  it should "be reported with the size of its proof, since nothing else measures that" in {
    Names.foreach { name =>
      val theorem = fact(name)
      info(
        s"$name: ${Derivation.size(theorem)} inferences over " +
          s"${Derivation.axiomsOf(theorem).size} axioms"
      )
    }
  }

  /* ------------------------------------------------------ the limit, as a theorem */

  "A non-zero divisor" should "divide everything, which is the limit of this file" in {
    statement(Divisibility.NonZeroDivides) shouldBe
      "!x:real. !y:real. ~(x = 0) ==> Divides x y"
  }

  it should "make `Divides 2 3` a theorem, which it is not over the integers" in {
    // The assertion that probes the design. `~(2 = 0)` is a theorem for a numeral, so the
    // antecedent is discharged and what is left is unconditional: this development proves that two
    // divides three. A consumer that reads `Divides a b` as the integers' relation would build an
    // argument on that, and the statement it wanted is not available here at all.
    val theorem = force(
      for {
        two <- reals.term("2")
        three <- reals.term("3")
        lemma <- divisibility.nonZeroDivides
        instance <- rules.specAll(lemma, List(two, three))
        nonZero <- ring.positivity.numeralNonZero(2)
        related <- rules.mp(instance, nonZero)
      } yield related
    )

    // Compared against the term this development builds rather than only against its spelling, so
    // the assertion is about the proposition and not about the printer.
    theorem.conclusion shouldBe force(
      for {
        two <- reals.term("2")
        three <- reals.term("3")
        related <- divisibility.divides(two, three)
      } yield related
    )
    divisibility.show(theorem.conclusion) shouldBe "Divides 2 3"
    theorem.hypotheses shouldBe empty
  }

  it should "leave content at exactly one place, which is where the divisor is zero" in {
    // The other half of the pair. `~(Divides 0 1)` is a theorem too, by the field axiom that one is
    // not zero, so the relation is not vacuous: it says something at `a = 0` and nothing anywhere
    // else. Anything a consumer wants beyond that has to come from its own hypotheses, and
    // coprimality is the case the card names.
    val theorem = force(
      for {
        one <- reals.term("1")
        lemma <- divisibility.zeroDivides
        instance <- rules.spec(one, lemma)
        reversed <- Conv.sym(instance)
        rule <- Rewrite.Rule.of(logic, reversed)
        notZero <- reals.law("ONE_NOT_ZERO")
        negated <- Rewrite.inTheorem(Vector(rule), notZero)
      } yield negated
    )

    divisibility.show(theorem.conclusion) shouldBe "~(Divides 0 1)"
    theorem.hypotheses shouldBe empty
  }

  /* ---------------------------------------------------------------------- helpers */

  /**
   * The linear combination at chosen scalars, with the combination rewritten to the form a step is
   * written in.
   *
   * The rewrite is a ring identity, so what it replaces `1 * b + -1 * c` by is `b - c` and not
   * something that merely evaluates to it at every point.
   */
  private def combined(left: String, right: String, shape: String): Kernel.Thm =
    force(
      for {
        scalarLeft <- reals.term(left)
        scalarRight <- reals.term(right)
        lemma <- divisibility.linearCombination
        instance <- rules
          .specAll(lemma, List(divisor, dividendLeft, dividendRight, scalarLeft, scalarRight))
        readable <- ring.prove(s"$left * b:real + $right * c = $shape")
        rule <- Rewrite.Rule.of(logic, readable)
        rewritten <- Rewrite.inTheorem(Vector(rule), instance)
      } yield rewritten
    )
}
