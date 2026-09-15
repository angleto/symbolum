package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A digit string reads at the type its context forces, and this is where that is interrogated.
 *
 * Until 2026-09-12 a numeral was always a real, because the parser decided its type from the
 * declared type of `1` and there was only one encoding to decide between. `num` has one now, so the
 * elaborator decides instead: a numeral takes a metavariable and is expanded once unification has
 * said what its surroundings required. Everything below is about whether that decision is the right
 * one in each of the cases it can be wrong in.
 *
 * == What each test is guarded against, since that is what makes them worth running ==
 *
 * **A test that only asked "does it parse" would pass on a broken type checker.** So the readings
 * are asserted by taking the term apart, not by reading the text back: `Power 2 3` is checked to
 * have a real where the base goes and a natural where the exponent goes, at those positions.
 *
 * **A test that only asserted the refusal would pass on any parse failure at all.** So every
 * refusal here is paired with the reading that must still work: the same text annotated, and the
 * same text against a signature with one encoding. If the numerals were simply broken, those two
 * would fail and the refusal would go on passing.
 *
 * **A round trip over one value proves nothing about an encoding.** `1` is one node whatever the
 * base, so the values below are chosen to exercise both bits and a carry: 12 is `1100` and 255 is
 * eight ones.
 *
 * **A rule set that reached its answer without being used would be the worst of the lot**, since
 * the three crossing lemmas exist precisely to be a set. So the last test proves the crossing and
 * then removes two of the three rules and asserts the same rewrite no longer arrives, which is what
 * says the set is doing the work rather than something else already in scope.
 */
class NumeralTypeSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val widest = chain.widest
  private val peano = chain.peano
  private val reals = chain.reals

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  private def term(text: String): Term = force(widest.term(text))

  /** Whether any of `names` occurs as a constant anywhere in `term`. */
  private def mentions(term: Term, names: Set[String]): Boolean = term match {
    case Const(name, _) => names.contains(name)
    case App(fn, argument) => mentions(fn, names) || mentions(argument, names)
    case Abs(_, body) => mentions(body, names)
    case BVar(_) | FVar(_, _) => false
  }

  /* ------------------------------------------------- the two readings are two terms */

  "A digit string" should "read at either type, and give two different terms" in {
    Term.typeOf(term("2:real")) shouldBe real
    Term.typeOf(term("2:num")) shouldBe numbers

    // The assertion the pair exists for. If `expand` built its digits at a type it took from
    // somewhere other than the one unification settled, these two would be the same term and every
    // test above would still pass.
    term("2:real") should not be term("2:num")
  }

  it should "be the constant the rest of the development is written with, at zero" in {
    // `0:num` is `ZERO` itself and not a fourth constant beside it. This is the load-bearing one:
    // a separate numeral zero would put every lemma stated about `ZERO` out of reach of every
    // statement written with `0`, and the failure would be a rewrite that silently stopped
    // matching rather than an error anybody saw.
    term("0:num") shouldBe force(LogicError.lift(widest.theory.constant(Natural.NumberZero, numbers)))

    // And the printer agrees, which is the other half of the same claim: if it did not, the
    // document would show a spelling the parser does not produce.
    widest.show(term("0:num")) shouldBe "0"
    widest.show(term("0:real")) shouldBe "0"
  }

  it should "not be read out of a term that is not a numeral" in {
    // `NUM_BIT0 0` denotes zero and is not the numeral zero, exactly as `BIT0 0` is not over the
    // reals: two terms printing as `0` would make printing lose information, and the round trip
    // below would stop being an identity rather than fail visibly.
    val doubledZero = term("NUM_BIT0 0")
    widest.show(doubledZero) should not be "0"
    widest.show(doubledZero) shouldBe "NUM_BIT0 0"
  }

  /* ------------------------------------------------- the context decides, with no annotation */

  "The type of a numeral" should "come from the operator it is an argument of" in {
    // The term the gap audit asked for and could not write: `Power : real -> num -> real`, so one
    // digit string is a real and the other a natural, in one application, with neither annotated.
    val powered = term("Power 2 3")

    powered match {
      case App(App(_, base), exponent) =>
        Term.typeOf(base) shouldBe real
        Term.typeOf(exponent) shouldBe numbers
      case other => fail(s"not an application of two arguments: ${widest.show(other)}")
    }
  }

  it should "come from both sides of an equation at once" in {
    // `real_of_num : num -> real`, so the two numerals in this statement are at different types
    // and neither is annotated. Taking it apart rather than reading it back, because the text
    // `real_of_num 3 = 3` prints the same either way and would not tell them apart.
    term("real_of_num 3 = 3") match {
      case App(App(_, App(_, inner)), outer) =>
        Term.typeOf(inner) shouldBe numbers
        Term.typeOf(outer) shouldBe real
      case other => fail(s"not an equation between an embedding and a numeral: ${widest.show(other)}")
    }
  }

  it should "reach the statement a consumer could not write before" in {
    // End to end rather than at the parser: `2:real`, `0:num` and `1:real` in one claim that the
    // prover then settles. A claim that only parsed would say nothing about whether the term built
    // is the one the lemmas are about.
    val proved = force(Ring.standard.prove("1 + 1 = 2"))
    proved.hypotheses shouldBe empty

    val powerAtZero = force(chain.series.fact(Series.PowerAtZero))
    force(chain.logic.rules.spec(term("2:real"), powerAtZero)).conclusion shouldBe
      term("Power 2 0 = 1")
  }

  /* ------------------------------------------------- the refusal, and what it is not */

  "A numeral nothing determines" should "be refused where the signature reads two, and named" in {
    val refusal = widest.term("2")
    refusal.isLeft shouldBe true

    // The message has to name the choice, or a reader is told the type is undetermined and not what
    // it could have been.
    val message = refusal.fold(_.message, _ => "")
    message should include("not determined")
    message should include("real")
    message should include("num")
  }

  it should "read once it is told, which is what says the refusal was about the ambiguity" in {
    // Paired with the test above on purpose. Without this one, a refusal test passes just as well
    // against a parser that had stopped reading numerals altogether.
    Term.typeOf(term("2:real")) shouldBe real
    Term.typeOf(term("2:num")) shouldBe numbers
  }

  it should "read unannotated where the signature offers one encoding" in {
    // The other half of the same pairing, and the measurement behind the rule: a signature holding
    // only the reals has no second reading to protect anybody from, and forty call sites in this
    // module parse the bare text `"0"` and `"1"` against exactly such a signature.
    Term.typeOf(force(reals.term("2"))) shouldBe real
    Term.typeOf(force(reals.term("0"))) shouldBe real
    Term.typeOf(force(reals.term("1"))) shouldBe real
  }

  it should "have one encoding per type, or the choice between them is made by position" in {
    // The vacuity this whole design is exposed to, asserted rather than assumed. `expand` finds an
    // encoding by the type its `one` is declared at and takes the first match; two encodings whose
    // `one` sat at one type would make that a choice by order of declaration, which is a coin toss
    // dressed as an answer and would be silent. `RegisterSpec` asserts the names are distinct,
    // which is a weaker claim: two names can be one type.
    val declared = widest.notation.numerals.flatMap(spelling =>
      widest.theory.constants.get(spelling.one).map(spelling.one -> _))

    declared.size shouldBe widest.notation.numerals.size
    declared.map(_._2).distinct.size shouldBe declared.size
    declared.map(_._2).toSet shouldBe Set(real, numbers)
  }

  it should "be refused at a type that has no numerals, naming the type" in {
    val refusal = widest.term("2:bool")
    refusal.isLeft shouldBe true
    refusal.fold(_.message, _ => "") should include("bool")
  }

  /* ------------------------------------------------- the round trip, at both types */

  "Every numeral of either encoding" should "print as digits and read back as itself" in {
    // Both bits and a carry, rather than a value that is one node whatever the encoding: 12 is
    // `1100`, 255 is eight ones, 256 is a one and eight zeroes.
    val values = Vector(0, 1, 2, 3, 4, 5, 7, 12, 100, 255, 256)

    values.foreach { value =>
      Vector("real", "num").foreach { at =>
        val built = term(s"$value:$at")
        widest.show(built) shouldBe value.toString

        // Read back with the annotation, since the printed digits alone are the ambiguity this
        // whole file is about: the claim is that the term survives, not that the text does.
        term(s"${widest.show(built)}:$at") shouldBe built
      }
    }
  }

  /* ------------------------------------------------- what it cost, and what it buys */

  "The three constants" should "be definitions, so the trusted base does not move" in {
    // Against the two theories this development was built over rather than against a number
    // written here, which is `ProductSpec`'s argument and the same one: a number written here
    // would have to be edited when a base moves for an unrelated reason, and editing it is the
    // moment the assertion exists to interrupt.
    peano.theory.axioms.toSet shouldBe
      peano.naturals.theory.axioms.toSet ++ peano.ring.reals.theory.axioms.toSet

    // And the sharper form of the same claim, which a count cannot make: no axiom anywhere in this
    // theory so much as mentions one of the three constants. A conservative extension is exactly
    // that, and it is what `docs/adr/0008` promises for a defined constant.
    val introduced = Set(Peano.NumeralOne, Peano.NumeralBit0, Peano.NumeralBit1)
    peano.theory.axioms.filter(mentions(_, introduced)) shouldBe empty

    peano.theory.definitions.keySet should contain allOf (
      Peano.NumeralOne, Peano.NumeralBit0, Peano.NumeralBit1
    )
  }

  "The crossing rules" should "carry a numeral of num to the real of the same value" in {
    val crossing = force(peano.numeralsCrossing)
    crossing.size shouldBe 3
    crossing.foreach(_.hypotheses shouldBe empty)

    val rules = force(
      Rewrite.Rule.all(peano.logic, crossing :+ force(peano.fact(Peano.EmbedsZero)))
    )

    Vector(0, 1, 2, 3, 12, 100).foreach { value =>
      val carried = force(Rewrite.rewrite(rules, term(s"real_of_num ($value:num)")))
      Term.destEq(carried.conclusion).map(_._2) shouldBe Some(term(s"$value:real"))
    }
  }

  it should "not arrive without the rules that do the work" in {
    // The assertion that keeps the one above from being about something else already in scope. With
    // only the lemma that closes a chain of bits, and not the two that step through it, `12` cannot
    // cross: if it still did, the crossing would be happening somewhere this set does not name and
    // the set would not be the thing to hand a consumer.
    val partial = force(
      Rewrite.Rule.all(
        peano.logic,
        Vector(force(peano.fact(Peano.EmbedsNumeralOne)), force(peano.fact(Peano.EmbedsZero)))
      )
    )

    val stalled = force(Rewrite.rewrite(partial, term("real_of_num (12:num)")))
    Term.destEq(stalled.conclusion).map(_._2) should not be Some(term("12:real"))
  }
  /* -------------------------------------- the operator's three, which are the numeral's three */

  /**
   * `docs/adr/0018` says the operator's refusals are "the numeral's three, in the same words", and
   * until this was written **two of the three had never been fired**. The overloading landed with a
   * suite that was green because the case each of those branches is for was one no test asked for,
   * which is the shape this file's own header calls a test that would pass on a broken checker.
   *
   * Paired the same way as the numerals above: each refusal sits beside a reading that must still
   * work, so a parser that had simply stopped reading `+` would fail the second half rather than go
   * on passing the first.
   */
  "An operator nothing determines" should "be refused where the signature reads two, and named" in {
    val refusal = widest.proposition("0 < 1")
    refusal.isLeft shouldBe true

    val message = refusal.fold(_.message, _ => "")
    message should include("not determined")
    message should include("<")
    message should include("real")
    message should include("num")
  }

  it should "read once one side is told, which is what says the refusal was about the ambiguity" in {
    widest.proposition("(0:real) < 1").isRight shouldBe true
    widest.proposition("(0:num) < 1").isRight shouldBe true
  }

  it should "read unannotated where the signature offers one candidate" in {
    // The reals alone declare one `<`, so there is no choice to protect anybody from and the text
    // reads exactly as it did before overloading existed. This is what keeps a development built
    // below `Peano` working, and it is the half that would go quiet if the collapse-to-one case in
    // `Parser.overloaded` were ever lost.
    reals.proposition("0 < 1").isRight shouldBe true
  }

  "An operator at a type no candidate is declared at" should "be refused naming the types there are" in {
    // The third refusal, and the one a wrong claim actually meets. `<` is `?a -> ?a -> bool` over
    // its candidates, so two booleans settle the shape at `bool`, which is neither `real` nor `num`.
    // Before overloading this was a unification failure deep inside an application; now it names the
    // operator and says where it does exist.
    val refusal = widest.proposition("(x:bool) < y:bool")
    refusal.isLeft shouldBe true

    val message = refusal.fold(_.message, _ => "")
    message should include("<")
    message should include("real")
    message should include("num")
  }

  "An operator no candidate of which the theory declares" should "say the notation is unavailable" in {
    // The first refusal. The notation is the chain's, so `+` carries two candidates, and the theory
    // is the bare logic, which declares neither: the symbol lexes, the reader builds the overloaded
    // node, and the elaborator finds nothing to choose between. A reader who meets this has put a
    // text to the wrong signature, which is the one diagnosis the message can offer.
    val refusal =
      Parser.proposition(Logic.standard.theory, widest.notation, "(x:real) + y:real = y + x")
    refusal.isLeft shouldBe true
    refusal.fold(_.message, _ => "") should include("+")
  }
}
