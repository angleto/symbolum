package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The type of finite words, and the two things it was asked for that it does not do.
 *
 * **What it does.** A word is a length and a function consulted below it, carried as a padded
 * `prod(num, num -> 'a)`. The padding is what makes the encoding canonical, and
 * `Word.Extensionality` is what the padding buys: two words of one length agreeing below it are one
 * word. Without that theorem the type would be a pair with a nicer name.
 *
 * **What it costs.** Nothing. The naturals' theory has nineteen axioms and so does this one, which
 * is asserted against the theory it was built over rather than against a number written here. Every
 * proof is walked, and what they reach is choice and eta: no axiom of the reals and none of the
 * naturals, which says the word type needs the *type* `num` and no arithmetic at all.
 *
 * **What it does not do, asserted rather than described.** There is no rotation, and the reason
 * changed under this file on the evening it was written, which is why the last two tests execute
 * the report rather than repeating it. The reason WAS a missing lemma: `NUM_MOD` is easy to define
 * and useless without the **uniqueness** half of the division theorem, because a `select` with
 * nothing proved about it is a constant nothing can be proved about, and `Modular` had existence
 * only. `NUM_DIVISION_UNIQUE` landed hours later. So what is missing now is a definition and a
 * derivation and no longer a lemma, which is a different kind of gap and is pinned as one.
 */
class WordSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val words = Word.standard
  private val peano = words.peano
  private val classical = words.product.classical
  private val rules = words.logic.rules

  private def fact(name: String): Kernel.Thm = force(words.fact(name))

  private val Derived: Vector[String] =
    Vector(Word.AbstractionOfRepresentation, Word.Characterisation) ++ Word.Statements.map(_._1)

  /* --------------------------------------------------------------- what it cost */

  "The word type and its constants" should "be defined rather than assumed" in {
    words.theory.axioms shouldBe peano.theory.axioms

    (words.theory.typeOperators.keySet -- peano.theory.typeOperators.keySet) shouldBe
      Set(Product.TypeName, Word.TypeName)
    words.theory.typeOperators(Word.TypeName) shouldBe 1

    words.theory.definitions.keySet should contain allOf (
      Word.Pad, Word.Length, Word.Nth, Word.Make
    )
    words.theory.definitions.keySet should not contain Word.Abstraction
    words.theory.definitions.keySet should not contain Word.RepresentationFunction
  }

  it should "carry every fact without a hypothesis left standing" in {
    Derived.foreach(name => withClue(s"$name: ")(fact(name).hypotheses shouldBe empty))
  }

  it should "reach the classical axioms and no axiom of arithmetic at all" in {
    // The measurement worth having: `num` enters this file as a **type** and nothing here adds,
    // multiplies or compares anything, so none of the sixteen axioms of the reals and not the
    // axiom of infinity is reached. `NUM_LT` appears in every statement and is never used as an
    // order, which is why the guard can be carried across an equation and nothing else asked of it.
    val choice = force(classical.axiom(Classical.Choice)).conclusion
    val eta = force(classical.axiom(Classical.Eta)).conclusion

    Derived.foreach { name =>
      withClue(s"$name: ")(Derivation.axiomsOf(fact(name)).diff(Set(choice, eta)) shouldBe empty)
    }

    // And the split inside those two, which is not decoration: extensionality is the one fact that
    // turns a pointwise agreement into an equation between functions, so it is the one that reaches
    // eta. Everything else gets by with the choice `WORD_PAD` and the projections already cost.
    Derivation.axiomsOf(fact(Word.Extensionality)) shouldBe Set(choice, eta)
    Derivation.axiomsOf(fact(Word.NthAbove)) shouldBe Set(choice)
  }

  it should "cost the number of inferences measured, within an order" in {
    // Counted rather than timed, and counted to the facts it cites since `docs/adr/0047`: what
    // `Product` and the logic published is one inference each here, so the figures are this file's
    // own work. On 2026-09-11, when they still counted everything underneath, they were 1214 for
    // each half of the bijection, 1452 for the padding law, 1863 for each law of the constructor
    // and 3452 for extensionality. A band rather than an equality, because a cheaper `existsIntro`
    // would move all six.
    Derived.foreach { name =>
      info(s"$name: ${Derivation.size(fact(name))}")
      withClue(s"$name: ") {
        Derivation.size(fact(name)) should be > 50
        Derivation.size(fact(name)) should be < 12000
      }
    }

    Derivation.size(fact(Word.Extensionality)) should be > Derivation.size(fact(Word.NthAbove))
  }

  /* ------------------------------------------------------------------ the statements */

  "Every derived fact" should "read as the text this development is checked by" in {
    Word.Statements.foreach { case (name, text) =>
      withClue(s"$name: ")(fact(name).conclusion shouldBe force(words.proposition(text)))
    }
  }

  it should "name every fact the way the convention names one" in {
    val shape = "[A-Z][A-Z0-9]*(_[A-Z0-9]+)*".r

    Derived.foreach { name =>
      withClue(s"$name: ") {
        shape.matches(name) shouldBe true
        name should startWith("WORD_")
      }
    }

    // One spelling per concept: the corpus already spells extensionality `EXTENSIONALITY`, in
    // `Classical.FunctionExtensionality`, so this development does not add a shorter second one.
    Derived.filter(_.contains("_EXT")).filterNot(_.contains("EXTENSIONALITY")) shouldBe empty
  }

  /* ---------------------------------------------------------------------- using it */

  "The empty word" should "be built and measured, end to end" in {
    // Every premise discharged here rather than assumed, which is what "end to end" has to mean:
    // `WORD_MAKE` carries the padding premise and this is a caller proving it. The function is the
    // pad everywhere, so the proof does not use the guard at all.
    val pad = force(words.term("\\i:num. (WORD_PAD:'a)"))
    val zero = force(LogicError.lift(words.theory.constant(Natural.NumberZero, Word.Numbers)))
    val index = Term.variable("i", Word.Numbers)

    val applied = force(LogicError.lift(Term.app(pad, index)))
    val entry = force(Conv.betaRoot(applied))
    // `i:num`: `<` is two constants here since `docs/adr/0018` and the numeral is two encodings,
    // so nothing in this text says which order is meant.
    val guard = force(words.proposition("~(i:num < 0)"))
    val padded = force(rules.disch(guard, entry).flatMap(rules.gen(index, _)))

    val length = force(
      rules.specAll(fact(Word.MakeLength), List(zero, pad)).flatMap(rules.mp(_, padded))
    )

    words.show(length.conclusion) shouldBe "WORD_LENGTH (WORD_MAKE 0 (\\x:num. WORD_PAD)) = 0"
    length.hypotheses shouldBe empty
  }

  "Extensionality" should "state what it means to say at a concrete element type" in {
    // Instantiated at `num`, so the claim is about words of naturals: the thing the gap audit says
    // could not be written down. A type definition whose arity were wrong would fail here.
    val instantiated = Kernel.instType(
      Map(Classical.TypeVariable -> Word.Numbers),
      fact(Word.Extensionality)
    )

    words.show(instantiated.conclusion) shouldBe
      "!x:word(num). !y:word(num). WORD_LENGTH x = WORD_LENGTH y /\\ (!z:num. z < WORD_LENGTH x " +
        "==> WORD_NTH x z = WORD_NTH y z) ==> x = y"
  }

  /* ------------------------------------------------- the rotation that is not here */

  "Rotation" should "be absent, and the absence read off the code rather than off a comment" in {
    // `ModularSpec` asserts the same two names one file over and for the same reason: this is the
    // gap most likely to be assumed away by a reader who wants it.
    // **This is about `Word.standard` and not about the system, and the difference is the whole
    // value of the line.** `Word.standard` is built over `Chain.standard.peano`, which is below
    // `Modular`, so the two really are absent here. `Chain.standard.word` has both, because the
    // chain puts `Modular` first. Until 2026-09-12 this file's docstring read the assertion as the
    // second claim and said rotation was blocked on a missing constant; it is not, and the
    // assertion was right about a population nobody had chosen. Both readings are asserted, so
    // neither can be mistaken for the other again.
    words.theory.constants.keySet should contain noneOf ("NUM_MOD", "NUM_DIV")
    Chain.standard.word.theory.constants.keySet should contain allOf ("NUM_MOD", "NUM_DIV")
    words.theory.constants.keySet.filter(_.contains("ROTATE")) shouldBe empty
    words.facts.keySet.filter(_.contains("ROTATE")) shouldBe empty

    // The conditional was the other absence asserted here and **it is not an absence any more**.
    // `Classical` defines `COND` since 2026-09-12, so the padding constructor's body,
    // `\i. COND (NUM_LT i k) (f i) WORD_PAD`, is a term this signature reads. What is still not
    // here is the constructor, and that is the honest form of the gap: the constant exists, the
    // definition using it was not written, and a reader must not be told the first when the second
    // is what stopped it.
    words.theory.constants.keySet should contain(Classical.Conditional)

    val padding = words.term(
      "\\i:num. COND (NUM_LT i (k:num)) ((f:num->'a) i) (WORD_PAD:'a)"
    )
    padding.isRight shouldBe true
  }

  it should "be stopped by a definition and a derivation, and no longer by a lemma" in {
    // The report, executed, and the half of it that changed. A remainder **is** definable:
    // `select` of the division theorem's own predicate is a closed term this signature accepts, and
    // the parser building it is the proof of that.
    val remainder = words.term(
      "select (\\x:num. ?y:num. m = n * y + x /\\ x < n)"
    )

    remainder.isRight shouldBe true
    Term.typeOf(force(remainder)) shouldBe Word.Numbers

    // What the definition used to lack was any way to show the selected value is *the* remainder,
    // so it would have been a constant nothing could be proved about. `Modular` held the existence
    // half of the division theorem and said in its own docstring that uniqueness did not follow.
    // **It does now**, proved on the same evening as this file, which is why this assertion is that
    // the lemma is THERE and not that it is missing.
    val uniqueness = words.proposition(
      "!x:num. !y:num. !z:num. !u:num. !v:num. x * y + z = x * u + v /\\ z < x /\\ v < x ==> y = " +
        "u /\\ z = v"
    )

    uniqueness.isRight shouldBe true
    Modular.standard.fact(Modular.DivisionUnique).isRight shouldBe true

    // And this is the trap the first version of this test walked into. It asked
    // `Library.of(Chain.standard)` for the name and was satisfied that it was absent, which it then
    // was: `Modular` was not one of the chain's developments, so its facts were in no library the
    // chain assembled. The assertion passed while the claim beside it was false.
    //
    // **It is in the chain since 2026-09-12**, so the absence is gone and with it the trap. What is
    // asserted now is the opposite and is the stronger of the two: the lemma the report called
    // missing is in the library a reader searches, under the development that proved it.
    Library.of(Chain.standard).named(Modular.DivisionUnique).map(_.development) shouldBe
      Vector("Modular")
  }
}
