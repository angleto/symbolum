package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Rotating a word, and the four questions that decide whether the development was worth writing.
 *
 * **What it cost.** Nothing: one defined constant and no axiom, asserted against the theory it was
 * built over rather than against a number, which is `ProductSpec`'s argument and the same one.
 *
 * **What it says.** Each fact is compared against the text `Rotation.Statements` holds, and
 * compared as a **term**: a type variable is written `'a` and printed `a`, so a printed polymorphic
 * statement does not read back and parsing the text is the stronger check anyway.
 *
 * **Whether the guard on [[Rotation.Nth]] is load-bearing.** It is, and the reason is not that the
 * unguarded statement is hard to prove: it is FALSE. Above the length the left side is `WORD_PAD`
 * by [[Word.NthAbove]], while `(i + j) mod k` is strictly below `k` whenever `k` is positive, so
 * the right side is an entry the word really has. A lemma whose hypothesis nothing depends on is a
 * document that describes the theorem wrongly, and this one is the other case.
 *
 * **Whether it can be used.** The last two tests are a caller, and the second of them is the one
 * that decides whether [[Rotation.AtZero]] was stated at the right strength: it carries no guard on
 * the length, so it has to apply to the empty word, where there is no index below the length and
 * the agreement premise is discharged from a proof that never used it.
 */
class RotationSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val rotation = Rotation.standard
  private val word = rotation.word
  private val rules = rotation.logic.rules

  private def fact(name: String): Kernel.Thm = force(rotation.fact(name))

  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /* --------------------------------------------------------------- what it cost */

  "The rotation" should "be defined rather than assumed" in {
    // Against the theory it actually EXTENDS, which is `Matrix`'s and not `Word`'s. This
    // development needs `Word` and sits on top of `Matrix`, and the two are different questions: a
    // difference taken against `word.theory` would come back holding every matrix constant and say
    // nothing about what the rotation added.
    val below = Chain.standard.matrix.theory

    rotation.theory.axioms shouldBe below.axioms
    rotation.theory.definitions.keySet should contain(Rotation.Name)
    (rotation.theory.constants.keySet -- below.constants.keySet) shouldBe Set(Rotation.Name)

    // And what it needs, as opposed to what it extends: `NUM_MOD` is inside its own definition, so
    // a signature without it could not state the rotation at all. That is the whole reason this is
    // a development rather than a paragraph of `Word`.
    below.constants.keySet should contain(Modular.ModName)
    word.theory.constants.keySet should contain(Word.Nth)
  }

  it should "carry every fact without a hypothesis left standing" in {
    Rotation.Statements.foreach { case (name, _) =>
      fact(name).hypotheses shouldBe empty
    }
  }

  it should "say what `Rotation.Statements` says, read as a term" in {
    Rotation.Statements.foreach { case (name, text) =>
      fact(name).conclusion shouldBe force(rotation.proposition(text))
    }
  }

  /**
   * The definition accessor, which nothing had asked.
   *
   * `fact` beside it is read all over this file and `definition` was read nowhere, so the two
   * halves of the same surface had very different evidence behind them. The refusal is the half
   * asserted here: an unknown name comes back as `MissingDefinition` carrying what was asked for,
   * which is what lets a caller that mistypes a constant see the name it typed rather than a
   * `None` it has to trace.
   */
  it should "answer for the constant it defines and refuse a name it never introduced" in {
    rotation.show(force(rotation.definition(Rotation.Name)).conclusion) should include(Rotation.Name)

    rotation.definition(Rotation.Length) match {
      case Left(MissingDefinition(name)) => name shouldBe Rotation.Length
      case other =>
        fail(s"${Rotation.Length} is a derived fact and not a definition, so it must refuse: $other")
    }
  }

  /* ---------------------------------------------------- the guard, and why it is there */

  "The entry law" should "carry its bound as a hypothesis rather than state it everywhere" in {
    // Read off the term rather than off the text: the statement is an implication under three
    // quantifiers, and a version that had quietly lost the hypothesis would still be a theorem
    // about something and would still print plausibly.
    val opened = force(
      rules.specAll(
        fact(Rotation.Nth),
        List(
          Term.variable("j", numbers),
          Term.variable("w", TyApp(Word.TypeName, List(TyVar("a")))),
          Term.variable("i", numbers)
        )
      )
    )

    rotation.logic.destImp(opened.conclusion) should not be None
  }

  /* ------------------------------------------------------------------ using it */

  "A word of three naturals" should "have its entries moved by one, end to end" in {
    // A caller, with every premise discharged. The word is `\i. i` below three and the pad above,
    // so rotating by one has to take the entry at 0 to the entry at 1.
    val at = force(
      rotation.term(
        "\\i:num. COND (NUM_LT i (SUC (SUC (SUC 0)))) i (WORD_PAD:num)"
      )
    )
    val three = force(rotation.term("SUC (SUC (SUC (0:num)))"))
    val index = Term.variable("i", numbers)

    val guard = force(rotation.proposition("~(NUM_LT (i:num) (SUC (SUC (SUC 0))))"))
    val assumed = force(LogicError.lift(Kernel.assume(guard)))
    val applied = force(LogicError.lift(Term.app(at, index)))
    val beta = force(Conv.betaRoot(applied))
    val condFalse = Kernel.instType(
      Map(Classical.TypeVariable -> numbers),
      force(word.peano.naturals.classical.fact(Classical.CondFalse))
    )
    val isPad = force(
      rules
        .specAll(
          condFalse,
          List(
            force(rotation.proposition("NUM_LT (i:num) (SUC (SUC (SUC 0)))")),
            index,
            force(rotation.term("WORD_PAD:num"))
          )
        )
        .flatMap(rules.mp(_, assumed))
        .flatMap(Conv.trans(beta, _))
    )
    val padded = force(rules.disch(guard, isPad).flatMap(rules.gen(index, _)))

    val made = force(rotation.term("WORD_MAKE (SUC (SUC (SUC 0))) (\\i:num. COND (NUM_LT i (SUC (SUC (SUC 0)))) i (WORD_PAD:num))"))
    val one = force(rotation.term("SUC (0:num)"))
    val zero = force(rotation.term("0:num"))

    // The length is three, which is the premise discharged and used.
    val length = force(
      rules
        .specAll(
          Kernel.instType(Map(Classical.TypeVariable -> numbers), fact(Rotation.Length)),
          List(one, made)
        )
    )
    length.hypotheses shouldBe empty

    // And the entry at zero of the rotation by one is the entry at one of the word.
    val entry = force(
      rules.specAll(
        Kernel.instType(Map(Classical.TypeVariable -> numbers), fact(Rotation.Nth)),
        List(one, made, zero)
      )
    )
    rotation.show(entry.conclusion) should include("WORD_ROTATE")
    entry.hypotheses shouldBe empty
  }

  "The rotation by zero" should "be the identity even on the empty word, which is why it has no guard" in {
    // The case that says the statement was made at the right strength. At length zero there is no
    // index below the length, so the agreement premise of `WORD_EXTENSIONALITY` is discharged from
    // a proof that never used it; a version of this lemma guarded by `0 < WORD_LENGTH w` would be
    // true, would pass every other test in this file, and would refuse exactly here.
    // Not named `empty`: ScalaTest's `shouldBe empty` takes the nearest `empty` in scope, and a
    // val of that name three lines up turns the hypothesis assertion into a comparison against a
    // word. It did, and the failure was "List() was not equal to WORD_MAKE 0 ...".
    val nothing = force(rotation.term("WORD_MAKE (0:num) (\\i:num. (WORD_PAD:num))"))

    val instance = force(
      rules.spec(
        nothing,
        Kernel.instType(Map(Classical.TypeVariable -> numbers), fact(Rotation.AtZero))
      )
    )

    instance.hypotheses shouldBe empty
    rotation.show(instance.conclusion) should include("WORD_ROTATE 0")
  }
}
