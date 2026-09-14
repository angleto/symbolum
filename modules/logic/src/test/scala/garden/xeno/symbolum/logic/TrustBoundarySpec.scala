package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * What the type system is supposed to prevent, checked from outside the kernel.
 *
 * The correctness argument of the whole system is that a theorem can only come from an inference
 * rule and a term can only come from a constructor that type-checks it. Both are claims about
 * visibility, and a visibility modifier is one word: it can be widened in a moment by someone who
 * needs access for something reasonable, and no test that only runs code would notice.
 *
 * So each assertion comes in a pair. The negative one says the short way round does not compile;
 * the positive one says the sanctioned way does, which is what stops the negative from passing
 * for some unrelated reason such as a typo. This file lives in `logic` rather than in the kernel's
 * own tests because inside the kernel's package the restricted constructors are visible, and the
 * question is what someone outside it can reach. `TrustBoundaryTwinSpec` in the kernel compiles
 * the same snippets from inside the package, which is what shows that each refusal here is about
 * visibility and not about the snippet: keep the two files' snippets identical.
 */
class TrustBoundarySpec extends AnyFlatSpec with Matchers {

  private val bool = Type.Bool
  private val x = Term.variable("x", bool)
  private val theory = Logic.standard.theory

  "A theorem" should "come from an inference rule and not from its representation" in {
    assertCompiles("""Kernel.refl(x)""")
    assertDoesNotCompile("""val forged: Kernel.Thm = (List.empty[Term], x)""")
  }

  "An application" should "come from the constructor that checks the types" in {
    assertCompiles("""Term.app(Term.abs(x, x).toOption.get, x)""")
    assertDoesNotCompile("""App(Term.abs(x, x).toOption.get, x)""")
  }

  "An abstraction" should "come from the constructor that binds a variable" in {
    assertCompiles("""Term.abs(x, x)""")
    assertDoesNotCompile("""Abs(bool, x)""")
  }

  "A constant" should "come from a theory that declares it" in {
    assertCompiles("""theory.constant("T", bool)""")
    assertDoesNotCompile("""new Const("T", bool, None)""")
  }

  "A variable" should "come from the constructor rather than the case class" in {
    assertCompiles("""Term.variable("x", bool)""")
    assertDoesNotCompile("""FVar("x", bool)""")
  }

  "A bound index" should "not be writable from outside, and not be usable if one is obtained" in {
    // There is no sanctioned way to write one: an index is meaningful only relative to the binder
    // above it. The extractor on an abstraction does hand out its body, and that body has an index
    // with no binder above it, so the property is not that an index cannot be reached but that
    // nothing accepts it. Every operation that takes a term refuses; `SoundnessAttackSpec` in the
    // theories has the full set of refusals and the forgery that was possible before them.
    assertDoesNotCompile("""BVar(0)""")

    val loose = Term.abs(x, x).toOption.get match {
      case Abs(_, body) => body
      case other => fail(s"expected an abstraction, got $other")
    }

    Term.isLocallyClosed(loose) shouldBe false
    Term.app(Term.abs(x, x).toOption.get, loose).left.map(_.getClass) shouldBe
      Left(classOf[NotLocallyClosed])
  }

  "A theory" should "come from the primitive one and its extensions" in {
    assertCompiles("""Theory.primitive""")
    // Well-typed, so that the constructor's visibility is the only thing stopping it. The first
    // version passed a map of theorems where the constructor takes a map of terms, and was a type
    // error whatever the visibility.
    assertDoesNotCompile(
      """Theory(Map.empty[String, Int], Map.empty[String, Type], Map.empty[String, Term], List.empty[Term])"""
    )
  }

  "The axioms of a theory" should "be readable, since that is what the trusted base amounts to" in {
    assertCompiles("""Logic.standard.theory.axioms""")
    Logic.standard.theory.axioms shouldBe empty
  }
}
