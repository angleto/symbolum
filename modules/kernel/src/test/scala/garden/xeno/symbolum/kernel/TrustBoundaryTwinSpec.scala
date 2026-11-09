package garden.xeno.symbolum.kernel

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The other half of `TrustBoundarySpec`.
 *
 * That file, in the logic module, asserts that each line here does not compile from outside the
 * kernel package. A line that fails to compile for some other reason, a wrong argument type say,
 * passes that assertion while saying nothing about visibility, and one of them did until an audit
 * noticed. So the same lines, character for character, are asserted here to compile from inside
 * the package, where the constructors are visible. What is left as the reason for the refusal
 * outside is the visibility, which is the property under test.
 *
 * Keep the snippets in the two files identical.
 */
class TrustBoundaryTwinSpec extends AnyFlatSpec with Matchers {

  private val bool = Type.Bool
  private val x = Term.variable("x", bool)

  "Inside the kernel package, an application" should "be constructible directly" in {
    assertCompiles("""App(Term.abs(x, x).toOption.get, x)""")
  }

  "An abstraction" should "be constructible directly" in {
    assertCompiles("""Abs(bool, x)""")
  }

  "A constant" should "be constructible directly" in {
    assertCompiles("""Const("T", bool, None)""")
  }

  "A variable" should "be constructible directly" in {
    assertCompiles("""FVar("x", bool)""")
  }

  "A bound index" should "be constructible directly" in {
    assertCompiles("""BVar(0)""")
  }

  "A theory" should "be constructible directly, with the argument types the outside snippet uses" in {
    assertCompiles(
      """Theory(Map.empty[String, Int], Map.empty[String, Type], Map.empty[String, Term], List.empty[Term])"""
    )
  }

  "A theorem" should "not be constructible from its representation even here" in {
    // The representation is visible inside `object Kernel` alone, not in the package: the ten
    // rules are the boundary, and the rest of the kernel is on the outside of it with everyone
    // else. The pair is well-typed, so visibility is the only thing refusing it.
    assertDoesNotCompile("""val forged: Kernel.Thm = (List.empty[Term], x)""")
  }

  it should "not be reachable by a cast either, which the assertion above does not cover" in {
    // What that assertion missed until 2026-09-10. `Thm` was an opaque type over a pair, and an
    // opaque type is a compile-time fiction: it erases to what it wraps, so the cast below
    // compiled, ran, and produced `|- x` out of a tuple. The assertion above passed the whole time,
    // because it is about typechecking and this is about erasure.
    //
    // `Thm` is a class now and does not erase, so the same cast is a `ClassCastException`. This is
    // the half of the boundary the runtime enforces, and it is asserted rather than described
    // because the difference between the two is exactly what went unnoticed.
    val pair: (List[Term], Term) = (List.empty[Term], x)

    an[ClassCastException] should be thrownBy pair.asInstanceOf[Kernel.Thm].display
  }

  it should "be reachable by reflection, which is the threshold the argument stops at" in {
    // The other half of the same question, and it is the half the note on `Kernel.Thm` overstates.
    // That note says the class makes the boundary "enforced by the runtime rather than by the
    // compiler alone, which is the difference between a wall and a convention". The runtime
    // enforces the **type**, which is why the cast above throws. It does not enforce the
    // **construction**: `private[Kernel]` is a Scala access rule and the constructor it compiles
    // to is `public` in the bytecode, so a caller reaches it without even asking for access.
    //
    // Asserted rather than described, because a limit nobody measured is a limit that gets
    // forgotten and then relied on. What follows from it is in `Check`: a forged theorem whose
    // derivation does not add up is refused by the second checker, and one that adds up by naming
    // an axiom is refused since 2026-09-11 by comparing that axiom against the theory. Neither of
    // those is the kernel, and that is the point.
    val constructor = classOf[Kernel.Thm].getDeclaredConstructors.head

    java.lang.reflect.Modifier.isPublic(constructor.getModifiers) shouldBe true

    val forged = constructor
      .newInstance(List.empty[Term], x, Derivation.Assumption(x))
      .asInstanceOf[Kernel.Thm]

    forged.conclusion shouldBe x
    forged.hypotheses shouldBe empty
  }

  "A theorem's identity" should "be its sequent, whatever route derived it" in {
    // A class brings equality with it, and the kernel relies on theorems from two derivations of
    // one sequent comparing equal: the hypotheses are sorted and duplicate-free for that reason,
    // and a class that inherited reference equality would have quietly broken it.
    Kernel.refl(x) shouldBe Kernel.refl(x)
    Kernel.refl(x).hashCode shouldBe Kernel.refl(x).hashCode
  }
}
