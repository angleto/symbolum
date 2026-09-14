package garden.xeno.symbolum.kernel

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The trusted base cannot see anything else, asserted rather than described.
 *
 * The build is what enforces this: `kernel` declares no dependency, so the computer algebra
 * system and the layers above it are not on its compilation classpath. That arrangement is easy
 * to undo by adding one line to `build.sbt` with a good reason at the time, and nothing would
 * report it. These assertions fail when it happens.
 *
 * They are compile-time assertions because there is nothing to run: the property is that certain
 * code does not build.
 */
class IsolationSpec extends AnyFlatSpec with Matchers {

  "The kernel" should "not be able to see the computer algebra system" in {
    assertDoesNotCompile("""garden.xeno.symbolum.Num(1)""")
  }

  it should "not be able to see the logic built on top of it" in {
    assertDoesNotCompile("""garden.xeno.symbolum.logic.Logic.standard""")
  }

  it should "see its own constructors, so the two assertions above are about the boundary" in {
    assertCompiles("""Kernel.refl(Term.variable("x", Type.Bool))""")
  }
}
