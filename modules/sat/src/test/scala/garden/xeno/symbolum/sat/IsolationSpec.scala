package garden.xeno.symbolum.sat

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The solver cannot construct a theorem, asserted rather than described.
 *
 * This module declares no dependency, so the kernel is not on its compilation classpath and nothing
 * here can build a `Kernel.Thm` whatever it does. That is a stronger promise than the one
 * `garden.xeno.symbolum.tactics.Consistency` can make about itself: that file keeps the same
 * discipline with a test that **scans its own source** for the name of an inference rule, and its
 * comment says why a runtime check is not available to it, which is that `Kernel.Thm` erases to a
 * pair and a type assertion about it would pass whatever the file did.
 *
 * A module needs neither the scan nor the assertion. What it needs is a guard on the one line in
 * `build.sbt` that would undo it, which is what this file is: the dependency is easy to add with a
 * good reason at the time, and nothing else would report it.
 *
 * Compile-time assertions, because the property is that certain code does not build.
 */
class IsolationSpec extends AnyFlatSpec with Matchers {

  "The solver" should "not be able to see the kernel, so it cannot construct a theorem" in {
    assertDoesNotCompile("""garden.xeno.symbolum.kernel.Kernel.refl(null)""")
  }

  it should "not be able to see the rules that would replay its own refutations" in {
    assertDoesNotCompile("""garden.xeno.symbolum.logic.Logic.standard""")
  }

  it should "not be able to see the computer algebra system either" in {
    assertDoesNotCompile("""garden.xeno.symbolum.Num(1)""")
  }

  it should "see its own entry point, so the assertions above are about the boundary" in {
    assertCompiles("""Solver.solve(Cnf.Problem(0, Vector(Cnf.Empty)))""")
  }
}
