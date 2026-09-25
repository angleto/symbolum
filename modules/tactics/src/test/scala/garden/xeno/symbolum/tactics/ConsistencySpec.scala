package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The propositional fragment decided rather than proved, and the three answers it keeps apart.
 *
 * The question this exists for is one somebody actually asks of a formalised register of rules:
 * **do two rules oblige and forbid the same thing?** That is satisfiability over declared atoms,
 * and until this file `Refutation.satisfying(Vector("p:bool", "~ p:bool"))` answered `Survived` —
 * no witness at the points tried, which is not "there is none". The distinction between those two
 * is exactly what the cases of `Refutation.Outcome` exist to keep, and this is the place where the
 * strong answer was missing.
 */
class ConsistencySpec extends AnyFlatSpec with Matchers {

  private val consistency = Consistency.standard

  "Two rules that oblige and forbid the same thing" should "come back decided, not counted" in {
    // The card's own example, and the answer that was missing. `Survived` means "no witness at the
    // points I tried"; this is "no assignment exists", which is a different fact and the one a
    // reader of a register needs.
    consistency.reading(Vector("p:bool", "~(p:bool)")) shouldBe Consistency.Verdict.Contradictory
  }

  "A set of rules that can all hold" should "come back with the assignment that makes them hold" in {
    val verdict = consistency.reading(
      Vector("p:bool ==> q:bool", "q:bool ==> r:bool", "p:bool")
    )

    verdict match {
      case Consistency.Verdict.NotContradictory(assignment) =>
        assignment.toMap.get("p") shouldBe Some(true)
        assignment.toMap.get("q") shouldBe Some(true)
        assignment.toMap.get("r") shouldBe Some(true)
      case other => fail(s"expected an assignment, got $other")
    }
  }

  "A contradiction that needs the whole rule set to see" should "still be decided" in {
    // Not a pair of opposites: the contradiction is only visible after chaining three rules and
    // the denial. This is the shape a register produces and the pairwise check misses.
    consistency.reading(
      Vector("p:bool ==> q:bool", "q:bool ==> r:bool", "p:bool", "~(r:bool)")
    ) shouldBe Consistency.Verdict.Contradictory
  }

  "A tautology" should "have a contradictory denial, and be told so in those words" in {
    // The reading is deliberately not hidden behind a friendlier name. A caller that wants "valid"
    // has to notice it is being told something about the denial, because what this decides is
    // satisfiability and calling it validity would be a second name for one answer.
    val claim = consistency.reals.proposition("(p:bool) \\/ ~(p:bool)")

    consistency.denialOf(claim.toOption.get) shouldBe Consistency.Verdict.Contradictory
  }

  "A quantifier" should "be refused by name rather than taken as an atom" in {
    // The mistake this file was written to avoid. `!x. p x` is a proposition and is not a
    // connective, so a reader looking for maximal non-connective subterms would take it as an atom.
    // Then it and `p a` are unrelated, a genuine contradiction is missed, and the caller is told
    // "not contradictory" about premises that cannot hold.
    consistency.reading(Vector("!x:real. 0 < x")) match {
      case Consistency.Verdict.Refused(why) => why should include("quantifier")
      case other => fail(s"expected a refusal, got $other")
    }
  }

  "An atom that is not propositional in structure" should "still be an atom, with no meaning given" in {
    // `0 < x` is a bool-typed subterm and no connective, so it is an atom and NOTHING is assumed
    // about it. That is the opposite of the fallback that made `Quantified` answer `Holds` to
    // `p \/ ~p` on 2026-09-10: there an unreadable leaf was turned into `0 < p`, and
    // `0 < p \/ ~(0 < p)` is a tautology over an ordered field. An atom here is given no meaning,
    // so the pair below is contradictory for the structural reason and for no other.
    consistency.reading(Vector("0 < x:real", "~(0 < x:real)")) shouldBe
      Consistency.Verdict.Contradictory

    // And the weakness that comes with it, asserted rather than left to be discovered: two atoms
    // that mean the same thing are two atoms. This is why the answer is called NotContradictory
    // and not "consistent".
    consistency.reading(Vector("x:real = y:real", "~(y:real = x:real)")) should not be
      Consistency.Verdict.Contradictory
  }

  "A question over too many atoms" should "be refused by name rather than enumerated" in {
    val many = (0 until (Consistency.Atoms + 1)).map(index => s"p$index:bool").toVector

    consistency.reading(many) match {
      case Consistency.Verdict.Refused(why) => why should include(Consistency.Atoms.toString)
      case other => fail(s"expected a refusal, got $other")
    }
  }

  "The source" should "never reach for an inference rule, which is what keeps it untrusted" in {
    // The same scan `Quantified` carries, for the same reason and written the same way: a type
    // signature says this produces no theorem only until somebody adds a second entry point, and a
    // runtime check would be vacuous because `Kernel.Thm` erases to a pair.
    val source = java.nio.file.Files.readString(
      java.nio.file.Paths.get("modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Consistency.scala")
    )

    val rules = Vector(
      "Kernel.refl", "Kernel.trans", "Kernel.mkComb", "Kernel.abs", "Kernel.beta", "Kernel.assume",
      "Kernel.eqMp", "Kernel.deductAntisym", "Kernel.inst", "Kernel.instType",
      "Kernel.defineConstant", "Kernel.assertAxiom", "Kernel.defineType"
    )

    val reached = rules.filter(source.contains)
    withClue(s"names an inference rule: ${reached.mkString(", ")}\n") { reached shouldBe empty }

    // And it decides the thing it is named for, so the scan is not passing because the file is
    // empty.
    consistency.reading(Vector("p:bool", "~(p:bool)")) shouldBe Consistency.Verdict.Contradictory
  }
}
