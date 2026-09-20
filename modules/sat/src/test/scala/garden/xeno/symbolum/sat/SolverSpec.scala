package garden.xeno.symbolum.sat

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import Cnf.*

/**
 * The solver, checked against a procedure that cannot be wrong for the same reason it can.
 *
 * The assertion that carries this file is not that the verdicts are right. It is that **every
 * refutation checks**: a verdict is one bit and a defect in conflict analysis produces the right bit
 * with a derivation that does not hold together, which is exactly the failure that would reach
 * `Propositional` and cost 92 primitive inferences a step to discover there. The `check` line in
 * each test is the point.
 */
class SolverSpec extends AnyFlatSpec with Matchers {

  /** Pigeons into holes, one clause saying each pigeon is somewhere and one saying no hole is shared. */
  private def pigeonhole(holes: Int): Problem = {
    def variable(pigeon: Int, hole: Int) = pigeon * holes + hole + 1
    val somewhere = (0 to holes).map(pigeon => (0 until holes).map(hole => variable(pigeon, hole)))
    val unshared = for {
      hole <- 0 until holes
      first <- 0 to holes
      second <- (first + 1) to holes
    } yield Vector(-variable(first, hole), -variable(second, hole))
    Cnf.problem((holes + 1) * holes, somewhere ++ unshared)
  }

  private def refutationOf(problem: Problem): Derivation =
    Solver.solve(problem) match {
      case Solver.Answer.Unsatisfiable(derivation) => derivation
      case other => fail(s"expected a refutation, got $other")
    }

  "the solver" should "refute the pigeonhole principle and produce a derivation that checks" in {
    for (holes <- 2 to 5) withClue(s"$holes holes: ") {
      val problem = pigeonhole(holes)
      val derivation = refutationOf(problem)
      derivation.check(problem) match {
        case Left(why) => fail(s"the refutation does not check: $why")
        case Right(clauses) => clauses(derivation.empty) shouldBe empty
      }
    }
  }

  it should "read every input clause of the pigeonhole principle, because none of them is spare" in {
    // The core is the whole problem here and that is a property of the pigeonhole principle rather
    // than of the solver: drop any clause and the rest is satisfiable. It is asserted because it is
    // the one case where a core computed wrongly and a core computed rightly are the same size, so a
    // test on a problem with slack would pass on a `core` that returned everything it was given.
    val problem = pigeonhole(4)
    refutationOf(problem).core shouldBe problem.clauses.indices.toSet
  }

  it should "report a core smaller than the problem where the problem has a clause to spare" in {
    // The other half of the assertion above, and the one that would catch a `core` returning
    // everything: the same problem with an untouched clause bolted on.
    val holes = 3
    val spare = Vector((holes + 1) * holes + 1)
    val padded = Cnf.problem((holes + 1) * holes + 1, pigeonhole(holes).clauses :+ spare)
    val core = refutationOf(padded).core
    core should not contain (padded.clauses.length - 1)
    core.size shouldBe (padded.clauses.length - 1)
  }

  /**
   * Random instances, decided both ways.
   *
   * **Three thousand, and the count was chosen by what it found.** The first run of this fuzz over
   * three thousand instances produced 300 unsatisfiable ones and reported 298 derivations that did
   * not check, which was one defect: the step list was snapshotted before the refutation appended to
   * it, so every derivation named a step it did not contain. At three hundred instances the same run
   * produces about thirty refutations, which is enough to find a defect of that size and not enough
   * to find one that affects a tenth of them. Under a hundred the unsatisfiable bucket is small
   * enough to be empty on a bad seed, and a fuzz that quietly tests nothing is worse than none.
   *
   * The seed is fixed, so this is a fixed set of instances rather than a new sample each run: a
   * property test that draws afresh fails on the machine that drew badly and passes on the next.
   */
  it should "agree with an exhaustive reading on three thousand random instances" in {
    val random = new scala.util.Random(20260915)
    var unsatisfiable = 0

    for (_ <- 1 to Trials) {
      val variables = 3 + random.nextInt(8)
      val clauses = Vector.fill(1 + random.nextInt(5 * variables)) {
        Vector.fill(3)(
          if (random.nextBoolean()) random.nextInt(variables) + 1 else -(random.nextInt(variables) + 1)
        )
      }
      val problem = Cnf.problem(variables, clauses)

      val exhaustive = (0 until (1 << variables)).exists { row =>
        val assignment = (0 until variables).map(at => ((row >> at) & 1) == 1).toVector
        problem.clauses.forall(clause => Cnf.holds(clause, assignment))
      }

      Solver.solve(problem) match {
        case Solver.Answer.Satisfiable(assignment) =>
          withClue(s"$problem is unsatisfiable by exhaustion: ") { exhaustive shouldBe true }
          withClue(s"the model does not satisfy $problem: ") { problem.satisfiedBy(assignment) shouldBe true }

        case Solver.Answer.Unsatisfiable(derivation) =>
          unsatisfiable += 1
          withClue(s"$problem is satisfiable by exhaustion: ") { exhaustive shouldBe false }
          withClue(s"the refutation of $problem does not check: ") { derivation.check(problem).isRight shouldBe true }

        case other => fail(s"neither answer on $problem: $other")
      }
    }

    // The measurement that says the fuzz tested the half it exists for. A run where this is zero is
    // a run where every derivation assertion above was vacuous, which is the shape of guard this
    // repository asks to be attacked rather than trusted.
    withClue("no instance came out unsatisfiable, so nothing checked a derivation: ") {
      unsatisfiable should be > 100
    }
  }

  private val Trials: Int = 3000

  "a malformed problem" should "be refused by name rather than read" in {
    Solver.solve(Problem(2, Vector(Vector(1, 3)))) match {
      case Solver.Answer.Malformed(why) => why should include("within the 2 declared variables")
      case other => fail(s"expected a refusal, got $other")
    }
  }

  it should "be refused when a clause is not canonical, since a step names the clause it concludes" in {
    Solver.solve(Problem(2, Vector(Vector(2, 1)))) match {
      case Solver.Answer.Malformed(why) => why should include("canonical form")
      case other => fail(s"expected a refusal, got $other")
    }
  }

  "the bound" should "be named in the refusal rather than reached silently" in {
    Solver.solve(pigeonhole(6), conflictLimit = 1) match {
      case Solver.Answer.Undecided(why) => why should include("within 1 conflicts")
      case other => fail(s"expected the bound to be reported, got $other")
    }
  }

  "an empty input clause" should "be the refutation itself, with no search at all" in {
    val problem = Problem(1, Vector(Cnf.Empty))
    val derivation = refutationOf(problem)
    derivation.steps shouldBe Vector(Step.Input(0))
    derivation.check(problem) shouldBe Right(Vector(Cnf.Empty))
  }

  "two contradictory units" should "be refuted at level zero, in one resolution" in {
    val problem = Cnf.problem(1, Vector(Vector(1), Vector(-1)))
    val derivation = refutationOf(problem)
    derivation.check(problem).isRight shouldBe true
    derivation.core shouldBe Set(0, 1)
  }

  "a derivation" should "be refused where a step resolves on a pivot an antecedent does not hold" in {
    // The checker attacked rather than assumed: a derivation built by hand that is wrong in the one
    // way a defect in conflict analysis is wrong. Without this the checker could return `Right` on
    // everything and every assertion above would pass.
    val problem = Cnf.problem(2, Vector(Vector(1), Vector(-1)))
    val forged = Derivation(Vector(Step.Input(0), Step.Input(1), Step.Resolve(0, 1, 2)), 2)
    forged.check(problem) match {
      case Left(why) => why should include("the pivot 2 in the left antecedent")
      case Right(_) => fail("the checker accepted a step whose antecedent does not hold the pivot")
    }
  }

  it should "be refused where the step named as empty is not" in {
    val problem = Cnf.problem(1, Vector(Vector(1)))
    Derivation(Vector(Step.Input(0)), 0).check(problem) match {
      case Left(why) => why should include("to be the empty clause")
      case Right(_) => fail("the checker accepted a derivation that does not reach the empty clause")
    }
  }

  "a tautology" should "be normalised away rather than carried as a clause" in {
    Cnf.normalise(Vector(1, -1, 2)) shouldBe None
    Cnf.normalise(Vector(2, 1, 1)) shouldBe Some(Vector(1, 2))
    Cnf.problem(2, Vector(Vector(1, -1), Vector(2))).clauses shouldBe Vector(Vector(2))
  }
  /**
   * The step count in the refusal, at one and elsewhere.
   *
   * `sat` cannot see the counter the rest of the repository uses, because it depends on nothing,
   * so it carries a copy and this is what holds the copy. A refutation of one step is not a corner
   * here: it is what an input clause that is already empty produces.
   */
  "The refusal about the empty clause's index" should "take the singular at one step and the plural elsewhere" in {
    val problem = Cnf.problem(1, Vector(Vector(1)))

    def why(steps: Int, empty: Int): String =
      Derivation(Vector.fill(steps)(Step.Input(0)), empty).check(problem) match {
        case Left(message) => message
        case Right(_) => fail("expected the index to be refused")
      }

    // `endWith` and not `include`, and the harness is what says why: "is not one of 1 step" is a
    // SUBSTRING of "is not one of 1 steps", so the `include` this was written with passed under
    // the perturbation that puts the defect back. The count is the last thing in this message,
    // which is what makes the tighter matcher available here.
    why(1, 1) should endWith("is not one of 1 step")
    why(2, 9) should endWith("is not one of 2 steps")
  }
}
