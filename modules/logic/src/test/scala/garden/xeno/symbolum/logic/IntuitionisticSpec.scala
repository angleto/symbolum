package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * Intuitionistic propositional logic, decided, and the boundary either side of it.
 *
 * What carries this file is not that these statements are provable. It is that they are provable on
 * **no axioms**, negation and all: the excluded middle is derived in this system rather than
 * assumed, what it is derived from is the choice operator, and a classical procedure puts that
 * under every theorem it produces. The `axiomsOf` line in [[proved]] is the assertion, and it runs
 * on every goal below rather than on a chosen one.
 *
 * The other half is the refusals. A procedure that proved everything classical would be the
 * procedure this repository already had; what makes this one worth its lines is that it stops
 * exactly where intuitionistic provability stops, and the classical goals it refuses below, the
 * ones under "the boundary" among them, are where.
 */
class IntuitionisticSpec extends AnyFlatSpec with Matchers {

  private val logic = Logic.standard
  private val intuitionistic = Intuitionistic.standard

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private val p = Term.variable("p", Type.Bool)
  private val q = Term.variable("q", Type.Bool)
  private val r = Term.variable("r", Type.Bool)

  private def conj(left: Term, right: Term): Term = force(logic.mkConj(left, right))
  private def disj(left: Term, right: Term): Term = force(logic.mkDisj(left, right))
  private def imp(left: Term, right: Term): Term = force(logic.mkImp(left, right))
  private def not(inner: Term): Term = force(logic.mkNot(inner))
  private def all(variables: List[FVar], body: Term): Term =
    variables.foldRight(body)((variable, inner) => force(logic.mkForall(variable, inner)))

  /** Proved, concluding the goal itself, resting on nothing, and costing no axiom. */
  private def proved(goal: Term): Kernel.Thm = {
    val theorem = force(intuitionistic.prove(goal))
    theorem.conclusion shouldBe goal
    theorem.hypotheses shouldBe empty
    withClue(s"this calculus must cost nothing, and ${Derivation.size(theorem)} steps reached: ") {
      Derivation.axiomsOf(theorem) shouldBe empty
    }
    theorem
  }

  private def refused(goal: Term): Unit = intuitionistic.prove(goal).isLeft shouldBe true

  /* --------------------------------------------------------- what the fragment below reached */

  "Everything the negation-free fragment reaches" should "still be reached here" in {
    // `Minimal` delegates its search to this file, so these are its own tests run through the
    // wider calculus. They are repeated rather than cited because the delegation is what would
    // remove them: a change that made this file narrower would leave `MinimalSpec` red and nothing
    // saying which of the two had moved.
    proved(all(List(p, q), imp(conj(p, q), p)))
    proved(all(List(p, q), imp(p, disj(p, q))))

    val premises = conj(disj(p, q), conj(imp(p, r), imp(q, r)))
    proved(all(List(p, q, r), imp(premises, r)))
  }

  /* ------------------------------------------------------------------- what negation adds */

  "A contradiction" should "be refutable without any classical step" in {
    // `~(p /\ ~p)`, which `Minimal` could not state, let alone prove. Nothing classical is spent:
    // assume the conjunction, take both halves, and one is the negation of the other.
    proved(all(List(p), not(conj(p, not(p)))))
  }

  "Double negation" should "go in the direction that holds and not in the other" in {
    // The pair is the assertion. `p ==> ~~p` is intuitionistic and `~~p ==> p` is the classical
    // axiom in disguise, so a procedure that proved both would be a classical one wearing this
    // file's name, and a procedure that proved neither would be useless.
    proved(all(List(p), imp(p, not(not(p)))))
    refused(all(List(p), imp(not(not(p)), p)))
  }

  "Contraposition" should "hold in the direction that does not need the excluded middle" in {
    proved(all(List(p, q), imp(imp(p, q), imp(not(q), not(p)))))
    refused(all(List(p, q), imp(imp(not(q), not(p)), imp(p, q))))
  }

  "De Morgan" should "be split by this boundary rather than held whole" in {
    // Three of the four laws are intuitionistic and the fourth is not, which is the crispest
    // demonstration that this is a real fragment and not a weaker search over the classical one.
    proved(all(List(p, q), imp(not(disj(p, q)), conj(not(p), not(q)))))
    proved(all(List(p, q), imp(conj(not(p), not(q)), not(disj(p, q)))))
    proved(all(List(p, q), imp(disj(not(p), not(q)), not(conj(p, q)))))
    refused(all(List(p, q), imp(not(conj(p, q)), disj(not(p), not(q)))))
  }

  "Ex falso" should "reach any goal at all, which is the rule negation needs and costs nothing" in {
    proved(all(List(p, q), imp(conj(p, not(p)), q)))
  }

  /* ------------------------------------------------- the rule the contraction-free calculus adds */

  "An implication whose antecedent is an implication" should "be used without keeping it" in {
    // `((p ==> q) ==> r) ==> (q ==> r)`, which is what the four-rule left implication is for: the
    // hypothesis is consumed, `r ==> r` closes the right premise, and `q` on the left closes the
    // left one. Under the rule that keeps the implication and asks for its antecedent, the same
    // goal is reachable and the search that reaches it does not terminate on its own.
    proved(all(List(p, q, r), imp(imp(imp(p, q), r), imp(q, r))))
  }

  it should "terminate where the naive rule loops" in {
    // `((p ==> p) ==> q) ==> q`. The naive left rule asks for `p ==> p` from a sequent that still
    // holds `(p ==> p) ==> q`, and the state it recurses on is the state it came from. Here the
    // hypothesis is replaced by something strictly lighter and the search ends. What this test
    // pins is that it ends with a THEOREM: a loop that was merely cut off by the fuel would refuse.
    proved(all(List(p, q), imp(imp(imp(p, p), q), q)))
  }

  "A goal needing both premises of that rule" should "not be reachable from one" in {
    // The rule has two premises and a search that dropped either would still pass every test above.
    // `((p ==> q) ==> r) ==> r` is what separates them: the right premise `r |- r` closes at once,
    // and the left one asks for `p ==> q` from nothing, which does not hold. So a search that
    // required only the right premise would prove this, and it must not.
    refused(all(List(p, q, r), imp(imp(imp(p, q), r), r)))
  }

  /* ------------------------------------------------------------------------ the boundary */

  "Peirce's law" should "be refused here and proved classically, which is the whole trade" in {
    // The pair, asserted together, because either half alone says nothing. The first says this
    // calculus stops; the second says the goal is a theorem anyway and names what reaching it
    // costs. `MinimalSpec` holds the same boundary for the narrower fragment.
    val peirce = all(List(p, q), imp(imp(imp(p, q), p), p))

    refused(peirce)

    val classical = force(Propositional.standard.prove(peirce))
    classical.conclusion shouldBe peirce
    Derivation.axiomsOf(classical) should have size 1
  }

  "The excluded middle" should "be refused here for the same reason" in {
    val excluded = all(List(p), disj(p, not(p)))

    refused(excluded)
    force(Propositional.standard.prove(excluded)).conclusion shouldBe excluded
  }

  /* ------------------------------------------------------------------------ the address */

  "A goal with no connective in it" should "not be addressed here" in {
    // An atom is given no meaning, so a goal that is one is not a question this can answer, and
    // saying so before spending anything is what keeps a statement from being routed here when a
    // procedure that reads its atoms could settle it.
    intuitionistic.reads(all(List(p), p)) shouldBe false
    intuitionistic.reads(all(List(p), not(p))) shouldBe true
    intuitionistic.reads(Term.variable("x", TyVar("A"))) shouldBe false
  }

  "A refusal" should "say nothing about the goal, and carry the standing that says so" in {
    // The same argument `SkeletonFailsAt` makes on the classical side. `~(x = y) ==> ~(y = x)` is
    // true and is refused here, because the two equations are two atoms and this calculus never
    // looks inside one. A refusal that carried `Decided` would be a claim about the mathematics,
    // and this one is a claim about the fragment.
    val subject = TyVar("A")
    val x = Term.variable("x", subject)
    val y = Term.variable("y", subject)
    val equals = force(Term.eq(x, y))
    val reversed = force(Term.eq(y, x))

    val goal = all(List(x, y), imp(not(equals), not(reversed)))

    intuitionistic.prove(goal) match {
      case Right(theorem) => fail(s"an atom has no meaning here, and this needs one: $theorem")
      case Left(refusal) => refusal.standing shouldBe LogicError.Standing.Unread
    }
  }

  "This calculus" should "reach no solver at all, which is what makes its cost checkable" in {
    // `Propositional` sends a goal to `modules/sat` and re-derives what comes back, and its whole
    // argument is that nothing the solver says is believed. This file makes the stronger claim: it
    // never asks. A theorem it produces is the search itself, step by step, so there is no replay
    // to get wrong.
    //
    // Written as a scan for the reason `Quantified`'s own is: a runtime assertion about what a file
    // did not call is not expressible, and the import list is where the answer actually lives. The
    // second half is the guard against a scan that passes because the file is empty.
    val source = java.nio.file.Files.readString(
      java.nio.file.Paths.get("modules/logic/src/main/scala/garden/xeno/symbolum/logic/Intuitionistic.scala")
    )

    val imports = source.linesIterator.filter(_.trim.startsWith("import")).toVector
    withClue(s"the imports are ${imports.mkString(", ")}\n") {
      imports.filter(_.contains("sat")) shouldBe empty
    }

    val solver = Vector("Solver", "Cnf.", "Resolution", "Literal")
    withClue(s"names the solver: ${solver.filter(source.contains).mkString(", ")}\n") {
      solver.filter(source.contains) shouldBe empty
    }

    source should include("Dyckhoff")
    proved(all(List(p), not(conj(p, not(p)))))
  }

  /* -------------------------------------------------------------- the claim it was written for */

  "A claim of a domain that is not mathematics" should "cost no foundational axiom" in {
    // The skeleton of `DomainTheorySpec`'s release gate, with the domain's predicates as bare
    // propositional variables: a change meeting none of the three grounds does not ship. This is
    // the shape that had no procedure until now — `Minimal` refuses it for the three negations and
    // `Propositional` takes it and charges the choice axiom — and it is what this file exists for.
    val two = Term.variable("two", Type.Bool)
    val one = Term.variable("one", Type.Bool)
    val green = Term.variable("green", Type.Bool)
    val revert = Term.variable("revert", Type.Bool)
    val ships = Term.variable("ships", Type.Bool)

    val converse = imp(ships, disj(two, disj(conj(one, green), revert)))
    val denied = conj(not(two), conj(not(green), not(revert)))

    val theorem = proved(all(List(two, one, green, revert, ships), imp(converse, imp(denied, not(ships)))))
    info(s"${Derivation.size(theorem)} inferences, ${Derivation.axiomsOf(theorem).size} axioms")
  }
}
