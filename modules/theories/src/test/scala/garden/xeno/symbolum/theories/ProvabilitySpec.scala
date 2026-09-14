package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What the embedded theory can prove, and the two things a reader has to be shown about it.
 *
 * **That something is provable.** A predicate nothing satisfies satisfies every equation above it,
 * so the three definitions here are worth nothing until a formula is derived. `NUM_PROV_PA` and
 * `NUM_PROV_LOGIC` are that in general and are checked below at a **concrete** code, which is a
 * different assertion: it says the three definitions, the two axiom sets and the beta function
 * compose, rather than each being right on its own.
 *
 * **That the step relation is not everything.** The two rules of inference each need an earlier
 * step, and that bound is the only thing making a derivation well founded. Drop it and `NUM_PROV`
 * holds of every formula, every equation in the file still holds, and both assertions above still
 * pass. What refuses that is the last test here: at index zero neither rule can be the reason,
 * because nothing is below zero.
 */
class ProvabilitySpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val provability = chain.provability
  private val logic = provability.logic
  private val rules = logic.rules
  private val numbers = TyApp(Natural.TypeName, Nil)

  private def term(text: String): Term =
    force(Parser.term(provability.theory, provability.notation, text, numbers))

  private def proposition(text: String): Term =
    force(Parser.proposition(provability.theory, provability.notation, text))

  "Provability" should "be the statements this development publishes" in {
    Provability.Statements.foreach { case (name, text) =>
      val theorem = force(provability.fact(name))
      withClue(s"$name: ") {
        theorem.conclusion shouldBe proposition(text)
        theorem.hypotheses shouldBe empty
      }
    }
  }

  /**
   * What the three definitions cost, which is nothing, and what the two derivations cost.
   *
   * The same split `LanguageSpec` records for the axiom sets and for the same reason: a definition
   * that does not descend into a code is settled by unfolding it. That all three are of that kind
   * is the return on coding a sequence with the beta function, since a derivation walked rather
   * than indexed would have been a recursion over its length.
   */
  it should "define by cases and cost nothing for it" in {
    val equations = Vector(
      Provability.StepCases,
      Provability.ProofCases,
      Provability.ProvableCases
    )

    equations.foreach { name =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(force(provability.fact(name))) shouldBe empty
      }
    }

    Vector(Provability.ProvablePeano, Provability.ProvableLogic).foreach { name =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(force(provability.fact(name))) should have size 2
      }
    }
  }

  /**
   * One concrete formula, derived end to end.
   *
   * `NUM_PA_SUC_NOT_ZERO` is the code of `!v0. ~(S v0 = 0)`, and `NUM_PROV` of it composes the
   * membership fact with the one-line derivation. Nothing here is general: the point is that the
   * general fact can be **used**, which is not what proving it established.
   */
  it should "prove a particular axiom of the embedded theory" in {
    val axiom = force(provability.fact(Provability.ProvablePeano))
    val member = force(chain.language.fact("NUM_PA_SUC_NOT_ZERO"))

    val code = member.conclusion match {
      case App(_, argument) => argument
      case other => fail(s"a claim about a code was expected, found $other")
    }

    val proved = force(rules.spec(code, axiom).flatMap(rules.mp(_, member)))

    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe force(
      LogicError.lift(
        Term.app(
          force(LogicError.lift(
            provability.theory.constant(Provability.ProvableName, Type.fun(numbers, Type.Bool)))),
          code
        )
      )
    )
    Derivation.axiomsOf(proved) should have size 2
  }

  /**
   * The shift at zero is the transfer, which is the claim the lemma is stated once for.
   *
   * `NUM_STEP_SHIFT` says a justified step survives its sequence being renumbered. Two derivations
   * put end to end need that twice: the second block moves and the first does not, and the first
   * is this lemma at a shift of zero. Deriving it here rather than stating a second lemma is the
   * assertion that the general one really does cover the special case, which a reader can doubt by
   * eye because `NUM_ADD ZERO i` and `i` are different terms.
   *
   * What makes it cheap is that the rewrite goes under the binder: the agreement quantifies its
   * own index, so `NUM_ZERO_ADD` has to reach inside a `!` to be of any use here.
   */
  it should "give the unshifted transfer as the case where nothing moves" in {
    def variable(name: String): Term = Term.variable(name, numbers)

    val instance = force(
      rules.specAll(
        force(provability.fact(Provability.StepShift)),
        List(
          variable("a"), variable("b"), term("ZERO"),
          variable("u"), variable("v"), variable("m"), variable("j")
        )
      )
    )

    val rule = force(Rewrite.Rule.of(logic, force(chain.peano.fact(Peano.ZeroPlus))))
    val transferred = force(Rewrite.inTheorem(Vector(rule), instance))

    transferred.hypotheses shouldBe empty
    transferred.conclusion shouldBe proposition(
      "(!i:num. NUM_LE i m ==> NUM_BETA a b i = NUM_BETA u v i) ==> " +
        "NUM_LE j m ==> NUM_STEP u v j ==> NUM_STEP a b j"
    )
    Derivation.axiomsOf(transferred) should have size 2
  }

  /**
   * At index zero a step must be an axiom, which is the bound on the rules doing its work.
   *
   * Modus ponens asks for two steps below the index and generalisation for one, so at zero neither
   * can apply: `NUM_NOT_LT_ZERO` refutes the first conjunct of each. What comes out is that the
   * four-way disjunction collapses to its first two disjuncts there.
   *
   * This is the assertion that would fail if either bound were dropped, and nothing else here
   * would. A step relation without them makes every formula provable, which is a theory that
   * proves `0 = 1` and satisfies every other test in this file.
   */
  it should "allow only an axiom as the first step of a derivation" in {
    val left = Term.variable("a", numbers)
    val right = Term.variable("b", numbers)
    val zero = term("ZERO")

    val cases = force(
      rules.specAll(force(provability.fact(Provability.StepCases)), List(left, right, zero))
    )
    val disjunction = Term.destEq(cases.conclusion).map(_._2).getOrElse(fail("an equation"))

    val parts = {
      val (first, rest) = logic.destDisj(disjunction).getOrElse(fail("a disjunction"))
      val (second, tail) = logic.destDisj(rest).getOrElse(fail("a disjunction"))
      val (third, fourth) = logic.destDisj(tail).getOrElse(fail("a disjunction"))
      Vector(first, second, third, fourth)
    }

    val axioms = force(logic.mkDisj(parts(0), parts(1)))
    val never = force(chain.peano.fact(Peano.NotBelowZero))

    /**
     * A rule's clause refuted: its first witness is below zero, and nothing is.
     *
     * Both clauses bind two variables, which is worth saying because only one of the two looks
     * like it. Modus ponens binds the two steps it reads; generalisation binds the step and the
     * INDEX it quantifies, and that index is bounded by nothing. What refutes either is the first
     * witness alone, so the second is opened and never used.
     */
    def refuted(clause: Term): Kernel.Thm = {
      val assumed = force(LogicError.lift(Kernel.assume(clause)))

      def open(existential: Kernel.Thm, name: String, taken: Set[FVar])(
        reach: (FVar, Kernel.Thm) => Kernel.Thm
      ): Kernel.Thm = {
        val predicate = logic
          .destExistsPredicate(existential.conclusion)
          .getOrElse(fail("an existential was expected"))
        val variable = Conv.freshVariable(name, numbers, taken)
        val applied = force(LogicError.lift(Term.app(predicate, variable)))
        val contraction = force(Conv.betaRoot(applied))
        val body = Term.destEq(contraction.conclusion).map(_._2).getOrElse(fail("an equation"))
        val instance = force(LogicError.lift(Kernel.assume(body)))
        force(rules.existsElim(existential, variable, reach(variable, instance)))
      }

      // The refutation has to happen INSIDE the innermost opening. `Rules.existsElim` refuses a
      // case whose conclusion names the witness, and a closure that hands the instance back out so
      // the caller can take it apart is exactly that: the conclusion is then the body.
      val absurd = open(assumed, "x", Set(left, right)) { (witness, atWitness) =>
        def contradict(reached: Kernel.Thm): Kernel.Thm = {
          val below = force(rules.conjElim1(reached))
          force(rules.notElim(force(rules.spec(witness, never)), below))
        }

        open(atWitness, "y", Set(left, right, witness)) { (_, atSecond) => contradict(atSecond) }
      }

      force(rules.notIntro(clause, absurd))
    }

    val noModusPonens = refuted(parts(2))
    val noGeneralisation = refuted(parts(3))

    val step = force(LogicError.lift(Kernel.assume(proposition("NUM_STEP a b ZERO"))))
    val opened = force(LogicError.lift(Kernel.eqMp(cases, step)))

    // The nest is right-associated and has four disjuncts, so it is taken apart the way
    // `LanguageSpec` takes `NUM_FORM_CASES` apart: two assumed tails and three eliminations.
    val onlyAxioms = {
      def refusedCase(clause: Term, never: Kernel.Thm): Kernel.Thm = {
        val assumed = force(LogicError.lift(Kernel.assume(clause)))
        force(rules.falsityElim(axioms, force(rules.notElim(never, assumed))))
      }

      val fromFirst = force(
        rules.disjIntro1(parts(1), force(LogicError.lift(Kernel.assume(parts(0)))))
      )
      val fromSecond = force(
        rules.disjIntro2(parts(0), force(LogicError.lift(Kernel.assume(parts(1)))))
      )
      val fromThird = refusedCase(parts(2), noModusPonens)
      val fromFourth = refusedCase(parts(3), noGeneralisation)

      val tail = force(LogicError.lift(Kernel.assume(force(logic.mkDisj(parts(2), parts(3))))))
      val rest = force(LogicError.lift(Kernel.assume(
        force(logic.mkDisj(parts(1), force(logic.mkDisj(parts(2), parts(3))))))))
      val insideTail = force(rules.disjElim(tail, fromThird, fromFourth))
      val insideRest = force(rules.disjElim(rest, fromSecond, insideTail))
      force(rules.disjElim(opened, fromFirst, insideRest))
    }

    val settled = force(rules.disch(step.conclusion, onlyAxioms))

    settled.hypotheses shouldBe empty
    settled.conclusion shouldBe proposition(
      "NUM_STEP a b ZERO ==> " +
        "(NUM_PA (NUM_BETA a b ZERO) \\/ NUM_LOGIC (NUM_BETA a b ZERO))"
    )
  }
}
