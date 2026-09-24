package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What the embedded theory can prove, and the two things a reader has to be shown about it.
 *
 * **That something is provable.** A predicate nothing satisfies satisfies every equation above it,
 * so `NUM_STEP`, `NUM_PROOF` and `NUM_PROV` are worth nothing until a formula is derived.
 * `NUM_PROV_PA` and `NUM_PROV_LOGIC` are that in general and are checked below at a **concrete**
 * code, which is a different assertion: it says those definitions, `NUM_PA`, `NUM_LOGIC` and the
 * beta function compose, rather than each being right on its own.
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

  /* The object language, as terms, because three tests below build codes by hand. */

  private val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))

  private def constant(name: String, ty: Type): Term =
    force(LogicError.lift(provability.theory.constant(name, ty)))

  private def applied(head: Term, arguments: List[Term]): Term =
    force(LogicError.lift(Term.appAll(head, arguments)))

  private val pairing = constant(Numbering.PairName, arithmetic)
  private val coding = constant(Numbering.CodeName, arithmetic)

  private def implies(left: Term, right: Term): Term =
    applied(coding, List(term("7"), applied(pairing, List(left, right))))

  private def forAll(index: Term, body: Term): Term =
    applied(coding, List(term("8"), applied(pairing, List(index, body))))

  private def predicate(name: String)(subject: Term): Term =
    applied(constant(name, Type.fun(numbers, Type.Bool)), List(subject))

  private val isFormula = predicate(Language.FormulaName)
  private val isLogical = predicate(Language.LogicName)
  private val isProvable = predicate(Provability.ProvableName)

  /** The code a concrete membership fact is about. */
  private def codeOf(member: Kernel.Thm): Term = member.conclusion match {
    case App(_, argument) => argument
    case other => fail(s"a claim about a code was expected, found $other")
  }

  private lazy val firstAxiom = force(chain.language.fact("NUM_PA_SUC_NOT_ZERO"))
  private lazy val secondAxiom = force(chain.language.fact("NUM_PA_ADD_ZERO"))
  private lazy val first = codeOf(firstAxiom)
  private lazy val second = codeOf(secondAxiom)

  private def formula(member: Kernel.Thm, code: Term): Kernel.Thm =
    force(
      rules
        .spec(code, force(chain.language.fact(Language.AxiomFormula)))
        .flatMap(rules.mp(_, member))
    )

  /**
   * `NUM_PROV (B ==> A)` for the two axioms `A` and `B`, by weakening `A` and discharging it.
   *
   * Held here rather than inside one test because two of them want it: the first asks what it is,
   * the second generalises it. `A ==> (B ==> A)` is an instance of `NUM_LOGIC_WEAKEN`, so it is
   * provable, `A` is provable because it is an axiom, and modus ponens leaves `B ==> A`.
   */
  private lazy val discharged: Kernel.Thm = {
    val weakened = implies(first, implies(second, first))
    val logical = force(
      rules
        .specTo(
          force(chain.language.fact("NUM_LOGIC_WEAKEN")),
          force(logic.mkImp(
            isFormula(first),
            force(logic.mkImp(isFormula(second), isLogical(weakened)))))
        )
        .flatMap(rules.mp(_, formula(firstAxiom, first)))
        .flatMap(rules.mp(_, formula(secondAxiom, second)))
    )
    val premise = force(
      rules
        .spec(weakened, force(provability.fact(Provability.ProvableLogic)))
        .flatMap(rules.mp(_, logical))
    )
    val antecedent = force(
      rules
        .spec(first, force(provability.fact(Provability.ProvablePeano)))
        .flatMap(rules.mp(_, firstAxiom))
    )
    force(
      rules
        .specTo(
          force(provability.fact(Provability.ModusPonens)),
          force(logic.mkImp(
            isProvable(weakened),
            force(logic.mkImp(isProvable(first), isProvable(implies(second, first))))))
        )
        .flatMap(rules.mp(_, premise))
        .flatMap(rules.mp(_, antecedent))
    )
  }

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
   * What `NUM_STEP`, `NUM_PROOF` and `NUM_PROV` cost, which is nothing, and what the facts derived
   * over them cost.
   *
   * The same split `LanguageSpec` records for the axiom sets and for the same reason: a definition
   * that does not descend into a code is settled by unfolding it. That each of these is of that
   * kind is the return on coding a sequence with the beta function, since a derivation walked
   * rather than indexed would have been a recursion over its length.
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

    Vector(
      Provability.ProvablePeano,
      Provability.ProvableLogic,
      Provability.StepShift,
      Provability.ModusPonens,
      Provability.Generalisation
    ).foreach { name =>
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
   * A theorem of the embedded theory that is not one of its axioms, derived end to end.
   *
   * Until `NUM_PROV_MP` landed, every formula this predicate was known to hold of was an axiom of
   * one of the two sets, because the only two inhabitation lemmas say exactly that. So the
   * assertion with teeth about closure is not that it holds, which the statement check above
   * already covers, but that it **produces something new**: `A ==> A'` where `A` is the axiom
   * `!v0. ~(S v0 = 0)` and `A'` is `B ==> A` for a second axiom `B`, obtained by weakening `A` and
   * discharging it against itself.
   *
   * The composition is the point. Three general facts and two concrete membership facts have to
   * meet: `NUM_PA_FORM` to know the codes are formulas, `NUM_LOGIC_WEAKEN` to get the implication,
   * `NUM_PROV_LOGIC` and `NUM_PROV_PA` to get both premises provable, and closure to discharge.
   *
   * **The two axioms are different on purpose.** `A ==> (A ==> A)` would be symmetric, and a
   * version of closure that read the pair backwards, concluding the antecedent rather than the
   * consequent, would pass against it. With `A ==> (B ==> A)` the two answers are different terms,
   * and the specialisation below is written as the instance it wants rather than by position, so a
   * statement with the pair reversed refuses here rather than proving the other thing.
   *
   * What is **not** asserted, because it costs more than it is worth here: that `B ==> A` is not
   * itself an axiom of either set. `NUM_PA_CASES` is PA's fixed codes, each nested several
   * constructors deep, and a scheme, and refuting membership in it is the long shape `LanguageSpec`
   * pays for the term and formula refusals. That it is not an axiom is an observation about the
   * tags, not a theorem here.
   */
  it should "derive a formula the two axiom sets do not hold, which is what closure is for" in {
    first should not be second

    discharged.hypotheses shouldBe empty
    discharged.conclusion shouldBe isProvable(implies(second, first))
    discharged.conclusion should not be isProvable(first)
    Derivation.axiomsOf(discharged) should have size 2
  }

  /**
   * The two rules compose, which is what being closed under the system means.
   *
   * `NUM_PROV_MP` and `NUM_PROV_GEN` are each checked against their statement above, and each
   * used once below that. Neither says the two work together, and a derivation reached by one
   * rule has to be usable by the other or the predicate is closed under each rule separately and
   * under the system not at all. So this generalises what modus ponens produced: `!i. (B ==> A)`
   * is a theorem of the embedded theory that needs both rules and is an axiom of neither set.
   *
   * **The index reaches the code, which is the second assertion and not decoration.** Generalising
   * at `0` and at `1` gives different terms, so a closure that dropped the index, or bound the
   * wrong one of the pair, would produce the same answer twice and fail here. It is the same
   * discrimination the test above makes for the implication's two sides, done for the quantifier's
   * two arguments.
   *
   * Nothing is asked of the index and nothing should be: the object language's quantifier binds
   * an index whether or not it occurs in the formula, and here it does not occur, which is the
   * vacuous case being a theorem rather than an oversight.
   */
  it should "close under both rules, which with the schemes is the whole system" in {
    val conclusion = implies(second, first)

    def generalisedAt(index: Term): Kernel.Thm =
      force(
        rules
          .specTo(
            force(provability.fact(Provability.Generalisation)),
            force(logic.mkImp(isProvable(conclusion), isProvable(forAll(index, conclusion))))
          )
          .flatMap(rules.mp(_, discharged))
      )

    val atZero = generalisedAt(term("0"))
    atZero.hypotheses shouldBe empty
    atZero.conclusion shouldBe isProvable(forAll(term("0"), conclusion))
    Derivation.axiomsOf(atZero) should have size 2

    generalisedAt(term("1")).conclusion should not be atZero.conclusion
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
