package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Derivations of the embedded theory, and the one thing a reader has to be shown about them.
 *
 * The statements are checked below the way every development's are. What that does not say is that
 * they can be **used**, which is a different claim and the one this layer exists for: a scheme
 * proved over a variable formula is worth nothing until a caller can hand it a code, discharge the
 * `NUM_FORM` condition it carries, and get a provability fact back. So the last test builds a chain
 * of object-level implications out of three concrete axioms and reads the end off it.
 *
 * The three codes are deliberately **different** axioms. A syllogism wired to return one of its two
 * premises rather than their composition is a true theorem about the wrong pair, and with `A`, `B`
 * and `C` distinct the three candidate answers are three distinct terms.
 */
class DeductionSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val deduction = chain.deduction
  private val logic = deduction.logic
  private val rules = logic.rules
  private val numbers = TyApp(Natural.TypeName, Nil)
  private val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))

  private def term(text: String): Term =
    force(Parser.term(deduction.theory, deduction.notation, text, numbers))

  private def proposition(text: String): Term =
    force(Parser.proposition(deduction.theory, deduction.notation, text))

  private def constant(name: String, ty: Type): Term =
    force(LogicError.lift(deduction.theory.constant(name, ty)))

  private def applied(head: Term, arguments: List[Term]): Term =
    force(LogicError.lift(Term.appAll(head, arguments)))

  private val pairing = constant(Numbering.PairName, arithmetic)
  private val coding = constant(Numbering.CodeName, arithmetic)

  private def imp(left: Term, right: Term): Term =
    applied(coding, List(term("7"), applied(pairing, List(left, right))))

  private def predicate(name: String)(subject: Term): Term =
    applied(constant(name, Type.fun(numbers, Type.Bool)), List(subject))

  private val isFormula = predicate(Language.FormulaName)
  private val isLogical = predicate(Language.LogicName)
  private val isProvable = predicate(Provability.ProvableName)

  private def imply(left: Term, right: Term): Term = force(logic.mkImp(left, right))

  "Deduction" should "be the statements this development publishes" in {
    Deduction.Statements.foreach { case (name, text) =>
      val theorem = force(deduction.fact(name))
      withClue(s"$name: ") {
        theorem.conclusion shouldBe proposition(text)
        theorem.hypotheses shouldBe empty
      }
    }
  }

  /**
   * What a derivation of the embedded theory costs, which is what everything above it costs.
   *
   * An equality and not a ceiling, the way `CodingSpec` and `LanguageSpec` state theirs. Two is
   * what the naturals cost, choice and infinity, and a layer that started spending anything else
   * would be spending it on the embedded theory's behalf, which is the one number this whole
   * development is not allowed to move.
   */
  it should "cost the naturals' two axioms and nothing else" in {
    Deduction.Statements.foreach { case (name, _) =>
      withClue(s"$name: ") {
        Derivation.axiomsOf(force(deduction.fact(name))) should have size 2
      }
    }
  }

  /**
   * It declares nothing, which is what makes it the first link that is not an extension.
   *
   * `docs/adr/0013` asks for a development whose product is object-level derivations, and the
   * measurable consequence is here: the theory it hands on is the one it was given, constant for
   * constant. If a definition ever lands in this file the assertion goes red, which is the moment
   * to decide whether it belongs here or one floor down.
   */
  it should "extend the theory it was built over by nothing at all" in {
    deduction.theory.constants shouldBe chain.provability.theory.constants
    deduction.theory.axioms shouldBe chain.provability.theory.axioms
  }

  /**
   * The deduction theorem at a concrete formula, with nothing left assumed.
   *
   * Both of its conditions are discharged here rather than carried: `NUM_FORM h` from
   * `NUM_PA_FORM`, and `!i. ~(NUM_FREE_FORM i h)` from `Language.notFreeIn`, which walks the code.
   * The second is why this test can exist at all. Until that walk landed, the theorem was proved
   * and applied to no formula anybody could name, and this file said so where this docstring now
   * says the opposite.
   *
   * The derivation it consumes is the smallest there is, the one line that **is** `h`, built from
   * `NUM_BETA_SEQUENCE` the way every inhabitation in `Provability` is. What comes out is
   * `NUM_PROV (h ==> h)` with **no hypotheses**, which is the whole point: a closed theorem about a
   * particular formula of the embedded theory, reached through the deduction theorem rather than
   * around it.
   *
   * `NUM_PROV_SELF` gives the same conclusion directly, and the agreement is the assertion rather
   * than a redundancy: this route exercises both definitions, the induction and the hypothesis
   * case, and the direct one touches none of them.
   */
  it should "apply at a concrete formula, with both of its conditions discharged" in {
    val axiom = force(chain.language.fact("NUM_PA_SUC_NOT_ZERO"))
    val h = axiom.conclusion match {
      case App(_, argument) => argument
      case other => fail(s"a claim about a code was expected, found $other")
    }

    val formulaH = force(
      rules
        .spec(h, force(chain.language.fact(Language.AxiomFormula)))
        .flatMap(rules.mp(_, axiom)))
    val notFree = force(chain.language.notFreeIn(h))

    val zero = term("ZERO")
    val one = term("SUC ZERO")

    // The sequence whose only entry is `h`, taken up to one.
    val constantSequence = force(LogicError.lift(Term.abs(Term.variable("j", numbers), h)))
    val taken = force(
      rules.specAll(force(chain.coding.fact(Coding.BetaSequence)), List(constantSequence, one)))
    val opened = force(
      Conv.betaNormalise(taken.conclusion)
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, taken))))

    def openOne(existential: Kernel.Thm, name: String, avoid: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val inner = logic.destExistsPredicate(existential.conclusion)
        .getOrElse(fail("an existential was expected"))
      val fresh = Conv.freshVariable(
        name, numbers, avoid ++ Term.freeVariables(existential.conclusion))
      val body = Term
        .destEq(force(Conv.betaRoot(applied(inner, List(fresh)))).conclusion)
        .map(_._2)
        .getOrElse(fail("an equation was expected"))
      force(rules.existsElim(existential, fresh,
        reach(fresh, force(LogicError.lift(Kernel.assume(body))))))
    }

    val reached = openOne(opened, "a", Set.empty) { (a, atA) =>
      openOne(atA, "b", Set(a)) { (b, atB) =>
        // The entry at zero is `h`, since zero is below one.
        val here = force(
          rules
            .spec(zero, atB)
            .flatMap(rules.mp(_, force(
              rules.spec(zero, force(chain.peano.fact(Peano.SuccessorPositive)))))))

        // So the step at zero is justified by being the hypothesis, and it is a formula.
        val stepCases = force(
          rules.specAll(force(chain.provability.fact(Provability.StepFromCases)),
            List(h, a, b, zero)))
        val body = Term.destEq(stepCases.conclusion).map(_._2).getOrElse(fail("an equation"))
        val (_, choice) = logic.destConj(body).getOrElse(fail("a conjunction"))

        val formulaHere = force(
          Conv
            .apTerm(constant(Language.FormulaName, Type.fun(numbers, Type.Bool)), here)
            .flatMap(Conv.sym)
            .flatMap(step => LogicError.lift(Kernel.eqMp(step, formulaH))))
        val justified = force(
          rules
            .conjIntro(formulaHere, force(rules.disjIntro2(
              logic.destDisj(choice).map(_._1).getOrElse(fail("a disjunction")), here)))
            .flatMap(pair => Conv.sym(stepCases)
              .flatMap(step => LogicError.lift(Kernel.eqMp(step, pair)))))

        // Every index at most zero is zero, so that one step is the whole derivation.
        val marker = Term.variable("j", numbers)
        val boundTerm = proposition("NUM_LE j ZERO")
        val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))
        val isZero = force(
          rules
            .spec(marker, force(chain.peano.fact(Peano.AtMostZero)))
            .flatMap(rules.mp(_, bounded)))
        val everyStep = force(
          Conv
            .apTerm(
              applied(
                constant(Provability.StepFromName,
                  Type.fun(numbers, Type.fun(numbers, Type.fun(numbers,
                    Type.fun(numbers, Type.Bool))))),
                List(h, a, b)),
              isZero)
            .flatMap(Conv.sym)
            .flatMap(step => LogicError.lift(Kernel.eqMp(step, justified)))
            .flatMap(rules.disch(boundTerm, _))
            .flatMap(rules.gen(marker, _)))

        val fromCases = force(
          rules.specAll(force(chain.provability.fact(Provability.ProvableFromCases)), List(h, h)))
        val fromBody = Term.destEq(fromCases.conclusion).map(_._2).getOrElse(fail("an equation"))

        def instantiate(existential: Term, argument: Term): Term = {
          val inner = logic.destExistsPredicate(existential).getOrElse(fail("an existential"))
          Term
            .destEq(force(Conv.betaRoot(applied(inner, List(argument)))).conclusion)
            .map(_._2)
            .getOrElse(fail("an equation"))
        }
        val atLength = instantiate(fromBody, zero)
        val atFirst = instantiate(atLength, a)

        def under(existential: Term, witness: Term, proof: Kernel.Thm): Kernel.Thm =
          force(rules.existsIntro(
            logic.destExistsPredicate(existential).getOrElse(fail("an existential")),
            witness, proof))

        val derivation = force(
          rules
            .conjIntro(here, everyStep)
            .map(pair => under(fromBody, zero, under(atLength, a, under(atFirst, b, pair))))
            .flatMap(packed => Conv.sym(fromCases)
              .flatMap(step => LogicError.lift(Kernel.eqMp(step, packed)))))

        force(
          rules
            .specTo(
              force(deduction.fact(Deduction.DeductionTheorem)),
              imply(isFormula(h), imply(notFree.conclusion,
                imply(applied(
                  constant(Provability.ProvableFromName,
                    Type.fun(numbers, Type.fun(numbers, Type.Bool))),
                  List(h, h)), isProvable(imp(h, h))))))
            .flatMap(rules.mp(_, formulaH))
            .flatMap(rules.mp(_, notFree))
            .flatMap(rules.mp(_, derivation)))
      }
    }

    reached.hypotheses shouldBe empty
    reached.conclusion shouldBe isProvable(imp(h, h))
    Derivation.axiomsOf(reached) should have size 2

    // The direct route agrees, which is what makes this a check of the long one.
    val direct = force(
      rules
        .specTo(force(deduction.fact(Deduction.SelfImplication)),
          imply(isFormula(h), isProvable(imp(h, h))))
        .flatMap(rules.mp(_, formulaH)))
    direct.conclusion shouldBe reached.conclusion
  }

  /**
   * The deduction theorem's rules, composed into something neither gives alone.
   *
   * `NUM_PROV_WEAKEN` and `NUM_PROV_IMP_MP` are checked against their statements above. What that
   * does not say is that they fit together, which is the only reason either exists: the deduction
   * theorem's induction applies the first at its axiom cases and the second at its modus ponens
   * case, and if the shapes did not meet the induction would not close.
   *
   * So this does one step of that induction by hand. `A ==> (C ==> A)` is weakening and therefore
   * provable; carried under `B` it is `B ==> (A ==> (C ==> A))`. `A` is an axiom, so `B ==> A` is
   * provable the same way. Modus ponens under the hypothesis `B` then detaches `A` and leaves
   * `B ==> (C ==> A)`, which is not an axiom of either set and is not reachable by weakening alone.
   *
   * The three codes are distinct axioms, so a rule that returned one of its arguments rather than
   * their composition has three wrong answers available and the assertion below rejects them.
   *
   * What is **not** asserted here, and it is the third rule: `NUM_PROV_IMP_GEN` is not exercised at
   * a concrete code, because its side condition is `~(NUM_FREE_FORM i h)` and discharging that for
   * a particular `h` means walking the code through the freeness clauses. The rule is checked
   * against its statement like the others; that its side condition is satisfiable at a real code is
   * work the deduction theorem itself will have to do.
   */
  it should "compose weakening with modus ponens under a hypothesis, which is one step of the induction" in {
    val axioms = Vector("NUM_PA_SUC_NOT_ZERO", "NUM_PA_ADD_ZERO", "NUM_PA_MUL_ZERO")
      .map(name => force(chain.language.fact(name)))

    def codeOf(member: Kernel.Thm): Term = member.conclusion match {
      case App(_, argument) => argument
      case other => fail(s"a claim about a code was expected, found $other")
    }

    val Vector(first, second, third) = axioms.map(codeOf)
    Vector(first, second, third).distinct should have size 3

    val areFormulas = force(chain.language.fact(Language.AxiomFormula))
    def formula(member: Kernel.Thm): Kernel.Thm =
      force(rules.spec(codeOf(member), areFormulas).flatMap(rules.mp(_, member)))

    def provableAxiom(member: Kernel.Thm): Kernel.Thm =
      force(
        rules
          .spec(codeOf(member), force(chain.provability.fact(Provability.ProvablePeano)))
          .flatMap(rules.mp(_, member))
      )

    def carriedUnder(hypothesis: Term, held: Kernel.Thm, subject: Term, form: Kernel.Thm)
      : Kernel.Thm =
      force(
        rules
          .specTo(
            force(deduction.fact(Deduction.Weaken)),
            imply(
              isFormula(hypothesis),
              imply(isFormula(subject), imply(isProvable(subject), isProvable(imp(hypothesis, subject))))))
          .flatMap(rules.mp(_, formula(axioms(1))))
          .flatMap(rules.mp(_, form))
          .flatMap(rules.mp(_, held))
      )

    // `A ==> (C ==> A)` is weakening, hence provable.
    val weakened = imp(first, imp(third, first))
    val weakeningIsLogical = force(
      rules
        .specTo(
          force(chain.language.fact("NUM_LOGIC_WEAKEN")),
          imply(isFormula(first), imply(isFormula(third), isLogical(weakened))))
        .flatMap(rules.mp(_, formula(axioms(0))))
        .flatMap(rules.mp(_, formula(axioms(2))))
    )
    val weakeningIsProvable = force(
      rules
        .spec(weakened, force(chain.provability.fact(Provability.ProvableLogic)))
        .flatMap(rules.mp(_, weakeningIsLogical))
    )

    val formulaOfWeakened = force(
      rules
        .specTo(
          force(chain.language.fact("NUM_FORM_IMP")),
          imply(
            isFormula(first),
            imply(isFormula(imp(third, first)), isFormula(weakened))))
        .flatMap(rules.mp(_, formula(axioms(0))))
        .flatMap(rules.mp(_, force(
          rules
            .specTo(
              force(chain.language.fact("NUM_FORM_IMP")),
              imply(isFormula(third), imply(isFormula(first), isFormula(imp(third, first)))))
            .flatMap(rules.mp(_, formula(axioms(2))))
            .flatMap(rules.mp(_, formula(axioms(0)))))))
    )

    val underB = carriedUnder(second, weakeningIsProvable, weakened, formulaOfWeakened)
    val antecedent = carriedUnder(second, provableAxiom(axioms(0)), first, formula(axioms(0)))

    val detached = force(
      rules
        .specTo(
          force(deduction.fact(Deduction.ImplicationModusPonens)),
          imply(
            isFormula(second),
            imply(
              isFormula(first),
              imply(
                isFormula(imp(third, first)),
                imply(
                  isProvable(imp(second, imp(first, imp(third, first)))),
                  imply(
                    isProvable(imp(second, first)),
                    isProvable(imp(second, imp(third, first)))))))))
        .flatMap(rules.mp(_, formula(axioms(1))))
        .flatMap(rules.mp(_, formula(axioms(0))))
        .flatMap(rules.mp(_, force(
          rules
            .specTo(
              force(chain.language.fact("NUM_FORM_IMP")),
              imply(isFormula(third), imply(isFormula(first), isFormula(imp(third, first)))))
            .flatMap(rules.mp(_, formula(axioms(2))))
            .flatMap(rules.mp(_, formula(axioms(0)))))))
        .flatMap(rules.mp(_, underB))
        .flatMap(rules.mp(_, antecedent))
    )

    detached.hypotheses shouldBe empty
    detached.conclusion shouldBe isProvable(imp(second, imp(third, first)))
    detached.conclusion should not be isProvable(imp(second, first))
    detached.conclusion should not be isProvable(weakened)
    Derivation.axiomsOf(detached) should have size 2
  }

  /**
   * Three axioms chained into one implication, which is the assertion that the layer is usable.
   *
   * `B` is provable because it is an axiom, so weakening gives `NUM_PROV (A ==> B)`; the same for
   * `C` gives `NUM_PROV (B ==> C)`; and the syllogism composes them. Everything below has to hold
   * together for that to come out: the membership facts, `NUM_PA_FORM` for the side conditions,
   * `NUM_LOGIC_WEAKEN`, `NUM_PROV_LOGIC`, `NUM_PROV_MP` inside the syllogism, and the syllogism
   * itself.
   *
   * The identity is checked at the same `A`, and it is the one place a reader can see that a
   * scheme proved over a variable formula really does apply to a code.
   */
  it should "chain three concrete axioms into an implication none of them is" in {
    val axioms = Vector("NUM_PA_SUC_NOT_ZERO", "NUM_PA_ADD_ZERO", "NUM_PA_MUL_ZERO")
      .map(name => force(chain.language.fact(name)))

    def codeOf(member: Kernel.Thm): Term = member.conclusion match {
      case App(_, argument) => argument
      case other => fail(s"a claim about a code was expected, found $other")
    }

    val Vector(first, second, third) = axioms.map(codeOf)
    Vector(first, second, third).distinct should have size 3

    val areFormulas = force(chain.language.fact(Language.AxiomFormula))
    def formula(member: Kernel.Thm): Kernel.Thm =
      force(rules.spec(codeOf(member), areFormulas).flatMap(rules.mp(_, member)))

    def provableAxiom(member: Kernel.Thm): Kernel.Thm =
      force(
        rules
          .spec(codeOf(member), force(chain.provability.fact(Provability.ProvablePeano)))
          .flatMap(rules.mp(_, member))
      )

    /** `NUM_PROV (x ==> y)` whenever `y` is provable, by weakening it under `x`. */
    def weakenedTo(x: Term, member: Kernel.Thm): Kernel.Thm = {
      val y = codeOf(member)
      val code = imp(y, imp(x, y))
      val logical = force(
        rules
          .specTo(
            force(chain.language.fact("NUM_LOGIC_WEAKEN")),
            imply(isFormula(y), imply(isFormula(x), isLogical(code))))
          .flatMap(rules.mp(_, formula(member)))
          .flatMap(rules.mp(_, formula(axioms.find(other => codeOf(other) == x).getOrElse(
            fail("the antecedent has to be one of the three axioms")))))
      )
      val provable = force(
        rules
          .spec(code, force(chain.provability.fact(Provability.ProvableLogic)))
          .flatMap(rules.mp(_, logical))
      )
      force(
        rules
          .specTo(
            force(chain.provability.fact(Provability.ModusPonens)),
            imply(isProvable(code), imply(isProvable(y), isProvable(imp(x, y)))))
          .flatMap(rules.mp(_, provable))
          .flatMap(rules.mp(_, provableAxiom(member)))
      )
    }

    val firstStep = weakenedTo(first, axioms(1))
    val secondStep = weakenedTo(second, axioms(2))
    firstStep.conclusion shouldBe isProvable(imp(first, second))
    secondStep.conclusion shouldBe isProvable(imp(second, third))

    val chained = force(
      rules
        .specTo(
          force(deduction.fact(Deduction.Syllogism)),
          imply(
            isFormula(first),
            imply(
              isFormula(second),
              imply(
                isFormula(third),
                imply(
                  isProvable(imp(first, second)),
                  imply(isProvable(imp(second, third)), isProvable(imp(first, third)))))))
        )
        .flatMap(rules.mp(_, formula(axioms(0))))
        .flatMap(rules.mp(_, formula(axioms(1))))
        .flatMap(rules.mp(_, formula(axioms(2))))
        .flatMap(rules.mp(_, firstStep))
        .flatMap(rules.mp(_, secondStep))
    )

    chained.hypotheses shouldBe empty
    chained.conclusion shouldBe isProvable(imp(first, third))
    chained.conclusion should not be isProvable(imp(first, second))
    chained.conclusion should not be isProvable(imp(second, third))
    Derivation.axiomsOf(chained) should have size 2

    val identity = force(
      rules
        .specTo(
          force(deduction.fact(Deduction.SelfImplication)),
          imply(isFormula(first), isProvable(imp(first, first))))
        .flatMap(rules.mp(_, formula(axioms(0))))
    )
    identity.hypotheses shouldBe empty
    identity.conclusion shouldBe isProvable(imp(first, first))
    Derivation.axiomsOf(identity) should have size 2
  }
}
