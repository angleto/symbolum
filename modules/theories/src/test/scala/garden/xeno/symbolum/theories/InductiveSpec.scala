package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The set defined by rules, and the one question that decides whether it was worth defining.
 *
 * **What it cost.** Two constants and no axiom, asserted against the theory it was built over
 * rather than against a number, which is `ProductSpec`'s argument and the same one.
 *
 * **What it says.** Each fact is compared against the text `Inductive.Statements` holds, read as a
 * term: `RotationSpec`'s reason applies unchanged, a type variable being written `'a` and printed
 * `a`.
 *
 * **Whether a membership can be proved.** The even numbers, as the least set holding `ZERO` and
 * closed under two successors. Two applications of [[Inductive.Introduction]], and the monotonicity
 * of that operator proved by hand in front of them, which is the measurement the file's docstring
 * quotes when it says no procedure decides monotonicity here.
 *
 * **Whether a NON-membership can be proved, which is the test this development exists for.** A
 * closure computed forwards answers the first question and cannot answer this one: it enumerates
 * members, so a non-member is indistinguishable from a member further away than the budget. Here
 * `~(EVEN (SUC ZERO))` is derived from [[Inductive.Induction]] at the set of numbers that are not
 * one, and the derivation uses **no** monotonicity, which is the asymmetry the docstring claims
 * and this is where it is checked.
 *
 * The membership test is also the guard against the failure that would make everything else here
 * vacuous. `INDUCTIVE f` with an empty extension satisfies the induction principle trivially and
 * every non-membership above it would pass; so a test suite that proved only non-memberships would
 * be green on a definition that says nothing. That is the question `CLAUDE.md` asks of every guard
 * — what input makes it trivially true — and the answer is the one test that has to be a
 * membership.
 */
class InductiveSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private def lift[T](result: Either[KernelError, T]): T = force(LogicError.lift(result))

  private val chain = Chain.standard
  private val inductive = chain.inductive
  private val logic = inductive.logic
  private val rules = logic.rules

  private def fact(name: String): Kernel.Thm = force(inductive.fact(name))

  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val numberSets: Type = Type.fun(numbers, Type.Bool)
  private val numberOperators: Type = Type.fun(numberSets, numberSets)

  /** A polymorphic fact, at `num`. Everything concrete below starts here. */
  private def atNumbers(theorem: Kernel.Thm): Kernel.Thm =
    Kernel.instType(Map(Classical.TypeVariable -> numbers), theorem)

  /** `|- t` becomes `|- t'`, with `t'` the beta normal form of `t`. */
  private def reduced(theorem: Kernel.Thm): Kernel.Thm = {
    val equation = force(Conv.betaNormalise(theorem.conclusion))
    lift(Kernel.eqMp(equation, theorem))
  }

  /** A proof of the beta normal form of `target` becomes a proof of `target` itself. */
  private def shaped(target: Term, theorem: Kernel.Thm): Kernel.Thm = {
    val equation = force(Conv.betaNormalise(target))
    lift(Kernel.eqMp(force(Conv.sym(equation)), theorem))
  }

  private def rightOf(theorem: Kernel.Thm): Term =
    force(Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion)))

  private def impliesOf(term: Term): (Term, Term) =
    force(logic.destImp(term).toRight(NotOfForm("an implication", term)))

  private def disjunctsOf(term: Term): (Term, Term) =
    force(logic.destDisj(term).toRight(NotOfForm("a disjunction", term)))

  private def equationOf(left: Term, right: Term): Term =
    lift(Term.appAll(Term.equalityAt(Term.typeOf(left)), List(left, right)))

  private val successorOf: Term =
    lift(inductive.theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers)))

  /* --------------------------------------------------------------- what it cost */

  "The least fixed point" should "be defined rather than assumed" in {
    // Against the theory it EXTENDS, which is not a theory it NEEDS: this development needs nothing
    // but the logic, and the two orders are different questions.
    //
    // The name on the right moved once already, from `Transcendental` to `Concatenation`, when a
    // link landed between them hours after this was written. It is the same class as the `widest`
    // pin two tests down and it is kept by name anyway, because what the assertion buys is that
    // EXACTLY two constants were added, and a version quantified over "whatever is below" could not
    // say that. `Chain.construct` is where the answer lives.
    val below = chain.concatenation.theory

    inductive.theory.axioms shouldBe below.axioms
    (inductive.theory.constants.keySet -- below.constants.keySet) shouldBe
      Set(Inductive.Monotone, Inductive.Name)
    inductive.theory.definitions.keySet should contain(Inductive.Name)
    inductive.theory.definitions.keySet should contain(Inductive.Monotone)
  }

  it should "be reachable from the widest signature, which is the property rather than being it" in {
    // It WAS `Chain.widest` for the few hours between landing and `Reaching` landing on top of it,
    // and this test said so by name. That is the defect the `widest` field's own docstring is
    // about, met here rather than read: the name of the last link is not a property of this
    // development and it moved before the day was out. What does not move is that a constant
    // declared here is nameable in the widest signature, which is the whole reason the link is in
    // the chain rather than beside it.
    chain.widest.theory.constants.keySet should contain allElementsOf inductive.theory.constants.keySet
    chain.widest.theory.constants.keySet should contain(Inductive.Name)
    chain.widest.theory.constants.keySet should contain(Inductive.Monotone)
  }

  it should "carry every fact without a hypothesis left standing" in {
    // Not decoration. `Rules.mp` does not check that the antecedent it is handed is the one the
    // implication wants: a mismatch comes back `Right`, with the antecedent still on the left of
    // the turnstile. The conclusion of a derivation built through it is therefore half the check
    // and this is the other half.
    Inductive.Statements.foreach { case (name, _) =>
      withClue(s"$name: ")(fact(name).hypotheses shouldBe empty)
    }
  }

  it should "say what `Inductive.Statements` says, read as a term" in {
    Inductive.Statements.foreach { case (name, text) =>
      withClue(s"$name: ")(fact(name).conclusion shouldBe force(inductive.proposition(text)))
    }
  }

  it should "prove its induction principle without asking anything of the operator" in {
    // The claim the file's docstring turns on, read off the statement rather than off the proof:
    // the induction principle's only hypothesis is that `S` is closed, and `MONOTONE` does not
    // occur in it at all. If it ever did, every non-membership below would cost a monotonicity
    // proof and the asymmetry this development is built on would be gone.
    val monotone = lift(inductive.theory.constant(Inductive.Monotone, Type.fun(Inductive.Operators, Type.Bool)))

    Term.freeVariables(fact(Inductive.Induction).conclusion) should not contain monotone
    inductive.show(fact(Inductive.Induction).conclusion) should not include Inductive.Monotone
    inductive.show(fact(Inductive.Introduction).conclusion) should include(Inductive.Monotone)
  }

  /* ------------------------------------------------- a rule set, and both of its faces */

  /** `\S n. n = ZERO \/ ?m. S m /\ n = SUC (SUC m)` — the even numbers, as a rule set. */
  private val evenRules: Term = force(
    inductive.term("\\S:num->bool. \\n:num. n = ZERO \\/ (?m:num. S m /\\ n = SUC (SUC m))")
  )

  /** `INDUCTIVE evenRules`, the set those rules generate. */
  private val evens: Term = {
    val constant = lift(inductive.theory.constant(Inductive.Name, Type.fun(numberOperators, numberSets)))
    lift(Term.app(constant, evenRules))
  }

  private def isEven(number: Term): Term = lift(Term.app(evens, number))

  private val zero: Term = force(inductive.term("ZERO", numbers))
  private val one: Term = force(inductive.term("SUC ZERO", numbers))
  private val two: Term = force(inductive.term("SUC (SUC ZERO)", numbers))

  /**
   * `|- MONOTONE evenRules`, by hand, which is what the docstring's "it does not prove monotonicity
   * for you" costs measured rather than asserted.
   *
   * The shape is the one every rule set has: a disjunction of clauses in which the set argument
   * occurs only positively, so each clause is carried by the inclusion and reassembled. A procedure
   * recognising that shape would replace this function and does not exist.
   */
  private lazy val evenIsMonotone: Kernel.Thm = {
    val definition = atNumbers(force(inductive.definition(Inductive.Monotone)))
    val unfolded = force(Conv.unfold(definition, List(evenRules)))
    val body = rightOf(unfolded)

    val normalising = force(Conv.betaNormalise(body))
    val normal = rightOf(normalising)

    val (sets, inner) = force(Logic.stripForall(normal))
    val smaller = sets(0)
    val larger = sets(1)
    val (inclusion, everywhere) = impliesOf(inner)
    val assumedInclusion = lift(Kernel.assume(inclusion))

    val (points, clause) = force(Logic.stripForall(everywhere))
    val point = points(0)
    val (premise, target) = impliesOf(clause)
    val assumedPremise = lift(Kernel.assume(premise))

    val (isZero, hasPredecessor) = disjunctsOf(premise)
    val (targetZero, targetPredecessor) = disjunctsOf(target)

    // The base clause says nothing about the set, so it crosses unchanged.
    val base = force(rules.disjIntro1(targetPredecessor, lift(Kernel.assume(isZero))))

    // The step clause is where the inclusion is spent, once, on the one positive occurrence.
    val predicate = force(
      logic.destExistsPredicate(hasPredecessor).toRight(NotOfForm("an existential", hasPredecessor))
    )
    val targetPredicate = force(
      logic
        .destExistsPredicate(targetPredecessor)
        .toRight(NotOfForm("an existential", targetPredecessor))
    )
    val witness = Conv.freshVariable("m", numbers, Term.freeVariables(target) ++ Term.freeVariables(premise))
    // Assumed in BETA-REDUCED form, which is what `Rules.existsElim` looks for when it discharges
    // the instance: it compares against the contraction of `predicate witness`, not against the
    // application. Assuming the application instead leaves a hypothesis that is the same
    // proposition and not the same term, and the refusal names the one it wanted.
    val instance = rightOf(force(Conv.betaRoot(lift(Term.app(predicate, witness)))))
    val opened = lift(Kernel.assume(instance))
    val inSmaller = force(rules.conjElim1(opened))
    val equation = force(rules.conjElim2(opened))
    val inLarger = force(rules.spec(witness, assumedInclusion).flatMap(rules.mp(_, inSmaller)))
    val rebuilt = force(rules.conjIntro(inLarger, equation))
    val introduced = force(rules.existsIntro(targetPredicate, witness, rebuilt))
    val step = force(
      rules.existsElim(
        lift(Kernel.assume(hasPredecessor)),
        witness,
        force(rules.disjIntro2(targetZero, introduced))
      )
    )

    val split = force(rules.disjElim(assumedPremise, base, step))
    val proved = force(
      rules
        .disch(premise, split)
        .flatMap(rules.gen(point, _))
        .flatMap(rules.disch(inclusion, _))
        .flatMap(rules.gen(larger, _))
        .flatMap(rules.gen(smaller, _))
    )

    lift(Kernel.eqMp(force(Conv.sym(unfolded)), shaped(body, proved)))
  }

  "The rules of the even numbers" should "be monotone, proved rather than assumed" in {
    evenIsMonotone.hypotheses shouldBe empty
  }

  it should "admit `SUC (SUC ZERO)` through the introduction rules" in {
    // The clause at `x` is `evenRules (INDUCTIVE evenRules) x`, which beta-reduces to the
    // disjunction the rule set was written as. So a membership is: pick a disjunct, supply what it
    // asks for, fold back.
    val introduction =
      force(rules.spec(evenRules, atNumbers(fact(Inductive.Introduction))).flatMap(rules.mp(_, evenIsMonotone)))

    def admit(number: Term, witnessing: Term => Kernel.Thm): Kernel.Thm = {
      val clause = force(rules.spec(number, introduction))
      val (premise, _) = impliesOf(clause.conclusion)
      force(rules.mp(clause, shaped(premise, witnessing(rightOf(force(Conv.betaNormalise(premise)))))))
    }

    // `ZERO`, by the base clause: `ZERO = ZERO`.
    val evenZero = admit(
      zero,
      normal => {
        val (isZero, hasPredecessor) = disjunctsOf(normal)
        force(rules.disjIntro1(hasPredecessor, Conv.refl(zero)))
      }
    )
    evenZero.hypotheses shouldBe empty
    evenZero.conclusion shouldBe isEven(zero)

    // `SUC (SUC ZERO)`, by the step clause at the witness `ZERO`, which is where the first one is
    // spent. A development that could prove only the base would pass every non-membership below and
    // would be saying nothing.
    val evenTwo = admit(
      two,
      normal => {
        val (isZero, hasPredecessor) = disjunctsOf(normal)
        val predicate = force(
          logic.destExistsPredicate(hasPredecessor).toRight(NotOfForm("an existential", hasPredecessor))
        )
        val pair = force(rules.conjIntro(evenZero, Conv.refl(two)))
        force(rules.disjIntro2(isZero, force(rules.existsIntro(predicate, zero, pair))))
      }
    )
    evenTwo.hypotheses shouldBe empty
    evenTwo.conclusion shouldBe isEven(two)
  }

  it should "refuse `SUC ZERO`, which is the half a forward closure cannot reach" in {
    // The induction principle at the set of numbers that are not one. It is closed under the rules
    // — `ZERO` is not one, and `SUC (SUC m)` is not one whatever `m` is — so it contains the whole
    // closure, so the closure does not contain one.
    //
    // No monotonicity anywhere in this derivation, which is the asymmetry the file claims: the
    // half that decides a non-membership is the half that asks nothing of the operator.
    val notOne = force(inductive.term("\\n:num. ~(n = SUC ZERO)", numberSets))

    val induction = force(rules.specAll(atNumbers(fact(Inductive.Induction)), List(evenRules, notOne)))
    val (closure, _) = impliesOf(induction.conclusion)
    val closureNormal = rightOf(force(Conv.betaNormalise(closure)))

    val (points, clause) = force(Logic.stripForall(closureNormal))
    val point = points(0)
    val (premise, target) = impliesOf(clause)
    val (isZero, hasPredecessor) = disjunctsOf(premise)
    val negated = force(logic.destNot(target).toRight(NotOfForm("a negation", target)))

    val successorNotZero = force(chain.naturals.fact(Natural.SuccessorNotZero))
    val successorInjective = force(chain.naturals.fact(Natural.SuccessorInjective))

    // Base: `n = ZERO` and `n = SUC ZERO` would make `SUC ZERO = ZERO`.
    val base = {
      val assumedOne = lift(Kernel.assume(negated))
      val assumedZero = lift(Kernel.assume(isZero))
      val collapsed = force(Conv.sym(assumedOne).flatMap(Conv.trans(_, assumedZero)))
      val refusal = force(rules.spec(zero, successorNotZero))
      force(rules.notElim(refusal, collapsed).flatMap(rules.notIntro(negated, _)))
    }

    // Step: `n = SUC (SUC m)` and `n = SUC ZERO` would make `SUC m = ZERO` by injectivity.
    val step = {
      val predicate = force(
        logic.destExistsPredicate(hasPredecessor).toRight(NotOfForm("an existential", hasPredecessor))
      )
      val witness = Conv.freshVariable("m", numbers, Term.freeVariables(clause))
      // Beta-reduced, for the reason the monotonicity proof above gives.
      val instance = rightOf(force(Conv.betaRoot(lift(Term.app(predicate, witness)))))
      val opened = lift(Kernel.assume(instance))
      val equation = force(rules.conjElim2(opened))

      val assumedOne = lift(Kernel.assume(negated))
      val collapsed = force(Conv.sym(equation).flatMap(Conv.trans(_, assumedOne)))
      // By the instance and not by position. `NUM_SUC_INJECTIVE` is `!m n. SUC m = SUC n ==> m = n`
      // and both binders are `num`, so a swapped positional call comes back a theorem — the true
      // one about the other instance — and the type checker cannot see it.
      val wanted = force(
        logic.mkImp(collapsed.conclusion, equationOf(lift(Term.app(successorOf, witness)), zero))
      )
      val cancelled = force(rules.specTo(successorInjective, wanted).flatMap(rules.mp(_, collapsed)))
      val refusal = force(rules.spec(witness, successorNotZero))
      val refused = force(rules.notElim(refusal, cancelled).flatMap(rules.notIntro(negated, _)))
      force(rules.existsElim(lift(Kernel.assume(hasPredecessor)), witness, refused))
    }

    val split = force(rules.disjElim(lift(Kernel.assume(premise)), base, step))
    val closed = force(
      rules.disch(premise, split).flatMap(rules.gen(point, _))
    )
    val everywhere = force(rules.mp(induction, shaped(closure, closed)))

    val assumedMember = lift(Kernel.assume(isEven(one)))
    val notItself = reduced(force(rules.spec(one, everywhere).flatMap(rules.mp(_, assumedMember))))
    val contradiction = force(rules.notElim(notItself, Conv.refl(one)))
    val refusal = force(rules.notIntro(isEven(one), contradiction))

    refusal.hypotheses shouldBe empty
    refusal.conclusion shouldBe force(logic.mkNot(isEven(one)))
  }
}
