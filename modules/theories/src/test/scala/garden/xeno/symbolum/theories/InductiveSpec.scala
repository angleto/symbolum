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

  /** `MONOTONE operator`, the proposition, at `num`. */
  private def monotoneOf(operator: Term): Term = {
    val constant =
      lift(inductive.theory.constant(Inductive.Monotone, Type.fun(numberOperators, Type.Bool)))
    lift(Term.app(constant, operator))
  }

  private val zero: Term = force(inductive.term("ZERO", numbers))
  private val one: Term = force(inductive.term("SUC ZERO", numbers))
  private val two: Term = force(inductive.term("SUC (SUC ZERO)", numbers))

  /**
   * `|- MONOTONE evenRules`, from [[Monotone.prove]] rather than by hand.
   *
   * This was 52 lines of derivation until 2026-09-16, and those lines are half the measurement
   * `Monotone`'s docstring quotes. The walk they performed is the walk every rule set needs, so it
   * belongs to a procedure and not to each caller; what is worth asserting here is what comes back,
   * which the test below does by conclusion as well as by hypothesis count.
   */
  private lazy val evenIsMonotone: Kernel.Thm = force(Monotone.prove(logic, inductive, evenRules))

  "The rules of the even numbers" should "be monotone, proved rather than assumed" in {
    // The conclusion as well as the hypotheses, which the hand proof did not need to assert and a
    // procedure does: a walk that went astray cannot produce a theorem about something else here,
    // because the last step folds it back across `MONOTONE`'s definition, but the assertion that
    // says so belongs at the caller rather than in the procedure's own docstring.
    evenIsMonotone.hypotheses shouldBe empty
    evenIsMonotone.conclusion shouldBe monotoneOf(evenRules)
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

  /* ---------------------------------------- the procedure, and what it refuses */

  /**
   * `\S n. !m. m < n ==> S m`, the shape neither consumer of [[Monotone.prove]] exercises.
   *
   * The even numbers and `Reaching`'s derivations are both disjunctions of existentials, so between
   * them they walk the positive shapes `Monotone` lists except the universal and the implication,
   * which they leave untouched. This is a real rule set rather than a shape invented for the test
   * (it is the one a well-founded definition is written in, "in the set if everything below it
   * is"), and it is the only place the positive side of an implication is carried.
   */
  private val belowRules: Term =
    force(inductive.term("\\S:num->bool. \\n:num. !m:num. m < n ==> S m", numberOperators))

  /** `\S n. ~(S n)`, the operator the refusal exists for. */
  private val negationRules: Term =
    force(inductive.term("\\S:num->bool. \\n:num. ~(S n)", numberOperators))

  /** `\S n. S n ==> n = ZERO`, negative for the other of the two reasons. */
  private val antecedentRules: Term =
    force(inductive.term("\\S:num->bool. \\n:num. S n ==> n = ZERO", numberOperators))

  "The monotonicity procedure" should "carry a set argument under a universal and to the right of an implication" in {
    val proved = force(Monotone.prove(logic, inductive, belowRules))

    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe monotoneOf(belowRules)
  }

  it should "refuse an operator whose set argument is under a negation, naming the subterm" in {
    // The subterm and not the operator, because that is what a caller has to go and change. The set
    // variable's own name is not asserted: it comes from stripping `MONOTONE`'s binders and is
    // freshened, so pinning it would be pinning the printer rather than the refusal.
    val refusal = Monotone.prove(logic, inductive, negationRules)

    refusal.isLeft shouldBe true
    refusal.left.toOption.get match {
      case NotOfForm(expected, found) =>
        expected should include("only positively")
        withClue(s"the refusal should name the negation itself, and named $found: ") {
          logic.destNot(found) should not be empty
        }
      case other => fail(s"expected a refusal about the shape, got ${other.message}")
    }

    // `Unread` and emphatically not `Decided`: nothing here searched anything, and the next test is
    // what says the two are different questions even where the answers agree.
    refusal.left.toOption.get.standing shouldBe LogicError.Standing.Unread
    LogicError.decided(refusal) shouldBe false
  }

  it should "be right to refuse that one: its monotonicity is false, and derivably so" in {
    // The half that makes the refusal worth having. A procedure that refuses everything it does not
    // recognise is doing its job whether or not the operator was monotone, so what has to be shown
    // once is an operator it refuses that is genuinely NOT monotone. This is that operator, and the
    // derivation is short because `INDUCTIVE_FIXPOINT` does the work: `MONOTONE` of it would give
    // `INDUCTIVE f 0 = ~(INDUCTIVE f 0)`, and a proposition equal to its own negation is falsity.
    //
    // It is not a claim that every refusal is of a non-monotone operator, and cannot be: two
    // negations is monotone and is refused, which `Monotone`'s own docstring says. It is a claim
    // that this one is not conservatism.
    val monotone = monotoneOf(negationRules)
    val assumed = lift(Kernel.assume(monotone))

    val fixpoint = force(
      rules.spec(negationRules, atNumbers(fact(Inductive.Fixpoint))).flatMap(rules.mp(_, assumed))
    )
    val equation = reduced(force(rules.spec(zero, fixpoint)))
    val proposition = force(
      Term.destEq(equation.conclusion).map(_._1).toRight(NotOfForm("an equation", equation.conclusion))
    )

    // `p = ~p` twice: once to refuse `p`, and once to prove it from that refusal.
    val assumedProposition = lift(Kernel.assume(proposition))
    val refuted = force(
      rules
        .notElim(lift(Kernel.eqMp(equation, assumedProposition)), assumedProposition)
        .flatMap(rules.notIntro(proposition, _))
    )
    val held = lift(Kernel.eqMp(force(Conv.sym(equation)), refuted))
    val falsity = force(rules.notElim(refuted, held))
    val refusal = force(rules.notIntro(monotone, falsity))

    refusal.hypotheses shouldBe empty
    refusal.conclusion shouldBe force(logic.mkNot(monotone))
  }

  it should "refuse an operator whose set argument is an antecedent, naming that antecedent" in {
    // The second of the two negative positions, and it arrives by a different route: the negation
    // above is a shape no handler reads, this one is a shape that IS read and whose left-hand side
    // is checked. Keeping both means the check is not resting on the negation happening to be
    // unreadable.
    val refusal = Monotone.prove(logic, inductive, antecedentRules)

    refusal.isLeft shouldBe true
    refusal.left.toOption.get match {
      case NotOfForm(expected, found) =>
        expected should include("only positively")
        withClue(s"the refusal should name the antecedent, and named $found: ") {
          logic.destImp(found) shouldBe empty
          logic.destNot(found) shouldBe empty
        }
      case other => fail(s"expected a refusal about the shape, got ${other.message}")
    }
  }

  it should "refuse a term that is not an operator over sets at all" in {
    // A different question from the two above and it is worth keeping them apart: those are
    // operators written in a shape this cannot walk, this is not an operator. A caller that hands
    // over a set where an operator was wanted gets told which, rather than a refusal about
    // positivity that would send it looking at the wrong thing.
    val set = force(inductive.term("\\n:num. n = ZERO", numberSets))
    val refusal = Monotone.prove(logic, inductive, set)

    refusal.isLeft shouldBe true
    refusal.left.toOption.get.message should include("('a -> bool) -> 'a -> bool")
  }

}
