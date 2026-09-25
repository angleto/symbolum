package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * The definitions and the rules derived from them.
 *
 * The first assertion is the one the whole layer rests on: after defining eight connectives the
 * theory still has no axioms. Everything below it is a derivation, so if that stays true then
 * nothing here can have made the system able to prove more than the kernel could.
 */
class LogicSpec extends AnyFlatSpec with Matchers {


  /**
   * Abstraction, forced.
   *
   * `Term.abs` refuses a body that is not locally closed, since 2026-09-10, so it returns a
   * refusal like `app` and `eq` do. Every body below is built out of variables and constants a
   * line or two above and none of them can be open, so forcing here is reading the signature and
   * not ignoring it. A test that meant to hand it an open body says so by calling `Term.abs`
   * directly and looking at the `Left`.
   */
  private def lam(variable: FVar, body: Term): Term =
    Term.abs(variable, body).fold(error => fail(s"unexpected refusal: $error"), identity)

  private val logic = Logic.standard
  private val rules = logic.rules

  private val p = Term.variable("p", Type.Bool)
  private val q = Term.variable("q", Type.Bool)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  "The standard theory" should "build" in {
    Logic.construct() should matchPattern { case Right(_) => }
  }

  it should "assert nothing" in {
    logic.theory.axioms shouldBe empty
  }

  it should "define every connective and leave nothing undefined but equality" in {
    logic.theory.definitions.keySet shouldBe Set(
      Logic.Truth, Logic.Falsity, Logic.Conjunction, Logic.Disjunction,
      Logic.Implication, Logic.Negation, Logic.Universal, Logic.Existential
    )
    logic.theory.undefinedConstants shouldBe Set(Term.EqualityName)
  }

  "Truth" should "be provable with no hypotheses" in {
    val theorem = force(rules.truth)

    theorem.conclusion shouldBe logic.truth
    theorem.hypotheses shouldBe empty
  }

  "Equality with truth" should "be introduced and eliminated back to the same theorem" in {
    val assumed = force(Kernel.assume(p))
    val asEquation = force(rules.eqTruthIntro(assumed))
    val back = force(rules.eqTruthElim(asEquation))

    Term.destEq(asEquation.conclusion).map(_._2) shouldBe Some(logic.truth)
    back.conclusion shouldBe p
  }

  it should "be introduced when a hypothesis mentions a function of two propositions" in {
    // The rule abstracts over a function variable `f`, and the first version did so on the
    // caller's theorems, choosing `f` to avoid only the two conclusions; a hypothesis mentioning
    // `f : bool -> bool -> bool` then made the kernel's abstraction rule refuse. An audit probe
    // found it. The abstraction now happens once, over the schema's variables, and this test is
    // what keeps that arrangement from regressing.
    val selectorType = Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool))
    val f = Term.variable("f", selectorType)
    val truth = force(rules.truth).conclusion
    val hypothesis = force(Term.appAll(f, List(truth, truth)))

    val assumed = force(Kernel.assume(hypothesis))
    val theorem = force(rules.conjIntro(assumed, assumed))

    theorem.conclusion shouldBe force(logic.mkConj(hypothesis, hypothesis))
    theorem.hypotheses shouldBe List(hypothesis)
  }

  "Conjunction" should "be introduced from both sides" in {
    val theorem = force(rules.conjIntro(force(Kernel.assume(p)), force(Kernel.assume(q))))

    theorem.conclusion shouldBe force(logic.mkConj(p, q))
    theorem.hypotheses shouldBe List(p, q).sorted(using Term.ordering)
  }

  it should "give back its left side" in {
    val conjunction = force(logic.mkConj(p, q))
    val theorem = force(rules.conjElim1(force(Kernel.assume(conjunction))))

    theorem.conclusion shouldBe p
    theorem.hypotheses shouldBe List(conjunction)
  }

  it should "give back its right side" in {
    val conjunction = force(logic.mkConj(p, q))
    val theorem = force(rules.conjElim2(force(Kernel.assume(conjunction))))

    theorem.conclusion shouldBe q
  }

  it should "refuse to be taken apart when it is not a conjunction" in {
    rules.conjElim1(force(Kernel.assume(p))).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
  }

  "Implication" should "discharge its antecedent" in {
    val theorem = force(rules.disch(p, force(Kernel.assume(q))))

    theorem.conclusion shouldBe force(logic.mkImp(p, q))
    theorem.hypotheses shouldBe List(q)
  }

  it should "discharge an antecedent that was a hypothesis" in {
    val theorem = force(rules.disch(p, force(Kernel.assume(p))))

    theorem.conclusion shouldBe force(logic.mkImp(p, p))
    theorem.hypotheses shouldBe empty
  }

  it should "detach its consequent" in {
    val implication = force(rules.disch(p, force(Kernel.assume(q))))
    val theorem = force(rules.mp(implication, force(Kernel.assume(p))))

    theorem.conclusion shouldBe q
  }

  it should "carry an unmatched antecedent rather than refusing it" in {
    // The property a caller must not mistake, asserted so that nobody argues from the opposite.
    // Modus ponens here does not compare the premise's conclusion with the antecedent: a theorem of
    // something else leaves `p` undischarged, and what comes back is a `Right` whose conclusion is
    // the one that was wanted. Sound, because the result says it assumes `p`; not a check.
    // **This asserted the opposite until 2026-09-16 and the reversal is what it is here to pin.**
    // `mp` used to accept an antecedent proving something else: it went through `proveHyp`, which
    // is a cut and leaves what it cannot discharge standing, so the answer was `Right`, its
    // conclusion was `q`, and the undischarged antecedent travelled on the left of the turnstile
    // beside the wrong premise's own baggage. Sound, and not a refusal, and nothing looked.
    val truth = force(rules.truth)
    val implication = force(rules.disch(truth.conclusion, force(Kernel.assume(q))))
    val unrelated = force(Kernel.assume(Term.variable("r", Type.Bool)))

    rules.mp(implication, unrelated).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])

    // The refusal has to name what it was handed, or this test passes against a rule that refuses
    // everything. That is the half the old assertion had and the shape of the new one must keep:
    // "it refused" and "it refused about the right thing" are two outcomes.
    rules.mp(implication, unrelated).fold(_.message, _ => "") should include("r")

    // And the matching case still detaches, discharging the antecedent rather than carrying it.
    // Without this the refusal above is consistent with `mp` having stopped working altogether.
    val detached = force(rules.mp(implication, truth))
    detached.conclusion shouldBe q
    detached.hypotheses should not contain truth.conclusion
  }

  it should "refuse to detach from something that is not an implication" in {
    rules.mp(force(Kernel.assume(p)), force(Kernel.assume(p))).left.map(_.getClass) shouldBe
      Left(classOf[NotOfForm])
  }

  it should "reconcile a beta difference that is not at the root, which nothing else reaches" in {
    // `mp` reconciles an antecedent that differs from the implication's by beta, and it does it in
    // two ways: a redex at the root, which is three kernel steps, and anything else, which
    // normalises both sides. The first is what the repository's two real callers have, both of them
    // the choice axiom at an unreduced `P w`. **The second had no caller at all**: measured on
    // 2026-09-16 over every test source, nothing named `provingExactly` and nothing built a shape
    // that reaches it, so the branch was covered by construction and by nothing else.
    //
    // This is that shape. The antecedent wanted is a conjunction whose LEFT side is a redex, so the
    // whole term is an application of the conjunction and `Term.betaReduce` at the root answers
    // nothing; what settles it is normalising both sides. A caller meeting this in the wild is one
    // whose lemma carried a lambda inside a compound, which is the ordinary way a redex survives a
    // specialisation that did not reduce.
    val identity = lam(Term.variable("x", Type.Bool), Term.variable("x", Type.Bool))
    val unreduced = force(logic.mkConj(force(Term.app(identity, p)), q))
    val reduced = force(logic.mkConj(p, q))

    // The premise of the test rather than its subject: if these two were equal, or if the root
    // reduction settled it, the branch under test would not be entered and the assertions below
    // would pass against the wrong code path.
    unreduced should not be reduced
    Term.betaReduce(unreduced) should not be Some(reduced)

    val implication = force(rules.disch(unreduced, force(Kernel.assume(q))))
    val detached = force(rules.mp(implication, force(Kernel.assume(reduced))))

    detached.conclusion shouldBe q

    // Converted and not merely accepted, which is the distinction the rule's own documentation
    // draws: a check that agreed the terms match would leave the cut unable to discharge one form
    // against the other, and the implication's OWN antecedent would travel on in the hypotheses.
    // That is the discriminating assertion and it is this one.
    detached.hypotheses should not contain unreduced

    // And the other form must be there, which this asserted the opposite of at first. The
    // antecedent handed over is `p /\ q |- p /\ q`, so its own assumption travels with it exactly
    // as `G, D |- q` says it should; a rule that discharged that too would be discharging something
    // nobody proved. The failure read as the conversion not happening and was the assertion being
    // wrong about the contract.
    detached.hypotheses should contain(reduced)

    // And it still refuses where normalisation does not reconcile, so what is being exercised is
    // the branch rather than a rule that stopped looking.
    val different = force(logic.mkConj(q, p))
    rules.mp(implication, force(Kernel.assume(different))).left.map(_.getClass) shouldBe
      Left(classOf[NotOfForm])
  }

  "Negation" should "follow from a contradiction" in {
    val theorem = force(rules.notIntro(logic.falsity, force(Kernel.assume(logic.falsity))))

    theorem.conclusion shouldBe force(logic.mkNot(logic.falsity))
    theorem.hypotheses shouldBe empty
  }

  it should "give falsity when the proposition it denies is proved" in {
    val negated = force(logic.mkNot(p))
    val theorem = force(rules.notElim(force(Kernel.assume(negated)), force(Kernel.assume(p))))

    theorem.conclusion shouldBe logic.falsity
    theorem.hypotheses should contain(negated)
    theorem.hypotheses should contain(p)
  }

  "The universal quantifier" should "generalise a theorem over a variable" in {
    val x = Term.variable("x", TyVar("A"))
    val theorem = force(rules.gen(x, Kernel.refl(x)))

    theorem.conclusion shouldBe force(logic.mkForall(x, force(Term.eq(x, x))))
  }

  it should "refuse a variable that is free in the hypotheses" in {
    val assumed = force(Kernel.assume(p))

    rules.gen(p, assumed).left.map(_.getClass) shouldBe Left(classOf[FromKernel])
  }

  it should "specialise to any term of the right type" in {
    val x = Term.variable("x", TyVar("A"))
    val y = Term.variable("y", TyVar("A"))
    val general = force(rules.gen(x, Kernel.refl(x)))
    val theorem = force(rules.spec(y, general))

    theorem.conclusion shouldBe force(Term.eq(y, y))
  }

  it should "refuse to specialise something that is not quantified" in {
    rules.spec(p, force(Kernel.assume(p))).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
  }

  /**
   * `|- !x y z. x = x`, which is enough for the three assertions below.
   *
   * What they are about is the shape of the call and not anything the statement says, so the
   * statement is the smallest one with three quantifiers in front of it.
   */
  private lazy val threeDeep: Kernel.Thm = {
    val x = Term.variable("x", TyVar("A"))
    val y = Term.variable("y", TyVar("A"))
    val z = Term.variable("z", TyVar("A"))

    force(rules.genAll(Kernel.refl(x), List(x, y, z)))
  }

  "Specialising at fewer arguments than quantifiers" should "be refused, naming both numbers" in {
    // Until 2026-09-12 this was a partial instance rather than an error, and the theorem it gave
    // went on to fail somewhere else: a session reached `NUM_DIVISION_UNIQUE` holding
    // `NUM_DIV_MOD_UNIQUE`'s arguments, one fewer than it has variables, and read the first
    // symptom at an unrelated `mp` with a message about an implication. Both numbers are in the
    // refusal because the useful reading of them is together: three against two usually means a
    // caller reached a different lemma from the one it meant to.
    rules.specAll(threeDeep, List(Term.variable("a", TyVar("A")))) match {
      case Left(PartialInstance(quantifiers, arguments, _)) =>
        quantifiers shouldBe 3
        arguments shouldBe 1

      case other => fail(s"expected a partial instance to be refused, got $other")
    }
  }

  it should "still be reachable under a name that says so" in {
    // The call in `SeriesSpec` that wants a partial instance is the measurement that kept the
    // operation. What it must not be is something a caller arrives at by accident.
    val partial = force(rules.specPrefix(threeDeep, List(Term.variable("a", TyVar("A")))))

    Logic.stripForall(partial.conclusion).map(_._1.length) shouldBe Right(2)
  }

  it should "leave a list that is neither short nor long alone" in {
    val x = Term.variable("x", TyVar("A"))

    force(rules.specAll(threeDeep, List(x, x, x))).conclusion shouldBe force(Term.eq(x, x))
  }

  /* ------------------------------------ specialising by what is wanted rather than by position */

  private val alpha: Type = TyVar("A")
  private val pairing: FVar =
    Term.variable("f", Type.fun(alpha, Type.fun(alpha, alpha)))
  private val a: FVar = Term.variable("a", alpha)
  private val b: FVar = Term.variable("b", alpha)

  /** `f x y`, which is the smallest body that tells two same-typed binders apart. */
  private def applied(first: Term, second: Term): Term =
    force(Term.appAll(pairing, List(first, second)))

  /**
   * The same statement, quantified in the two possible orders.
   *
   * This is the incident of 2026-09-13 in miniature. One derivation was rewritten for an unrelated
   * reason and the lemma it produces came out quantified the other way round; a consumer
   * specialising by position was reading the first and got the second.
   */
  private lazy val firstThenSecond: Kernel.Thm = {
    val x = Term.variable("x", alpha)
    val y = Term.variable("y", alpha)
    force(rules.genAll(Kernel.refl(applied(x, y)), List(x, y)))
  }

  private lazy val secondThenFirst: Kernel.Thm = {
    val x = Term.variable("x", alpha)
    val y = Term.variable("y", alpha)
    force(rules.genAll(Kernel.refl(applied(x, y)), List(y, x)))
  }

  "Two leading quantifiers over one type" should "make a reversal invisible to positional specialisation" in {
    // The premise of the demonstration below, asserted rather than assumed: if the two binders had
    // different types the reversal would be a type error and there would be nothing to show. On
    // 2026-09-13 that is exactly why the consumer's build stopped instead of shipping a wrong
    // theorem, and on that day 142 of the library's 260 lemmas did not have that luck.
    val left = force(Logic.stripForall(firstThenSecond.conclusion))._1
    val right = force(Logic.stripForall(secondThenFirst.conclusion))._1

    left.map(_.ty) shouldBe right.map(_.ty)
    left.map(_.ty).distinct.length shouldBe 1
  }

  it should "give a different theorem from each, with neither refusing" in {
    // The silence is the defect. Both calls succeed, both results are theorems, and they are not
    // the same theorem: a caller that wrote the arguments for one of these two lemmas and is
    // handed the other learns nothing at the call site.
    val fromFirst = force(rules.specAll(firstThenSecond, List(a, b)))
    val fromSecond = force(rules.specAll(secondThenFirst, List(a, b)))

    fromFirst.conclusion shouldBe force(Term.eq(applied(a, b), applied(a, b)))
    fromSecond.conclusion shouldBe force(Term.eq(applied(b, a), applied(b, a)))
    fromFirst.conclusion should not be fromSecond.conclusion
  }

  it should "give one answer to specTo, because the order is nowhere in the call" in {
    // The same pair of lemmas and the same caller, asking for what it wants instead of for a
    // position. The two agree, which is the property the positional call does not have.
    val wanted = force(Term.eq(applied(a, b), applied(a, b)))

    force(rules.specTo(firstThenSecond, wanted)).conclusion shouldBe wanted
    force(rules.specTo(secondThenFirst, wanted)).conclusion shouldBe wanted
  }

  "specTo" should "refuse a target no instantiation reaches" in {
    val unreachable = force(Term.eq(a, b))

    rules.specTo(firstThenSecond, unreachable) should matchPattern {
      case Left(NotOfForm(_, _)) =>
    }
  }

  /**
   * `!P. a = a ==> !x. P x ==> P (s x)`, a principle whose predicate recurs applied to something
   * that is not a binder.
   *
   * The inner quantifier sits behind an implication so that `specTo` does not strip it with `P`: it
   * has to stay a binder, since a variable applied to a non-binder is only the fragment's question
   * when a binder is in scope.
   */
  private lazy val stepPrinciple: Kernel.Thm = force(
    Kernel.assume(
      force(
        logic.mkForall(
          stepPredicate,
          behindGuard(
            force(
              logic.mkImp(
                force(Term.app(stepPredicate, stepVariable)),
                force(Term.app(stepPredicate, force(Term.app(stepFunction, stepVariable))))
              )
            )
          )
        )
      )
    )
  )

  private lazy val stepPredicate = Term.variable("P", Type.fun(alpha, Type.Bool))
  private lazy val stepFunction = Term.variable("s", Type.fun(alpha, alpha))
  private lazy val stepVariable = Term.variable("x", alpha)

  private def behindGuard(body: Term): Term =
    force(logic.mkImp(force(Term.eq(a, a)), force(logic.mkForall(stepVariable, body))))

  "specToReduced" should "specialise a principle whose predicate recurs applied to a non-binder" in {
    // `a = a ==> !x. x = a ==> s x = a` is an instance at `P := \x. x = a`. The matcher decides
    // `P` from its first occurrence, and since 2026-09-25 checks the second against what it
    // decided instead of refusing it. Until then this came back as a refusal, first as
    // `NotOfForm("an instance of ...")` and for part of that day as `BeyondMatching`, and neither
    // was true of a target that is an instance.
    val instance = behindGuard(
      force(
        logic.mkImp(
          force(Term.eq(stepVariable, a)),
          force(Term.eq(force(Term.app(stepFunction, stepVariable)), a))
        )
      )
    )

    // `specToReduced` and not `specTo`: `P` is decided as a lambda, so the instance `spec` leaves
    // carries `(\y. y = a) x`, and the term a reader writes is the reduced one. `specTo` refuses
    // that comparison, which is the distinction the pair exists for and not this change's concern.
    force(rules.specToReduced(stepPrinciple, instance)).conclusion shouldBe instance
  }

  "specTo" should "say the fragment was left, and not that the target is no instance, where the matcher cannot decide it" in {
    // `!P. a = a ==> !x. P (s x)` against `a = a ==> !x. s x = a`, which IS an instance at
    // `P := \y. y = a`. Here `P` has no earlier occurrence to be decided by, so this is the
    // fragment's question: a variable applied to a term that is not a binder, which has several
    // answers in general. `NotOfForm("an instance of ...")` would say the opposite of what is
    // true; the refusal names the variable instead, which is what the caller has to supply.
    val principle = force(
      Kernel.assume(
        force(
          logic.mkForall(
            stepPredicate,
            behindGuard(force(Term.app(stepPredicate, force(Term.app(stepFunction, stepVariable)))))
          )
        )
      )
    )
    val instance = behindGuard(force(Term.eq(force(Term.app(stepFunction, stepVariable)), a)))

    // Named by type and not by name, as the open quantifier is named in the test below: `specTo`
    // opens the lemma's quantifiers with names coined from their position, so the variable the
    // refusal carries is the lemma's first quantifier as the lemma prints, not the `P` built here.
    rules.specTo(principle, instance) match {
      case Left(BeyondMatching(_, _, Matching.Refusal.ArgumentIsNotABinder(variable))) =>
        variable.ty shouldBe stepPredicate.ty
      case other => fail(s"expected the fragment's refusal naming the predicate, got $other")
    }
  }

  it should "refuse a target that leaves a quantifier open, naming it" in {
    // A quantifier the body does not mention: every value gives the target, so there is no answer
    // rather than several. Picking one would be the silent choice this whole method exists to
    // refuse, and it is the one branch of it that no lemma in the library reaches, which is why
    // the case is built here by hand.
    val x = Term.variable("x", alpha)
    val vacuous = force(rules.gen(x, Kernel.refl(p)))

    rules.specTo(vacuous, force(Term.eq(p, p))) match {
      case Left(Undetermined(variable)) => variable.ty shouldBe alpha
      case other => fail(s"expected the open quantifier to be named, got $other")
    }
  }

  it should "carry the hypotheses of the theorem it specialised" in {
    // Not obvious from the implementation, which reads `theorem.conclusion` and compares the
    // result's conclusion against the target: nothing in either of those mentions a hypothesis, so
    // a reader cannot tell from the shape whether one survives. It does, because `spec` carries it,
    // and a theorem that quietly lost what it rests on would be the worst failure this method
    // could have.
    val assumed = force(Kernel.assume(p))
    val over = Term.variable("x", alpha)
    val paired = force(rules.conjIntro(assumed, Kernel.refl(over)))
    val quantified = force(rules.gen(over, paired))
    val wanted = force(logic.mkConj(p, force(Term.eq(a, a))))

    val instance = force(rules.specTo(quantified, wanted))

    instance.conclusion shouldBe wanted
    instance.hypotheses shouldBe quantified.hypotheses
    instance.hypotheses shouldBe List(p)
  }

  it should "give the target and not something else, even where two instantiations reach it" in {
    // The guard at the end, pointed at the one input that could make the matcher's choice visible:
    // a target in which both quantifiers must become the same term. Whichever assignment the match
    // returns, what comes back has to be the term that was written, and this is what says so.
    val over = Term.variable("x", alpha)
    val also = Term.variable("y", alpha)
    val lemma = force(rules.genAll(Kernel.refl(applied(over, also)), List(over, also)))
    val wanted = force(Term.eq(applied(a, a), applied(a, a)))

    force(rules.specTo(lemma, wanted)).conclusion shouldBe wanted
  }

  it should "decide the type variables too, from the target and nothing else" in {
    // A lemma stated over a type variable, of which this repository has several: everything about
    // `prod` and about `word` is. The target is at `bool`, so the match has to decide `A := bool`
    // before the quantifier can be specialised at all, since `spec` would otherwise be applying a
    // predicate over `A` to a term of another type. Nothing here comes from the caller: the type
    // is read off the target, which is the argument `Matching.Instantiation.instance` makes for
    // the same step being sound.
    val over = Term.variable("x", alpha)
    val polymorphic = force(rules.gen(over, Kernel.refl(over)))
    val wanted = force(Term.eq(p, p))

    force(rules.specTo(polymorphic, wanted)).conclusion shouldBe wanted
  }

  it should "refuse a theorem with no quantifier at all" in {
    rules.specTo(Kernel.refl(p), force(Term.eq(p, p))) should matchPattern {
      case Left(NotOfForm(_, _)) =>
    }
  }

  /* ------------------------------------------------ the instance, and the instance reduced */

  private val transform: FVar = Term.variable("f", Type.fun(alpha, alpha))
  private val named: FVar = Term.variable("h", Type.fun(alpha, alpha))
  private val collect: FVar = Term.variable("s", Type.fun(Type.fun(alpha, alpha), alpha))

  /**
   * `|- !f. s (\i. f i) = s (\i. f i)`, which is the consumer's shape with nothing else in it.
   *
   * A function applied to a bound variable under a binder the lemma owns, which is what `Sum` does
   * to a summand and is what makes the instance carry a redex when the caller's argument is a
   * lambda. Nothing else about `SUM_LINEAR` matters to the two operations below, so nothing else
   * is here.
   */
  private lazy val overSummand: Kernel.Thm = {
    val i = Term.variable("i", alpha)
    val body = force(Term.app(collect, lam(i, force(Term.app(transform, i)))))
    force(rules.gen(transform, Kernel.refl(body)))
  }

  /**
   * The summand a caller supplies, and the two forms the instance then has.
   *
   * Not `\y. h y`, and the difference is the whole reason this pair exists rather than one
   * operation. Both leave a redex in the instance; what differs is what the MATCH finds. Against
   * the reduced form of the first, it comes back with `f := h`, so `specTo` specialises at a name,
   * nothing is left to contract, and it reaches the target with no second operation involved. A
   * summand whose body is not an application of something to the index gives `f := \y. f2 y y`,
   * the instance keeps `(\y. f2 y y) i` under the binder, and the reduced form is out of
   * `specTo`'s reach. That is the shape `SUM_LINEAR` meets at a consumer, where the summand is
   * `\j. h j + 1`.
   *
   * The first version of this test used the eta case and passed for the wrong reason. The
   * assertion below is what refuses that now, and it is a different statement from the one that
   * was written there before measuring: the eta case is not free of redexes, it is free of the
   * ambiguity.
   */
  private lazy val supplied: Term = {
    val y = Term.variable("y", alpha)
    lam(y, applied(y, y))
  }

  private lazy val asSpecialised: Term = force(rules.specAll(overSummand, List(supplied))).conclusion

  private lazy val asReduced: Term = {
    val i = Term.variable("i", alpha)
    val body = force(Term.app(collect, lam(i, applied(i, i))))
    force(Term.eq(body, body))
  }

  "An instance whose argument is a lambda" should "not be the term a reader compares" in {
    // The premise of the pair, asserted rather than assumed: if `spec` reduced what it substituted
    // there would be one operation and not two, and this assertion is what would say so.
    asSpecialised should not be asReduced
    force(Conv.betaNormalise(asSpecialised)).conclusion shouldBe force(Term.eq(asSpecialised, asReduced))
  }

  it should "be reachable by specTo, which compares the instance as spec leaves it" in {
    force(rules.specTo(overSummand, asSpecialised)).conclusion shouldBe asSpecialised

    // And the reduced one is not, which is the whole reason the second operation exists rather
    // than the first growing a flag.
    rules.specTo(overSummand, asReduced) should matchPattern { case Left(NotOfForm(_, _)) => }
  }

  it should "be reachable reduced by specToReduced, which is a different theorem" in {
    // The matcher is what this rests on and it was measured before the operation was written: the
    // pattern holds `f i` under a binder and the target holds the reduced body, so finding the
    // instantiation is higher-order matching, and it is solved.
    force(rules.specToReduced(overSummand, asReduced)).conclusion shouldBe asReduced

    rules.specToReduced(overSummand, asSpecialised) should matchPattern {
      case Left(NotOfForm(_, _)) =>
    }
  }

  it should "be reachable by specTo alone when the summand is a name, which is why it is not one here" in {
    // The assertion the docstring above points at, and it is not the one that was written there
    // first. `\y. h y` does leave a redex in the instance, exactly as the richer summand does; what
    // is different is the MATCH. Against `s (\i. h i)` it comes back with `f := h`, a name where a
    // name was, so `specTo` specialises at `h`, gets the reduced form with nothing left to
    // contract, and reaches the target on its own. A version of this pair demonstrated on that
    // summand would pass while showing nothing, which is what this refuses.
    val y = Term.variable("y", alpha)
    val i = Term.variable("i", alpha)
    val eta = lam(y, force(Term.app(named, y)))
    val instance = force(rules.specAll(overSummand, List(eta)))
    val reducedBody = force(Term.app(collect, lam(i, force(Term.app(named, i)))))
    val reduced = force(Term.eq(reducedBody, reducedBody))

    instance.conclusion should not be reduced
    force(rules.specTo(overSummand, reduced)).conclusion shouldBe reduced
  }

  it should "agree with specTo wherever there is nothing to reduce" in {
    // Paired with the three above: without this, `specToReduced` passing them would be consistent
    // with its being a different operation everywhere rather than at the redex.
    val wanted = force(Term.eq(applied(a, b), applied(a, b)))

    force(rules.specToReduced(firstThenSecond, wanted)).conclusion shouldBe
      force(rules.specTo(firstThenSecond, wanted)).conclusion
  }

  "Falsity" should "give any proposition at all" in {
    // Ex falso, and it needs no classical principle: `F` is `!x:bool. x`, so the rule unfolds the
    // definition and specialises. It is the converse, `~~p` to `p`, that this logic cannot reach.
    val theorem = force(rules.falsityElim(p, force(Kernel.assume(logic.falsity))))

    theorem.conclusion shouldBe p
    theorem.hypotheses shouldBe List(logic.falsity)
  }

  it should "refuse a theorem that does not prove falsity" in {
    rules.falsityElim(q, force(Kernel.assume(p))).left.map(_.getClass) shouldBe
      Left(classOf[NotOfForm])
  }

  it should "refuse a target that is not a proposition" in {
    val x = Term.variable("x", TyVar("A"))

    rules.falsityElim(x, force(Kernel.assume(logic.falsity))).left.map(_.getClass) shouldBe
      Left(classOf[NotOfForm])
  }

  "Disjunction" should "be introduced from either disjunct" in {
    val left = force(rules.disjIntro1(q, force(Kernel.assume(p))))
    val right = force(rules.disjIntro2(p, force(Kernel.assume(q))))
    val disjunction = force(logic.mkDisj(p, q))

    left.conclusion shouldBe disjunction
    left.hypotheses shouldBe List(p)
    right.conclusion shouldBe disjunction
    right.hypotheses shouldBe List(q)
  }

  it should "be eliminated into what both cases prove" in {
    val disjunction = force(logic.mkDisj(p, q))
    val assumed = force(Kernel.assume(disjunction))
    val leftCase = force(rules.disjIntro2(q, force(Kernel.assume(p))))
    val rightCase = force(rules.disjIntro1(p, force(Kernel.assume(q))))

    val eliminated = force(rules.disjElim(assumed, leftCase, rightCase))
    val theorem = force(rules.disch(disjunction, eliminated))

    theorem.hypotheses shouldBe empty
    Show.show(theorem) shouldBe "|- p \\/ q ==> q \\/ p"
  }

  it should "eliminate a case that did not need its disjunct" in {
    // `disch` discharges an antecedent whether or not it was assumed, so a branch that reaches the
    // conclusion without using its own disjunct is still a branch. Refusing it would make the rule
    // about the shape of the hypothesis set rather than about case analysis.
    val disjunction = force(logic.mkDisj(p, q))
    val assumed = force(Kernel.assume(disjunction))
    val eliminated = force(
      rules.disjElim(assumed, force(rules.truth), force(rules.truth))
    )

    eliminated.conclusion shouldBe logic.truth
    eliminated.hypotheses shouldBe List(disjunction)
  }

  it should "refuse two cases that prove different things" in {
    val assumed = force(Kernel.assume(force(logic.mkDisj(p, q))))

    rules
      .disjElim(assumed, force(Kernel.assume(p)), force(Kernel.assume(q)))
      .left
      .map(_.getClass) shouldBe Left(classOf[NotOfForm])
  }

  it should "refuse to eliminate something that is not a disjunction" in {
    val assumed = force(Kernel.assume(p))

    rules.disjElim(assumed, assumed, assumed).left.map(_.getClass) shouldBe
      Left(classOf[NotOfForm])
  }

  "The existential quantifier" should "be introduced from a witness" in {
    val x = Term.variable("x", TyVar("A"))
    val y = Term.variable("y", TyVar("A"))
    val predicate = lam(x, force(Term.eq(x, x)))

    val theorem = force(rules.existsIntro(predicate, y, Kernel.refl(y)))

    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe force(logic.mkExists(x, force(Term.eq(x, x))))
  }

  it should "be introduced with a predicate that is not an abstraction" in {
    // Without eta, `f` and `\x. f x` are two terms, and the rule is stated over whichever the
    // caller names. This is the branch where the application the derivation builds is not a redex,
    // so the contraction it asks for comes back a reflexivity: the rule must go through on that
    // path too, or it would silently require its predicate to be written one particular way.
    val v = Term.variable("v", TyVar("A"))
    val f = Term.variable("f", Type.fun(TyVar("A"), Type.Bool))
    val instance = force(Term.app(f, v))
    val existential = force(
      logic.existentialAt(TyVar("A")).flatMap(quantifier => LogicError.lift(Term.app(quantifier, f)))
    )

    val theorem = force(rules.existsIntro(f, v, force(Kernel.assume(instance))))

    theorem.conclusion shouldBe existential
    theorem.hypotheses shouldBe List(instance)
  }

  it should "refuse a theorem that does not prove the predicate at the witness" in {
    val x = Term.variable("x", TyVar("A"))
    val y = Term.variable("y", TyVar("A"))
    val predicate = lam(x, force(Term.eq(x, y)))

    rules.existsIntro(predicate, y, force(Kernel.assume(p))).left.map(_.getClass) shouldBe
      Left(classOf[NotOfForm])
  }

  it should "be eliminated over a witness that appears nowhere else" in {
    val x = Term.variable("x", TyVar("A"))
    val v = Term.variable("v", TyVar("A"))
    val f = Term.variable("f", Type.fun(TyVar("A"), Type.Bool))
    val existential = force(logic.mkExists(x, force(Term.app(f, x))))

    // A case that assumes the instance and proves something the witness does not occur in.
    val instance = force(Kernel.assume(force(Term.app(f, v))))
    val conjoined = force(rules.conjIntro(instance, force(Kernel.assume(q))))
    val caseTheorem = force(rules.conjElim2(conjoined))

    val theorem = force(rules.existsElim(force(Kernel.assume(existential)), v, caseTheorem))

    theorem.conclusion shouldBe q
    theorem.hypotheses shouldBe List(existential, q).sorted(using Term.ordering)
  }

  it should "refuse a witness that occurs in the conclusion" in {
    // The whole content of the side condition: proving `f v` from the existence of some `f x`
    // would be proving it for that particular witness.
    val x = Term.variable("x", TyVar("A"))
    val v = Term.variable("v", TyVar("A"))
    val f = Term.variable("f", Type.fun(TyVar("A"), Type.Bool))
    val existential = force(logic.mkExists(x, force(Term.app(f, x))))
    val instance = force(Kernel.assume(force(Term.app(f, v))))

    rules
      .existsElim(force(Kernel.assume(existential)), v, instance)
      .left
      .map(_.getClass) shouldBe Left(classOf[EscapingVariable])
  }

  it should "refuse a case that does not assume the instance" in {
    val x = Term.variable("x", TyVar("A"))
    val v = Term.variable("v", TyVar("A"))
    val f = Term.variable("f", Type.fun(TyVar("A"), Type.Bool))
    val existential = force(logic.mkExists(x, force(Term.app(f, x))))

    rules.existsElim(force(Kernel.assume(existential)), v, force(Kernel.assume(q))) shouldBe
      Left(MissingHypothesis(force(Term.app(f, v)), "eliminating an existential"))
  }

  it should "refuse a witness that occurs in the predicate" in {
    // The half that fails silently if the check goes: `gen` would close over the `v` inside the
    // predicate too, the antecedent would stop matching the one `spec` produced, and `mp` compares
    // no antecedents, so the result would be `q` under an extra hypothesis rather than an error.
    val x = Term.variable("x", TyVar("A"))
    val v = Term.variable("v", TyVar("A"))
    val f = Term.variable("f", Type.fun(TyVar("A"), Type.fun(TyVar("A"), Type.Bool)))
    val predicate = lam(x, force(Term.appAll(f, List(v, x))))
    val existential = force(
      logic
        .existentialAt(TyVar("A"))
        .flatMap(quantifier => LogicError.lift(Term.app(quantifier, predicate)))
    )
    val instance = force(Term.appAll(f, List(v, v)))
    val caseTheorem = force(
      rules.conjElim2(
        force(rules.conjIntro(force(Kernel.assume(instance)), force(Kernel.assume(q))))
      )
    )

    rules.existsElim(force(Kernel.assume(existential)), v, caseTheorem) shouldBe
      Left(EscapingVariable(v, "the predicate it is the witness for"))
  }

  it should "refuse a witness that is free in the rest of the case's hypotheses" in {
    // The third condition, and the only one of the three the kernel catches: it arrives from
    // `Kernel.abs` through `gen`, which is why the error is a `FromKernel` and not one of ours.
    val x = Term.variable("x", TyVar("A"))
    val v = Term.variable("v", TyVar("A"))
    val f = Term.variable("f", Type.fun(TyVar("A"), Type.Bool))
    val g = Term.variable("g", Type.fun(TyVar("A"), Type.Bool))
    val existential = force(logic.mkExists(x, force(Term.app(f, x))))
    val instance = force(Term.app(f, v))
    val elsewhere = force(Term.app(g, v))

    val stacked = force(
      rules.conjIntro(
        force(Kernel.assume(instance)),
        force(rules.conjIntro(force(Kernel.assume(elsewhere)), force(Kernel.assume(q))))
      )
    )
    val caseTheorem = force(rules.conjElim2(force(rules.conjElim2(stacked))))

    rules
      .existsElim(force(Kernel.assume(existential)), v, caseTheorem)
      .left
      .map(_.getClass) shouldBe Left(classOf[FromKernel])
  }

  it should "work at a domain other than the one its schema is stated over" in {
    // `unfoldExistential` instantiates the definition's type variable, and every other test in this
    // block ranges over that same variable, so the instantiation is a no-op in all of them and a
    // wrong key would go unseen. This one ranges over a different type variable, so it does not.
    val b = TyVar("B")
    val x = Term.variable("x", b)
    val v = Term.variable("v", b)
    val f = Term.variable("f", Type.fun(b, Type.Bool))
    val instance = force(Term.app(f, v))
    val existential = force(logic.mkExists(x, force(Term.app(f, x))))

    val introduced =
      force(rules.existsIntro(lam(x, force(Term.app(f, x))), v, force(Kernel.assume(instance))))
    introduced.conclusion shouldBe existential

    val caseTheorem = force(
      rules.conjElim2(
        force(rules.conjIntro(force(Kernel.assume(instance)), force(Kernel.assume(q))))
      )
    )
    val eliminated = force(rules.existsElim(force(Kernel.assume(existential)), v, caseTheorem))

    eliminated.conclusion shouldBe q
    eliminated.hypotheses shouldBe List(existential, q).sorted(using Term.ordering)
  }

  "The derived rules together" should "carry an existential across a pointwise implication" in {
    // Both new rules and most of the old ones in one derivation, and the first statement in this
    // development that needs a witness it never names.
    val x = Term.variable("x", TyVar("A"))
    val v = Term.variable("v", TyVar("A"))
    val f = Term.variable("f", Type.fun(TyVar("A"), Type.Bool))
    val g = Term.variable("g", Type.fun(TyVar("A"), Type.Bool))

    val existsF = force(logic.mkExists(x, force(Term.app(f, x))))
    val existsG = force(logic.mkExists(x, force(Term.app(g, x))))
    val monotone =
      force(logic.mkForall(x, force(logic.mkImp(force(Term.app(f, x)), force(Term.app(g, x))))))

    val atWitness = force(rules.spec(v, force(Kernel.assume(monotone))))
    val carried = force(rules.mp(atWitness, force(Kernel.assume(force(Term.app(f, v))))))
    val caseTheorem = force(rules.existsIntro(lam(x, force(Term.app(g, x))), v, carried))
    val eliminated = force(rules.existsElim(force(Kernel.assume(existsF)), v, caseTheorem))

    val theorem = force(
      for {
        withoutExistential <- rules.disch(existsF, eliminated)
        closed <- rules.disch(monotone, withoutExistential)
      } yield closed
    )

    theorem.hypotheses shouldBe empty
    // The quotes on `A` arrived on 2026-09-12 with the printer that writes the syntax its own
    // parser reads: a type variable is `'A` and a bare `A` is a type operator of that name.
    Show.show(theorem) shouldBe "|- (!x:'A. f x ==> g x) ==> (?x:'A. f x) ==> (?x:'A. g x)"
  }

  it should "prove that conjunction commutes" in {
    val conjunction = force(logic.mkConj(p, q))
    val assumed = force(Kernel.assume(conjunction))

    val theorem = force(
      for {
        left <- rules.conjElim1(assumed)
        right <- rules.conjElim2(assumed)
        swapped <- rules.conjIntro(right, left)
        discharged <- rules.disch(conjunction, swapped)
      } yield discharged
    )

    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe force(logic.mkImp(conjunction, force(logic.mkConj(q, p))))
    Show.show(theorem) shouldBe "|- p /\\ q ==> q /\\ p"
  }

  "A statement containing a redex" should "go through every rule exactly as it was written" in {
    // The rules instantiate schemas proved once over variables, so nothing a caller passes is
    // reduced on the way through. The first version unfolded each definition on the caller's own
    // terms and normalised the result, which reduced those terms too, and every introduction rule
    // then refused a redex because the statement it had built no longer matched. An audit found
    // it.
    val z = Term.variable("z", Type.Bool)
    val redex = force(Term.app(lam(z, z), p))
    val assumedRedex = force(Kernel.assume(redex))
    val assumedQ = force(Kernel.assume(q))
    val conjunction = force(logic.mkConj(redex, q))
    val implication = force(rules.disch(redex, assumedQ))

    force(rules.conjIntro(assumedRedex, assumedQ)).conclusion shouldBe conjunction
    force(rules.conjElim1(force(Kernel.assume(conjunction)))).conclusion shouldBe redex
    implication.conclusion shouldBe force(logic.mkImp(redex, q))
    force(rules.mp(implication, assumedRedex)).conclusion shouldBe q
    force(rules.notIntro(redex, force(Kernel.assume(logic.falsity)))).conclusion shouldBe
      force(logic.mkNot(redex))
    force(rules.gen(p, Kernel.refl(redex))).conclusion shouldBe
      force(logic.mkForall(p, force(Term.eq(redex, redex))))

    // The three disjunction rules reduce nothing at all, so the redex has to survive each of them.
    force(rules.disjIntro1(q, assumedRedex)).conclusion shouldBe force(logic.mkDisj(redex, q))
    force(rules.disjIntro2(redex, assumedQ)).conclusion shouldBe force(logic.mkDisj(redex, q))

    val disjunction = force(logic.mkDisj(redex, q))
    val eliminated = force(rules.disjElim(force(Kernel.assume(disjunction)), assumedQ, assumedQ))
    eliminated.conclusion shouldBe q
    eliminated.hypotheses should contain(disjunction)
  }

  "Introducing an existential" should "contract the application it built and nothing in the witness" in {
    // The mirror of the `spec` case below, and the assertion that would fail first if the rule
    // reached for `betaNormalise` instead of `betaRoot`: the reduced instance would become `f v`
    // and would no longer be the conclusion the caller handed in.
    val x = Term.variable("x", TyVar("A"))
    val y = Term.variable("y", TyVar("A"))
    val v = Term.variable("v", TyVar("A"))
    val f = Term.variable("f", Type.fun(TyVar("A"), Type.Bool))
    val witness = force(Term.app(lam(y, y), v))
    val instance = force(Term.app(f, witness))

    val theorem =
      force(rules.existsIntro(lam(x, force(Term.app(f, x))), witness, force(Kernel.assume(instance))))

    theorem.conclusion shouldBe force(logic.mkExists(x, force(Term.app(f, x))))
    theorem.hypotheses shouldBe List(instance)
  }

  "Specialising" should "contract the applications it built and nothing inside the argument" in {
    // HOL Light's SPEC does the same. The redex in the argument is the caller's, and a rule that
    // reduced it would be returning a statement about a different term.
    val x = Term.variable("x", TyVar("A"))
    val y = Term.variable("y", TyVar("A"))
    val redex = force(Term.app(lam(y, y), x))
    val general = force(rules.gen(x, Kernel.refl(x)))

    force(rules.spec(redex, general)).conclusion shouldBe force(Term.eq(redex, redex))
  }
}
