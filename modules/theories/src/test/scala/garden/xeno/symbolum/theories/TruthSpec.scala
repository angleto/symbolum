package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The truth of a formula of the embedded theory, and whether it says anything.
 *
 * **What it says.** Every clause is compared against the text `Truth.Statements` holds, as a term,
 * and the list of statements against the map of facts in both directions.
 *
 * **What it cost.** Three definitions and no axiom, asserted as a difference against the theory it
 * extends, and what the facts spend asserted as an equality per fact.
 *
 * **Whether it discriminates**, which is the part a list of equations cannot show. A truth
 * predicate that answered `T` everywhere, or one whose quantifier forgot to update the environment,
 * would satisfy every clause read as a rewrite in the wrong hands, so three formulas are evaluated
 * to an answer: `0 = S 0` is refuted at every environment; `~ !v0. v0 = 0` is proved at the
 * environment sending everything to zero, which is exactly where a quantifier that ignored its
 * update would read `0 = 0` and answer the other way; and the graph of the triangle is proved at
 * one environment and refuted at another, which spends both directions of its representation.
 */
class TruthSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard
  private lazy val truth: Truth = chain.truth

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private def fact(name: String): Kernel.Thm = force(truth.fact(name))
  private def term(text: String): Term = force(truth.term(text))
  private def proposition(text: String): Term = force(truth.proposition(text))
  private lazy val rules = truth.logic.rules
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /** Rewrite to a fixed point, reducing every redex a substituted environment leaves behind. */
  private def evaluate(subject: Term, equations: Vector[Kernel.Thm]): Kernel.Thm = {
    val conditionals = force(Language.conditionalRules(truth.logic, chain.classical, numbers))
    val ruleSet = force(Rewrite.Rule.all(truth.logic, equations ++ conditionals))
    def round(current: Kernel.Thm, left: Int): Kernel.Thm = {
      val right = force(Term.destEq(current.conclusion).map(_._2).toRight("an equation"))
      val reduced = force(Conv.betaNormalise(right))
      val rewritten = force(Rewrite.rewrite(ruleSet, force(Term.destEq(reduced.conclusion)
        .map(_._2).toRight("an equation"))))
      val next = force(Conv.trans(current, reduced).flatMap(Conv.trans(_, rewritten)))
      if (next.conclusion == current.conclusion || left == 0) next else round(next, left - 1)
    }
    round(Conv.refl(subject), 6)
  }

  private def rightOf(theorem: Kernel.Thm): Term =
    force(Term.destEq(theorem.conclusion).map(_._2).toRight("an equation"))

  /* ------------------------------------------------------------------------ what it says */

  "The truth of the object language" should "prove every statement it publishes, owing nothing" in {
    Truth.Statements.foreach { case (name, text) =>
      val proved = fact(name)
      withClue(s"$name: ") {
        proved.hypotheses shouldBe empty
        proved.conclusion shouldBe proposition(text)
      }
    }
  }

  it should "publish a fact for every name in its statement list, and nothing else" in {
    Truth.Statements.map(_._1).distinct.size shouldBe Truth.Statements.size
    Truth.Statements.map(_._1).toSet shouldBe truth.facts.keySet
  }

  /* ------------------------------------------------------------------------ what it cost */

  it should "define the constants it names and assert no axiom" in {
    val below = chain.provability.theory
    truth.theory.axioms shouldBe below.axioms
    (truth.theory.constants.keySet -- below.constants.keySet) shouldBe
      Set(Truth.ValueName, Truth.TrueName, Truth.GroundName, Truth.BoundedName, Truth.RankName, Truth.SigmaName,
        Truth.TriangleGraphName)
    truth.theory.typeOperators.keySet shouldBe below.typeOperators.keySet
  }

  it should "spend what the naturals cost, fact by fact" in {
    // Measured at the commit that landed this and asserted as an equality for each fact, so a
    // derivation that starts or stops spending an axiom goes red naming itself. The clauses spend
    // choice through the witness the recursion is named by and infinity through `num`.
    val choice = chain.classical.axioms(Classical.Choice).conclusion
    val infinity = chain.naturals.axioms(Natural.Infinity).conclusion
    val eta = chain.classical.axioms(Classical.Eta).conclusion
    val named = Map(choice -> "SELECT", infinity -> "INFINITY", eta -> "ETA")
    val perFact = Truth.Statements.map { case (name, _) =>
      name -> Derivation.axiomsOf(fact(name))
    }
    val report = perFact
      .map { case (name, axioms) =>
        val names = axioms.toVector.map(a => named.getOrElse(a, truth.show(a))).sorted
        s"$name: " + names.mkString(", ")
      }
      .mkString("; ")
    info(report)
    val expected: Map[String, Set[Term]] =
      Truth.Statements.map { case (name, _) => name -> Set(choice, infinity) }.toMap
    withClue(s"per fact: $report\n") {
      perFact.toMap shouldBe expected
    }
  }

  /* -------------------------------------------------------------- whether it discriminates */

  "An equation between zero and a successor" should "be false at every environment" in {
    val code = "NUM_CODE 5 (NUM_PAIR (NUM_CODE 1 0) (NUM_CODE 2 (NUM_CODE 1 0)))"
    val environment = Term.variable("e", Type.fun(numbers, numbers))
    val claim = force(LogicError.lift(Term.appAll(term(s"NUM_TRUE ($code)"), List(environment))))
    val evaluated = evaluate(claim, Vector(
      fact(Truth.TrueEquality), fact(Truth.ValueZero), fact(Truth.ValueSuccessor)))
    rightOf(evaluated) shouldBe proposition("ZERO = SUC ZERO")

    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val equated = force(LogicError.lift(Kernel.eqMp(evaluated, assumed)))
    val never = force(
      chain.naturals.fact(Natural.SuccessorNotZero).flatMap(rules.spec(term("ZERO"), _)))
    val refuted = force(
      Conv.sym(equated).flatMap(rules.notElim(never, _)).flatMap(rules.notIntro(claim, _)))
    val general = force(rules.gen(environment, refuted))
    general.hypotheses shouldBe empty
    general.conclusion shouldBe proposition(s"!e:num -> num. ~(NUM_TRUE ($code) e)")
  }

  "A quantifier" should "read its body at the updated environment, which the update settles" in {
    // `~ !v0. v0 = 0` at the environment sending every variable to zero. With the update, the body
    // is read at `n` and the claim is that not every `n` is zero, which is true. A quantifier that
    // read its body at `e` unchanged would ask whether `e 0 = 0` for every `n`, which is `0 = 0`
    // here, and the negation would be false.
    val code =
      "NUM_CODE 6 (NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0)))))"
    val claim = proposition(s"NUM_TRUE ($code) (\\k:num. ZERO)")
    val zeroIsZero = force(rules.eqTruthIntro(Kernel.refl(term("0:num"))))
    val evaluated = evaluate(claim, Vector(
      fact(Truth.TrueNegation), fact(Truth.TrueUniversal), fact(Truth.TrueEquality),
      fact(Truth.ValueVariable), fact(Truth.ValueZero), zeroIsZero))
    rightOf(evaluated) shouldBe proposition("~(!n:num. n = ZERO)")

    val everything = proposition("!n:num. n = ZERO")
    val assumed = force(LogicError.lift(Kernel.assume(everything)))
    val one = force(rules.spec(term("SUC ZERO"), assumed))
    val never = force(
      chain.naturals.fact(Natural.SuccessorNotZero).flatMap(rules.spec(term("ZERO"), _)))
    val denied = force(rules.notElim(never, one).flatMap(rules.notIntro(everything, _)))
    val proved = force(Conv.sym(evaluated).flatMap(e => LogicError.lift(Kernel.eqMp(e, denied))))
    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe claim
  }

  "A numeral put for a variable" should "change the truth as sending the variable to it does" in {
    // Two universals at `x = 0` and the numeral of two. Under `!v_1` the substitution goes in and
    // the update at `0` survives the quantifier's own at `1`, so both sides say `!n. 2 = n`. Under
    // `!v_0` the substitution stops at the binder and the quantifier's update at `0` overwrites the
    // one at `0`, so both sides say `!n. n = e 1`. A lemma that let the substitution in under `!v_0`,
    // or kept the outer update there, would make the second pair disagree.
    val environment = Term.variable("e", Type.fun(numbers, numbers))
    val two = term("SUC (SUC ZERO)")
    val lemma = fact(Truth.TrueAtNumeral)
    lemma.hypotheses shouldBe empty
    val language = chain.language
    // The guards the two environments and the substitution leave are between the indices 0 and
    // 1, and they are decided here as equations with T and F, as the quantifier test above does.
    def decided(held: Kernel.Thm): Kernel.Thm = force(rules.eqTruthIntro(held))
    def refuted(claim: Term, denied: Kernel.Thm): Kernel.Thm = {
      val falsity = force(LogicError.lift(Kernel.assume(claim)).flatMap(rules.notElim(denied, _)))
      val fromFalsity = force(LogicError.lift(Kernel.assume(falsity.conclusion)).flatMap(rules.falsityElim(claim, _)))
      Kernel.deductAntisym(fromFalsity, falsity)
    }
    val oneIsSuccessor = force(chain.peano.fact(Peano.NumeralOneIsSuccessorOfZero))
    val oneNotZero = force(chain.naturals.fact(Natural.SuccessorNotZero).flatMap(rules.spec(term("ZERO"), _))
      .flatMap(Rewrite.inTheorem(force(Conv.sym(oneIsSuccessor).flatMap(e => Rewrite.Rule.all(truth.logic, Vector(e)))), _)))
    val zeroNotOne = force(rules.notIntro(proposition("(ZERO:num) = NUM_ONE"),
      force(rules.notElim(oneNotZero, force(LogicError.lift(Kernel.assume(proposition("(ZERO:num) = NUM_ONE")))
        .flatMap(Conv.sym))))))
    val guards = Vector(
      decided(Kernel.refl(term("ZERO"))),
      decided(Kernel.refl(term("NUM_ONE"))),
      refuted(proposition("NUM_ONE = ZERO"), oneNotZero),
      refuted(proposition("(ZERO:num) = NUM_ONE"), zeroNotOne))
    val unfolding = guards ++ Vector(
      fact(Truth.TrueUniversal), fact(Truth.TrueEquality), fact(Truth.ValueVariable), fact(Truth.ValueNumeral),
      force(language.fact(Language.FormulaSubstituteUniversal)),
      force(language.fact(Language.FormulaSubstituteEquality)),
      force(language.fact(Language.SubstituteVariable)))
    def bothSides(code: String): (Term, Term) = {
      val p = term(code)
      val instance = force(rules.specAll(lemma, List(term("0:num"), two, p))
        .flatMap(rules.mp(_, force(language.wellFormedIn(p))))
        .flatMap(rules.spec(environment, _)))
      instance.hypotheses shouldBe empty
      val (left, right) = force(Term.destEq(instance.conclusion).toRight("an equation"))
      (rightOf(evaluate(left, unfolding)), rightOf(evaluate(right, unfolding)))
    }

    val (inLeft, inRight) =
      bothSides("NUM_CODE 8 (NUM_PAIR 1 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 1))))")
    inLeft shouldBe proposition("!n:num. SUC (SUC ZERO) = n")
    inRight shouldBe inLeft

    val (stopLeft, stopRight) =
      bothSides("NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 1))))")
    val atOne = force(LogicError.lift(Term.appAll(environment, List(term("1:num")))))
    stopLeft shouldBe force(LogicError.lift(Term.eq(term("n:num"), atOne)).flatMap(body =>
      truth.logic.mkForall(Term.variable("n", numbers), body)))
    stopRight shouldBe stopLeft
  }

  "The bounded class" should "take a universal below a numeral, and neither an unbounded one nor one whose order binds its own index" in {
    // `!v_0. v_0 < 3 ==> v_0 = v_0` with the order's witness at 1 is in the class. The same with
    // the witness at 0 is not, the order then binding the index it is about, and `!v_0. v_0 = v_0`
    // is not either: a universal in the class is a universal below, and that one's body is an
    // equation where the class wants an order's implication. A class that took every universal,
    // or read the clause without the condition on the witness, would prove one of the two denials
    // false. The two denials come first, so that a class which lost a condition goes red at the
    // denial it makes false rather than at the instance that no longer reads.
    val equation = "NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0))"
    val clause = fact(Truth.BoundedAllBelow)
    val bounded = term("NUM_BOUNDED")
    def holds(text: String): Term = force(LogicError.lift(Term.app(bounded, term(text))))

    val logic = truth.logic
    val three = term("NUM_NUMERAL 3")
    val ownIndex = holds(s"NUM_ALL_BELOW 0 0 (NUM_NUMERAL 3) ($equation)")
    val refusedOwn = force(for {
      opened <- rules.specAll(clause, List(term("0:num"), term("0:num"), three, term(equation)))
      assumed <- LogicError.lift(Kernel.assume(ownIndex))
      read <- LogicError.lift(Kernel.eqMp(opened, assumed))
      apart <- rules.conjElim1(read)
      absurd <- rules.notElim(apart, Kernel.refl(term("0:num")))
      out <- rules.notIntro(ownIndex, absurd)
    } yield out)
    refusedOwn.hypotheses shouldBe empty
    refusedOwn.conclusion shouldBe force(logic.mkNot(ownIndex))

    val unbounded = holds(s"NUM_CODE 8 (NUM_PAIR 0 ($equation))")
    val numbering = chain.numbering
    def inside(existential: Term, name: String): (FVar, Term) = {
      val predicate = force(logic.destExistsPredicate(existential).toRight("an existential"))
      val variable = Term.variable(name, numbers)
      val applied = force(LogicError.lift(Term.app(predicate, variable)))
      (variable, force(Term.betaReduce(applied).toRight("a predicate")))
    }
    val shaped = force(rules.specAll(fact(Truth.BoundedUniversal), List(term("0:num"), term(equation)))
      .flatMap(inversion => LogicError.lift(Kernel.assume(unbounded)).flatMap(rules.mp(inversion, _))))
    val (z, overT) = inside(shaped.conclusion, "z")
    val (t, overP) = inside(overT, "t")
    val (p, body) = inside(overP, "p")
    val refusedUnbounded = force(for {
      held <- LogicError.lift(Kernel.assume(body))
      cases <- chain.language.fact(Language.AllBelowCases)
      unfolded <- rules.specAll(cases, List(z, term("0:num"), t, p))
      codes <- Conv.trans(held, unfolded)
      codeInjective <- numbering.fact(Numbering.CodeInjective)
      pairInjective <- numbering.fact(Numbering.PairInjective)
      outer <- (rightOf(codes) match {
        case App(_, payload) =>
          rules.specAll(codeInjective, List(term("8:num"), term(s"NUM_PAIR 0 ($equation)"), term("8:num"), payload))
        case other => Left(NotOfForm("a code", other))
      }).flatMap(rules.mp(_, codes)).flatMap(rules.conjElim2)
      bodies <- (rightOf(outer) match {
        case App(App(_, first), second) =>
          rules.specAll(pairInjective, List(term("0:num"), term(equation), first, second))
        case other => Left(NotOfForm("a pair", other))
      }).flatMap(rules.mp(_, outer)).flatMap(rules.conjElim2)
      tags <- (rightOf(bodies) match {
        case App(App(_, tag), payload) =>
          rules.specAll(codeInjective, List(term("5:num"), term("NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0)"), tag, payload))
        case other => Left(NotOfForm("a code", other))
      }).flatMap(rules.mp(_, bodies)).flatMap(rules.conjElim1)
      apart <- chain.successor.distinct(term("5:num"), term("7:num"))
      absurd <- rules.notElim(apart, tags)
      overPAssumed <- LogicError.lift(Kernel.assume(overP))
      atT <- rules.existsElim(overPAssumed, p, absurd)
      overTAssumed <- LogicError.lift(Kernel.assume(overT))
      atZ <- rules.existsElim(overTAssumed, t, atT)
      none <- rules.existsElim(shaped, z, atZ)
      out <- rules.notIntro(unbounded, none)
    } yield out)
    refusedUnbounded.hypotheses shouldBe empty
    refusedUnbounded.conclusion shouldBe force(logic.mkNot(unbounded))

    val oneIsSuccessor = force(chain.peano.fact(Peano.NumeralOneIsSuccessorOfZero))
    val oneNotZero = force(chain.naturals.fact(Natural.SuccessorNotZero).flatMap(rules.spec(term("ZERO"), _))
      .flatMap(Rewrite.inTheorem(force(Conv.sym(oneIsSuccessor).flatMap(e => Rewrite.Rule.all(truth.logic, Vector(e)))), _)))
    val isNumeral = force(rules.existsIntro(term("\\n:num. NUM_NUMERAL 3 = NUM_NUMERAL n"), term("3:num"),
      Kernel.refl(three)))
    val equationBounded = force(rules.specAll(fact(Truth.BoundedEquality), List(term("NUM_CODE 0 0"), term("NUM_CODE 0 0")))
      .flatMap(rules.eqTruthElim))
    val below = force(rules.specAll(clause, List(term("1:num"), term("0:num"), three, term(equation))))
    val (_, conditions) = force(Term.destEq(below.conclusion).toRight("an equation"))
    val bound = force(logic.destConj(conditions).map(_._2).flatMap(logic.destConj).map(_._1).toRight("a conjunction"))
    val variableBound = force(logic.destDisj(bound).map(_._1).toRight("a disjunction"))
    val taken = force(for {
      either <- rules.disjIntro2(variableBound, isNumeral)
      rest <- rules.conjIntro(either, equationBounded)
      all <- rules.conjIntro(oneNotZero, rest)
      back <- Conv.sym(below)
      out <- LogicError.lift(Kernel.eqMp(back, all))
    } yield out)
    taken.hypotheses shouldBe empty
    taken.conclusion shouldBe holds(s"NUM_ALL_BELOW 1 0 (NUM_NUMERAL 3) ($equation)")

  }

  "A numeral put for a variable" should "keep a formula in the bounded class when the variable is a bound" in {
    // `!v_0. v_0 < v_2 ==> v_0 = v_0`, with the order's witness at 1, is in the class with the
    // variable v_2 for its bound, and 3 is put for v_2: the substitution reaches the bound, so this
    // is the case where the class's two kinds of bound have to meet, the variable turning into the
    // numeral. Both conditions of the fact are discharged here rather than assumed, so the instance
    // says the closure applies to a formula the class was shown to hold, with nothing owed.
    val equation = "NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0))"
    val bound = term("NUM_CODE 0 2")
    val formula = term(s"NUM_ALL_BELOW 1 0 (NUM_CODE 0 2) ($equation)")
    val logic = truth.logic
    val language = chain.language
    def holds(predicate: String, subject: Term): Term =
      force(LogicError.lift(Term.app(term(predicate), subject)))

    val isFormula = force(for {
      variables <- language.fact(Language.TermVariable)
      atZero <- rules.spec(term("0:num"), variables)
      atTwo <- rules.spec(term("2:num"), variables)
      equality <- language.fact(Language.FormulaEquality)
        .flatMap(rules.specAll(_, List(term("NUM_CODE 0 0"), term("NUM_CODE 0 0"))))
        .flatMap(rules.mp(_, atZero)).flatMap(rules.mp(_, atZero))
      out <- language.fact(Language.AllBelowFormula)
        .flatMap(rules.specAll(_, List(term("1:num"), term("0:num"), bound, term(equation))))
        .flatMap(rules.mp(_, atTwo)).flatMap(rules.mp(_, equality))
    } yield out)
    isFormula.conclusion shouldBe holds("NUM_FORM", formula)

    val clause = force(rules.specAll(fact(Truth.BoundedAllBelow), List(term("1:num"), term("0:num"), bound, term(equation))))
    val (_, conditions) = force(Term.destEq(clause.conclusion).toRight("an equation"))
    val bounds = force(logic.destConj(conditions).map(_._2).flatMap(logic.destConj).map(_._1).toRight("a conjunction"))
    val (variableBound, numeralBound) = force(logic.destDisj(bounds).toRight("a disjunction"))
    val isBounded = force(for {
      oneNotZero <- chain.successor.distinct(term("1:num"), term("0:num"))
      twoNotZero <- chain.successor.distinct(term("2:num"), term("0:num"))
      twoNotOne <- chain.successor.distinct(term("2:num"), term("1:num"))
      apart <- rules.conjIntro(twoNotZero, twoNotOne)
      atTwo <- rules.conjIntro(Kernel.refl(bound), apart)
      predicate <- logic.destExistsPredicate(variableBound).toRight(NotOfForm("an existential", variableBound))
      variable <- rules.existsIntro(predicate, term("2:num"), atTwo)
      either <- rules.disjIntro1(numeralBound, variable)
      body <- rules.specAll(fact(Truth.BoundedEquality), List(term("NUM_CODE 0 0"), term("NUM_CODE 0 0")))
        .flatMap(rules.eqTruthElim)
      rest <- rules.conjIntro(either, body)
      all <- rules.conjIntro(oneNotZero, rest)
      back <- Conv.sym(clause)
      out <- LogicError.lift(Kernel.eqMp(back, all))
    } yield out)
    isBounded.hypotheses shouldBe empty
    isBounded.conclusion shouldBe holds("NUM_BOUNDED", formula)

    val closed = force(rules.specAll(fact(Truth.BoundedAtNumeral), List(term("2:num"), term("3:num"), formula))
      .flatMap(rules.mp(_, isFormula)).flatMap(rules.mp(_, isBounded)))
    closed.hypotheses shouldBe empty
    closed.conclusion shouldBe holds("NUM_BOUNDED", term(s"NUM_SUBST_FORM 2 (NUM_NUMERAL 3) (NUM_ALL_BELOW 1 0 (NUM_CODE 0 2) ($equation))"))
  }

  "The rank of a formula" should "count its connectives, and not move when a numeral is put for a variable" in {
    // `!v_1. v_0 = v_1 ==> ~(v_0 = v_1)`: a universal over an implication whose right side is a
    // negation, so all four clauses are read, and the rank is 1 + (1 + (0 + (1 + 0))). The
    // numeral of 2 is put for v_0, which the universal does not bind, so the substitution reaches
    // both equations and changes the code; the fact says the rank stays, with the formula's
    // well-formedness discharged rather than assumed.
    val equation = "NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 1))"
    val formula = term(s"NUM_CODE 8 (NUM_PAIR 1 (NUM_CODE 7 (NUM_PAIR ($equation) (NUM_CODE 6 ($equation)))))")
    val rank = force(LogicError.lift(Term.app(term("NUM_RANK"), formula)))
    val clauses = Vector(Truth.RankEquality, Truth.RankNegation, Truth.RankImplication, Truth.RankUniversal)
      .map(fact)
    clauses.foreach(_.hypotheses shouldBe empty)
    rightOf(evaluate(rank, clauses)) shouldBe term("SUC (SUC (NUM_ADD ZERO (SUC ZERO)))")

    val kept = force(rules.specAll(fact(Truth.RankAtNumeral), List(term("0:num"), term("2:num"), formula))
      .flatMap(rules.mp(_, force(chain.language.wellFormedIn(formula)))))
    kept.hypotheses shouldBe empty
    kept.conclusion shouldBe proposition(s"NUM_RANK (NUM_SUBST_FORM 0 (NUM_NUMERAL 2) ($formula)) = NUM_RANK ($formula)")
  }

  "A numeral put for a variable" should "leave the variable it replaced free nowhere" in {
    // `!v_1. v_0 = v_1` has v_0 free. Asked about v_0 itself after the numeral of 2 is put for it,
    // the fact's second conjunct is `~(0 = 0)`, which reflexivity refutes, so v_0 is not free in
    // the instance: what the completeness induction needs to call an instance of a closed
    // universal closed. A lemma that said only "free after means free before" would not give
    // this, since v_0 was free before.
    val formula = term("NUM_CODE 8 (NUM_PAIR 1 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 1))))")
    val zero = term("0:num")
    val asked = force(rules.specAll(fact(Truth.FreeFormAtNumeral), List(zero, term("2:num"), formula))
      .flatMap(rules.mp(_, force(chain.language.wellFormedIn(formula))))
      .flatMap(rules.spec(zero, _)))
    asked.hypotheses shouldBe empty
    val freeAfter = proposition(s"NUM_FREE_FORM 0 (NUM_SUBST_FORM 0 (NUM_NUMERAL 2) ($formula))")
    val nowhere = force(for {
      held <- LogicError.lift(Kernel.assume(freeAfter))
      both <- rules.mp(asked, held)
      apart <- rules.conjElim2(both)
      absurd <- rules.notElim(apart, Kernel.refl(zero))
      out <- rules.notIntro(freeAfter, absurd)
    } yield out)
    nowhere.hypotheses shouldBe empty
    nowhere.conclusion shouldBe force(truth.logic.mkNot(freeAfter))
  }

  "A closed bounded formula" should "be provable in PA when it is true, with nothing assumed" in {
    // `!v_0. v_0 < 2 ==> v_0 = v_0`, the order's witness at 1. Every premise of the completeness
    // theorem is discharged here: well formed by the introduction rules, in the class by its
    // clause, closed by walking the code, and true by reading the universal at each value below 2.
    // What comes out is PA's proof of it, owing nothing, which no fact before this one gave for
    // any formula with a quantifier.
    val equation = "NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0))"
    val two = term("SUC (SUC ZERO)")
    val bound = term("NUM_NUMERAL (SUC (SUC ZERO))")
    val formula = term(s"NUM_ALL_BELOW 1 0 (NUM_NUMERAL (SUC (SUC ZERO))) ($equation)")
    val logic = truth.logic
    val language = chain.language
    val zero = term("0:num")
    val one = term("1:num")
    def holds(predicate: String, subject: Term): Term =
      force(LogicError.lift(Term.app(term(predicate), subject)))

    val isFormula = force(for {
      atZero <- language.fact(Language.TermVariable).flatMap(rules.spec(zero, _))
      boundIsTerm <- language.fact(Language.NumeralIsTerm).flatMap(rules.spec(two, _))
      equality <- language.fact(Language.FormulaEquality)
        .flatMap(rules.specAll(_, List(term("NUM_CODE 0 0"), term("NUM_CODE 0 0"))))
        .flatMap(rules.mp(_, atZero)).flatMap(rules.mp(_, atZero))
      out <- language.fact(Language.AllBelowFormula)
        .flatMap(rules.specAll(_, List(one, zero, bound, term(equation))))
        .flatMap(rules.mp(_, boundIsTerm)).flatMap(rules.mp(_, equality))
    } yield out)
    isFormula.conclusion shouldBe holds("NUM_FORM", formula)

    val clause = force(rules.specAll(fact(Truth.BoundedAllBelow), List(one, zero, bound, term(equation))))
    val (_, conditions) = force(Term.destEq(clause.conclusion).toRight("an equation"))
    val bounds = force(logic.destConj(conditions).map(_._2).flatMap(logic.destConj).map(_._1).toRight("a conjunction"))
    val (variableBound, numeralBound) = force(logic.destDisj(bounds).toRight("a disjunction"))
    val apart = force(chain.successor.distinct(one, zero))
    val isBounded = force(for {
      predicate <- logic.destExistsPredicate(numeralBound).toRight(NotOfForm("an existential", numeralBound))
      numeral <- rules.existsIntro(predicate, two, Kernel.refl(bound))
      either <- rules.disjIntro2(variableBound, numeral)
      body <- rules.specAll(fact(Truth.BoundedEquality), List(term("NUM_CODE 0 0"), term("NUM_CODE 0 0")))
        .flatMap(rules.eqTruthElim)
      rest <- rules.conjIntro(either, body)
      all <- rules.conjIntro(apart, rest)
      back <- Conv.sym(clause)
      out <- LogicError.lift(Kernel.eqMp(back, all))
    } yield out)
    isBounded.conclusion shouldBe holds("NUM_BOUNDED", formula)

    // closed: the abbreviations and the numeral unfolded into the code they name, which the walk reads
    val unfolding = force(Vector(Language.AllBelowCases, Language.LessCases, Language.ExistsCases,
      Language.NumeralAtZero, Language.NumeralAtSuccessor)
      .map(name => language.fact(name)).foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty))(
        (carried, next) => carried.flatMap(found => next.map(found :+ _)))
      .flatMap(Rewrite.Rule.all(logic, _)).flatMap(Rewrite.rewrite(_, formula)))
    val raw = force(Term.destEq(unfolding.conclusion).map(_._2).toRight("an equation"))
    val rawClosed = force(language.notFreeIn(raw))
    val negationHead = force(logic.mkNot(proposition("T"))) match {
      case App(head, _) => head
      case other => fail(s"not a negation: $other")
    }
    val isClosed = force(for {
      back <- Conv.sym(unfolding)
      w = Term.variable("w", numbers)
      atW <- rules.spec(w, rawClosed)
      freeHead <- LogicError.lift(Term.app(term("NUM_FREE_FORM"), w))
      moved <- Conv.apTerm(freeHead, back).flatMap(Conv.apTerm(negationHead, _))
      out <- LogicError.lift(Kernel.eqMp(moved, atW)).flatMap(rules.gen(w, _))
    } yield out)

    val e = Term.variable("e", Type.fun(numbers, numbers))
    val decided = force(rules.specAll(fact(Truth.ProvesBounded), List(e, formula))
      .flatMap(rules.mp(_, isFormula)).flatMap(rules.mp(_, isBounded)).flatMap(rules.mp(_, isClosed)))
    decided.hypotheses shouldBe empty

    // true: every value below 2 makes `v_0 = v_0` true, by reflexivity of its value
    val reading = force(rules.specAll(fact(Truth.TrueAllBelowNumeral), List(e, one, zero, two, term(equation)))
      .flatMap(rules.mp(_, apart)))
    val (_, everyValue) = force(Term.destEq(reading.conclusion).toRight("an equation"))
    val m = Term.variable("m", numbers)
    val isTrue = force(for {
      predicate <- logic.destForallPredicate(everyValue).toRight(NotOfForm("a universal", everyValue))
      atM <- LogicError.lift(Term.app(predicate, m)).flatMap(t => Term.betaReduce(t).toRight(NotOfForm("a redex", t)))
      sidesOfImp <- logic.destImp(atM).toRight(NotOfForm("an implication", atM))
      below = sidesOfImp._1
      environment = sidesOfImp._2 match { case App(_, env) => env; case other => other }
      clauseAt <- rules.specAll(fact(Truth.TrueEquality), List(environment, term("NUM_CODE 0 0"), term("NUM_CODE 0 0")))
      valueSide = force(Term.destEq(clauseAt.conclusion).map(_._2).flatMap(Term.destEq).map(_._1).toRight("a value"))
      bodyHolds <- Conv.sym(clauseAt).flatMap(c => LogicError.lift(Kernel.eqMp(c, Kernel.refl(valueSide))))
      every <- rules.disch(below, bodyHolds).flatMap(rules.gen(m, _))
      back <- Conv.sym(reading)
      out <- LogicError.lift(Kernel.eqMp(back, every))
    } yield out)
    val proved = force(rules.conjElim1(decided).flatMap(rules.mp(_, isTrue)))
    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe holds("NUM_PROV", formula)
  }

  "A closed Sigma-1 sentence" should "be provable in PA when it is true, with nothing assumed" in {
    // `?v_0. v_0 = S 0`, one existential over an equation. In the class at one existential by its two
    // clauses, closed by walking the code, and true at the witness 1. What comes out is PA's proof
    // of a sentence with an unbounded quantifier, owing nothing: the step of the induction goes to
    // the instance `1 = S 0`, which the bounded completeness proves, and introduces the existential.
    val logic = truth.logic
    val language = chain.language
    val zero = term("0:num")
    val variable = term("NUM_CODE 0 0")
    val one = term("NUM_CODE 2 (NUM_CODE 1 0)")
    val body = term("NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 2 (NUM_CODE 1 0)))")
    val sentence = term("NUM_EXISTS 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 2 (NUM_CODE 1 0))))")
    val count = term("SUC ZERO")
    def holds(predicate: String, subject: Term): Term =
      force(LogicError.lift(Term.app(term(predicate), subject)))

    val bodyIsFormula = force(for {
      atZero <- language.fact(Language.TermVariable).flatMap(rules.spec(zero, _))
      zeroTerm <- language.fact(Language.TermZero)
      oneTerm <- language.fact(Language.TermSuccessor).flatMap(rules.spec(term("NUM_CODE 1 0"), _))
        .flatMap(rules.mp(_, zeroTerm))
      out <- language.fact(Language.FormulaEquality).flatMap(rules.specAll(_, List(variable, one)))
        .flatMap(rules.mp(_, atZero)).flatMap(rules.mp(_, oneTerm))
    } yield out)
    val bodyBounded = force(rules.specAll(fact(Truth.BoundedEquality), List(variable, one))
      .flatMap(rules.eqTruthElim))
    val bottom = force(rules.conjIntro(bodyIsFormula, bodyBounded).flatMap(both =>
      rules.spec(body, fact(Truth.SigmaZero)).flatMap(Conv.sym)
        .flatMap(back => LogicError.lift(Kernel.eqMp(back, both)))))
    bottom.conclusion shouldBe proposition(s"NUM_SIGMA ZERO ($body)")

    val clause = force(rules.specAll(fact(Truth.SigmaSuccessor), List(term("ZERO"), sentence)))
    val (_, witnessed) = force(Term.destEq(clause.conclusion).toRight("an equation"))
    val inClass = force(for {
      outer <- logic.destExistsPredicate(witnessed).toRight(NotOfForm("an existential", witnessed))
      atIndex <- LogicError.lift(Term.app(outer, zero)).flatMap(Conv.betaNormalise)
      inner = force(Term.destEq(atIndex.conclusion).map(_._2).toRight("an equation"))
      innerPredicate <- logic.destExistsPredicate(inner).toRight(NotOfForm("an existential", inner))
      both <- rules.conjIntro(Kernel.refl(sentence), bottom)
      atBody <- rules.existsIntro(innerPredicate, body, both)
      atBoth <- rules.existsIntro(outer, zero, atBody)
      back <- Conv.sym(clause)
      out <- LogicError.lift(Kernel.eqMp(back, atBoth))
    } yield out)
    inClass.conclusion shouldBe holds("NUM_SIGMA (SUC ZERO)", sentence)

    // closed: the abbreviation unfolded into the code it names, which the walk reads
    val unfolding = force(language.fact(Language.ExistsCases).flatMap(rules.specAll(_, List(zero, body))))
    val raw = force(Term.destEq(unfolding.conclusion).map(_._2).toRight("an equation"))
    val rawClosed = force(language.notFreeIn(raw))
    val negationHead = force(logic.mkNot(proposition("T"))) match {
      case App(head, _) => head
      case other => fail(s"not a negation: $other")
    }
    val isClosed = force(for {
      back <- Conv.sym(unfolding)
      w = Term.variable("w", numbers)
      atW <- rules.spec(w, rawClosed)
      freeHead <- LogicError.lift(Term.app(term("NUM_FREE_FORM"), w))
      moved <- Conv.apTerm(freeHead, back).flatMap(Conv.apTerm(negationHead, _))
      out <- LogicError.lift(Kernel.eqMp(moved, atW)).flatMap(rules.gen(w, _))
    } yield out)

    // true: at the witness 1 both sides of the body are worth 1
    val e = Term.variable("e", Type.fun(numbers, numbers))
    val reading = force(rules.specAll(fact(Truth.TrueExists), List(e, zero, body)))
    val (_, someValue) = force(Term.destEq(reading.conclusion).toRight("an equation"))
    val isTrue = force(for {
      predicate <- logic.destExistsPredicate(someValue).toRight(NotOfForm("an existential", someValue))
      atOne <- LogicError.lift(Term.app(predicate, count)).flatMap(Conv.betaNormalise)
      instance = force(Term.destEq(atOne.conclusion).map(_._2).toRight("an equation"))
      zeroIsZero <- rules.eqTruthIntro(Kernel.refl(zero))
      evaluated = evaluate(instance, Vector(fact(Truth.TrueEquality), fact(Truth.ValueVariable),
        fact(Truth.ValueSuccessor), fact(Truth.ValueZero), zeroIsZero))
      _ = rightOf(evaluated) shouldBe proposition("SUC ZERO = SUC ZERO")
      atInstance <- Conv.sym(evaluated).flatMap(back => LogicError.lift(Kernel.eqMp(back, Kernel.refl(count))))
      some <- rules.existsIntro(predicate, count, atInstance)
      back <- Conv.sym(reading)
      out <- LogicError.lift(Kernel.eqMp(back, some))
    } yield out)

    val proved = force(rules.specAll(fact(Truth.ProvesSigma), List(count, e, sentence))
      .flatMap(rules.mp(_, inClass)).flatMap(rules.mp(_, isClosed)).flatMap(rules.mp(_, isTrue)))
    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe holds("NUM_PROV", sentence)
  }

  "A universal below a numeral" should "be true where its body is true at every value below" in {
    // NUM_ALL_BELOW 1 0 3 p, the order's witness apart from the index by 1 and 0 differing, which
    // is the condition the fact asks for and is discharged here rather than assumed.
    val e = Term.variable("e", Type.fun(numbers, numbers))
    val body = term("NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0))")
    val apart = force(chain.successor.distinct(term("1:num"), term("0:num")))
    val read = force(rules.specAll(fact(Truth.TrueAllBelowNumeral), List(e, term("1:num"), term("0:num"),
      term("3:num"), body)).flatMap(rules.mp(_, apart)))
    read.hypotheses shouldBe empty
    read.conclusion shouldBe proposition(
      s"NUM_TRUE (NUM_ALL_BELOW 1 0 (NUM_NUMERAL 3) ($body)) (e:num -> num) = " +
        s"(!m:num. m < 3 ==> NUM_TRUE ($body) (\\j:num. COND (j = 0) m ((e:num -> num) j)))")
    // and the order's code alone, read at the variable's value
    val less = force(rules.specAll(fact(Truth.TrueLessNumeral), List(e, term("1:num"), term("0:num"),
      term("3:num"))).flatMap(rules.mp(_, apart)))
    less.hypotheses shouldBe empty
    less.conclusion shouldBe proposition(
      "NUM_TRUE (NUM_LESS 1 (NUM_CODE 0 0) (NUM_NUMERAL 3)) (e:num -> num) = (e:num -> num) 0 < 3")
  }

  "The graph of the triangle" should "hold where the value is the triangle, fail elsewhere" in {
    val graph = fact(Truth.TriangleGraphTrue)
    val arithmetic = Vector(
      force(chain.numbering.fact(Numbering.TriangleAtZero)),
      force(chain.numbering.fact(Numbering.TriangleAtSuccessor)),
      force(chain.peano.fact(Peano.ZeroPlus)),
      force(chain.peano.fact(Peano.AddAtSuccessor)),
      force(chain.peano.fact(Peano.AddAtZero)))

    // At zero everywhere: `0 = NUM_TRI 0`, which is the triangle's first equation.
    val atZero = force(rules.spec(term("\\k:num. ZERO"), graph))
    val zeroReading = evaluate(rightOf(atZero), arithmetic)
    rightOf(zeroReading) shouldBe proposition("ZERO = ZERO")
    val holds = force(Conv.trans(atZero, zeroReading).flatMap(Conv.sym)
      .flatMap(e => LogicError.lift(Kernel.eqMp(e, Kernel.refl(term("ZERO"))))))
    holds.hypotheses shouldBe empty
    holds.conclusion shouldBe proposition("NUM_TRUE NUM_TRI_GRAPH (\\k:num. ZERO)")

    // At two everywhere: `2 = NUM_TRI 2`, and the triangle of two is three. This is the direction
    // that spends the uniqueness half of the representation: the graph is refuted, not merely
    // left unproved.
    val two = "SUC (SUC ZERO)"
    val atTwo = force(rules.spec(term(s"\\k:num. $two"), graph))
    val twoReading = evaluate(rightOf(atTwo), arithmetic)
    rightOf(twoReading) shouldBe proposition(s"$two = SUC ($two)")
    val claim = proposition(s"NUM_TRUE NUM_TRI_GRAPH (\\k:num. $two)")
    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val reached = force(Conv.trans(atTwo, twoReading)
      .flatMap(e => LogicError.lift(Kernel.eqMp(e, assumed))))
    // Two successors taken off both sides leave `0 = SUC 0`. `Successor.distinct` would say it in
    // one line, and it reads numerals rather than the successor form the triangle unfolds into.
    val injective = force(chain.naturals.fact(Natural.SuccessorInjective))
    def peel(equation: Kernel.Thm): Kernel.Thm = equation.conclusion match {
      case App(App(_, App(_, left)), App(_, right)) =>
        force(rules.specAll(injective, List(left, right)).flatMap(rules.mp(_, equation)))
      case other => fail(s"not an equation between successors: $other")
    }
    val bottom = peel(peel(reached))
    val never = force(
      chain.naturals.fact(Natural.SuccessorNotZero).flatMap(rules.spec(term("ZERO"), _)))
    val refuted = force(
      Conv.sym(bottom).flatMap(rules.notElim(never, _)).flatMap(rules.notIntro(claim, _)))
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"~(NUM_TRUE NUM_TRI_GRAPH (\\k:num. $two))")
  }

  "The value of a numeral" should "be its number at an environment that says nothing about it" in {
    // `NUM_VALUE_NUMERAL` is general, so it is true of an empty case; this reads it at a number
    // and an environment chosen so that the answer could only come from the numeral.
    val read = force(rules.specAll(fact(Truth.ValueNumeral),
      List(term("\\k:num. SUC k"), term("SUC (SUC ZERO)"))))
    read.conclusion shouldBe
      proposition("NUM_VALUE (NUM_NUMERAL (SUC (SUC ZERO))) (\\k:num. SUC k) = SUC (SUC ZERO)")
  }

  /* ------------------------------------------------------- where truth meets provability */

  "A closed term" should "be proved equal to the numeral of its value, with nothing assumed" in {
    // `NUM_PROV_VALUE` is an implication about every closed term, and an implication whose
    // antecedents nobody can discharge is a theorem about nothing. This discharges both at the code
    // of `S 0 + S 0`, from the facts that build a term and a closed term, and reads the answer.
    val one = "NUM_CODE 2 (NUM_CODE 1 0)"
    val sum = s"NUM_CODE 3 (NUM_PAIR ($one) ($one))"
    val language = chain.language
    def lf(name: String): Kernel.Thm = force(language.fact(name))
    val oneIsTerm = force(rules.spec(term("NUM_CODE 1 0"), lf(Language.TermSuccessor))
      .flatMap(rules.mp(_, lf(Language.TermZero))))
    val oneIsClosed = force(rules.spec(term("NUM_CODE 1 0"), lf(Language.ClosedSuccessor))
      .flatMap(rules.mp(_, lf(Language.ClosedZero))))
    val sumIsTerm = force(rules.specAll(lf(Language.TermSum), List(term(one), term(one)))
      .flatMap(rules.mp(_, oneIsTerm)).flatMap(rules.mp(_, oneIsTerm)))
    val sumIsClosed = force(rules.specAll(lf(Language.ClosedSum), List(term(one), term(one)))
      .flatMap(rules.mp(_, oneIsClosed)).flatMap(rules.mp(_, oneIsClosed)))

    val proved = force(
      rules.specAll(fact(Truth.ProvesValue), List(term("\\k:num. k"), term(sum)))
        .flatMap(rules.mp(_, sumIsTerm))
        .flatMap(rules.mp(_, sumIsClosed)))
    proved.hypotheses shouldBe empty
    val read = evaluate(proved.conclusion, Vector(
      fact(Truth.ValueSum), fact(Truth.ValueSuccessor), fact(Truth.ValueZero)))
    rightOf(read) shouldBe proposition(
      s"NUM_PROV (NUM_CODE 5 (NUM_PAIR ($sum) (NUM_NUMERAL (NUM_ADD (SUC ZERO) (SUC ZERO)))))")

    // And the equation half at the same term: `S 0 + S 0 = S 0 + S 0` is true at every
    // environment, so it is provable, with the truth discharged rather than assumed.
    val holds = force(
      rules.specAll(fact(Truth.TrueEquality), List(term("\\k:num. k"), term(sum), term(sum)))
        .flatMap(Conv.sym)
        .flatMap(e => LogicError.lift(Kernel.eqMp(e, Kernel.refl(term(
          s"NUM_VALUE ($sum) (\\k:num. k)"))))))
    val equation = force(
      rules.specAll(fact(Truth.ProvesTrueEquation), List(term("\\k:num. k"), term(sum), term(sum)))
        .flatMap(rules.mp(_, sumIsTerm)).flatMap(rules.mp(_, sumIsClosed))
        .flatMap(rules.mp(_, sumIsTerm)).flatMap(rules.mp(_, sumIsClosed))
        .flatMap(rules.mp(_, holds)))
    equation.hypotheses shouldBe empty
    equation.conclusion shouldBe proposition(s"NUM_PROV (NUM_CODE 5 (NUM_PAIR ($sum) ($sum)))")

    // And the other half: `S 0 + S 0 = S 0` is false, so its negation is provable. The falsity is
    // derived from the clauses and the naturals, not assumed: a premise nobody can discharge would
    // make the provability a statement about nothing.
    val denied = s"NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR ($sum) ($one)))"
    val fails = proposition(s"NUM_TRUE ($denied) (\\k:num. k)")
    val reading = evaluate(fails, Vector(
      fact(Truth.TrueNegation), fact(Truth.TrueEquality), fact(Truth.ValueSum),
      fact(Truth.ValueSuccessor), fact(Truth.ValueZero),
      force(chain.peano.fact(Peano.AddAtSuccessor)), force(chain.peano.fact(Peano.AddAtZero))))
    rightOf(reading) shouldBe proposition("~(SUC (SUC ZERO) = SUC ZERO)")
    val equal = proposition("SUC (SUC ZERO) = SUC ZERO")
    val peeled = force(
      rules.specAll(force(chain.naturals.fact(Natural.SuccessorInjective)),
        List(term("SUC ZERO"), term("ZERO")))
        .flatMap(rules.mp(_, force(LogicError.lift(Kernel.assume(equal))))))
    val falsity = force(
      chain.naturals.fact(Natural.SuccessorNotZero).flatMap(rules.spec(term("ZERO"), _))
        .flatMap(rules.notElim(_, peeled))
        .flatMap(rules.notIntro(equal, _))
        .flatMap(apart => Conv.sym(reading).flatMap(e => LogicError.lift(Kernel.eqMp(e, apart)))))
    falsity.hypotheses shouldBe empty

    val refuted = force(
      rules.specAll(fact(Truth.ProvesFalseEquation), List(term("\\k:num. k"), term(sum), term(one)))
        .flatMap(rules.mp(_, sumIsTerm)).flatMap(rules.mp(_, sumIsClosed))
        .flatMap(rules.mp(_, oneIsTerm)).flatMap(rules.mp(_, oneIsClosed))
        .flatMap(rules.mp(_, falsity)))
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"NUM_PROV ($denied)")
  }

  /**
   * `~(0 = 0)` is a closed formula with no quantifier and it is false, so `NUM_PROV_GROUND` refutes
   * it: the negation case and the equation case met at once, with both of the theorem's conditions
   * discharged here rather than assumed. What comes back is `NUM_PROV ~~(0 = 0)`.
   */
  it should "refute a false closed formula without a quantifier, with both conditions discharged" in {
    val language = chain.language
    val zero = term("NUM_CODE 1 0")
    val equation = term("NUM_CODE 5 (NUM_PAIR (NUM_CODE 1 0) (NUM_CODE 1 0))")
    val denial = term("NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 1 0) (NUM_CODE 1 0)))")
    val zeroTerm = force(language.fact(Language.TermZero))
    val zeroClosed = force(language.fact(Language.ClosedZero))
    val equationForm = force(rules.specAll(force(language.fact(Language.FormulaEquality)), List(zero, zero))
      .flatMap(rules.mp(_, zeroTerm)).flatMap(rules.mp(_, zeroTerm)))
    val denialForm = force(rules.spec(equation, force(language.fact(Language.FormulaNegation)))
      .flatMap(rules.mp(_, equationForm)))
    val equationGround = force(for {
      clause <- rules.specAll(fact(Truth.GroundEquality), List(zero, zero))
      back <- Conv.sym(clause)
      closed <- rules.conjIntro(zeroClosed, zeroClosed)
      out <- LogicError.lift(Kernel.eqMp(back, closed))
    } yield out)
    val denialGround = force(for {
      clause <- rules.spec(equation, fact(Truth.GroundNegation))
      back <- Conv.sym(clause)
      out <- LogicError.lift(Kernel.eqMp(back, equationGround))
    } yield out)

    val e = Term.variable("e", Type.fun(numbers, numbers))
    val decided = force(rules.specAll(fact(Truth.ProvesGround), List(e, denial))
      .flatMap(rules.mp(_, denialForm)).flatMap(rules.mp(_, denialGround)))
    // the denial is false at every environment: `0 = 0` is true there
    val equationTrue = force(for {
      clause <- rules.specAll(fact(Truth.TrueEquality), List(e, zero, zero))
      back <- Conv.sym(clause)
      out <- LogicError.lift(Kernel.eqMp(back, Kernel.refl(term("NUM_VALUE (NUM_CODE 1 0) (e:num -> num)"))))
    } yield out)
    val denialTrue = proposition("NUM_TRUE (NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 1 0) (NUM_CODE 1 0)))) (e:num -> num)")
    val denialFalse = force(for {
      clause <- rules.specAll(fact(Truth.TrueNegation), List(e, equation))
      assumed <- LogicError.lift(Kernel.assume(denialTrue))
      opened <- LogicError.lift(Kernel.eqMp(clause, assumed))
      absurd <- rules.notElim(opened, equationTrue)
      out <- rules.notIntro(denialTrue, absurd)
    } yield out)
    val refuted = force(rules.conjElim2(decided).flatMap(rules.mp(_, denialFalse)))
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(
      "NUM_PROV (NUM_CODE 6 (NUM_CODE 6 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 1 0) (NUM_CODE 1 0)))))")
  }
}
