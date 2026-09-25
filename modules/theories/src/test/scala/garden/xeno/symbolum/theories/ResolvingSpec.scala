package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Resolution reasoned about rather than run, and what that first theorem cost.
 *
 * The assertions that carry the file are these, and none of them is "this is provable".
 *
 * **Which of resolution's four conditions the conclusion spends.** Two, and a reader of the
 * definition would not have guessed which two: the ones saying the pivot **occurs** are not used,
 * and the ones saying every other literal carries into the resolvent are. That is the same question
 * `DomainTheorySpec` asks of its four domain axioms, asked of a definition instead.
 *
 * **What it costs.** One axiom on the step, `SELECT`, spent on the case split over `a x`, and
 * **none at all** on the empty clause. The pair is the measurement: a file where everything cost one
 * axiom would say nothing about where the classical step is.
 *
 * **What it declares, since it became a link on 2026-09-25.** Four constants, all definitions, and
 * no axiom, asserted as a difference against the theory below it so that a fifth goes red.
 *
 * **That a lower bound can be written here, which is the measurement the link was made for.**
 * Haken's theorem for the pigeonhole principle is stated over the four constants and has to
 * elaborate with nothing free in it. The statement's hypotheses are then shown to be ones something
 * satisfies, at the smallest instance, because a lower bound whose hypotheses nothing meets is true
 * and says nothing, and a statement that merely parses would pass everything else in this file.
 */
class ResolvingSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard
  private lazy val resolving: Resolving = chain.resolving

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private def fact(name: String): Kernel.Thm = force(resolving.fact(name))

  private val choice: Set[Term] =
    Set(Chain.standard.classical.axiom(Classical.Choice).fold(error => fail(error.toString), identity).conclusion)

  "One resolution step" should "be sound, and the statement should be the one a reader checks" in {
    val theorem = fact(Resolving.StepSound)
    theorem.hypotheses shouldBe empty

    // Read back rather than described. The two halves a reader compares with resolution are that a
    // literal other than the pivot carries into the resolvent, and that the resolvent is satisfied.
    val printed = resolving.show(theorem.conclusion)
    printed should include("<")
    printed should include("==>")
    withClue(s"the statement is $printed: ") {
      printed.count(_ == '?') should be >= 3
    }
  }

  it should "cost exactly the choice axiom, which is what the case split is" in {
    // The same axiom `logic.Propositional` spends and for the same reason: deciding that a boolean
    // is one of two things is classical here. Asserted as an equality of the set rather than as a
    // ceiling, so a derivation that quietly starts spending something else goes red.
    Derivation.axiomsOf(fact(Resolving.StepSound)) shouldBe choice
  }

  "The two conditions saying the pivot occurs" should "not be spent, which is the finding" in {
    // The corollary carries resolution's four conditions; the theorem it is derived from carries
    // two. So the occurrence conditions are assumed and never used, and this is the assertion that
    // says so: the corollary's statement has two more antecedents than the theorem's, and both
    // conclude the same thing.
    val step = fact(Resolving.StepSound)
    val resolvent = fact(Resolving.StepSoundOfResolvent)

    def antecedents(theorem: Kernel.Thm): Int = {
      val logic = resolving.logic
      def peel(term: Term, seen: Int): Int =
        logic.destImp(term) match {
          case Some((_, rest)) => peel(rest, seen + 1)
          case None => seen
        }
      peel(force(Logic.stripForall(theorem.conclusion))._2, 0)
    }

    antecedents(step) shouldBe 4
    antecedents(resolvent) shouldBe 6

    // And the same conclusion under the same number of binders, so the corollary really is the
    // theorem with two conditions in front and not a claim about something else.
    force(Logic.stripForall(step.conclusion))._1.length shouldBe
      force(Logic.stripForall(resolvent.conclusion))._1.length
    resolvent.hypotheses shouldBe empty
  }

  "The empty clause" should "be satisfied by nothing, and cost MORE than the step does" in {
    val theorem = fact(Resolving.EmptyUnsatisfiable)
    theorem.hypotheses shouldBe empty

    // **The measurement, and it is the opposite way round from the guess this test first made.**
    //
    // The step above has the classical case split in it and costs **one** axiom, choice. This has
    // no case split at all and costs **two**, choice and infinity, because it is the only one of the
    // two that spends a fact about `num`: `Peano.NUM_NOT_LT_ZERO`, and `num` is a defined type
    // carved out of an infinite one, so every lemma about it carries the naturals' two.
    //
    // Read together the pair says where the cost of this development actually is, and it is not
    // where the reasoning looks hardest: the step never looks inside `num` at all. `NUM_LT` occurs
    // in its statement as a constant that is carried around and never unfolded, which is why a
    // theorem full of arithmetic notation spends no arithmetic.
    val spent = Derivation.axiomsOf(theorem)
    val stepSpends = Derivation.axiomsOf(fact(Resolving.StepSound))

    withClue(s"at ${Derivation.size(theorem)} inferences: ") {
      spent should have size 2
      spent should contain allElementsOf choice
    }
    stepSpends shouldBe choice
    withClue("the step must cost strictly less, or the pair measures nothing: ") {
      (spent -- stepSpends) should have size 1
    }
  }

  "A whole derivation" should "be sound, which is what makes this a proof system" in {
    val theorem = fact(Resolving.DerivationSound)
    theorem.hypotheses shouldBe empty

    // The shape a reader checks: two antecedents, the inputs satisfied and every step justified,
    // and a conclusion about every step rather than about one.
    val logic = resolving.logic
    def antecedents(term: Term, seen: Int): Int =
      logic.destImp(term) match {
        case Some((_, rest)) => antecedents(rest, seen + 1)
        case None => seen
      }
    antecedents(force(Logic.stripForall(theorem.conclusion))._2, 0) shouldBe 2
  }

  it should "cost what the naturals cost, because the induction is a fact about `num`" in {
    // The pair that says where the cost is. `RES_STEP_SOUND` carries the classical case split and
    // spends one axiom; this carries strong induction and the transitivity of the order, both facts
    // about `num`, and spends two. The reasoning did not get harder between them: the difference is
    // entirely that one of the two looks inside `num` and the other never does.
    val spent = Derivation.axiomsOf(fact(Resolving.DerivationSound))
    val step = Derivation.axiomsOf(fact(Resolving.StepSound))

    spent should have size 2
    spent should contain allElementsOf choice
    step shouldBe choice
    (spent -- step) should have size 1
  }

  "A derivation reaching the empty clause" should "say that NOTHING satisfies the inputs" in {
    // The statement `modules/sat` makes every time it answers unsatisfiable, and which nothing in
    // this repository could state until now.
    val theorem = fact(Resolving.Refutes)
    theorem.hypotheses shouldBe empty

    // The half that carries the claim: the assignment is quantified **inside** the negation, so the
    // conclusion is about every assignment and not about one. Without that this would be
    // `RES_SOUND` read at a point, which is a much weaker thing wearing the same words.
    val logic = resolving.logic
    val body = force(Logic.stripForall(theorem.conclusion))._2
    def conclusionOf(term: Term): Term = logic.destImp(term).map(pair => conclusionOf(pair._2)).getOrElse(term)
    val negated = logic
      .destNot(conclusionOf(body))
      .getOrElse(fail(s"the conclusion must be a negation: ${resolving.show(conclusionOf(body))}"))

    withClue(s"what is denied must itself be an existential over the assignment: ${resolving.show(negated)} ") {
      logic.destExistsPredicate(negated) should not be empty
    }

    // And the assignment must not also be bound outside, or the statement is about one after all.
    force(Logic.stripForall(theorem.conclusion))._1.map(_.ty) should not contain
      Type.fun(force(Logic.stripForall(theorem.conclusion))._1.last.ty, Type.Bool)
  }

  "This development" should "add the constants it names, all of them definitions, and no axiom" in {
    // It declared nothing until 2026-09-25 and this test said so; the difference is taken against the
    // link below it rather than against the widest signature, which this now is.
    val below = chain.continuity.theory
    resolving.theory.axioms shouldBe below.axioms
    (resolving.theory.constants.keySet -- below.constants.keySet) shouldBe
      Set(Resolving.Satisfied, Resolving.JustifiedName, Resolving.Refutation, Resolving.Width)
    resolving.theory.typeOperators.keySet shouldBe below.typeOperators.keySet
    resolving.definitions.keySet shouldBe
      Set(Resolving.Satisfied, Resolving.JustifiedName, Resolving.Refutation, Resolving.Width)
  }

  it should "state every fact over the constants as it is written, with nothing assumed" in {
    Resolving.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe force(resolving.proposition(text))
        fact(name).hypotheses shouldBe empty
      }
    }
    // The five written-out soundness theorems and the seven over the names, and nothing else.
    resolving.facts.keySet shouldBe Resolving.Statements.map(_._1).toSet ++ Set(
      Resolving.StepSound, Resolving.StepSoundOfResolvent, Resolving.EmptyUnsatisfiable,
      Resolving.DerivationSound, Resolving.Refutes
    )
  }

  "The statements" should "need nothing the chain does not already have" in {
    // The measurement that decided the shape of this development, kept as an assertion. The card
    // that asked for it assumed the objects would have to be arithmetised, as `Provability` codes a
    // derivation of PA; they do not, because proof complexity quantifies over derivations and does
    // not talk about itself. If this ever stops reading, the decision is back open.
    val statements = Vector(
      "!x:num -> bool. !y:num -> num. !z:num -> num -> num. !u:num -> num -> bool. !v:num. " +
        "(?w:num. w < y v /\\ x (z v w) = u v w) ==> 0 <= y v",
      "!x:num -> num. !y:num -> num -> num. !z:num -> num -> bool. !u:num. !v:num. !w:bool. " +
        "(?x1:num. x1 < x u /\\ y u x1 = v /\\ z u x1 = w) ==> 0 <= x u"
    )

    statements.foreach(text => withClue(s"$text: ") { chain.widest.proposition(text).isRight shouldBe true })
  }

  /* ----------------------------------------------------------------- the width */

  "The width" should "cost what the soundness of a derivation costs" in {
    // Choice through the case split `COND` is read with, and infinity through every fact about
    // `num`. An equality against `RES_SOUND`'s set rather than a count, so a derivation that began to
    // spend eta, or one of the reals' sixteen, would go red here.
    val naturals = Derivation.axiomsOf(fact(Resolving.DerivationSound))
    Vector(Resolving.WidthBound, Resolving.WidthAttained, Resolving.WidthLeast).foreach(name =>
      withClue(s"$name: ") { Derivation.axiomsOf(fact(name)) shouldBe naturals })
  }

  it should "be pinned by its bound and its attainment together, which neither is alone" in {
    // What would make each of the two vacuous is a different function, so each is the guard for the
    // other. A constant `ZERO` satisfies the attainment, since its left disjunct is `ZERO`, and not
    // the bound. The sum of the lengths satisfies the bound and not the attainment. Read together
    // they say the width is ONE of the lengths, or zero, and at least every one of them: the largest.
    // Asserted on the statements' shape, because what separates them is which side of the order the
    // width stands on.
    val logic = resolving.logic
    def headOf(term: Term): Option[String] = term match {
      case App(fn, _) => headOf(fn)
      case Const(name, _) => Some(name)
      case _ => None
    }

    // The bound: a length on the left of the order and the width on the right.
    val bound = force(Logic.stripForall(fact(Resolving.WidthBound).conclusion))._2
    val (_, boundConclusion) = logic.destImp(bound).getOrElse(fail("the bound must be an implication"))
    boundConclusion match {
      case App(App(order, _), width) =>
        headOf(order) shouldBe Some("NUM_LE")
        headOf(width) shouldBe Some(Resolving.Width)
      case other => fail(s"not an order: ${resolving.show(other)}")
    }

    // The attainment: the width is zero, or it equals a length.
    val attained = force(Logic.stripForall(fact(Resolving.WidthAttained).conclusion))._2
    val (zero, clause) = logic.destDisj(attained).getOrElse(fail("the attainment must be a disjunction"))
    val (width, nothing) = Term.destEq(zero).getOrElse(fail("the left disjunct must be an equation"))
    headOf(width) shouldBe Some(Resolving.Width)
    nothing shouldBe force(resolving.term("0:num"))
    logic.destExistsPredicate(clause) should not be empty
  }

  /* --------------------------------------------------- the refutation, by name */

  "A refutation read through the names" should "cost exactly what the written-out one costs" in {
    // Derived from `RES_REFUTES` by opening each definition once, so it rests on nothing that one
    // does not. A named statement proved some other way would read the same and could spend more.
    Derivation.axiomsOf(fact(Resolving.RefutationUnsatisfiable)) shouldBe
      Derivation.axiomsOf(fact(Resolving.Refutes))
  }

  /* ---------------------------------------------------------- the lower bound */

  /** Variable `p * n + h`, the pigeon `p` in the hole `h`, which is injective for `h < n`. */
  private def hole(pigeon: String, at: String): String = s"NUM_ADD (NUM_MUL $pigeon n) $at"

  /**
   * Clause `j` of the derivation is one of the clauses of the pigeonhole principle for `n + 1`
   * pigeons and `n` holes, as a set of literals: the pigeon clause of some `p <= n`, every literal
   * `p` in some hole and every hole present; or the hole clause of some `p < q <= n` at a hole `h`,
   * both negative literals present and nothing else.
   *
   * A set rather than a list because a clause is one, so both directions of the membership are
   * written; the one saying nothing else occurs is what stops a clause being a weakening, which the
   * principle does not contain.
   */
  private val PigeonholeClause: String =
    "(?p:num. NUM_LE p n /\\ " +
      s"(!i:num. NUM_LT i (k j) ==> ?h:num. NUM_LT h n /\\ v j i = ${hole("p", "h")} /\\ s j i = T) /\\ " +
      s"(!h:num. NUM_LT h n ==> ?i:num. NUM_LT i (k j) /\\ v j i = ${hole("p", "h")} /\\ s j i = T)) \\/ " +
      "(?p:num. ?q:num. ?h:num. NUM_LT p q /\\ NUM_LE q n /\\ NUM_LT h n /\\ " +
      s"(!i:num. NUM_LT i (k j) ==> (v j i = ${hole("p", "h")} \\/ v j i = ${hole("q", "h")}) /\\ s j i = F) /\\ " +
      s"(?i:num. NUM_LT i (k j) /\\ v j i = ${hole("p", "h")} /\\ s j i = F) /\\ " +
      s"(?i:num. NUM_LT i (k j) /\\ v j i = ${hole("q", "h")} /\\ s j i = F))"

  /** Every refutation of the pigeonhole principle for `n + 1` pigeons satisfies `conclusion`. */
  private def everyRefutation(conclusion: String): String =
    "!n:num. !k:num->num. !v:num->num->num. !s:num->num->bool. !inputs:num. !m:num. " +
      s"(!j:num. NUM_LT j inputs ==> $PigeonholeClause) ==> " +
      s"RES_REFUTATION k v s inputs m ==> $conclusion"

  /**
   * Haken's theorem, in the form a reader checks against the literature: some `c > 0` makes every
   * refutation of the pigeonhole principle at least `2^(n DIV c)` steps long.
   *
   * Haken, "The intractability of resolution", Theoretical Computer Science 39 (1985): resolution
   * refutations of the pigeonhole principle for `n + 1` pigeons have size `2^(Omega(n))`. The
   * constant is existential here because the statement is about the order of growth; a `c` large
   * enough also covers the small `n` below the threshold of the asymptotic statement, where
   * `n DIV c` is zero and the bound is the one step every refutation has.
   *
   * **Stated and not proved.** What this file establishes is that it can be written, which is the
   * question Mycelium `edc1f509` asked first. The lower bound proved over these names since
   * 2026-09-25 is `Pigeonhole.RES_PHP_DERIVED_WIDTH`, on the width of a derived clause; size from
   * width is Ben-Sasson and Wigderson's step, and it is not taken anywhere here.
   */
  private val Haken: String =
    "?c:num. NUM_LT 0 c /\\ (" +
      everyRefutation("NUM_LE (NUM_POW (SUC (SUC 0)) (NUM_DIV n c)) m") + ")"

  "A lower bound on refutations" should "be statable over the names, with nothing free in it" in {
    // The measurement `edc1f509` put first. A derivation did not have to become a number: the
    // quantifier over every refutation is three universally quantified functions and two numbers.
    val statement = force(resolving.proposition(Haken))
    Term.freeVariables(statement) shouldBe empty

    // Nothing free is necessary and not enough: an unknown letter-initial name parses as a free
    // variable, so the check above is what catches a misspelt constant, and this is what says the
    // statement names the ones it means.
    constantsIn(statement) should contain allOf (Resolving.Refutation, "NUM_POW", "NUM_DIV", "NUM_MUL", "NUM_ADD")
  }

  it should "have hypotheses something satisfies, at the smallest instance" in {
    // A bound whose hypotheses nothing meets is a true sentence about nothing, and it would pass the
    // test above. At `n = 0` there is one pigeon and no hole, so its pigeon clause is the empty
    // clause: the derivation of one step, `k = \j. 0`, whose only input is that clause, meets both
    // hypotheses. They are derived here, with nothing assumed.
    val rules = resolving.logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val zero = force(resolving.term("0:num"))
    val one = force(resolving.term("SUC 0"))
    val lengths = force(resolving.term("\\j:num. 0", Type.fun(numbers, numbers)))
    val variables = force(resolving.term("\\j:num. \\i:num. 0", Type.fun(numbers, Type.fun(numbers, numbers))))
    val polarities = force(resolving.term("\\j:num. \\i:num. T", Type.fun(numbers, Type.fun(numbers, Type.Bool))))

    val statement = force(resolving.proposition(everyRefutation("NUM_LT 0 m")))
    val instance = opened(force(rules.specAll(
      force(LogicError.lift(Kernel.assume(statement))), List(zero, lengths, variables, polarities, one, one))))
    val (inputsTerm, rest) = resolving.logic.destImp(instance.conclusion).getOrElse(fail("two hypotheses"))
    val (refutationTerm, _) = resolving.logic.destImp(rest).getOrElse(fail("two hypotheses"))

    force(everyInputIsTheEmptyPigeonClause(inputsTerm)).hypotheses shouldBe empty
    force(theOneStepRefutes(refutationTerm)).hypotheses shouldBe empty
  }

  it should "detach its trivial instance from the fact that a refutation has a step" in {
    // The same shape with the bound at its weakest, `0 < m`, derived from `RES_REFUTATION_NONEMPTY`
    // by discharging the pigeonhole hypothesis unused. What it shows is that the shape Haken's
    // theorem is written in is one this development can derive into, not that the theorem holds.
    val rules = resolving.logic.rules
    val statement = force(resolving.proposition(everyRefutation("NUM_LT 0 m")))
    val (binders, body) = force(Logic.stripForall(statement))
    val (inputsTerm, rest) = resolving.logic.destImp(body).getOrElse(fail("two hypotheses"))
    val (refutationTerm, _) = resolving.logic.destImp(rest).getOrElse(fail("two hypotheses"))
    val derivation = binders.drop(1).toList.map(variable => variable: Term)

    val proved = force(
      for {
        refutation <- LogicError.lift(Kernel.assume(refutationTerm))
        positive <- rules.specAll(fact(Resolving.RefutationNonEmpty), derivation).flatMap(rules.mp(_, refutation))
        discharged <- rules.disch(refutationTerm, positive).flatMap(rules.disch(inputsTerm, _))
        closed <- rules.genAll(discharged, binders.toList)
      } yield closed
    )

    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe statement
  }

  private def constantsIn(term: Term): Set[String] = term match {
    case Const(name, _) => Set(name)
    case App(operator, argument) => constantsIn(operator) ++ constantsIn(argument)
    case Abs(_, body) => constantsIn(body)
    case _ => Set.empty
  }

  private def opened(theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(theorem.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))

  /** `|- !j. NUM_LT j (SUC 0) ==> <clause j is a pigeonhole clause at n = 0>`, clause `j` being empty. */
  private def everyInputIsTheEmptyPigeonClause(target: Term): Either[LogicError, Kernel.Thm] = {
    val logic = resolving.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val j = Term.variable("j", numbers)
    for {
      atJ <- logic.destForallPredicate(target).toRight(NotOfForm("a universal", target))
        .flatMap(predicate => LogicError.lift(Term.app(predicate, j)).flatMap(Conv.betaRoot))
      body <- Term.destEq(atJ.conclusion).map(_._2).toRight(NotOfForm("an equation", atJ.conclusion))
      pair1 <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (belowTerm, clauseTerm) = pair1
      pair2 <- logic.destDisj(clauseTerm).toRight(NotOfForm("a disjunction", clauseTerm))
      (pigeonTerm, holeTerm) = pair2
      predicate <- logic.destExistsPredicate(pigeonTerm).toRight(NotOfForm("an existential", pigeonTerm))
      zero <- resolving.term("0:num")
      atZero <- LogicError.lift(Term.app(predicate, zero)).flatMap(Conv.betaRoot)
      witnessBody <- Term.destEq(atZero.conclusion).map(_._2).toRight(NotOfForm("an equation", atZero.conclusion))
      pair3 <- logic.destConj(witnessBody).toRight(NotOfForm("a conjunction", witnessBody))
      (atMost, both) = pair3
      pair4 <- logic.destConj(both).toRight(NotOfForm("a conjunction", both))
      (everyLiteral, everyHole) = pair4
      zeroAtMost <- chain.peano.fact(Peano.ZeroIsLeast).flatMap(rules.spec(zero, _))
      literals <- vacuous(everyLiteral)
      holes <- vacuous(everyHole)
      witnessed <- rules.conjIntro(literals, holes).flatMap(rules.conjIntro(zeroAtMost, _))
      _ <- if (witnessed.conclusion == witnessBody) Right(()) else Left(NotOfForm("the witness's claim", witnessed.conclusion))
      pigeon <- rules.existsIntro(predicate, zero, witnessed)
      clause <- rules.disjIntro1(holeTerm, pigeon)
      result <- rules.disch(belowTerm, clause).flatMap(rules.gen(j, _))
    } yield result
  }

  /** `|- !x. NUM_LT x 0 ==> P x`, by ex falso: nothing is below zero. */
  private def vacuous(target: Term): Either[LogicError, Kernel.Thm] = {
    val logic = resolving.logic
    val rules = logic.rules
    for {
      stripped <- Logic.stripForall(target)
      (binders, body) = stripped
      x <- binders.headOption.toRight(NotOfForm("a universal", target))
      pair5 <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (belowTerm, claim) = pair5
      below <- LogicError.lift(Kernel.assume(belowTerm))
      absurd <- chain.peano.fact(Peano.NotBelowZero).flatMap(rules.spec(x, _)).flatMap(rules.notElim(_, below))
      reached <- rules.falsityElim(claim, absurd)
      result <- rules.disch(belowTerm, reached).flatMap(rules.gen(x, _))
    } yield result
  }

  /** `|- RES_REFUTATION (\j. 0) v s (SUC 0) (SUC 0)`: one step, an input, and empty. */
  private def theOneStepRefutes(target: Term): Either[LogicError, Kernel.Thm] = {
    val logic = resolving.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val j = Term.variable("j", numbers)
    def unfold(name: String, arguments: List[Term]): Either[LogicError, Kernel.Thm] =
      for {
        definition <- resolving.definition(name)
        equation <- Conv.unfold(definition, arguments)
        right <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
        normal <- Conv.betaNormalise(right)
        joined <- Conv.trans(equation, normal)
      } yield joined
    def argumentsOf(term: Term, taken: List[Term]): List[Term] = term match {
      case App(fn, argument) => argumentsOf(fn, argument :: taken)
      case _ => taken
    }
    val derivation = argumentsOf(target, Nil)
    for {
      opening <- unfold(Resolving.Refutation, derivation)
      body <- Term.destEq(opening.conclusion).map(_._2).toRight(NotOfForm("an equation", opening.conclusion))
      pair6 <- logic.destConj(body).toRight(NotOfForm("a conjunction", body))
      (everyStep, reachesEmpty) = pair6

      atJ <- logic.destForallPredicate(everyStep).toRight(NotOfForm("a universal", everyStep))
        .flatMap(predicate => LogicError.lift(Term.app(predicate, j)).flatMap(Conv.betaRoot))
      stepBody <- Term.destEq(atJ.conclusion).map(_._2).toRight(NotOfForm("an equation", atJ.conclusion))
      pair7 <- logic.destImp(stepBody).toRight(NotOfForm("an implication", stepBody))
      (belowTerm, justifiedTerm) = pair7
      below <- LogicError.lift(Kernel.assume(belowTerm))
      justifiedOpening <- unfold(Resolving.JustifiedName, argumentsOf(justifiedTerm, Nil))
      justifiedBody <- Term.destEq(justifiedOpening.conclusion).map(_._2)
        .toRight(NotOfForm("an equation", justifiedOpening.conclusion))
      pair8 <- logic.destDisj(justifiedBody).toRight(NotOfForm("a disjunction", justifiedBody))
      (_, resolvent) = pair8
      asInput <- rules.disjIntro1(resolvent, below)
      justified <- Conv.sym(justifiedOpening).flatMap(back => LogicError.lift(Kernel.eqMp(back, asInput)))
      steps <- rules.disch(belowTerm, justified).flatMap(rules.gen(j, _))

      predicate <- logic.destExistsPredicate(reachesEmpty).toRight(NotOfForm("an existential", reachesEmpty))
      zero <- resolving.term("0:num")
      atZero <- LogicError.lift(Term.app(predicate, zero)).flatMap(Conv.betaRoot)
      witnessBody <- Term.destEq(atZero.conclusion).map(_._2).toRight(NotOfForm("an equation", atZero.conclusion))
      pair9 <- logic.destConj(witnessBody).toRight(NotOfForm("a conjunction", witnessBody))
      (_, isEmpty) = pair9
      zeroBelowOne <- chain.peano.fact(Peano.BelowSuccessor).flatMap(rules.spec(zero, _))
      empty <- Conv.betaNormalise(isEmpty).flatMap(equation =>
        Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
          .flatMap(normal => Term.destEq(normal).toRight(NotOfForm("an equation", normal)))
          .flatMap { case (left, _) => Conv.sym(equation).flatMap(back => LogicError.lift(Kernel.eqMp(back, Conv.refl(left)))) })
      witnessed <- rules.conjIntro(zeroBelowOne, empty)
      reached <- rules.existsIntro(predicate, zero, witnessed)

      both <- rules.conjIntro(steps, reached)
      result <- Conv.sym(opening).flatMap(back => LogicError.lift(Kernel.eqMp(back, both)))
    } yield result
  }
}
