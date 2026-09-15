package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The Goedel numbering of the object language, starting with the pairing everything is built from.
 *
 * `docs/adr/0014` is the decision this file implements: a term and a formula of the embedded theory
 * are **numbers**, being one is a predicate on `num`, a constructor of fixed arity codes its
 * arguments with a **pairing**, and a sequence of unbounded length is coded by the beta function of
 * [[Coding]]. That record also says why both mechanisms are here and neither is redundant, which is
 * the question a reader arrives with: a pair is not a sequence, and `docs/adr/0013` rejected
 * **iterating** the pairing rather than the pairing.
 *
 * **The pairing is Cantor's and is written without a division**, which is the reason to read the
 * definition rather than assume the usual one. `NUM_PAIR a b` is `NUM_TRI (a + b) + a`, where
 * `NUM_TRI n` is `0 + 1 + ... + n`; the familiar closed form is `(a + b)(a + b + 1) / 2 + a` and
 * writing it that way would drag `NUM_DIV` and its guard into every proof about syntax. The
 * triangular numbers are a recursion on `num` and cost nothing, so the halving never happens.
 *
 * **The bound is the point of the whole construction and it is [[PairLeft]] and [[PairRight]].**
 * Both components of a pair are at most the pair. That is what lets [[Descent]] define a predicate
 * by recursion on a code, since every sub-code is a smaller number, and it is what will let the
 * object theory's version of that predicate quantify over sub-codes **boundedly**, which is what
 * Delta-0 means. `docs/adr/0014` says it at more length.
 *
 * **The bound is not strict, and that is a fact about the pairing rather than a weakness.**
 * `NUM_PAIR ZERO ZERO` is `ZERO`, so a component can equal its pair, and only there. A constructor
 * that wants to descend adds a tag, which makes its codes successors and therefore strictly above
 * both components; that is the constructor's job and not this lemma's, and stating the strict bound
 * here would be stating something false.
 */
final class Numbering private (
  val coding: Coding,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  val peano: Peano = coding.peano

  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Numbering {

  /** `NUM_TRI n` is `0 + 1 + ... + n`, by recursion and not by a division. */
  val TriangleName: String = "NUM_TRI"

  /** `|- NUM_TRI ZERO = ZERO`. */
  val TriangleAtZero: String = "NUM_TRI_ZERO"

  /** `|- !n. NUM_TRI (SUC n) = NUM_ADD (NUM_TRI n) (SUC n)`. */
  val TriangleAtSuccessor: String = "NUM_TRI_SUC"

  /**
   * `|- !m n. NUM_LE m n ==> NUM_LE (NUM_TRI m) (NUM_TRI n)`
   *
   * The one fact about the triangular numbers the pairing needs, and it is needed in the place a
   * reader would not guess: not to show that a pair determines its components, but to show that it
   * determines their **sum**. Two pairs with different sums are separated by a whole row of the
   * triangle, and this is what says the rows do not overlap.
   */
  val TriangleMonotone: String = "NUM_TRI_MONOTONE"

  /** `NUM_PAIR a b` is `NUM_TRI (NUM_ADD a b) + a`, Cantor's pairing without the halving. */
  val PairName: String = "NUM_PAIR"

  /** `|- !a b. NUM_LE a (NUM_PAIR a b)`. Not strict: `NUM_PAIR ZERO ZERO` is `ZERO`. */
  val PairLeft: String = "NUM_PAIR_LE_LEFT"

  /** `|- !a b. NUM_LE b (NUM_PAIR a b)`. Not strict, for the same reason and only there. */
  val PairRight: String = "NUM_PAIR_LE_RIGHT"

  /**
   * `|- !a b c d. NUM_PAIR a b = NUM_PAIR c d ==> a = c /\ b = d`
   *
   * A pair determines both of its components, which is what makes a code a code: without it two
   * different terms of the object language could have one number and the whole arithmetisation
   * would be about something other than syntax.
   *
   * Two steps and the first is the one with content. The sums are equal, because if one were below
   * the other its whole row would fit strictly below the other's first entry: `a <= a + b` puts the
   * pair at most at the end of its row, and [[TriangleMonotone]] puts the next row at or above the
   * other pair. Once the sums agree the triangles agree, and cancelling a common summand twice
   * gives first `a = c` and then `b = d`.
   */
  val PairInjective: String = "NUM_PAIR_INJECTIVE"

  /**
   * `NUM_CODE t p` is `SUC (NUM_PAIR t p)`: a tag, a payload, and the successor that makes it
   * descend.
   *
   * The constructor `docs/adr/0014` describes and [[PairLeft]]'s docstring promises. Every code of
   * the object language is one of these, so every code is a **successor**, and that is what turns
   * the pairing's non-strict bound into the strict one [[Descent]] needs: a sub-code is at most the
   * pair and the pair is strictly below its own successor.
   *
   * The successor is not decoration and it buys a second thing: `ZERO` is not a code, so the
   * predicate that says "this number is a term" is false at zero without a case for it.
   */
  val CodeName: String = "NUM_CODE"

  /** `|- !t p u q. NUM_CODE t p = NUM_CODE u q ==> t = u /\ p = q`. */
  val CodeInjective: String = "NUM_CODE_INJECTIVE"

  /** `|- !t p. NUM_LT t (NUM_CODE t p)`. The strict bound, which the pairing alone cannot give. */
  val CodeLeft: String = "NUM_CODE_LT_LEFT"

  /** `|- !t p. NUM_LT p (NUM_CODE t p)`. The one a recursion on the payload descends by. */
  val CodeRight: String = "NUM_CODE_LT_RIGHT"

  /** `|- !t p. ~(NUM_CODE t p = ZERO)`. Zero is not a code, so a syntactic predicate refuses it. */
  val CodeNotZero: String = "NUM_CODE_NOT_ZERO"

  /**
   * `NUM_FST p` is the left component of `p` read as a pair, chosen rather than computed.
   *
   * **The four projections are what a function over codes needs and a predicate over them does
   * not.** `NUM_TERM` never takes a code apart: it says a code IS `NUM_CODE t p` for some `t` and
   * `p` and works under the existential. A function has to produce an answer built from the parts,
   * so it has to name them.
   *
   * Chosen by `select` the way `Modular.NUM_GCD` is, for the reason `docs/adr/0010` gives: nothing
   * in the kernel computes. What makes the choice pin down an answer is [[PairInjective]], and at a
   * number that is not of the shape being projected the choice falls somewhere and nothing is
   * provable about it, which is the same silence `NUM_GCD ZERO ZERO` leaves.
   */
  val FirstName: String = "NUM_FST"

  /** `NUM_SND p` is the right component, the same way. */
  val SecondName: String = "NUM_SND"

  /** `NUM_TAG c` is the tag of `c` read as a code. */
  val TagName: String = "NUM_TAG"

  /** `NUM_PAYLOAD c` is the payload of `c` read as a code. */
  val PayloadName: String = "NUM_PAYLOAD"

  /** `|- !a b. NUM_FST (NUM_PAIR a b) = a`. */
  val FirstOfPair: String = "NUM_FST_PAIR"

  /** `|- !a b. NUM_SND (NUM_PAIR a b) = b`. */
  val SecondOfPair: String = "NUM_SND_PAIR"

  /** `|- !t p. NUM_TAG (NUM_CODE t p) = t`. */
  val TagOfCode: String = "NUM_TAG_CODE"

  /** `|- !t p. NUM_PAYLOAD (NUM_CODE t p) = p`. */
  val PayloadOfCode: String = "NUM_PAYLOAD_CODE"

  /** Every statement this development publishes, as text, for the reason `Peano` gives. */
  val Statements: Vector[(String, String)] = Vector(
    TriangleAtZero -> "NUM_TRI ZERO = ZERO",
    TriangleAtSuccessor -> "!n:num. NUM_TRI (SUC n) = NUM_ADD (NUM_TRI n) (SUC n)",
    TriangleMonotone ->
      "!m:num n:num. NUM_LE m n ==> NUM_LE (NUM_TRI m) (NUM_TRI n)",
    PairLeft -> "!a:num b:num. NUM_LE a (NUM_PAIR a b)",
    PairRight -> "!a:num b:num. NUM_LE b (NUM_PAIR a b)",
    PairInjective ->
      ("!a:num b:num c:num d:num. NUM_PAIR a b = NUM_PAIR c d ==> " +
        "a = c /\\ b = d"),
    CodeInjective ->
      ("!t:num p:num u:num q:num. NUM_CODE t p = NUM_CODE u q ==> " +
        "t = u /\\ p = q"),
    CodeLeft -> "!t:num p:num. NUM_LT t (NUM_CODE t p)",
    CodeRight -> "!t:num p:num. NUM_LT p (NUM_CODE t p)",
    CodeNotZero -> "!t:num p:num. ~(NUM_CODE t p = ZERO)",
    FirstOfPair -> "!a:num b:num. NUM_FST (NUM_PAIR a b) = a",
    SecondOfPair -> "!a:num b:num. NUM_SND (NUM_PAIR a b) = b",
    TagOfCode -> "!t:num p:num. NUM_TAG (NUM_CODE t p) = t",
    PayloadOfCode -> "!t:num p:num. NUM_PAYLOAD (NUM_CODE t p) = p"
  )

  /** Build it over the beta function, in that development's own notation. */
  def construct(coding: Coding): Either[LogicError, Numbering] =
    construct(coding, coding.theory, coding.notation)

  /**
   * The same, extending a theory that already holds something else.
   *
   * The chain entry point, and the notation travels with the base for the reason [[Coding]] gives
   * at the same place: this is `Chain.widest` now, `docs/lemmas.md` is printed through it, and a
   * notation narrower than the theory generates a document naming constants it cannot write.
   */
  def construct(coding: Coding, base: Theory, notation: Notation): Either[LogicError, Numbering] = {
    val peano = coding.peano
    val numbers = TyApp(Natural.TypeName, Nil)

    for {
      recursion <- peano.naturals.recursion
      defined <- Recursion.define(
        coding.logic,
        peano.naturals,
        base,
        notation,
        recursion,
        TriangleName,
        numbers,
        "ZERO",
        "\\v:num. \\i:num. NUM_ADD v (SUC i)",
        None
      )
      (triangleTheory, triangleDefinition, atZero, atSuccessor) = defined

      pairBody <- Parser.term(
        triangleTheory,
        notation,
        "\\a:num b:num. NUM_ADD (NUM_TRI (NUM_ADD a b)) a"
      )
      withPair <- LogicError.lift(Kernel.defineConstant(triangleTheory, PairName, pairBody))
      (pairTheory, pairDefinition) = withPair

      codeBody <- Parser.term(
        pairTheory,
        notation,
        "\\t:num p:num. SUC (NUM_PAIR t p)"
      )
      withCode <- LogicError.lift(Kernel.defineConstant(pairTheory, CodeName, codeBody))
      (codeTheory, codeDefinition) = withCode

      // The four projections, each chosen by `select` over the shape it undoes.
      projections <- Vector(
        FirstName -> "\\p:num. select (\\a:num. ?b:num. p = NUM_PAIR a b)",
        SecondName -> "\\p:num. select (\\b:num. ?a:num. p = NUM_PAIR a b)",
        TagName -> "\\c:num. select (\\t:num. ?p:num. c = NUM_CODE t p)",
        PayloadName -> "\\c:num. select (\\p:num. ?t:num. c = NUM_CODE t p)"
      ).foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](
        Right((codeTheory, Map.empty))
      ) { (carried, entry) =>
        for {
          state <- carried
          body <- Parser.term(state._1, notation, entry._2)
          defined <- LogicError.lift(Kernel.defineConstant(state._1, entry._1, body))
        } yield (defined._1, state._2.updated(entry._1, defined._2))
      }
      (theory, projectionDefinitions) = projections

      logic <- coding.logic.over(theory)
      induction <- peano.naturals.fact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)

      vocabulary <- Vocabulary.of(coding, theory, notation, logic)
      zeroChecked <- vocabulary.checked(TriangleAtZero, atZero)
      successorChecked <- vocabulary.checked(TriangleAtSuccessor, atSuccessor)
      monotone <- triangleIsMonotone(vocabulary, driver, zeroChecked, successorChecked)
      left <- componentBelowPair(vocabulary, pairDefinition, successorChecked, PairLeft)
      right <- componentBelowPair(vocabulary, pairDefinition, successorChecked, PairRight)
      injective <- pairDeterminesBoth(vocabulary, pairDefinition, monotone, successorChecked)
      codeInjective <- codeDeterminesBoth(vocabulary, codeDefinition, injective)
      codeLeft <- componentBelowCode(vocabulary, codeDefinition, left, CodeLeft)
      codeRight <- componentBelowCode(vocabulary, codeDefinition, right, CodeRight)
      codeNotZero <- codeNeverVanishes(vocabulary, codeDefinition)

      firstOfPair <- projectionAt(
        vocabulary, projectionDefinitions, injective, vocabulary.pair, FirstOfPair)
      secondOfPair <- projectionAt(
        vocabulary, projectionDefinitions, injective, vocabulary.pair, SecondOfPair)
      tagOfCode <- projectionAt(
        vocabulary, projectionDefinitions, codeInjective, vocabulary.code, TagOfCode)
      payloadOfCode <- projectionAt(
        vocabulary, projectionDefinitions, codeInjective, vocabulary.code, PayloadOfCode)
    } yield new Numbering(
      coding,
      theory,
      notation,
      logic,
      Map(
        TriangleName -> triangleDefinition,
        PairName -> pairDefinition,
        CodeName -> codeDefinition
      ) ++ projectionDefinitions,
      Map(
        TriangleAtZero -> zeroChecked,
        TriangleAtSuccessor -> successorChecked,
        TriangleMonotone -> monotone,
        PairLeft -> left,
        PairRight -> right,
        PairInjective -> injective,
        CodeInjective -> codeInjective,
        CodeLeft -> codeLeft,
        CodeRight -> codeRight,
        CodeNotZero -> codeNotZero,
        FirstOfPair -> firstOfPair,
        SecondOfPair -> secondOfPair,
        TagOfCode -> tagOfCode,
        PayloadOfCode -> payloadOfCode
      )
    )
  }

  /** What the derivations below reach for, gathered once, as `Coding` and `Modular` both do. */
  private final case class Vocabulary(
    peano: Peano,
    theory: Theory,
    notation: Notation,
    logic: Logic,
    numbers: Type,
    zero: Term,
    successor: Term,
    below: Term,
    atMost: Term,
    plus: Term,
    triangle: Term,
    pair: Term,
    code: Term,
    strictOrder: Kernel.Thm,
    facts: Map[String, Kernel.Thm]
  ) {

    val rules: Rules = logic.rules

    def sum(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(plus, List(left, right)))

    def triangleAt(argument: Term): Either[LogicError, Term] =
      LogicError.lift(Term.app(triangle, argument))

    def paired(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(pair, List(left, right)))

    def coded(tag: Term, payload: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(code, List(tag, payload)))

    def atMostTerm(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(atMost, List(left, right)))

    def belowTerm(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(below, List(left, right)))

    def fact(name: String): Either[LogicError, Kernel.Thm] =
      facts.get(name).toRight(MissingDefinition(name))

    def statement(name: String): Either[LogicError, Term] =
      Statements
        .collectFirst { case (key, text) if key == name => text }
        .toRight(MissingDefinition(name))
        .flatMap(Parser.proposition(theory, notation, _))

    def checked(name: String, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      statement(name).flatMap { expected =>
        if (theorem.conclusion == expected) Right(theorem)
        else Left(NotOfForm(s"the statement published for $name", theorem.conclusion))
      }

    /** Carry `theorem` across an equation, by congruence under a fixed context. */
    def carry(context: Term, equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        congruence <- Conv.apTerm(context, equation)
        result <- LogicError.lift(Kernel.eqMp(congruence, theorem))
      } yield result

    /** `NUM_LE first last` from the two halves, which this file does six times. */
    def transitively(
      first: Term,
      middle: Term,
      last: Term,
      below: Kernel.Thm,
      above: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      rules
        .conjIntro(below, above)
        .flatMap(pair =>
          fact(Peano.Transitive)
            .flatMap(rules.specAll(_, List(first, middle, last)))
            .flatMap(rules.mp(_, pair))
        )

    /** `NUM_LE x (NUM_ADD x y)`, one step from what the order is defined as. */
    def atMostSum(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      for {
        total <- sum(left, right)
        definition <- peano.definition(Peano.NonStrictOrder)
        unfolded <- Conv.unfold(definition, List(left, total))
        body <- Term
          .destEq(unfolded.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", unfolded.conclusion))
        predicate <- logic
          .destExistsPredicate(body)
          .toRight(NotOfForm("an existential", body))
        witnessed <- rules.existsIntro(predicate, right, Conv.refl(total))
        back <- Conv.sym(unfolded)
        result <- LogicError.lift(Kernel.eqMp(back, witnessed))
      } yield result
  }

  private object Vocabulary {

    def of(
      coding: Coding,
      theory: Theory,
      notation: Notation,
      logic: Logic
    ): Either[LogicError, Vocabulary] = {
      val peano = coding.peano
      val numbers = TyApp(Natural.TypeName, Nil)
      val binary = Type.fun(numbers, Type.fun(numbers, Type.Bool))
      val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))

      val needed = Vector(
        Peano.ZeroIsLeast,
        Peano.BelowThenAtMost,
        Peano.AddCommutative,
        Peano.Transitive,
        Peano.Reflexive,
        Peano.AtMostZero,
        Peano.AtMostFromBelow,
        Peano.BelowOrEqual,
        Peano.BelowSuccessorCases,
        Peano.BelowSuccessor,
        Peano.StrictIrreflexive,
        Peano.Trichotomy,
        Peano.AddCancelsLeft,
        Peano.AddAtSuccessor,
        Peano.AddMonotone,
        Peano.AtMostThenBelow
      )

      for {
        zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
        successor <- LogicError.lift(
          theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
        )
        below <- LogicError.lift(theory.constant(Peano.StrictOrder, binary))
        atMost <- LogicError.lift(theory.constant(Peano.NonStrictOrder, binary))
        plus <- LogicError.lift(theory.constant(Peano.Addition, arithmetic))
        triangle <- LogicError.lift(
          theory.constant(TriangleName, Type.fun(numbers, numbers))
        )
        pair <- LogicError.lift(theory.constant(PairName, arithmetic))
        code <- LogicError.lift(theory.constant(CodeName, arithmetic))
        strictOrder <- peano.definition(Peano.StrictOrder)
        collected <- needed.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](
          Right(Map.empty)
        ) { (acc, name) =>
          for {
            found <- acc
            theorem <- peano.fact(name)
          } yield found.updated(name, theorem)
        }
      } yield Vocabulary(
        peano,
        theory,
        notation,
        logic,
        numbers,
        zero,
        successor,
        below,
        atMost,
        plus,
        triangle,
        pair,
        code,
        strictOrder,
        collected
      )
    }
  }

  /** `NUM_LE y (NUM_ADD x y)`, the sum's other summand, by commuting the one above. */
  private def atMostSumRight(
    vocabulary: Vocabulary,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      swapped <- vocabulary.atMostSum(right, left)
      commuted <- vocabulary
        .fact(Peano.AddCommutative)
        .flatMap(vocabulary.rules.specAll(_, List(right, left)))
      headed <- LogicError.lift(Term.app(vocabulary.atMost, right))
      result <- vocabulary.carry(headed, commuted, swapped)
    } yield result

  /**
   * [[TriangleMonotone]], by induction on the upper bound with the lower one generalised outside.
   *
   * At zero the premise forces the two to be equal. At `SUC k` the premise splits three ways and
   * not two, which is the shape `Coding.factorialDivides` meets for the same reason: `NUM_LE_CASES`
   * gives below or equal, and below has to be split again by `NUM_LT_SUC_CASES`, because what the
   * hypothesis wants is `m <= k` and neither half of the first split is that.
   */
  private def triangleIsMonotone(
    vocabulary: Vocabulary,
    driver: Induct,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- vocabulary.statement(TriangleMonotone)
      proved <- driver.proveBy(
        statement,
        goal => monotoneAtZero(vocabulary, goal),
        step => monotoneAtSuccessor(vocabulary, atSuccessor, step)
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(TriangleMonotone, proved)
      _ = atZero
    } yield result

  /** Nothing is below zero, so the premise makes the two arguments the same number. */
  private def monotoneAtZero(
    vocabulary: Vocabulary,
    goal: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
      (premise, conclusion) = parts
      lower <- premise match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a comparison", other))
      }
      assumed <- LogicError.lift(Kernel.assume(premise))
      isZero <- vocabulary
        .fact(Peano.AtMostZero)
        .flatMap(rules.spec(lower, _))
        .flatMap(rules.mp(_, assumed))
      atLower <- vocabulary.triangleAt(lower)
      reflexive <- vocabulary.fact(Peano.Reflexive).flatMap(rules.spec(atLower, _))
      headed <- LogicError.lift(Term.app(vocabulary.atMost, atLower))
      carried <- Conv
        .apTerm(vocabulary.triangle, isZero)
        .flatMap(equation => vocabulary.carry(headed, equation, reflexive))
      _ <-
        if (carried.conclusion == conclusion) Right(())
        else Left(NotOfForm("the base case as it is written", carried.conclusion))
      result <- rules.disch(premise, carried)
    } yield result
  }

  /** The step: below the successor is at most the predecessor, and one row is added on top. */
  private def monotoneAtSuccessor(
    vocabulary: Vocabulary,
    atSuccessor: Kernel.Thm,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
      (premise, conclusion) = parts
      lower <- premise match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a comparison", other))
      }
      assumed <- LogicError.lift(Kernel.assume(premise))

      successor <- LogicError.lift(Term.app(vocabulary.successor, step.variable))
      atLower <- vocabulary.triangleAt(lower)
      atStep <- vocabulary.triangleAt(step.variable)
      atSuccessorTerm <- vocabulary.triangleAt(successor)
      recurrence <- rules.spec(step.variable, atSuccessor)

      // `NUM_TRI k <= NUM_TRI k + SUC k`, which the recurrence turns into `<= NUM_TRI (SUC k)`.
      rowAdded <- vocabulary.atMostSum(atStep, successor)
      headed <- LogicError.lift(Term.app(vocabulary.atMost, atStep))
      stepReaches <- Conv
        .sym(recurrence)
        .flatMap(equation => vocabulary.carry(headed, equation, rowAdded))

      cases <- vocabulary
        .fact(Peano.BelowOrEqual)
        .flatMap(rules.specAll(_, List(lower, successor)))
        .flatMap(rules.mp(_, assumed))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (strictly, equal) = split

      fromStrict <- for {
        assumedStrict <- LogicError.lift(Kernel.assume(strictly))
        inner <- vocabulary
          .fact(Peano.BelowSuccessorCases)
          .flatMap(rules.specAll(_, List(step.variable, lower)))
          .flatMap(rules.mp(_, assumedStrict))
        innerSplit <- logic
          .destDisj(inner.conclusion)
          .toRight(NotOfForm("a disjunction", inner.conclusion))
        (belowStep, equalStep) = innerSplit
        fromBelow <- LogicError
          .lift(Kernel.assume(belowStep))
          .flatMap(strict =>
            vocabulary
              .fact(Peano.AtMostFromBelow)
              .flatMap(rules.specAll(_, List(lower, step.variable)))
              .flatMap(rules.mp(_, strict))
          )
        fromEqualStep <- for {
          assumedEqual <- LogicError.lift(Kernel.assume(equalStep))
          reflexive <- vocabulary.fact(Peano.Reflexive).flatMap(rules.spec(lower, _))
          lowerHeaded <- LogicError.lift(Term.app(vocabulary.atMost, lower))
          carried <- vocabulary.carry(lowerHeaded, assumedEqual, reflexive)
        } yield carried
        atMostStep <- rules.disjElim(inner, fromBelow, fromEqualStep)
        shorter <- rules.mp(step.hypothesis, atMostStep)
        settled <- vocabulary.transitively(
          atLower, atStep, atSuccessorTerm, shorter, stepReaches)
      } yield settled

      fromEqual <- for {
        assumedEqual <- LogicError.lift(Kernel.assume(equal))
        reflexive <- vocabulary.fact(Peano.Reflexive).flatMap(rules.spec(atLower, _))
        lowerHeaded <- LogicError.lift(Term.app(vocabulary.atMost, atLower))
        carried <- Conv
          .apTerm(vocabulary.triangle, assumedEqual)
          .flatMap(equation => vocabulary.carry(lowerHeaded, equation, reflexive))
      } yield carried

      settled <- rules.disjElim(cases, fromStrict, fromEqual)
      _ <-
        if (settled.conclusion == conclusion) Right(())
        else Left(NotOfForm("what the step has to reach", settled.conclusion))
      result <- rules.disch(premise, settled)
    } yield result
  }

  /**
   * `NUM_LE n (NUM_TRI n)`, which is a case split and not an induction.
   *
   * At zero it is that nothing is below zero. At a successor the recurrence puts `SUC k` on the
   * right of a sum, so the bound is the summand and nothing about the row below it is needed. That
   * is why the triangular numbers need no separate lemma about growth: each row contains its own
   * index.
   */
  private def indexBelowTriangle(
    vocabulary: Vocabulary,
    atSuccessor: Kernel.Thm,
    subject: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      atSubject <- vocabulary.triangleAt(subject)
      wanted <- vocabulary.atMostTerm(subject, atSubject)
      cases <- vocabulary.peano.naturals
        .fact(Natural.ZeroOrSuccessor)
        .flatMap(rules.spec(subject, _))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (isZero, hasPredecessor) = split

      fromZero <- for {
        assumed <- LogicError.lift(Kernel.assume(isZero))
        least <- vocabulary.fact(Peano.ZeroIsLeast).flatMap(rules.spec(atSubject, _))
        back <- Conv.sym(assumed)
        carried <- Conv
          .apTerm(vocabulary.atMost, back)
          .flatMap(Conv.apThm(_, atSubject))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, least)))
      } yield carried

      fromSuccessor <- for {
        assumedExistential <- LogicError.lift(Kernel.assume(hasPredecessor))
        predicate <- logic
          .destExistsPredicate(hasPredecessor)
          .toRight(NotOfForm("an existential", hasPredecessor))
        variable = Conv.freshVariable(
          "k",
          vocabulary.numbers,
          Term.freeVariables(hasPredecessor) ++ Term.freeVariables(subject)
        )
        applied <- LogicError.lift(Term.app(predicate, variable))
        contraction <- Conv.betaRoot(applied)
        instance <- Term
          .destEq(contraction.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", contraction.conclusion))
        assumedInstance <- LogicError.lift(Kernel.assume(instance))

        successor <- LogicError.lift(Term.app(vocabulary.successor, variable))
        recurrence <- rules.spec(variable, atSuccessor)
        atStep <- vocabulary.triangleAt(variable)
        bound <- atMostSumRight(vocabulary, atStep, successor)
        headed <- LogicError.lift(Term.app(vocabulary.atMost, successor))
        atTheSuccessor <- Conv
          .sym(recurrence)
          .flatMap(equation => vocabulary.carry(headed, equation, bound))

        // `SUC k` is `n`, on both sides of the comparison.
        back <- Conv.sym(assumedInstance)
        atTriangle <- vocabulary.triangleAt(successor)
        movedLeft <- Conv
          .apTerm(vocabulary.atMost, back)
          .flatMap(Conv.apThm(_, atTriangle))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atTheSuccessor)))
        subjectHeaded <- LogicError.lift(Term.app(vocabulary.atMost, subject))
        moved <- Conv
          .apTerm(vocabulary.triangle, back)
          .flatMap(equation => vocabulary.carry(subjectHeaded, equation, movedLeft))
        closed <- rules.existsElim(assumedExistential, variable, moved)
      } yield closed

      result <- rules.disjElim(cases, fromZero, fromSuccessor)
      _ <-
        if (result.conclusion == wanted) Right(())
        else Left(NotOfForm("the bound it was asked for", result.conclusion))
    } yield result
  }

  /**
   * [[PairLeft]] and [[PairRight]], which are the same shape over two different summands.
   *
   * `NUM_PAIR a b` is `NUM_TRI (a + b) + a`, so the left component is a summand of it outright. The
   * right one goes the long way, `b <= a + b <= NUM_TRI (a + b) <= NUM_PAIR a b`, and the middle
   * step is [[indexBelowTriangle]].
   */
  private def componentBelowPair(
    vocabulary: Vocabulary,
    pairDefinition: Kernel.Thm,
    atSuccessor: Kernel.Thm,
    which: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val a = Term.variable("a", numbers)
    val b = Term.variable("b", numbers)

    for {
      total <- vocabulary.sum(a, b)
      triangle <- vocabulary.triangleAt(total)
      asSum <- vocabulary.sum(triangle, a)
      opened <- Conv.unfold(pairDefinition, List(a, b))
      back <- Conv.sym(opened)

      component = if (which == PairLeft) a else b
      inSum <-
        if (which == PairLeft) atMostSumRight(vocabulary, triangle, a)
        else
          for {
            intoTotal <- atMostSumRight(vocabulary, a, b)
            intoTriangle <- indexBelowTriangle(vocabulary, atSuccessor, total)
            intoPair <- vocabulary.atMostSum(triangle, a)
            throughTriangle <- vocabulary.transitively(
              b, total, triangle, intoTotal, intoTriangle)
            throughPair <- vocabulary.transitively(
              b, triangle, asSum, throughTriangle, intoPair)
          } yield throughPair

      headed <- LogicError.lift(Term.app(vocabulary.atMost, component))
      carried <- vocabulary.carry(headed, back, inSum)
      general <- rules.genAll(carried, List(a, b))
      result <- vocabulary.checked(which, general)
    } yield result
  }

  /**
   * [[PairInjective]]: the sums agree first, and then the components.
   *
   * Once the sums agree the triangles agree, and what is left is one equation between two sums with
   * a common left summand, twice. `Peano.AddCancelsLeft` is both of those steps.
   */
  private def pairDeterminesBoth(
    vocabulary: Vocabulary,
    pairDefinition: Kernel.Thm,
    monotone: Kernel.Thm,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val a = Term.variable("a", numbers)
    val b = Term.variable("b", numbers)
    val c = Term.variable("c", numbers)
    val d = Term.variable("d", numbers)

    for {
      leftPair <- vocabulary.paired(a, b)
      rightPair <- vocabulary.paired(c, d)
      premise <- LogicError.lift(Term.eq(leftPair, rightPair))
      assumed <- LogicError.lift(Kernel.assume(premise))

      leftOpened <- Conv.unfold(pairDefinition, List(a, b))
      rightOpened <- Conv.unfold(pairDefinition, List(c, d))
      asSums <- Conv
        .sym(leftOpened)
        .flatMap(Conv.trans(_, assumed))
        .flatMap(Conv.trans(_, rightOpened))

      leftTotal <- vocabulary.sum(a, b)
      rightTotal <- vocabulary.sum(c, d)
      sameTotal <- totalsAgree(
        vocabulary, monotone, atSuccessor, a, b, c, d, leftTotal, rightTotal, asSums)

      rightTriangle <- vocabulary.triangleAt(rightTotal)
      alignedTriangle <- Conv.apTerm(vocabulary.triangle, sameTotal)
      aligned <- Conv
        .apTerm(vocabulary.plus, alignedTriangle)
        .flatMap(Conv.apThm(_, a))
      cancelled <- Conv.sym(aligned).flatMap(Conv.trans(_, asSums))
      firstAgree <- vocabulary
        .fact(Peano.AddCancelsLeft)
        .flatMap(rules.specAll(_, List(a, c, rightTriangle)))
        .flatMap(rules.mp(_, cancelled))

      shiftedTotal <- Conv
        .apTerm(vocabulary.plus, firstAgree)
        .flatMap(Conv.apThm(_, b))
        .flatMap(Conv.sym)
        .flatMap(Conv.trans(_, sameTotal))
      secondAgree <- vocabulary
        .fact(Peano.AddCancelsLeft)
        .flatMap(rules.specAll(_, List(b, d, c)))
        .flatMap(rules.mp(_, shiftedTotal))

      both <- rules.conjIntro(firstAgree, secondAgree)
      discharged <- rules.disch(premise, both)
      general <- rules.genAll(discharged, List(a, b, c, d))
      result <- vocabulary.checked(PairInjective, general)
    } yield result
  }

  /**
   * The two sums agree, which is the half of injectivity with any content in it.
   *
   * By trichotomy, and the two losing branches are one argument run twice. If one sum is below the
   * other, the whole of its row sits strictly below the other pair: `a <= a + b` puts the first
   * pair at most at `NUM_TRI s + s`, that is strictly below `NUM_TRI (SUC s)` because the next row
   * begins one higher, and [[TriangleMonotone]] puts `NUM_TRI (SUC s)` at or below `NUM_TRI t`,
   * which is at most the second pair. So the first pair is strictly below the second, and they were
   * assumed equal.
   *
   * Both mixed transitivities of `Peano` are spent here and that is what wanted the second one:
   * the chain runs `<=`, then `<`, then `<=`, and neither pure transitivity crosses either join.
   */
  private def totalsAgree(
    vocabulary: Vocabulary,
    monotone: Kernel.Thm,
    atSuccessor: Kernel.Thm,
    a: Term,
    b: Term,
    c: Term,
    d: Term,
    leftTotal: Term,
    rightTotal: Term,
    asSums: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    def strictlyBelow(
      lowFirst: Term,
      lowSecond: Term,
      lowTotal: Term,
      highTotal: Term,
      highFirst: Term,
      order: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        lowTriangle <- vocabulary.triangleAt(lowTotal)
        highTriangle <- vocabulary.triangleAt(highTotal)
        lowPair <- vocabulary.sum(lowTriangle, lowFirst)
        highPair <- vocabulary.sum(highTriangle, highFirst)
        topOfRow <- vocabulary.sum(lowTriangle, lowTotal)

        // `NUM_TRI s + a <= NUM_TRI s + s`, because `a <= a + b` and addition is monotone.
        firstAtMostTotal <- vocabulary.atMostSum(lowFirst, lowSecond)
        shifted <- vocabulary
          .fact(Peano.AddMonotone)
          .flatMap(rules.specAll(_, List(lowTriangle, lowFirst, lowTotal)))
          .flatMap(rules.mp(_, firstAtMostTotal))

        // `NUM_TRI s + s < NUM_TRI (SUC s)`: the next row begins one higher.
        successor <- LogicError.lift(Term.app(vocabulary.successor, lowTotal))
        atNextRow <- vocabulary.triangleAt(successor)
        recurrence <- rules.spec(lowTotal, atSuccessor)
        asSuccessor <- vocabulary
          .fact(Peano.AddAtSuccessor)
          .flatMap(rules.specAll(_, List(lowTriangle, lowTotal)))
        belowNext <- vocabulary.fact(Peano.BelowSuccessor).flatMap(rules.spec(topOfRow, _))
        headed <- LogicError.lift(Term.app(vocabulary.below, topOfRow))
        throughAdd <- Conv
          .sym(asSuccessor)
          .flatMap(equation => vocabulary.carry(headed, equation, belowNext))
        rowBelowNext <- Conv
          .sym(recurrence)
          .flatMap(equation => vocabulary.carry(headed, equation, throughAdd))

        // `NUM_TRI (SUC s) <= NUM_TRI t <= NUM_TRI t + c`.
        nextAtMost <- rules.specAll(monotone, List(successor, highTotal)).flatMap(rules.mp(_, order))
        intoPair <- vocabulary.atMostSum(highTriangle, highFirst)
        reachesHigh <- vocabulary.transitively(
          atNextRow, highTriangle, highPair, nextAtMost, intoPair)

        // `<` then `<=`, and then `<=` then `<`, which is both of Peano's mixed transitivities.
        rowBelowHigh <- rules
          .conjIntro(rowBelowNext, reachesHigh)
          .flatMap(pair =>
            vocabulary
              .fact(Peano.BelowThenAtMost)
              .flatMap(rules.specAll(_, List(topOfRow, atNextRow, highPair)))
              .flatMap(rules.mp(_, pair))
          )
        result <- rules
          .conjIntro(shifted, rowBelowHigh)
          .flatMap(pair =>
            vocabulary
              .fact(Peano.AtMostThenBelow)
              .flatMap(rules.specAll(_, List(lowPair, topOfRow, highPair)))
              .flatMap(rules.mp(_, pair))
          )
      } yield result

    for {
      wanted <- LogicError.lift(Term.eq(leftTotal, rightTotal))
      cases <- vocabulary
        .fact(Peano.Trichotomy)
        .flatMap(rules.specAll(_, List(leftTotal, rightTotal)))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (ascending, tailCases) = split
      tailSplit <- logic.destDisj(tailCases).toRight(NotOfForm("a disjunction", tailCases))
      (equal, descending) = tailSplit

      fromAscending <- for {
        assumedOrder <- LogicError.lift(Kernel.assume(ascending))
        unfolded <- Conv
          .unfold(vocabulary.strictOrder, List(leftTotal, rightTotal))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumedOrder)))
        strict <- strictlyBelow(a, b, leftTotal, rightTotal, c, unfolded)
        absurd <- refuteWithEquality(vocabulary, strict, asSums)
        anything <- rules.falsityElim(wanted, absurd)
      } yield anything

      fromEqual <- LogicError.lift(Kernel.assume(equal))

      fromDescending <- for {
        assumedOrder <- LogicError.lift(Kernel.assume(descending))
        unfolded <- Conv
          .unfold(vocabulary.strictOrder, List(rightTotal, leftTotal))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumedOrder)))
        strict <- strictlyBelow(c, d, rightTotal, leftTotal, a, unfolded)
        reversed <- Conv.sym(asSums)
        absurd <- refuteWithEquality(vocabulary, strict, reversed)
        anything <- rules.falsityElim(wanted, absurd)
      } yield anything

      assumedTail <- LogicError.lift(Kernel.assume(tailCases))
      tail <- rules.disjElim(assumedTail, fromEqual, fromDescending)
      result <- rules.disjElim(cases, fromAscending, tail)
    } yield result
  }

  /** `x < y` and `x = y` cannot both hold, and this is where the trichotomy's two ends close. */
  private def refuteWithEquality(
    vocabulary: Vocabulary,
    strict: Kernel.Thm,
    equality: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      upper <- strict.conclusion match {
        case App(App(_, _), right) => Right(right)
        case other => Left(NotOfForm("a comparison", other))
      }
      carried <- Conv
        .apTerm(vocabulary.below, equality)
        .flatMap(Conv.apThm(_, upper))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, strict)))
      never <- vocabulary.fact(Peano.StrictIrreflexive).flatMap(rules.spec(upper, _))
      result <- rules.notElim(never, carried)
    } yield result
  }

  /* ------------------------------------------------------------------ the constructor */

  /**
   * [[CodeInjective]], which is [[PairInjective]] with one successor stripped first.
   *
   * `NUM_CODE` is a successor of a pair, so two equal codes have equal pairs by the injectivity of
   * the successor, and equal pairs have equal components by the injectivity of the pairing. Nothing
   * here is about syntax: it is the two facts underneath composed once, so that every constructor
   * of the object language inherits both from one lemma.
   */
  private def codeDeterminesBoth(
    vocabulary: Vocabulary,
    codeDefinition: Kernel.Thm,
    pairInjective: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val t = Term.variable("t", numbers)
    val p = Term.variable("p", numbers)
    val u = Term.variable("u", numbers)
    val q = Term.variable("q", numbers)

    for {
      leftCode <- vocabulary.coded(t, p)
      rightCode <- vocabulary.coded(u, q)
      premise <- LogicError.lift(Term.eq(leftCode, rightCode))
      assumed <- LogicError.lift(Kernel.assume(premise))

      leftOpened <- Conv.unfold(codeDefinition, List(t, p))
      rightOpened <- Conv.unfold(codeDefinition, List(u, q))
      asSuccessors <- Conv
        .sym(leftOpened)
        .flatMap(Conv.trans(_, assumed))
        .flatMap(Conv.trans(_, rightOpened))

      leftPair <- vocabulary.paired(t, p)
      rightPair <- vocabulary.paired(u, q)
      asPairs <- vocabulary.peano.naturals
        .fact(Natural.SuccessorInjective)
        .flatMap(rules.specAll(_, List(leftPair, rightPair)))
        .flatMap(rules.mp(_, asSuccessors))

      both <- rules.specAll(pairInjective, List(t, p, u, q)).flatMap(rules.mp(_, asPairs))
      discharged <- rules.disch(premise, both)
      general <- rules.genAll(discharged, List(t, p, u, q))
      result <- vocabulary.checked(CodeInjective, general)
    } yield result
  }

  /**
   * [[CodeLeft]] and [[CodeRight]], the strict bounds, which are the whole reason for the successor.
   *
   * One step from the pairing's non-strict bound and `Peano.BelowSuccessor`, joined by the mixed
   * transitivity: a component is at most the pair, the pair is strictly below its successor, and the
   * successor is the code. This is what `docs/adr/0014` means by the constructor's job.
   */
  private def componentBelowCode(
    vocabulary: Vocabulary,
    codeDefinition: Kernel.Thm,
    pairBound: Kernel.Thm,
    which: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val t = Term.variable("t", numbers)
    val p = Term.variable("p", numbers)

    for {
      paired <- vocabulary.paired(t, p)
      coded <- vocabulary.coded(t, p)
      component = if (which == CodeLeft) t else p

      bounded <- rules.specAll(pairBound, List(t, p))
      next <- vocabulary.fact(Peano.BelowSuccessor).flatMap(rules.spec(paired, _))
      successor <- LogicError.lift(Term.app(vocabulary.successor, paired))
      strict <- rules
        .conjIntro(bounded, next)
        .flatMap(pieces =>
          vocabulary
            .fact(Peano.AtMostThenBelow)
            .flatMap(rules.specAll(_, List(component, paired, successor)))
            .flatMap(rules.mp(_, pieces))
        )

      headed <- LogicError.lift(Term.app(vocabulary.below, component))
      opened <- Conv.unfold(codeDefinition, List(t, p))
      carried <- Conv
        .sym(opened)
        .flatMap(equation => vocabulary.carry(headed, equation, strict))
      general <- rules.genAll(carried, List(t, p))
      result <- vocabulary.checked(which, general)
      _ = coded
    } yield result
  }

  /**
   * [[CodeNotZero]]: a code is a successor, and no successor is zero.
   *
   * The second thing the successor buys, and it is what lets a syntactic predicate be false at zero
   * without carrying a case for it: there is no tag and no payload whose code is `ZERO`, so `ZERO`
   * is refused by the shape of a code rather than by a clause about it.
   */
  private def codeNeverVanishes(
    vocabulary: Vocabulary,
    codeDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val t = Term.variable("t", numbers)
    val p = Term.variable("p", numbers)

    for {
      coded <- vocabulary.coded(t, p)
      paired <- vocabulary.paired(t, p)
      isZero <- LogicError.lift(Term.eq(coded, vocabulary.zero))
      assumed <- LogicError.lift(Kernel.assume(isZero))

      opened <- Conv.unfold(codeDefinition, List(t, p))
      successorIsZero <- Conv.sym(opened).flatMap(Conv.trans(_, assumed))
      never <- vocabulary.peano.naturals
        .fact(Natural.SuccessorNotZero)
        .flatMap(rules.spec(paired, _))
      contradiction <- rules.notElim(never, successorIsZero)
      refuted <- rules.notIntro(isZero, contradiction)
      general <- rules.genAll(refuted, List(t, p))
      result <- vocabulary.checked(CodeNotZero, general)
    } yield result
  }

  /* ----------------------------------------------------------------- the four projections */

  /**
   * The equation a projection satisfies at the shape it undoes, which is one derivation for four.
   *
   * The choice is over "there is a way to write this as a pair with **this** in the slot", so the
   * existential it is chosen from is provable at the component itself, with the other component as
   * the inner witness. `Classical.witness` turns that into the same claim about what was chosen,
   * and the injectivity of the constructor says what was chosen is the component.
   *
   * The only thing that differs between the four is which slot is being read, and that is read off
   * the statement rather than passed as a flag: the published text says what the answer is.
   */
  private def projectionAt(
    vocabulary: Vocabulary,
    definitions: Map[String, Kernel.Thm],
    injective: Kernel.Thm,
    constructor: Term,
    statement: String
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val left = Term.variable(if (statement == TagOfCode || statement == PayloadOfCode) "t" else "a", numbers)
    val right = Term.variable(if (statement == TagOfCode || statement == PayloadOfCode) "p" else "b", numbers)
    val takeLeft = statement == FirstOfPair || statement == TagOfCode
    val name = statement match {
      case FirstOfPair => FirstName
      case SecondOfPair => SecondName
      case TagOfCode => TagName
      case _ => PayloadName
    }

    for {
      definition <- definitions.get(name).toRight(MissingDefinition(name))
      applied <- LogicError.lift(Term.appAll(constructor, List(left, right)))
      unfolded <- Conv.unfold(definition, List(applied))
      chosen <- Term
        .destEq(unfolded.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", unfolded.conclusion))
      predicate <- chosen match {
        case App(_, inner) => Right(inner)
        case other => Left(NotOfForm("a choice", other))
      }

      // The existential the choice was made from, proved at the component itself.
      component = if (takeLeft) left else right
      other = if (takeLeft) right else left
      atComponent <- LogicError.lift(Term.app(predicate, component))
      contraction <- Conv.betaRoot(atComponent)
      body <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      innerPredicate <- logic
        .destExistsPredicate(body)
        .toRight(NotOfForm("an existential", body))
      // `Rules.existsIntro` wants the predicate at the witness BETA-REDUCED, which is what `inner`
      // already is: contracting it the other way and handing that over is what the first version
      // did, and the refusal names both forms.
      inner <- rules.existsIntro(innerPredicate, other, Conv.refl(applied))
      existential <- rules.existsIntro(predicate, component, inner)

      // What was chosen satisfies it, and the constructor is injective, so it is the component.
      satisfied <- vocabulary.peano.naturals.classical.witness(existential)
      reduced <- Conv
        .betaNormalise(satisfied.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, satisfied)))
      recovered <- withWitness(vocabulary, reduced, "w", Set(left, right)) { (found, shape) =>
        for {
          sides <- Term
            .destEq(shape.conclusion)
            .toRight(NotOfForm("an equation", shape.conclusion))
          parts <- sides._2 match {
            case App(App(_, first), second) => Right((first, second))
            case term => Left(NotOfForm("a constructor applied to two arguments", term))
          }
          both <- rules
            .specAll(injective, List(left, right, parts._1, parts._2))
            .flatMap(rules.mp(_, shape))
          half <- if (takeLeft) rules.conjElim1(both) else rules.conjElim2(both)
          _ = found
          // `half` reads component-equals-chosen and the equation wants it the other way.
          result <- Conv.sym(half)
        } yield result
      }

      reached <- Conv.trans(unfolded, recovered)
      general <- rules.genAll(reached, List(left, right))
      result <- vocabulary.checked(statement, general)
    } yield result
  }

  /** Open `?x. p x` with a fresh name, leaving the existential itself assumed. */
  private def withWitness(
    vocabulary: Vocabulary,
    existential: Kernel.Thm,
    name: String,
    avoid: Set[FVar]
  )(
    reach: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      predicate <- logic
        .destExistsPredicate(existential.conclusion)
        .toRight(NotOfForm("an existential", existential.conclusion))
      variable = Conv.freshVariable(
        name,
        vocabulary.numbers,
        avoid ++ Term.freeVariables(existential.conclusion)
      )
      applied <- LogicError.lift(Term.app(predicate, variable))
      contraction <- Conv.betaRoot(applied)
      instance <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      assumed <- LogicError.lift(Kernel.assume(instance))
      reached <- reach(variable, assumed)
      result <- rules.existsElim(existential, variable, reached)
    } yield result
  }
}
