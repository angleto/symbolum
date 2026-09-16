package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The rewriting system $$S_2$$, its counted sub-relation, its potential and its marked words.
 *
 * Source: `collatz@8b991e5`, `code/referee/checks_rewriting.py` lines 9 to 15, which is where the
 * eleven rules are written down and is the repository that owns them. Nothing here was transcribed
 * by eye: the rule table below was **generated** from those lines, and the letters, the splits and
 * the potential all follow the same source.
 *
 * == Why this is a development of its own and not part of `Forward` ==
 *
 * `Forward` is generic in the system: `WORD_RFC R` is about any `R`. This file is the one `R` that
 * one investigation is about. Keeping them apart is what lets the closure be reused and what keeps
 * a reader of `WORD_RFC` from thinking the eleven rules are part of what a closure is.
 *
 * == The alphabet, and why the digits are not named ==
 *
 * Seven letters, encoded as numbers, and the three digits are **0, 1 and 2 themselves**. That is
 * the decision worth knowing before reading anything below: `c` is a digit exactly when `c < 3`,
 * which is one comparison rather than a three-way disjunction, and it is what makes [[Potential]]
 * one `NUM_SUM` over the positions. The other four letters are the numerals above the digits, and
 * they are named because a reader meeting `3` in a rule has no way to know it is `f`.
 *
 * The cost of the encoding is that a letter is a number and nothing stops a term naming the letter
 * `9`. Nothing below cares: every rule names its letters, and a word over letters this system has
 * no rule for is a word no rule applies to, which is a normal form and not an error.
 *
 * == The three groups, which is the structure part C uses ==
 *
 * `D` is the two rules that consume the marker, `A` the six that commute a digit past a letter, and
 * `B` the three that act at the head. [[Counted]] is `A` alone, and it is what a potential-function
 * argument instantiates as the counted sub-relation of `REACH`: every `A`-step moves one digit one
 * place nearer the head, so it drops [[Potential]] by exactly one, and no other rule lowers it.
 *
 * **The direction of that second condition is the one this repository has already got backwards
 * once.** `REACH_POTENTIAL` asks that no uncounted step LOWERS the measure, not that none raises
 * it. Two of the eleven do raise it, so the version with the inequality the other way round is
 * true, unusable, and was what a card carried until it was measured against the source.
 */
final class Collatz private (
  val forward: Forward,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = forward.inductive.classical.logic
    .over(theory)
    .fold(
      error => throw new IllegalStateException(s"the logic does not extend: ${error.message}"),
      identity
    )

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Collatz {

  /* ------------------------------------------------------------------ the alphabet */

  /** The letter `f`, which is `3`: the digits are 0, 1 and 2 and the rest sit above them. */
  val F: String = "S2_F"

  /** The letter `t`, which is `4`. */
  val T: String = "S2_T"

  /** The head marker `/`, which is `5`. Every word of the system starts with it. */
  val Head: String = "S2_HEAD"

  /** The tail marker `.`, which is `6`. A marked word ends with it and holds no other. */
  val Tail: String = "S2_TAIL"

  /* ------------------------------------------------------------------ the system */

  /** `S2 l r` — `l -> r` is one of the eleven rules. */
  val Name: String = "S2"

  /** `S2_COUNTED l r` — `l -> r` is one of the six commutation rules, which is `A`. */
  val Counted: String = "S2_COUNTED"

  /** `S2_PHI w` — the sum, over the digit occurrences of `w`, of the distance from the head. */
  val Potential: String = "S2_PHI"

  /** `S2_MARKED w` — exactly one tail marker, and it is the last letter. */
  val Marked: String = "S2_MARKED"

  /* ------------------------------------------------------------------ the facts */

  /** `|- !l r. S2_COUNTED l r ==> S2 l r` — the counted rules are rules. */
  val CountedIsRule: String = "S2_COUNTED_IS_RULE"

  /** `|- ?l r. S2 l r` — the system is inhabited, so nothing below is vacuously true. */
  val Inhabited: String = "S2_INHABITED"

  /**
   * `|- ~(S2 (WORD_SINGLETON S2_HEAD) (WORD_SINGLETON S2_HEAD))`.
   *
   * The refusal, and the reason it is the fact worth having rather than a courtesy. A relation that
   * held of everything would make `WORD_RFC S2` the set of all words and every statement downstream
   * true and empty. This is what says the eleven are eleven rules rather than a relation nobody
   * constrained, and it is derived by unfolding and refuting each of the eleven disjuncts on the
   * length of the words involved.
   */
  val Refused: String = "S2_REFUSED"

  /* ------------------------------------------------------------------ the types */

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Words: Type = TyApp(Word.TypeName, List(Numbers))

  private val LeftSide: FVar = Term.variable("l", Words)
  private val RightSide: FVar = Term.variable("r", Words)

  /* ------------------------------------------------------------------ the text */

  /**
   * The eleven rules, as a disjunction of eleven `l = ... /\ r = ...` clauses.
   *
   * **Generated from `checks_rewriting.py` rather than typed**, which is the whole reason this
   * block is unreadable in the source and readable in `docs/lemmas.md`: eleven rules written by
   * hand as nested `WORD_CONCAT` is eleven chances to put a letter in the wrong place, and the one
   * that went wrong would be a different rewriting system that still proved theorems.
   */
  private val SystemBody: String =
    "\\l:word(num). \\r:word(num). " +
      "(l = WORD_CONCAT (WORD_CONCAT (WORD_SINGLETON (S2_F:num)) (WORD_SINGLETON (S2_F:num))) " +
      "(WORD_SINGLETON (S2_TAIL:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON (0:num)) (WORD_SINGLETON " +
      "(S2_TAIL:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_T:num)) (WORD_SINGLETON " +
      "(S2_TAIL:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON (2:num)) (WORD_SINGLETON (S2_TAIL:num))) " +
      "\\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_T:num)) (WORD_SINGLETON (0:num)) /\\ r = " +
      "WORD_CONCAT (WORD_SINGLETON (1:num)) (WORD_SINGLETON (S2_T:num))) \\/ (l = WORD_CONCAT " +
      "(WORD_SINGLETON (S2_F:num)) (WORD_SINGLETON (0:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON " +
      "(0:num)) (WORD_SINGLETON (S2_F:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_T:num)) " +
      "(WORD_SINGLETON (1:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON (2:num)) (WORD_SINGLETON " +
      "(S2_F:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_F:num)) (WORD_SINGLETON (1:num)) /\\ r " +
      "= WORD_CONCAT (WORD_SINGLETON (0:num)) (WORD_SINGLETON (S2_T:num))) \\/ (l = WORD_CONCAT " +
      "(WORD_SINGLETON (S2_F:num)) (WORD_SINGLETON (2:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON " +
      "(1:num)) (WORD_SINGLETON (S2_F:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_T:num)) " +
      "(WORD_SINGLETON (2:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON (2:num)) (WORD_SINGLETON " +
      "(S2_T:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (0:num)) " +
      "/\\ r = WORD_CONCAT (WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (S2_T:num))) \\/ (l = " +
      "WORD_CONCAT (WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (1:num)) /\\ r = WORD_CONCAT " +
      "(WORD_CONCAT (WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (S2_F:num))) (WORD_SINGLETON " +
      "(S2_F:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (2:num)) " +
      "/\\ r = WORD_CONCAT (WORD_CONCAT (WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (S2_F:num))) " +
      "(WORD_SINGLETON (S2_T:num))) "

  /** The six commutation rules, from the same source and by the same generation. */
  private val CountedBody: String =
    "\\l:word(num). \\r:word(num). " +
      "(l = WORD_CONCAT (WORD_SINGLETON (S2_T:num)) (WORD_SINGLETON (0:num)) /\\ r = WORD_CONCAT " +
      "(WORD_SINGLETON (1:num)) (WORD_SINGLETON (S2_T:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON " +
      "(S2_F:num)) (WORD_SINGLETON (0:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON (0:num)) " +
      "(WORD_SINGLETON (S2_F:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_T:num)) " +
      "(WORD_SINGLETON (1:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON (2:num)) (WORD_SINGLETON " +
      "(S2_F:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_F:num)) (WORD_SINGLETON (1:num)) /\\ r " +
      "= WORD_CONCAT (WORD_SINGLETON (0:num)) (WORD_SINGLETON (S2_T:num))) \\/ (l = WORD_CONCAT " +
      "(WORD_SINGLETON (S2_F:num)) (WORD_SINGLETON (2:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON " +
      "(1:num)) (WORD_SINGLETON (S2_F:num))) \\/ (l = WORD_CONCAT (WORD_SINGLETON (S2_T:num)) " +
      "(WORD_SINGLETON (2:num)) /\\ r = WORD_CONCAT (WORD_SINGLETON (2:num)) (WORD_SINGLETON " +
      "(S2_T:num))) "

  private val PotentialBody: String =
    "\\w:word(num). NUM_SUM (\\i:num. COND (WORD_NTH w i < 3) (NUM_SUB i 1) 0) (WORD_LENGTH w)"

  private val MarkedBody: String =
    "\\w:word(num). 0 < WORD_LENGTH w /\\ " +
      "WORD_NTH w (NUM_SUB (WORD_LENGTH w) 1) = S2_TAIL /\\ " +
      "(!i:num. i < NUM_SUB (WORD_LENGTH w) 1 ==> ~(WORD_NTH w i = S2_TAIL))"

  /** The four letters that are not digits, in the order they are declared. */
  val Letters: Vector[(String, String)] =
    Vector(F -> "3", T -> "4", Head -> "5", Tail -> "6")

  /** Every definition this development introduces, as text, in dependency order. */
  val Bodies: Vector[(String, String)] =
    Letters.map { case (name, value) => name -> s"($value:num)" } ++
      Vector(
        Name -> SystemBody,
        Counted -> CountedBody,
        Potential -> PotentialBody,
        Marked -> MarkedBody
      )

  /** Every statement this development publishes, as text. */
  val Statements: Vector[(String, String)] = Vector(
    CountedIsRule -> "!l:word(num). !r:word(num). S2_COUNTED l r ==> S2 l r",
    Inhabited -> "?l:word(num). ?r:word(num). S2 l r",
    Refused ->
      ("~(S2 (WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (S2_HEAD:num)))")
  )

  /* ------------------------------------------------------------------ construction */

  /**
   * The development, built over [[Forward]] so that a claim about `WORD_RFC S2` is typable.
   *
   * Eight constants and no axiom. The four letters are defined before the rules that name them,
   * which is why [[Bodies]] is a vector rather than a map: a constant is reachable only from the
   * theory it was declared into, so the order is the construction and not a presentation choice.
   */
  def construct(
    forward: Forward,
    naturals: Natural,
    peano: Peano,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Collatz] = {
    val introduced = Bodies.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](
      Right((base, Map.empty))
    ) { (accumulated, entry) =>
      val (name, text) = entry
      for {
        state <- accumulated
        (theory, defined) = state
        body <- Parser.term(theory, notation, text)
        introduced <- LogicError.lift(Kernel.defineConstant(theory, name, body))
        (extended, definition) = introduced
      } yield (extended, defined + (name -> definition))
    }

    for {
      state <- introduced
      (theory, definitions) = state
      logic <- forward.inductive.classical.logic.over(theory)

      countedIsRule <- countedAreRules(logic, theory, notation, definitions)
      inhabited <- inhabitedProof(logic, theory, notation, definitions)
      refused <- refusal(
        logic, naturals, forward.concatenation, peano, theory, notation, definitions)
    } yield new Collatz(
      forward,
      theory,
      notation,
      definitions,
      Map(CountedIsRule -> countedIsRule, Inhabited -> inhabited, Refused -> refused)
    )
  }

  /* ------------------------------------------------------------------ the proofs */

  private def statement(
    theory: Theory,
    notation: Notation,
    name: String
  ): Either[LogicError, Term] =
    Statements
      .collectFirst { case (label, text) if label == name => text }
      .toRight(MissingDefinition(name))
      .flatMap(text => Parser.proposition(theory, notation, text))

  /**
   * [[CountedIsRule]]: every clause of `S2_COUNTED` is a clause of `S2`.
   *
   * The two definitions are disjunctions over the same shape and the six of `A` are literally six
   * of the eleven, so the proof is: unfold both, assume the six-way disjunction, and in each case
   * introduce the matching disjunct of the eleven. The rewriter does the unfolding and `Minimal`
   * does the propositional step, which is the one place in this file where a search is used at all
   * and it costs nothing: the fragment is a disjunction of conjunctions of equations with no
   * negation in it.
   */
  private def countedAreRules(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      target <- statement(theory, notation, CountedIsRule)
      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      counted <- definitions.get(Counted).toRight(MissingDefinition(Counted))
      rules <- unfoldingRules(logic, Vector(system, counted))

      // Minimal decides a propositional fragment, so the two quantifiers come off first and go
      // back on at the end. What is left between them is a disjunction of conjunctions of
      // equations with no negation in it, which is exactly the fragment, and it costs no axiom --
      // the reason this proof is not `Propositional`, which would decide the same goal and charge
      // `SELECT` for a classical step it does not need.
      body <- strippedBody(logic, target)
      opened <- Rewrite.rewrite(rules, body).flatMap(rightOf)
      proved <- Minimal(logic).prove(opened)
      inBody <- shapeBack(logic, rules, body, proved)
      result <- logic.rules.gen(RightSide, inBody).flatMap(logic.rules.gen(LeftSide, _))
    } yield result

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def unfoldingRules(
    logic: Logic,
    definitions: Vector[Kernel.Thm]
  ): Either[LogicError, Vector[Rewrite.Rule]] =
    definitions.foldLeft[Either[LogicError, Vector[Rewrite.Rule]]](Right(Vector.empty)) {
      (accumulated, definition) =>
        for {
          rules <- accumulated
          rule <- Rewrite.Rule.of(logic, definition)
        } yield rules :+ rule
    }

  private def shapeBack(
    logic: Logic,
    rules: Vector[Rewrite.Rule],
    target: Term,
    proved: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Rewrite.rewrite(rules, target).flatMap(Conv.sym).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, proved)))

  /**
   * [[Inhabited]]: the system relates something to something.
   *
   * The guard against the whole file being vacuous, and it is the cheapest of the three: `R1` is a
   * clause of the definition, so the proof is to unfold, supply that clause by reflexivity on both
   * sides, and close the two existentials at its own two words.
   */
  private def inhabitedProof(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      target <- statement(theory, notation, Inhabited)
      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      rules <- unfoldingRules(logic, Vector(system))
      opened <- Rewrite.rewrite(rules, target).flatMap(rightOf)

      // By hand and not by a search: this is an existential, and none of the three procedures in
      // this repository takes a quantifier. The witnesses are `R1`'s own two words, so each side
      // closes by reflexivity and the only work is putting the pair under the two binders.
      left <- Parser.term(theory, notation, RuleOneLeft, Words)
      right <- Parser.term(theory, notation, RuleOneRight, Words)
      witnessed <- firstDisjunctAt(logic, opened, left, right)
      result <- shapeBack(logic, rules, target, witnessed)
    } yield result

  /**
   * The innermost body of `?l r. c1 \/ rest` proved at two witnesses, by reflexivity on `R1`.
   *
   * The disjunction is right-nested and `R1` is the first clause, so the proof is one
   * `disjIntro1` over a conjunction of two reflexivities, closed under the two existentials.
   */
  private def firstDisjunctAt(
    logic: Logic,
    existential: Term,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      outer <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
      atLeft <- LogicError.lift(Term.app(outer, left))
      openedLeft <- Conv.betaRoot(atLeft).flatMap(rightOf)
      inner <- logic.destExistsPredicate(openedLeft).toRight(NotOfForm("an existential", openedLeft))
      atRight <- LogicError.lift(Term.app(inner, right))
      body <- Conv.betaRoot(atRight).flatMap(rightOf)

      sides <- logic.destDisj(body).toRight(NotOfForm("a disjunction", body))
      (clause, rest) = sides
      pair <- logic.destConj(clause).toRight(NotOfForm("a conjunction", clause))
      (leftEq, rightEq) = pair
      leftTerm <- Term.destEq(leftEq).map(_._1).toRight(NotOfForm("an equation", leftEq))
      rightTerm <- Term.destEq(rightEq).map(_._1).toRight(NotOfForm("an equation", rightEq))
      both <- rules.conjIntro(Conv.refl(leftTerm), Conv.refl(rightTerm))
      chosen <- rules.disjIntro1(rest, both)

      closedInner <- rules.existsIntro(inner, right, chosen)
      closedOuter <- rules.existsIntro(outer, left, closedInner)
    } yield closedOuter
  }

  /** `R1`'s two words, which are the witnesses [[Inhabited]] uses. */
  private val RuleOneLeft: String =
    "WORD_CONCAT (WORD_CONCAT (WORD_SINGLETON (S2_F:num)) (WORD_SINGLETON (S2_F:num))) " +
      "(WORD_SINGLETON (S2_TAIL:num))"

  private val RuleOneRight: String =
    "WORD_CONCAT (WORD_SINGLETON (0:num)) (WORD_SINGLETON (S2_TAIL:num))"

  /**
   * [[Refused]]: the head letter on its own does not rewrite to itself.
   *
   * The half that says the eleven are a constraint. Every clause of the definition equates `l` to a
   * word of length two or three, and `WORD_SINGLETON` has length one, so each disjunct dies on the
   * lengths. `Minimal` cannot take this one: it refuses a goal with a negation in it, and this goal
   * is a negation of a disjunction of eleven conjunctions of equations between words.
   *
   * So it goes to `Propositional` instead, over the length facts as atoms. What that costs is
   * written where this repository writes such things rather than hidden: the classical decision
   * closes with double negation and charges `SELECT`, where the intuitionistic one charges nothing.
   * The trade is taken here because the alternative is eleven hand refutations that differ only in
   * which numeral they compare, and because a refusal that costs one foundational axiom is still a
   * refusal the kernel checked.
   */
  private def refusal(
    logic: Logic,
    naturals: Natural,
    concatenation: Concatenation,
    peano: Peano,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      target <- statement(theory, notation, Refused)
      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      rules <- unfoldingRules(logic, Vector(system))
      lengthRules <- lengthRuleSet(logic, concatenation, peano)
      opened <- Rewrite.rewrite(rules, target).flatMap(rightOf)

      // `Propositional` was tried here first and refuses, correctly and with the right message:
      // the atoms are uninterpreted, so the skeleton of eleven disjuncts is satisfiable and the
      // refusal says so rather than guessing. Nothing about words is propositional, which is the
      // whole content of this lemma, so the eleven are refuted one at a time on their lengths.
      disjunction <- logic.destNot(opened).toRight(NotOfForm("a negation", opened))
      contradiction <- refuteDisjunction(logic, naturals, lengthRules, disjunction)
      negated <- logic.rules.notIntro(disjunction, contradiction)
      result <- shapeBack(logic, rules, target, negated)
    } yield result

  /**
   * Every disjunct refuted, and the disjunction with it.
   *
   * Right-nested, so this walks the spine: refute the head clause, recurse on the tail, and put
   * the two cases together with `disjElim` at falsity. Eleven clauses and one shape, because every
   * clause of this system says the left side **is** a particular word.
   */
  private def refuteDisjunction(
    logic: Logic,
    naturals: Natural,
    lengthRules: Vector[Rewrite.Rule],
    disjunction: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    logic.destDisj(disjunction) match {
      case None => refuteClause(logic, naturals, lengthRules, disjunction)
      case Some((clause, rest)) =>
        for {
          here <- refuteClause(logic, naturals, lengthRules, clause)
          there <- refuteDisjunction(logic, naturals, lengthRules, rest)
          assumed <- LogicError.lift(Kernel.assume(disjunction))
          split <- rules.disjElim(assumed, here, there)
        } yield split
    }
  }

  /**
   * One clause refuted on the length of the word its left conjunct names.
   *
   * The clause is `l = w /\ r = w'` with `l` already the one-letter word this lemma is about. So
   * the left conjunct equates a word of length one with a word of length two or three, and what
   * refutes it is applying `WORD_LENGTH` to both sides and asking `Successor` whether the two
   * numerals differ. No case analysis on the letters is needed and none is done: the letters could
   * all be equal and the clause would still be false.
   */
  private def refuteClause(
    logic: Logic,
    naturals: Natural,
    lengthRules: Vector[Rewrite.Rule],
    clause: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      parts <- logic.destConj(clause).toRight(NotOfForm("a conjunction", clause))
      (equation, _) = parts
      assumed <- LogicError.lift(Kernel.assume(clause))
      leftHalf <- rules.conjElim1(assumed)

      sides <- Term.destEq(equation).toRight(NotOfForm("an equation", equation))
      _ = sides
      lengthOf <- lengthFunction(logic)

      applied <- Conv.apTerm(lengthOf, leftHalf)
      computed <- Rewrite.inTheorem(lengthRules, applied)
      numerals <- Term.destEq(computed.conclusion).toRight(NotOfForm("an equation", computed.conclusion))
      (shortLength, longLength) = numerals

      falsity <- refuteSuccessors(logic, naturals, computed)
    } yield falsity
  }

  /**
   * `SUC^m 0 = SUC^n 0` with `m < n` refuted, by peeling the common successors off.
   *
   * `Successor.distinct` is the obvious tool and it is the wrong one here: it reads a numeral in
   * the bit encoding, and what the length rules produce is successor form, so it refuses with
   * "expected a numeral of num, found (SUC ZERO)". Converting to the bit encoding to ask it would
   * be a conversion in order to reach a procedure that then converts back.
   *
   * What refutes it directly is the two Peano facts the naturals already derive: strip the
   * successors both sides share with `NUM_SUC_INJECTIVE` until one side is `0`, and close with
   * `NUM_SUC_NOT_ZERO`. It terminates because each step removes one successor from each side and
   * the sides differ in how many they have.
   */
  private def refuteSuccessors(
    logic: Logic,
    naturals: Natural,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    def peel(current: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val sides = Term.destEq(current.conclusion)
      sides match {
        case None => Left(NotOfForm("an equation", current.conclusion))
        case Some((left, right)) =>
          (successorOf(left), successorOf(right)) match {
            case (Some(innerLeft), Some(innerRight)) =>
              for {
                injective <- naturals.fact(Natural.SuccessorInjective)
                // The INNER terms, not the sides: the lemma is `SUC x = SUC y ==> x = y`, so what
                // it is specialised at is what sits under each successor. Passing the sides builds
                // a true instance about two taller numbers whose antecedent nothing here proves,
                // which is what the first version did and what the refusal named.
                stripped <- rules.specAll(injective, List(innerLeft, innerRight))
                smaller <- rules.mp(stripped, current)
                result <- peel(smaller)
              } yield result

            // One side has run out of successors, so the other is `SUC something = 0` up to
            // symmetry, which is the fact the naturals publish.
            case (Some(_), None) => closeAgainstZero(logic, naturals, current)
            case (None, Some(_)) => Conv.sym(current).flatMap(closeAgainstZero(logic, naturals, _))
            case (None, None) =>
              Left(NotOfForm("two numerals of different height", current.conclusion))
          }
      }
    }

    peel(equation)
  }

  private def successorOf(term: Term): Option[Term] = term match {
    case App(Const(Natural.NumberSuccessor, _), argument) => Some(argument)
    case _ => None
  }

  private def closeAgainstZero(
    logic: Logic,
    naturals: Natural,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      notZero <- naturals.fact(Natural.SuccessorNotZero)
      sides <- Term.destEq(equation.conclusion).toRight(NotOfForm("an equation", equation.conclusion))
      (left, _) = sides
      inner <- successorOf(left).toRight(NotOfForm("a successor", left))
      instance <- logic.rules.spec(inner, notZero)
      falsity <- logic.rules.notElim(instance, equation)
    } yield falsity

  /** `WORD_LENGTH` at this development's word type, ready to be applied to both sides. */
  private def lengthFunction(logic: Logic): Either[LogicError, Term] =
    LogicError.lift(logic.theory.constant(Word.Length, Type.fun(Words, Numbers)))

  /** `!l r. body` minus its two leading quantifiers, which is what a propositional search takes. */
  private def strippedBody(logic: Logic, target: Term): Either[LogicError, Term] =
    for {
      outer <- logic.destForallPredicate(target).toRight(NotOfForm("a quantified claim", target))
      atLeft <- LogicError.lift(Term.app(outer, LeftSide))
      openedLeft <- Conv.betaRoot(atLeft).flatMap(rightOf)
      inner <- logic.destForallPredicate(openedLeft).toRight(NotOfForm("a quantified claim", openedLeft))
      atRight <- LogicError.lift(Term.app(inner, RightSide))
      body <- Conv.betaRoot(atRight).flatMap(rightOf)
    } yield body

  /**
   * What turns a concatenation of singletons into a numeral: the two length facts and the two
   * equations that evaluate the addition.
   *
   * `WORD_CONCAT_LENGTH` turns the word into a sum, `WORD_SINGLETON_LENGTH` turns each summand into
   * `SUC 0`, and `NUM_ADD_SUC` with `NUM_ADD_ZERO` walk the sum down to a numeral in successor
   * form, which is the form `Successor.distinct` reads. Four rules and no search.
   */
  private def lengthRuleSet(
    logic: Logic,
    concatenation: Concatenation,
    peano: Peano
  ): Either[LogicError, Vector[Rewrite.Rule]] =
    for {
      concatLength <- concatenation.fact(Concatenation.Length)
      singletonLength <- concatenation.fact(Concatenation.SingletonLength)
      addSuc <- peano.fact(Peano.AddAtSuccessor)
      addZero <- peano.fact(Peano.AddAtZero)
      rules <- unfoldingRules(logic, Vector(concatLength, singletonLength, addSuc, addZero))
    } yield rules
}
