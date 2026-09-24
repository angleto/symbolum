package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * An aggregate over a sequence, defined by recursion on the sequence rather than summed over its
 * indices.
 *
 * == Why this development exists at all ==
 *
 * `Listing` publishes `LIST_RECURSION`, and an existence theorem nobody spends is a capability
 * rather than a fact: a development can hold one for as long as it likes without anything going
 * red. This is the consumer, and it is the one thing here that could not have been written before
 * that theorem landed. [[Folding.Fold]] is **defined** by it, which is the whole point:
 * `LIST_INDUCT` would have proved any property of a fold one could write down, and it would not
 * have let anybody write one down.
 *
 * == What it replaces, measured against a fact this repository already holds ==
 *
 * `Concatenation.Tally` is this repository's answer to "aggregate over the letters of a word", and
 * it is written the way `word` makes available, which is a sum over the positions:
 *
 * {{{
 *   NUM_SUM (\i. f i (WORD_NTH (WORD_CONCAT u v) i)) (WORD_LENGTH (WORD_CONCAT u v)) =
 *     NUM_SUM (\i. f i (WORD_NTH u i)) (WORD_LENGTH u) +
 *     NUM_SUM (\i. f (WORD_LENGTH u + i) (WORD_NTH v i)) (WORD_LENGTH v)
 * }}}
 *
 * The `WORD_LENGTH u + i` in the second summand is not incidental: the letters of `v` sit that much
 * further along inside the concatenation than they do in `v` alone, so every consumer of that
 * lemma carries the correction whether its own aggregate cares about position or not. `S2_PHI` in
 * `Collatz` is the consumer that does care, and `Concatenation.Tally`'s own docstring says the
 * general `f` is there for it.
 *
 * [[Folding.FoldOfConcat]] is the same split for [[Folding.Fold]] and there is **no correction in
 * it**:
 *
 * {{{
 *   LIST_FOLD g a (WORD_CONCAT u v) = LIST_FOLD g (LIST_FOLD g a v) u
 * }}}
 *
 * Nothing is indexed, so nothing shifts; what the right-hand half produces is the accumulator the
 * left-hand half starts from. That is the difference the list orientation buys, and it is a
 * measurement against a lemma rather than a claim about style. What it **costs** is the other half
 * of the same sentence and is written here rather than left to be found: a fold cannot express a
 * measure that weighs a letter by where it sits, because the step never sees a position.
 * `Concatenation.Tally` is not superseded and this development does not replace it.
 *
 * == What it costs ==
 *
 * One constant and no axiom. What [[Folding.Fold]] rests on is three of the nineteen: choice,
 * infinity and eta. Choice twice over, once inside `LIST_RECURSION` and once here where the
 * existence theorem is turned into a name; infinity with the naturals; and eta because
 * `LIST_RECURSION` rests on `WORD_EXTENSIONALITY`, which `ListingSpec` asserts. This said
 * "the two axioms the naturals cost" until 2026-09-24, from the day it was written, and the test
 * that was meant to hold it was a ceiling that admitted the third.
 */
final class Folding private (
  val listing: Listing,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = listing.concatenation.word.product.classical.logic
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

object Folding {

  /* ---------------------------------------------------------------- the constant */

  /**
   * `LIST_FOLD g a w` — `a` with `g` applied along `w`, from the right.
   *
   * `LIST_FOLD g a (LIST_CONS x w)` is `g x (LIST_FOLD g a w)`, so the letters are consumed from
   * the head inwards and the accumulator comes back out. The step is handed the letter and the
   * value so far and **not** the tail, which is a decision rather than an omission:
   * `Listing.RecursionTheorem` offers the tail as well, and a step that took it would be a
   * paramorphism, for which [[FoldOfConcat]] is false. The two tails in that lemma's step differ --
   * `WORD_CONCAT u v` on one side and `u` on the other -- so a step that could read them would
   * separate two things the fold identifies.
   */
  val Fold: String = "LIST_FOLD"

  /* ------------------------------------------------------------------- the facts */

  /** `|- !g a. LIST_FOLD g a WORD_EMPTY = a`. */
  val FoldOfEmpty: String = "LIST_FOLD_EMPTY"

  /** `|- !g a x w. LIST_FOLD g a (LIST_CONS x w) = g x (LIST_FOLD g a w)`. */
  val FoldOfCons: String = "LIST_FOLD_CONS"

  /**
   * `|- !g a u v. LIST_FOLD g a (WORD_CONCAT u v) = LIST_FOLD g (LIST_FOLD g a v) u`.
   *
   * The lemma this development exists for, and the one to compare with `Concatenation.Tally`. It is
   * `Listing.Induct` on `u`, and the step is where the induction hypothesis is genuinely spent: the
   * concatenation of a cons is a cons of the concatenation, by associativity and the definition of
   * `LIST_CONS`, and what stands under `g` after [[FoldOfCons]] fires is exactly the hypothesis.
   */
  val FoldOfConcat: String = "LIST_FOLD_CONCAT"

  /* ------------------------------------------------------------------- the types */

  private val Element: Type = TyVar(Classical.TypeVariable)
  private val Values: Type = TyVar(Classical.CodomainVariable)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Words: Type = TyApp(Word.TypeName, List(Element))

  private def stepType: Type = Type.fun(Element, Type.fun(Values, Values))
  private def aggregateType: Type = Type.fun(Words, Values)
  private def foldType: Type = Type.fun(stepType, Type.fun(Values, aggregateType))
  private def consType: Type = Type.fun(Element, Type.fun(Words, Words))
  private def concatType: Type = Type.fun(Words, Type.fun(Words, Words))

  /**
   * What every derived fact says, as text, in the order they are derived.
   *
   * Compared as terms rather than as printed text, for the reason `Listing.Statements` gives: a
   * type variable is written `'a` and printed `a`, so a printed polymorphic statement does not read
   * back.
   */
  val Statements: Vector[(String, String)] = Vector(
    FoldOfEmpty ->
      "!g:'a->'b->'b. !a:'b. LIST_FOLD g a (WORD_EMPTY:word('a)) = a",
    FoldOfCons ->
      ("!g:'a->'b->'b. !a:'b. !x:'a. !w:word('a). " +
        "LIST_FOLD g a (LIST_CONS x w) = g x (LIST_FOLD g a w)"),
    FoldOfConcat ->
      ("!g:'a->'b->'b. !a:'b. !u:word('a). !v:word('a). " +
        "LIST_FOLD g a (WORD_CONCAT u v) = LIST_FOLD g (LIST_FOLD g a v) u")
  )

  /** The development in the chain's signature, which is the one a consumer reaches for. */
  lazy val standard: Folding = Chain.standard.folding

  /**
   * The development over a `Listing` and the theory to extend.
   *
   * `base` is not `listing.theory` for the reason `Listing.construct` gives about its own: what a
   * link extends is the chain's end when it is built.
   */
  def construct(listing: Listing, base: Theory): Either[LogicError, Folding] = {
    val classical = listing.concatenation.word.product.classical
    val notation = listing.notation

    for {
      recursion <- listing.fact(Listing.RecursionTheorem)
      consDefinition <- listing.definition(Listing.Cons)
      induct <- listing.fact(Listing.Induct)
      emptyLeft <- listing.concatenation.fact(Concatenation.EmptyLeft)
      associative <- listing.concatenation.fact(Concatenation.Associative)

      logicBelow <- classical.logic.over(base)
      introduced <- defineTheFold(logicBelow, classical, base, recursion)
      (theory, definition, atEmpty, atCons) = introduced

      logic <- classical.logic.over(theory)
      overConcat <- foldOverAConcatenation(
        logic, theory, notation, consDefinition, induct,
        (atEmpty, atCons, emptyLeft, associative))

      facts = Map(
        FoldOfEmpty -> atEmpty,
        FoldOfCons -> atCons,
        FoldOfConcat -> overConcat
      )

      // Each statement checked against the text a person reads it by, here rather than in the spec:
      // a development that built something other than what it says it built must not be handed out.
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { (acc, entry) =>
        val (name, text) = entry
        for {
          _ <- acc
          _ <- facts.get(name) match {
            case None => Right(())
            case Some(proved) =>
              for {
                expected <- Parser.proposition(theory, notation, text)
                _ <-
                  if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
                  else Left(NotOfForm(s"$name as it is written", proved.conclusion))
              } yield ()
          }
        } yield ()
      }
    } yield new Folding(listing, theory, notation, Map(Fold -> definition), facts)
  }

  /* --------------------------------------------------------------- the derivations */

  /**
   * The constant, and its two equations, out of `LIST_RECURSION`.
   *
   * The same dozen steps `Recursion.define` runs on `num` and not a call to it: that driver is
   * about a recursion over the naturals and takes at most one parameter, where a fold takes two and
   * the recursion it spends is the list's. What is shared is the shape rather than the code, and
   * the shape is: specialise the existence theorem at the two parameters, choose a witness, abstract
   * the chosen term over the parameters, define, and then carry the definition's own equation
   * across both sides of what the witness satisfies.
   *
   * **The step handed to `LIST_RECURSION` discards the tail.** `\x. \w. \r. g x r` is what makes
   * this a fold rather than a paramorphism, and [[Fold]]'s docstring says what that buys and what
   * it costs.
   */
  private def defineTheFold(
    logic: Logic,
    classical: Classical,
    base: Theory,
    recursion: Kernel.Thm
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val step = Term.variable("g", stepType)
    val start = Term.variable("a", Values)
    val letter = Term.variable("x", Element)
    val word = Term.variable("w", Words)
    val ignored = Term.variable("r", Values)

    for {
      // `\x. \w. \r. g x r`, which is the general step with the tail thrown away.
      applied <- LogicError.lift(Term.appAll(step, List(letter, ignored)))
      stepFunction <- LogicError.lift(Term.absAll(List(letter, word, ignored), applied))

      instance <- rules.specAll(recursion, List(start, stepFunction))
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))

      chosen <- classical.witness(opened)
      selected <- chosen.conclusion match {
        case App(_, term) => Right(term)
        case other => Left(NotOfForm("a predicate applied to what was chosen", other))
      }
      body <- LogicError.lift(Term.absAll(List(step, start), selected))
      defined <- LogicError.lift(Kernel.defineConstant(base, Fold, body))
      (theory, definition) = defined

      reduced <- Conv
        .betaNormalise(chosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))
      unfolded <- Conv.unfold(definition, List(step, start))

      empty <- LogicError.lift(theory.constant(Concatenation.Empty, Words))
      chosenAtEmpty <- rules.conjElim1(reduced)
      atEmpty <- Conv
        .apThm(unfolded, empty)
        .flatMap(Conv.trans(_, chosenAtEmpty))
        .flatMap(rules.genAll(_, List(step, start)))

      consConstant <- LogicError.lift(theory.constant(Listing.Cons, consType))
      consed <- LogicError.lift(Term.appAll(consConstant, List(letter, word)))
      chosenAtCons <- rules.conjElim2(reduced).flatMap(rules.specAll(_, List(letter, word)))
      onTheLeft <- Conv.apThm(unfolded, consed)
      back <- Conv.apThm(unfolded, word).flatMap(Conv.sym)
      partial <- LogicError.lift(Term.app(step, letter))
      onTheRight <- Conv.apTerm(partial, back)
      atCons <- Conv
        .trans(onTheLeft, chosenAtCons)
        .flatMap(Conv.trans(_, onTheRight))
        .flatMap(rules.genAll(_, List(step, start, letter, word)))
    } yield (theory, definition, atEmpty, atCons)
  }

  /**
   * [[FoldOfConcat]]: `Listing.Induct` on the left half.
   *
   * The base is the left unit of concatenation on one side and [[FoldOfEmpty]] on the other. The
   * step is the whole of it: `WORD_CONCAT (LIST_CONS x u) v` is `LIST_CONS x (WORD_CONCAT u v)`,
   * which is the definition of `LIST_CONS` opened, associativity, and the definition closed again;
   * [[FoldOfCons]] then puts the hypothesis's own left-hand side under `g`, and the second use of
   * [[FoldOfCons]] read backwards closes it.
   */
  private def foldOverAConcatenation(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    consDefinition: Kernel.Thm,
    induct: Kernel.Thm,
    held: (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm)
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (atEmpty, atCons, emptyLeft, associative) = held

    for {
      goal <- Parser.proposition(theory, notation, Statements.toMap.apply(FoldOfConcat))
      stripped <- Logic.stripForall(goal)
      variables = stripped._1
      step <- variables.headOption.toRight(NotOfForm("a claim about every step", goal))
      start <- variables.drop(1).headOption.toRight(NotOfForm("a claim about every start", goal))
      left <- variables.drop(2).headOption.toRight(NotOfForm("a claim about every word", goal))
      right <- variables.drop(3).headOption.toRight(NotOfForm("a claim about every word", goal))

      foldConstant <- LogicError.lift(theory.constant(Fold, foldType))
      concatConstant <- LogicError.lift(theory.constant(Concatenation.Name, concatType))
      empty <- LogicError.lift(theory.constant(Concatenation.Empty, Words))

      // `\u. LIST_FOLD g a (WORD_CONCAT u v) = LIST_FOLD g (LIST_FOLD g a v) u`
      //
      // `taken` holds the variables the STATEMENT binds and not only the ones free in it, and the
      // difference is not academic: the goal is closed, so what is free in it is empty, and a
      // variable chosen fresh against that set collided with the `v` the statement binds. The
      // abstraction then captured it and the base case came out about the empty word twice.
      taken = Term.freeVariables(goal) ++ variables.toSet
      subject = Conv.freshVariable("u", Words, taken)
      outer <- LogicError.lift(Term.appAll(foldConstant, List(step, start)))
      joined <- LogicError.lift(Term.appAll(concatConstant, List(subject, right)))
      onTheLeft <- LogicError.lift(Term.app(outer, joined))
      inner <- LogicError.lift(Term.app(outer, right))
      reFolded <- LogicError.lift(Term.appAll(foldConstant, List(step, inner)))
      onTheRight <- LogicError.lift(Term.app(reFolded, subject))
      equation <- LogicError.lift(Term.eq(onTheLeft, onTheRight))
      predicate <- LogicError.lift(Term.abs(subject, equation))

      instance <- rules.spec(predicate, induct)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      // The base: the left unit on one side, the fold's own value at the empty list on the other.
      unit <- rules.spec(right, emptyLeft).flatMap(Conv.apTerm(outer, _))
      collapsed <- rules.specAll(atEmpty, List(step, inner)).flatMap(Conv.sym)
      base <- Conv.trans(unit, collapsed)
      _ <-
        if (base.conclusion == baseTerm) Right(())
        else Left(NotOfForm("the split at the empty left half", base.conclusion))

      stepStripped <- Logic.stripForall(stepTerm)
      letter <- stepStripped._1.headOption.toRight(
        NotOfForm("a claim about every letter", stepTerm)
      )
      word <- stepStripped._1.drop(1).headOption.toRight(
        NotOfForm("a claim about every word", stepTerm)
      )
      stepParts <- logic
        .destImp(stepStripped._2)
        .toRight(NotOfForm("an implication", stepStripped._2))
      hypothesis <- LogicError.lift(Kernel.assume(stepParts._1))

      moved <- consOfAConcatenation(
        logic, theory, consDefinition, associative, concatConstant, (letter, word, right))
      carried <- Conv.apTerm(outer, moved)
      innerJoined <- LogicError.lift(Term.appAll(concatConstant, List(word, right)))
      unrolled <- rules.specAll(atCons, List(step, start, letter, innerJoined))
      partial <- LogicError.lift(Term.app(step, letter))
      underStep <- Conv.apTerm(partial, hypothesis)
      rolled <- rules.specAll(atCons, List(step, inner, letter, word)).flatMap(Conv.sym)
      reached <- Conv
        .trans(carried, unrolled)
        .flatMap(Conv.trans(_, underStep))
        .flatMap(Conv.trans(_, rolled))
      _ <-
        if (reached.conclusion == stepParts._2) Right(())
        else Left(NotOfForm("the split at a longer left half", reached.conclusion))

      stepCase <- rules
        .disch(stepParts._1, reached)
        .flatMap(rules.genAll(_, List(letter, word)))
      // The induction quantifies the left half OUTSIDE the right one, and the statement quantifies
      // them the way a reader writes them, which is the other way round. So what comes out is
      // specialised at the statement's own left half and then generalised over all four: a proof by
      // induction on `u` cannot produce `!u. !v.` directly, because `v` is free while the induction
      // runs and there is nowhere to bind it first.
      everywhere <- rules.conjIntro(base, stepCase).flatMap(rules.mp(opened, _))
      result <- rules.spec(left, everywhere).flatMap(rules.genAll(_, variables.toList))
      _ <-
        if (result.conclusion == goal) Right(())
        else Left(NotOfForm("the split as it is written", result.conclusion))
    } yield result
  }

  /**
   * `|- WORD_CONCAT (LIST_CONS x u) v = LIST_CONS x (WORD_CONCAT u v)`.
   *
   * The one fact the step runs on, and it is about the concatenation rather than about the fold. It
   * is not published here: a consumer wanting it wants it about lists and the place for it is
   * `Listing`, so putting it there is a change to that file rather than a fact this development may
   * declare on its behalf. `Listing.successorsCancel` records the same judgement for the same
   * reason one floor down, and two call sites is where it becomes worth moving.
   */
  private def consOfAConcatenation(
    logic: Logic,
    theory: Theory,
    consDefinition: Kernel.Thm,
    associative: Kernel.Thm,
    concatConstant: Term,
    arguments: (Term, Term, Term)
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (letter, left, right) = arguments

    for {
      opened <- Conv.unfold(consDefinition, List(letter, left))
      onTheLeft <- Conv.apTerm(concatConstant, opened).flatMap(Conv.apThm(_, right))

      singletonConstant <- LogicError.lift(
        theory.constant(Concatenation.Singleton, Type.fun(Element, Words))
      )
      singleton <- LogicError.lift(Term.app(singletonConstant, letter))
      shifted <- rules.specAll(associative, List(singleton, left, right))

      joined <- LogicError.lift(Term.appAll(concatConstant, List(left, right)))
      closed <- Conv.unfold(consDefinition, List(letter, joined)).flatMap(Conv.sym)
      result <- Conv.trans(onTheLeft, shifted).flatMap(Conv.trans(_, closed))
    } yield result
  }
}
