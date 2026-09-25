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
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

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

  /**
   * `|- !P w. LIST_FOLD (\x r. P x /\ r) T w = (!i. NUM_LT i (WORD_LENGTH w) ==> P (WORD_NTH w i))`.
   *
   * "Every letter satisfies `P`", read two ways: as a fold, which is what a definition by lists
   * writes, and by position, which is what every proof written before the lists reads. It is the
   * bridge that lets a development move a predicate onto the lists without rewriting what is built
   * on it, and `Collatz`'s two marker-free predicates are the first to cross it. `Listing.Induct` on
   * `w`, and the step is the one fact about positions a cons has: position zero is its letter and
   * position `SUC i` is the tail's `i`.
   */
  val FoldOfEvery: String = "LIST_FOLD_EVERY"

  /**
   * `|- !P u v. LIST_FOLD (\x r. P x /\ r) T (WORD_CONCAT u v) = (LIST_FOLD (\x r. P x /\ r) T u /\ LIST_FOLD (\x r. P x /\ r) T v)`.
   *
   * The same predicate split over a concatenation, from [[FoldOfConcat]] and one induction that
   * moves a starting value out of a fold of conjunctions. Nothing positional is in it: no index, no
   * length, no offset by `WORD_LENGTH u`, which is what the same statement proved by position has to
   * carry through every step.
   */
  val FoldOfEveryConcat: String = "LIST_FOLD_EVERY_CONCAT"

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
        "LIST_FOLD g a (WORD_CONCAT u v) = LIST_FOLD g (LIST_FOLD g a v) u"),
    FoldOfEvery ->
      ("!P:'a->bool. !w:word('a). LIST_FOLD (\\x:'a. \\r:bool. P x /\\ r) T w = " +
        "(!i:num. NUM_LT i (WORD_LENGTH w) ==> P (WORD_NTH w i))"),
    FoldOfEveryConcat ->
      ("!P:'a->bool. !u:word('a). !v:word('a). " +
        "LIST_FOLD (\\x:'a. \\r:bool. P x /\\ r) T (WORD_CONCAT u v) = " +
        "(LIST_FOLD (\\x:'a. \\r:bool. P x /\\ r) T u /\\ " +
        "LIST_FOLD (\\x:'a. \\r:bool. P x /\\ r) T v)")
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
      every <- foldOfEvery(logic, theory, notation, listing, (atEmpty, atCons))
      everyConcat <- everyOverAConcatenation(
        logic, theory, notation, induct, (atEmpty, atCons, overConcat))

      facts = Map(
        FoldOfEmpty -> atEmpty,
        FoldOfCons -> atCons,
        FoldOfConcat -> overConcat,
        FoldOfEvery -> every,
        FoldOfEveryConcat -> everyConcat
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
   * [[FoldOfEvery]], by `Listing.Induct` on the word with `P` left free and bound at the end.
   *
   * The base is the fold's value at the empty list against a bound nothing is below, which
   * `NUM_NOT_LT_ZERO` refuses; the step is [[FoldOfCons]], one beta step that opens the
   * conjunction, the hypothesis under it, and [[everyOfACons]] to close.
   */
  private def foldOfEvery(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    listing: Listing,
    held: (Kernel.Thm, Kernel.Thm)
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (atEmpty, atCons) = held
    def read(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)
    def free(text: String): Either[LogicError, FVar] = read(text).flatMap {
      case variable: FVar => Right(variable)
      case other => Left(NotOfForm("a variable", other))
    }

    for {
      goal <- Parser.proposition(theory, notation, Statements.toMap.apply(FoldOfEvery))
      // The predicate the derivation runs over is the one read below, and it is bound at the end by
      // that name: `stripForall` hands back a variable of its own choosing, which the derivation
      // never mentions, so generalising over it would bind nothing and leave `P` free.
      predicate <- free("P:'a->bool")
      step <- read("\\x:'a. \\r:bool. (P:'a->bool) x /\\ r")
      truth <- rules.truth
      atEmptyBool = Kernel.instType(Map(Classical.CodomainVariable -> Type.Bool), atEmpty)
      atConsBool = Kernel.instType(Map(Classical.CodomainVariable -> Type.Bool), atCons)
      induct <- listing.fact(Listing.Induct)
      emptyLength <- listing.concatenation.fact(Concatenation.EmptyLength)
      notBelowZero <- listing.peano.fact(Peano.NotBelowZero)
      consCase <- everyOfACons(logic, theory, notation, listing)

      // `\w. LIST_FOLD step T w = (!i. NUM_LT i (WORD_LENGTH w) ==> P (WORD_NTH w i))`
      subject <- read("\\w:word('a). LIST_FOLD (\\x:'a. \\r:bool. (P:'a->bool) x /\\ r) T w = " +
        "(!i:num. NUM_LT i (WORD_LENGTH w) ==> P (WORD_NTH w i))")
      instance <- rules.spec(subject, induct)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic.destImp(opened.conclusion).toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      // The base: nothing is below zero, so the claim about every position holds and equals `T`.
      atZero <- rules.specAll(atEmptyBool, List(step, truth.conclusion))
      index <- free("i:num")
      below <- read("NUM_LT (i:num) (WORD_LENGTH (WORD_EMPTY:word('a)))")
      assumed <- LogicError.lift(Kernel.assume(below))
      belowTerm <- read("NUM_LT (i:num)")
      atLength <- Conv.apTerm(belowTerm, emptyLength).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, assumed)))
      refused <- rules.spec(index, notBelowZero)
      absurd <- rules.notElim(refused, atLength)
      letter <- read("(P:'a->bool) (WORD_NTH (WORD_EMPTY:word('a)) (i:num))")
      anything <- rules.falsityElim(letter, absurd)
      vacuous <- rules.disch(below, anything).flatMap(rules.gen(index, _))
      asTruth <- rules.eqTruthIntro(vacuous).flatMap(Conv.sym)
      base <- Conv.trans(atZero, asTruth)
      _ <- if (base.conclusion == baseTerm) Right(())
           else Left(NotOfForm("the claim at the empty list", base.conclusion))

      // The step: one cons, the conjunction it opens, the hypothesis under it.
      stepStripped <- Logic.stripForall(stepTerm)
      head <- stepStripped._1.headOption.toRight(NotOfForm("a claim about every letter", stepTerm))
      tail <- stepStripped._1.drop(1).headOption.toRight(NotOfForm("a claim about every word", stepTerm))
      stepParts <- logic.destImp(stepStripped._2).toRight(NotOfForm("an implication", stepStripped._2))
      hypothesis <- LogicError.lift(Kernel.assume(stepParts._1))
      unrolled <- rules.specAll(atConsBool, List(step, truth.conclusion, head, tail))
      applied <- rightOfEquation(unrolled.conclusion)
      contracted <- Conv.betaNormalise(applied)
      opening <- Conv.trans(unrolled, contracted)
      conjunction <- rightOfEquation(opening.conclusion)
      withLetter <- conjunction match {
        case App(partial, _) => Right(partial)
        case other => Left(NotOfForm("a conjunction", other))
      }
      carried <- Conv.apTerm(withLetter, hypothesis)
      closed <- rules.specAll(consCase, List(head, tail))
      reached <- Conv.trans(opening, carried).flatMap(Conv.trans(_, closed))
      _ <- if (reached.conclusion == stepParts._2) Right(())
           else Left(NotOfForm("the claim at a cons", reached.conclusion))
      stepCase <- rules.disch(stepParts._1, reached).flatMap(rules.genAll(_, List(head, tail)))

      everywhere <- rules.conjIntro(base, stepCase).flatMap(rules.mp(opened, _))
      result <- rules.gen(predicate, everywhere)
      _ <- if (result.conclusion == goal) Right(())
           else Left(NotOfForm("every letter as it is written", result.conclusion))
    } yield result
  }

  /**
   * `|- !x w. ((P:'a->bool) x /\ (!i. NUM_LT i (WORD_LENGTH w) ==> P (WORD_NTH w i))) =
   *    (!i. NUM_LT i (WORD_LENGTH (LIST_CONS x w)) ==> P (WORD_NTH (LIST_CONS x w) i))`, `P` free.
   *
   * The two positions a cons has, and each direction is one of them. Going down, position zero
   * gives the letter and `SUC j` gives the tail's `j`, which needs `j < n` carried to
   * `SUC j < SUC n`. Going up, `NUM_CASES` splits the index and `NUM_LT_SUC_CASES` brings
   * `SUC y < SUC n` back to `y < n`. The two directions are joined by `Kernel.deductAntisym`, each
   * one's conclusion being the other's hypothesis.
   *
   * That the letter is at position zero is not a fact `Listing` publishes, and it is not needed as
   * one: `LIST_HEAD` is defined as the entry at zero and `LIST_HEAD_CONS` says it is the letter.
   */
  private def everyOfACons(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    listing: Listing
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val peano = listing.peano
    def read(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)
    def free(text: String): Either[LogicError, FVar] = read(text).flatMap {
      case variable: FVar => Right(variable)
      case other => Left(NotOfForm("a variable", other))
    }

    for {
      consLength <- listing.fact(Listing.ConsLength)
      consNth <- listing.fact(Listing.ConsNth)
      headOfCons <- listing.fact(Listing.HeadOfCons)
      headDefinition <- listing.definition(Listing.Head)
      zeroBelow <- peano.fact(Peano.SuccessorPositive)
      belowSuccessor <- peano.fact(Peano.BelowSuccessor)
      belowCases <- peano.fact(Peano.BelowSuccessorCases)
      transitive <- peano.fact(Peano.StrictTransitive)
      zeroOrSuccessor <- peano.naturals.fact(Natural.ZeroOrSuccessor)
      keepsOrder <- successorsKeepOrder(logic, theory, notation, peano)

      x <- free("x:'a")
      w <- free("w:word('a)")
      predicate <- read("P:'a->bool")
      cons <- read("LIST_CONS (x:'a) (w:word('a))")
      size <- read("WORD_LENGTH (w:word('a))")
      zero <- read("ZERO")
      nthOfCons <- read("WORD_NTH (LIST_CONS (x:'a) (w:word('a)))")
      less <- read("NUM_LT")
      ofCons <- read("!i:num. NUM_LT i (WORD_LENGTH (LIST_CONS (x:'a) (w:word('a)))) ==> " +
        "(P:'a->bool) (WORD_NTH (LIST_CONS x w) i)")
      split <- read("(P:'a->bool) (x:'a) /\\ (!i:num. NUM_LT i (WORD_LENGTH (w:word('a))) ==> " +
        "P (WORD_NTH w i))")

      length <- rules.specAll(consLength, List(x, w))
      unfolded <- Conv.unfold(headDefinition, List(cons))
      headAt <- rules.specAll(headOfCons, List(x, w))
      atZero <- Conv.sym(unfolded).flatMap(Conv.trans(_, headAt))

      // Down: from every position of the cons to the letter and every position of the tail.
      every <- LogicError.lift(Kernel.assume(ofCons))
      belowLength = (t: Term, proof: Kernel.Thm) =>
        LogicError.lift(Term.app(less, t)).flatMap(Conv.apTerm(_, length)).flatMap(Conv.sym)
          .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, proof)))
      zeroLess <- rules.spec(size, zeroBelow)
      zeroLessLength <- belowLength(zero, zeroLess)
      atFirst <- rules.spec(zero, every).flatMap(rules.mp(_, zeroLessLength))
      letter <- Conv.apTerm(predicate, atZero).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, atFirst)))
      j <- free("j:num")
      jBelow <- read("NUM_LT (j:num) (WORD_LENGTH (w:word('a)))")
      jAssumed <- LogicError.lift(Kernel.assume(jBelow))
      successorOfJ <- read("SUC (j:num)")
      jMoved <- rules.specAll(keepsOrder, List(j, size)).flatMap(rules.mp(_, jAssumed))
      jLess <- belowLength(successorOfJ, jMoved)
      atNext <- rules.spec(successorOfJ, every).flatMap(rules.mp(_, jLess))
      shifted <- rules.specAll(consNth, List(x, w, j)).flatMap(Conv.apTerm(predicate, _))
      tailLetter <- LogicError.lift(Kernel.eqMp(shifted, atNext))
      tailEvery <- rules.disch(jBelow, tailLetter).flatMap(rules.gen(j, _))
      down <- rules.conjIntro(letter, tailEvery)

      // Up: from the letter and every position of the tail to every position of the cons.
      both <- LogicError.lift(Kernel.assume(split))
      i <- free("i:num")
      iBelow <- read("NUM_LT (i:num) (WORD_LENGTH (LIST_CONS (x:'a) (w:word('a))))")
      iAssumed <- LogicError.lift(Kernel.assume(iBelow))
      iLess <- LogicError.lift(Term.app(less, i)).flatMap(Conv.apTerm(_, length))
        .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, iAssumed)))
      cases <- rules.spec(i, zeroOrSuccessor)

      isZero <- read("(i:num) = ZERO")
      zeroAssumed <- LogicError.lift(Kernel.assume(isZero))
      toZero <- Conv.apTerm(nthOfCons, zeroAssumed).flatMap(Conv.apTerm(predicate, _))
      toLetter <- Conv.apTerm(predicate, atZero).flatMap(Conv.trans(toZero, _))
      firstCase <- rules.conjElim1(both).flatMap(held => Conv.sym(toLetter)
        .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, held))))

      y <- free("y:num")
      isSuccessor <- read("(i:num) = SUC (y:num)")
      successorAssumed <- LogicError.lift(Kernel.assume(isSuccessor))
      successorOfY <- read("SUC (y:num)")
      bound <- read("SUC (WORD_LENGTH (w:word('a)))")
      yMoved <- Conv.apTerm(less, successorAssumed).flatMap(Conv.apThm(_, bound))
        .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, iLess)))
      yCases <- rules.specAll(belowCases, List(size, successorOfY)).flatMap(rules.mp(_, yMoved))
      yBelowItsSuccessor <- rules.spec(y, belowSuccessor)
      strictlyBelow <- read("NUM_LT (SUC (y:num)) (WORD_LENGTH (w:word('a)))")
      strictAssumed <- LogicError.lift(Kernel.assume(strictlyBelow))
      viaTransitivity <- rules.conjIntro(yBelowItsSuccessor, strictAssumed)
        .flatMap(pair => rules.specAll(transitive, List(y, successorOfY, size)).flatMap(rules.mp(_, pair)))
      equalToSize <- read("SUC (y:num) = WORD_LENGTH (w:word('a))")
      equalAssumed <- LogicError.lift(Kernel.assume(equalToSize))
      yLessThan <- LogicError.lift(Term.app(less, y))
      viaEquality <- Conv.apTerm(yLessThan, equalAssumed)
        .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, yBelowItsSuccessor)))
      yBelow <- rules.disjElim(yCases, viaTransitivity, viaEquality)
      tailAtY <- rules.conjElim2(both).flatMap(rules.spec(y, _)).flatMap(rules.mp(_, yBelow))
      consAtY <- rules.specAll(consNth, List(x, w, y)).flatMap(Conv.apTerm(predicate, _))
        .flatMap(Conv.sym).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, tailAtY)))
      backToI <- Conv.apTerm(nthOfCons, successorAssumed).flatMap(Conv.apTerm(predicate, _))
        .flatMap(Conv.sym).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, consAtY)))
      existential <- read("?y:num. (i:num) = SUC y")
      existentialAssumed <- LogicError.lift(Kernel.assume(existential))
      secondCase <- rules.existsElim(existentialAssumed, y, backToI)

      atI <- rules.disjElim(cases, firstCase, secondCase)
      up <- rules.disch(iBelow, atI).flatMap(rules.gen(i, _))

      joined = Kernel.deductAntisym(down, up)
      result <- rules.genAll(joined, List(x, w))
    } yield result
  }

  /**
   * `|- !m n. NUM_LT m n ==> NUM_LT (SUC m) (SUC n)`, which `Peano` does not publish.
   *
   * `NUM_ADD_LT_MONOTONE` at the summand `SUC ZERO`, with `SUC ZERO + m` rewritten to `SUC m` by the
   * two recurrences of addition read from the left. Private here for the reason
   * [[consOfAConcatenation]] gives: a fact about `num` belongs to `Peano`, and a second consumer is
   * where it becomes worth moving there.
   */
  private def successorsKeepOrder(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    peano: Peano
  ): Either[LogicError, Kernel.Thm] =
    for {
      monotone <- peano.fact(Peano.AddStrictlyMonotone)
      zeroPlus <- peano.fact(Peano.ZeroPlus)
      successorPlus <- peano.fact(Peano.SuccessorPlus)
      one <- Parser.term(theory, notation, "SUC ZERO")
      instance <- logic.rules.spec(one, monotone)
      rules <- Rewrite.Rule.all(logic, Vector(successorPlus, zeroPlus))
      result <- Rewrite.inTheorem(rules, instance)
      expected <- Parser.proposition(theory, notation, "!m:num n:num. NUM_LT m n ==> NUM_LT (SUC m) (SUC n)")
      _ <- if (result.conclusion == expected) Right(())
           else Left(NotOfForm("the order carried across a successor", result.conclusion))
    } yield result

  /**
   * [[FoldOfEveryConcat]]: [[FoldOfConcat]] puts the fold of `v` in the starting place of the fold
   * of `u`, and a fold of conjunctions started at `b` is the fold started at `T`, conjoined with
   * `b`. The second is `Listing.Induct` on `u` with `b` and `P` free; its step is one
   * reassociation of a conjunction, derived rather than looked up.
   */
  private def everyOverAConcatenation(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    induct: Kernel.Thm,
    held: (Kernel.Thm, Kernel.Thm, Kernel.Thm)
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (atEmpty, atCons, overConcat) = held
    val toBool = Map(Classical.CodomainVariable -> Type.Bool)
    def read(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)

    for {
      goal <- Parser.proposition(theory, notation, Statements.toMap.apply(FoldOfEveryConcat))
      stripped <- Logic.stripForall(goal)
      variables = stripped._1
      truth <- rules.truth
      atEmptyBool = Kernel.instType(toBool, atEmpty)
      atConsBool = Kernel.instType(toBool, atCons)
      overConcatBool = Kernel.instType(toBool, overConcat)
      step <- read("\\x:'a. \\r:bool. (P:'a->bool) x /\\ r")
      start <- read("b:bool")
      and <- read("T /\\ T").flatMap {
        case App(App(operator, _), _) => Right(operator)
        case other => Left(NotOfForm("a conjunction", other))
      }

      subject <- read("\\u:word('a). LIST_FOLD (\\x:'a. \\r:bool. (P:'a->bool) x /\\ r) (b:bool) u = " +
        "(LIST_FOLD (\\x:'a. \\r:bool. P x /\\ r) T u /\\ b)")
      instance <- rules.spec(subject, induct)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic.destImp(opened.conclusion).toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      // The base: `b` against `T /\ b`.
      fromStart <- rules.specAll(atEmptyBool, List(step, start))
      fromTruth <- rules.specAll(atEmptyBool, List(step, truth.conclusion))
        .flatMap(Conv.apTerm(and, _)).flatMap(Conv.apThm(_, start))
      startAlone <- LogicError.lift(Kernel.assume(start))
      withTruth <- rules.conjIntro(truth, startAlone)
      truthAnd <- read("T /\\ (b:bool)")
      conjoined <- LogicError.lift(Kernel.assume(truthAnd))
      dropped <- rules.conjElim2(conjoined)
      unit = Kernel.deductAntisym(dropped, withTruth)
      base <- Conv.sym(fromTruth).flatMap(Conv.trans(unit, _)).flatMap(Conv.trans(fromStart, _))
      _ <- if (base.conclusion == baseTerm) Right(())
           else Left(NotOfForm("the start moved out at the empty list", base.conclusion))

      // The step.
      stepStripped <- Logic.stripForall(stepTerm)
      head <- stepStripped._1.headOption.toRight(NotOfForm("a claim about every letter", stepTerm))
      tail <- stepStripped._1.drop(1).headOption.toRight(NotOfForm("a claim about every word", stepTerm))
      stepParts <- logic.destImp(stepStripped._2).toRight(NotOfForm("an implication", stepStripped._2))
      hypothesis <- LogicError.lift(Kernel.assume(stepParts._1))

      leftUnrolled <- rules.specAll(atConsBool, List(step, start, head, tail))
      leftOpened <- rightOfEquation(leftUnrolled.conclusion).flatMap(Conv.betaNormalise)
        .flatMap(Conv.trans(leftUnrolled, _))
      leftConjunction <- rightOfEquation(leftOpened.conclusion)
      withLetter <- leftConjunction match {
        case App(partial, _) => Right(partial)
        case other => Left(NotOfForm("a conjunction", other))
      }
      letter <- withLetter match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("a conjunction", other))
      }
      leftCarried <- Conv.apTerm(withLetter, hypothesis).flatMap(Conv.trans(leftOpened, _))

      rightUnrolled <- rules.specAll(atConsBool, List(step, truth.conclusion, head, tail))
      rightOpened <- rightOfEquation(rightUnrolled.conclusion).flatMap(Conv.betaNormalise)
        .flatMap(Conv.trans(rightUnrolled, _))
        .flatMap(Conv.apTerm(and, _)).flatMap(Conv.apThm(_, start))
      rightConjunction <- rightOfEquation(rightOpened.conclusion)
      inner <- rightConjunction match {
        case App(App(_, App(App(_, _), folded)), _) => Right(folded)
        case other => Left(NotOfForm("a conjunction of a conjunction", other))
      }
      associated <- reassociate(logic, and, letter, inner, start)
      reached <- Conv.sym(rightOpened).flatMap(Conv.trans(associated, _)).flatMap(Conv.trans(leftCarried, _))
      _ <- if (reached.conclusion == stepParts._2) Right(())
           else Left(NotOfForm("the start moved out at a cons", reached.conclusion))
      stepCase <- rules.disch(stepParts._1, reached).flatMap(rules.genAll(_, List(head, tail)))

      moved <- rules.conjIntro(base, stepCase).flatMap(rules.mp(opened, _))
      startFree <- start match {
        case variable: FVar => Right(variable)
        case other => Left(NotOfForm("a variable", other))
      }
      anyStart <- rules.gen(startFree, moved)

      predicate <- read("P:'a->bool").flatMap {
        case variable: FVar => Right(variable)
        case other => Left(NotOfForm("a variable", other))
      }
      left <- variables.drop(1).headOption.toRight(NotOfForm("a claim about every word", goal))
      right <- variables.drop(2).headOption.toRight(NotOfForm("a claim about every word", goal))
      ofRight <- read("LIST_FOLD (\\x:'a. \\r:bool. (P:'a->bool) x /\\ r) T")
        .flatMap(folded => LogicError.lift(Term.app(folded, right)))
      split <- rules.specAll(overConcatBool, List(step, truth.conclusion, left, right))
      movedOut <- rules.specAll(anyStart, List(ofRight, left))
      result <- Conv.trans(split, movedOut).flatMap(rules.genAll(_, List(predicate, left, right)))
      _ <- if (result.conclusion == goal) Right(())
           else Left(NotOfForm("every letter of a concatenation as it is written", result.conclusion))
    } yield result
  }

  /** `|- (p /\ (q /\ r)) = ((p /\ q) /\ r)`, from the conjunction's rules and nothing else. */
  private def reassociate(
    logic: Logic,
    and: Term,
    p: Term,
    q: Term,
    r: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      qr <- LogicError.lift(Term.appAll(and, List(q, r)))
      nested <- LogicError.lift(Term.appAll(and, List(p, qr)))
      pq <- LogicError.lift(Term.appAll(and, List(p, q)))
      flat <- LogicError.lift(Term.appAll(and, List(pq, r)))
      fromNested <- LogicError.lift(Kernel.assume(nested))
      nestedP <- rules.conjElim1(fromNested)
      nestedQR <- rules.conjElim2(fromNested)
      nestedQ <- rules.conjElim1(nestedQR)
      nestedR <- rules.conjElim2(nestedQR)
      toFlat <- rules.conjIntro(nestedP, nestedQ).flatMap(rules.conjIntro(_, nestedR))
      fromFlat <- LogicError.lift(Kernel.assume(flat))
      flatPQ <- rules.conjElim1(fromFlat)
      flatR <- rules.conjElim2(fromFlat)
      flatP <- rules.conjElim1(flatPQ)
      flatQ <- rules.conjElim2(flatPQ)
      toNested <- rules.conjIntro(flatQ, flatR).flatMap(rules.conjIntro(flatP, _))
    } yield Kernel.deductAntisym(toNested, toFlat)
  }

  private def rightOfEquation(term: Term): Either[LogicError, Term] =
    Term.destEq(term).map(_._2).toRight(NotOfForm("an equation", term))

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
