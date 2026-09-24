package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The list interface over `word`: a head, a tail, a constructor, and the principles that make a
 * sequence something a definition can descend through.
 *
 * == Why there is no `list` type here, which is the decision this file exists to carry ==
 *
 * The obvious reading of "this repository has no lists" is that a type is missing, and the card
 * that asked for the work said so. It is not what was measured. `word('a)` is a type operator of
 * arity one -- the arity is read off the predicate `\p:prod(num,num->'a). ...` that
 * [[Word.RepresentationBody]] carves with, so the element type is a variable and a word over any
 * type at all is a word -- and `Concatenation` already publishes `WORD_EMPTY`, `WORD_SINGLETON`,
 * `WORD_CONCAT` and an induction principle. A second type carved out of the **same** predicate
 * would be isomorphic to `word('a)` and would inherit none of its seventeen facts: every lemma
 * about concatenation, about a prefix, about a factor and about a tally would have to be proved a
 * second time on a carrier differing from the first in nothing.
 *
 * So what was missing was never the carrier. It is the **orientation**: [[Concatenation.Induction]]
 * extends a word on the right, and a definition by recursion on a sequence descends from the
 * **left**. Those are different principles about one type, and this development is the second of
 * them.
 *
 * == What it costs ==
 *
 * Three definitions and no axiom. [[Listing.Cons]] is not a constructor in the sense a carved free
 * algebra has one: it is `WORD_CONCAT (WORD_SINGLETON x) w` under a name, and every law about it
 * below comes out of `Concatenation`'s laws about those two. The empty list is `WORD_EMPTY` and
 * gets no second name, which is the whole of what a link rather than a duplicate means here: a
 * reader who has a word has a list, with no coercion between them and nothing to keep in step.
 *
 * == What the distinctness and injectivity of the two constructors rest on ==
 *
 * A carved free algebra gets `~(CONS h t = NIL)` from its tags. There are no tags here and the
 * facts are theorems instead: [[Listing.ConsNotEmpty]] is `SUC n` never being `ZERO` read through
 * the lengths, and [[Listing.ConsInjective]] is [[Listing.HeadOfCons]] and [[Listing.TailOfCons]]
 * applied to one equation. Nothing is weaker for it, and the two are what stop [[Listing.Cases]]
 * from being a disjunction whose halves can both hold.
 */
final class Listing private (
  val concatenation: Concatenation,
  val peano: Peano,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = concatenation.word.product.classical.logic
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

object Listing {

  /* ---------------------------------------------------------------- the constants */

  /**
   * `LIST_CONS x w` is `w` with `x` in front of it.
   *
   * The empty list has no constant of its own and is `WORD_EMPTY`. A `LIST_NIL` defined equal to it
   * would be a second name for one term, and then every fact would exist in two spellings with
   * nothing keeping them in step.
   */
  val Cons: String = "LIST_CONS"

  /**
   * The first letter, which is `WORD_NTH w ZERO`.
   *
   * At the empty word it is `WORD_PAD`, by [[Word.NthAbove]], and nothing here says so on purpose:
   * what `WORD_PAD` is, is not determined, so a fact about the head of the empty list would be a
   * fact about a term nobody can evaluate. Every statement below that mentions a head either has a
   * cons in it or carries the word's positive length.
   */
  val Head: String = "LIST_HEAD"

  /**
   * Everything after the first letter.
   *
   * At the empty word it is the empty word, since `PRE ZERO` is `ZERO`. That is a total function
   * answering somewhere rather than a claim that the empty list has a tail, and it is the same
   * shape `NUM_SUB`'s truncation has one floor down.
   */
  val Tail: String = "LIST_TAIL"

  /* ------------------------------------------------------------------- the facts */

  /** `|- !x w. WORD_LENGTH (LIST_CONS x w) = SUC (WORD_LENGTH w)`. */
  val ConsLength: String = "LIST_CONS_LENGTH"

  /** `|- !x w. LIST_HEAD (LIST_CONS x w) = x`. */
  val HeadOfCons: String = "LIST_HEAD_CONS"

  /**
   * `|- !x w i. WORD_NTH (LIST_CONS x w) (SUC i) = WORD_NTH w i`.
   *
   * No guard, and that is worth a line because the concatenation's own law carries one.
   * `WORD_CONCAT_NTH_RIGHT` states the entry at `WORD_LENGTH u + i` under `i < WORD_LENGTH v`;
   * above that length both sides here are `WORD_PAD`, so the equation holds there as well and the
   * case split is what buys the guard's removal. A consumer stepping along a list does not then
   * have to carry a bound it does not have.
   */
  val ConsNth: String = "LIST_CONS_NTH"

  /** `|- !x w. ~(LIST_CONS x w = WORD_EMPTY)`. */
  val ConsNotEmpty: String = "LIST_CONS_NOT_EMPTY"

  /** `|- !x w. LIST_TAIL (LIST_CONS x w) = w`. */
  val TailOfCons: String = "LIST_TAIL_CONS"

  /** `|- !x w y v. LIST_CONS x w = LIST_CONS y v ==> x = y /\ w = v`. */
  val ConsInjective: String = "LIST_CONS_INJECTIVE"

  /** `|- !w. w = WORD_EMPTY \/ w = LIST_CONS (LIST_HEAD w) (LIST_TAIL w)`. */
  val Cases: String = "LIST_CASES"

  /**
   * `|- !P. P WORD_EMPTY /\ (!x w. P w ==> P (LIST_CONS x w)) ==> !w. P w`
   *
   * Cons-induction, which is [[Concatenation.Induction]] read from the other end.
   */
  val Induct: String = "LIST_INDUCT"

  /**
   * `|- !a g. ?f. f WORD_EMPTY = a /\ (!x w. f (LIST_CONS x w) = g x w (f w))`
   *
   * Structural recursion, which is what a **definition** needs and what [[Induct]] does not give.
   * Induction proves a property of every list; it does not produce a function, and until this
   * landed the interface could be used in a proof and not in a definition.
   *
   * == Why the auxiliary function recurses on a number ==
   *
   * `word('a)` is a defined type and the only recursion principle it has is the one it was carved
   * with, which is `num`'s. So the function is built at one remove: `Recursion.theorem` at the
   * result type `word('a) -> 'b` gives an `F : num -> word('a) -> 'b` with
   *
   * {{{
   *   F ZERO    = \w. a
   *   F (SUC n) = \w. g (LIST_HEAD w) (LIST_TAIL w) (F n (LIST_TAIL w))
   * }}}
   *
   * and the witness is `\w. F (WORD_LENGTH w) w`. The two equations come out of it with **no
   * induction at all**: at the empty word the length is `ZERO`, and at a cons it is
   * `SUC (WORD_LENGTH w)` by [[ConsLength]], so the step's own equation fires once and
   * [[HeadOfCons]] and [[TailOfCons]] read the two arguments back. That the step's recursive call
   * lands on `w` rather than on something shorter-by-accident is [[TailOfCons]] and nothing else.
   *
   * **This is where [[Head]] and [[Tail]] being constants is spent.** `docs/adr/0038` says they are
   * constants rather than terms built inside a proof because the step above has to name them, and
   * this is the theorem that names them. `Concatenation` builds the front of a word inside its own
   * induction and writes that nobody had asked for a name; something asks here.
   *
   * == The uniqueness is a second theorem and not a `?!` ==
   *
   * This logic has no unique-existence quantifier, so [[RecursionUnique]] states the other half
   * separately. `Recursion.Statement` on `num` is written the same way for the same reason.
   */
  val RecursionTheorem: String = "LIST_RECURSION"

  /**
   * `|- !a g f h. <f satisfies the two equations> /\ <h satisfies them> ==> f = h`
   *
   * The other half of [[RecursionTheorem]]. [[Induct]] on `\w. f w = h w`, then `Classical.ext`:
   * the base is the two values at the empty word being one and the same `a`, and the step rewrites
   * the recursive call with the induction hypothesis under `g`.
   *
   * A consumer that defines a constant from [[RecursionTheorem]] gets its two equations and
   * **nothing saying they pin it down**; that is what this supplies, and it is what makes a
   * definition by recursion a definition rather than a choice among many.
   */
  val RecursionUnique: String = "LIST_RECURSION_UNIQUE"

  /* ------------------------------------------------------------------- the types */

  private val Element: Type = TyVar(Classical.TypeVariable)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Words: Type = TyApp(Word.TypeName, List(Element))
  private val Entries: Type = Type.fun(Numbers, Element)

  private def lengthType: Type = Type.fun(Words, Numbers)
  private def nthType: Type = Type.fun(Words, Entries)
  private def consType: Type = Type.fun(Element, Type.fun(Words, Words))
  private def headType: Type = Type.fun(Words, Element)
  private def tailType: Type = Type.fun(Words, Words)
  private def singletonType: Type = Type.fun(Element, Words)
  private def concatType: Type = Type.fun(Words, Type.fun(Words, Words))
  private def orderType: Type = Type.fun(Numbers, Type.fun(Numbers, Type.Bool))
  private def successorType: Type = Type.fun(Numbers, Numbers)
  private def predecessorType: Type = Type.fun(Numbers, Numbers)
  private def predicateType: Type = Type.fun(Words, Type.Bool)
  private def binaryNumbers: Type = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  /* ------------------------------------------------------------------ the bodies */

  /**
   * The three definitions, as text, in the order they are introduced.
   *
   * [[Tail]]'s body is the one to read. It is `WORD_MAKE` of a function reading `w` one place
   * further along, and the conditional is the padding rather than the operation: `WORD_MAKE`
   * carries a premise saying what it was handed is `WORD_PAD` at and above the length, and the
   * `COND` is how that premise is discharged by `COND_FALSE` alone. The same bookkeeping
   * `WORD_CONCAT`'s own body does, for the same reason and at one conditional fewer.
   */
  val Definitions: Vector[(String, String)] = Vector(
    Cons -> "\\x:'a. \\w:word('a). WORD_CONCAT (WORD_SINGLETON x) w",
    Head -> "\\w:word('a). WORD_NTH w ZERO",
    Tail ->
      ("\\w:word('a). WORD_MAKE (PRE (WORD_LENGTH w)) " +
        "(\\i:num. COND (NUM_LT i (PRE (WORD_LENGTH w))) (WORD_NTH w (SUC i)) WORD_PAD)")
  )

  /**
   * What every derived fact says, as text, in the order they are derived.
   *
   * Compared as terms rather than as printed text, for the reason `Product.Statements` gives: a
   * type variable is written `'a` and printed `a`, so a printed polymorphic statement does not read
   * back.
   */
  val Statements: Vector[(String, String)] = Vector(
    ConsLength ->
      "!x:'a. !w:word('a). WORD_LENGTH (LIST_CONS x w) = SUC (WORD_LENGTH w)",
    HeadOfCons ->
      "!x:'a. !w:word('a). LIST_HEAD (LIST_CONS x w) = x",
    ConsNth ->
      "!x:'a. !w:word('a). !i:num. WORD_NTH (LIST_CONS x w) (SUC i) = WORD_NTH w i",
    ConsNotEmpty ->
      "!x:'a. !w:word('a). ~(LIST_CONS x w = WORD_EMPTY)",
    TailOfCons ->
      "!x:'a. !w:word('a). LIST_TAIL (LIST_CONS x w) = w",
    ConsInjective ->
      ("!x:'a. !w:word('a). !y:'a. !v:word('a). LIST_CONS x w = LIST_CONS y v ==> " +
        "x = y /\\ w = v"),
    Cases ->
      "!w:word('a). w = WORD_EMPTY \\/ w = LIST_CONS (LIST_HEAD w) (LIST_TAIL w)",
    Induct ->
      ("!P:word('a)->bool. P WORD_EMPTY /\\ " +
        "(!x:'a. !w:word('a). P w ==> P (LIST_CONS x w)) ==> " +
        "!w:word('a). P w"),
    RecursionTheorem ->
      ("!a:'b. !g:'a->word('a)->'b->'b. ?f:word('a)->'b. " +
        "f WORD_EMPTY = a /\\ " +
        "(!x:'a. !w:word('a). f (LIST_CONS x w) = g x w (f w))"),
    RecursionUnique ->
      ("!a:'b. !g:'a->word('a)->'b->'b. !f:word('a)->'b. !h:word('a)->'b. " +
        "(f WORD_EMPTY = a /\\ " +
        "(!x:'a. !w:word('a). f (LIST_CONS x w) = g x w (f w))) /\\ " +
        "(h WORD_EMPTY = a /\\ " +
        "(!x:'a. !w:word('a). h (LIST_CONS x w) = g x w (h w))) ==> f = h")
  )

  /** The development in the chain's signature, which is the one a consumer reaches for. */
  lazy val standard: Listing = Chain.standard.listing

  /**
   * The development over a `Concatenation`, the `Peano` it was built over, and the theory to
   * extend.
   *
   * `base` is not `concatenation.theory` for the reason `Concatenation.construct` gives about its
   * own: what a link extends is the chain's end when it is built, and a development that extended
   * its prerequisite would declare its constants into a side branch nothing above can see.
   */
  def construct(
    concatenation: Concatenation,
    peano: Peano,
    base: Theory
  ): Either[LogicError, Listing] = {
    val classical = concatenation.word.product.classical
    val notation = concatenation.notation

    def define(
      theory: Theory,
      name: String,
      text: String
    ): Either[LogicError, (Theory, Kernel.Thm)] =
      for {
        body <- Parser.term(theory, notation, text)
        defined <- LogicError.lift(Kernel.defineConstant(theory, name, body))
      } yield defined

    for {
      first <- define(base, Cons, Definitions(0)._2)
      (withCons, consDefinition) = first
      second <- define(withCons, Head, Definitions(1)._2)
      (withHead, headDefinition) = second
      third <- define(withHead, Tail, Definitions(2)._2)
      (theory, tailDefinition) = third

      logic <- classical.logic.over(theory)
      held <- Held.of(peano, concatenation, classical)

      consLength <- lengthOfACons(logic, theory, consDefinition, held)
      headOfCons <- headOfACons(logic, theory, consDefinition, headDefinition, held)
      consNth <- nthOfACons(logic, theory, consDefinition, consLength, held)
      consNotEmpty <- aConsIsNotEmpty(logic, theory, consLength, held)
      tailOfCons <- tailOfACons(
        logic, theory, tailDefinition, consLength, consNth, held)
      consInjective <- aConsIsInjective(logic, theory, headOfCons, tailOfCons, held)
      cases <- theCases(
        logic, theory, notation, tailDefinition, headDefinition,
        consLength, consNth, headOfCons, held)
      induct <- consInduction(
        logic, theory, notation, tailDefinition, headDefinition,
        consLength, consNth, headOfCons, held)
      recursion <- structuralRecursion(
        logic, theory, notation, consLength, headOfCons, tailOfCons, held)
      recursionUnique <- recursionIsUnique(logic, theory, notation, induct, held)

      facts = Map(
        ConsLength -> consLength,
        HeadOfCons -> headOfCons,
        ConsNth -> consNth,
        ConsNotEmpty -> consNotEmpty,
        TailOfCons -> tailOfCons,
        ConsInjective -> consInjective,
        Cases -> cases,
        Induct -> induct,
        RecursionTheorem -> recursion,
        RecursionUnique -> recursionUnique
      )

      // Each statement checked against the text a person reads it by, here rather than in the spec:
      // a development that built something other than what it says it built must not be handed out.
      // A name not yet derived is skipped rather than refused, which is what lets this list carry
      // the whole surface while the development is still being built out.
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
    } yield new Listing(
      concatenation,
      peano,
      theory,
      notation,
      Map(
        Cons -> consDefinition,
        Head -> headDefinition,
        Tail -> tailDefinition
      ),
      facts
    )
  }

  /* --------------------------------------------------------------- the derivations */

  /**
   * [[ConsLength]]: the concatenation's length law, with the one-letter word's length in it.
   *
   * `|singleton x| + |w|` is `SUC ZERO + |w|`, and `NUM_SUC_ADD` then `NUM_ZERO_ADD` bring that to
   * `SUC |w|`. This way round rather than through `NUM_ADD_SUC`, because the successor is on the
   * **left** summand here and `NUM_ADD_SUC` opens the right one.
   */
  private def lengthOfACons(
    logic: Logic,
    theory: Theory,
    consDefinition: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", Element)
    val w = Term.variable("w", Words)

    for {
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      singletonConstant <- LogicError.lift(theory.constant(Concatenation.Singleton, singletonType))

      opened <- Conv.unfold(consDefinition, List(x, w))
      carried <- Conv.apTerm(lengthConstant, opened)

      letter <- LogicError.lift(Term.app(singletonConstant, x))
      split <- rules.specAll(held.concatLength, List(letter, w))
      asSum <- Conv.trans(carried, split)

      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      lengthOfW <- LogicError.lift(Term.app(lengthConstant, w))
      letterLength <- rules.spec(x, held.singletonLength)
      shaped <- Conv.apTerm(plus, letterLength).flatMap(Conv.apThm(_, lengthOfW))
      reached <- Conv.trans(asSum, shaped)

      collapsed <- oneMore(logic, theory, lengthOfW, held)
      value <- Conv.trans(reached, collapsed)
      result <- rules.genAll(value, List(x, w))
    } yield result
  }

  /**
   * [[HeadOfCons]]: the entry at zero of a concatenation whose left half has one letter.
   *
   * `WORD_CONCAT_NTH_LEFT` wants `ZERO < WORD_LENGTH (WORD_SINGLETON x)`, which is `ZERO < SUC ZERO`
   * once the one-letter word's length is in place, and that is `NUM_ZERO_LT_SUC`. Then
   * `WORD_SINGLETON_NTH` reads the letter off.
   */
  private def headOfACons(
    logic: Logic,
    theory: Theory,
    consDefinition: Kernel.Thm,
    headDefinition: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", Element)
    val w = Term.variable("w", Words)

    for {
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      singletonConstant <- LogicError.lift(theory.constant(Concatenation.Singleton, singletonType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      consConstant <- LogicError.lift(theory.constant(Cons, consType))

      consed <- LogicError.lift(Term.appAll(consConstant, List(x, w)))
      headOpened <- Conv.unfold(headDefinition, List(consed))

      consOpened <- Conv.unfold(consDefinition, List(x, w))
      atZero <- Conv.apTerm(nthConstant, consOpened).flatMap(Conv.apThm(_, zero))

      letter <- LogicError.lift(Term.app(singletonConstant, x))
      letterLength <- rules.spec(x, held.singletonLength)
      positive <- rules.spec(zero, held.successorPositive)
      below <- LogicError.lift(Term.app(strictOrder, zero))
      transported <- Conv.sym(letterLength).flatMap(Conv.apTerm(below, _))
      guard <- LogicError.lift(Kernel.eqMp(transported, positive))

      onTheLeft <- rules
        .specAll(held.concatNthLeft, List(letter, w, zero))
        .flatMap(rules.mp(_, guard))
      letterEntry <- rules.spec(x, held.singletonNth)

      value <- Conv
        .trans(headOpened, atZero)
        .flatMap(Conv.trans(_, onTheLeft))
        .flatMap(Conv.trans(_, letterEntry))
      result <- rules.genAll(value, List(x, w))
    } yield result
  }

  /**
   * [[ConsNth]]: the right half's own entry below its length, and the pad at or above it.
   *
   * Two branches, and the second is what removes the guard `WORD_CONCAT_NTH_RIGHT` carries. Below
   * the length the entry is `w`'s at `i`, once the index `WORD_LENGTH (WORD_SINGLETON x) + i` has
   * been brought to `SUC i`. At or above it, `Word.NthAbove` says both sides are `WORD_PAD`: on the
   * right directly, on the left after the cons's own length has turned `~(i < |w|)` into
   * `~(SUC i < |LIST_CONS x w|)`, which is [[successorIsAbove]].
   */
  private def nthOfACons(
    logic: Logic,
    theory: Theory,
    consDefinition: Kernel.Thm,
    consLength: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", Element)
    val w = Term.variable("w", Words)
    val i = Term.variable("i", Numbers)

    for {
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      singletonConstant <- LogicError.lift(theory.constant(Concatenation.Singleton, singletonType))
      concatConstant <- LogicError.lift(theory.constant(Concatenation.Name, concatType))
      consConstant <- LogicError.lift(theory.constant(Cons, consType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      successor <- LogicError.lift(theory.constant(Natural.NumberSuccessor, successorType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))

      letter <- LogicError.lift(Term.app(singletonConstant, x))
      lengthOfW <- LogicError.lift(Term.app(lengthConstant, w))
      successorOfI <- LogicError.lift(Term.app(successor, i))
      joined <- LogicError.lift(Term.appAll(concatConstant, List(letter, w)))
      consed <- LogicError.lift(Term.appAll(consConstant, List(x, w)))

      consOpened <- Conv.unfold(consDefinition, List(x, w))
      atIndex <- Conv.apTerm(nthConstant, consOpened).flatMap(Conv.apThm(_, successorOfI))

      // Below the length: the right half answers, at an index that has to be moved.
      guardTerm <- LogicError.lift(Term.appAll(strictOrder, List(i, lengthOfW)))
      assumed <- LogicError.lift(Kernel.assume(guardTerm))
      onTheRight <- rules
        .specAll(held.concatNthRight, List(letter, w, i))
        .flatMap(rules.mp(_, assumed))

      letterLength <- rules.spec(x, held.singletonLength)
      shifted <- Conv.apTerm(plus, letterLength).flatMap(Conv.apThm(_, i))
      toSuccessor <- oneMore(logic, theory, i, held)
      indexAgrees <- Conv.trans(shifted, toSuccessor)
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))
      carried <- Conv.apTerm(nthOfJoined, indexAgrees)
      below <- Conv.sym(carried).flatMap(Conv.trans(_, onTheRight))
      insideValue <- Conv.trans(atIndex, below)

      // At or above the length: both sides are the pad, by the type's own law.
      negated <- logic.mkNot(guardTerm)
      assumedAbove <- LogicError.lift(Kernel.assume(negated))
      rightIsPad <- rules.specAll(held.nthAbove, List(w, i)).flatMap(rules.mp(_, assumedAbove))
      consLengthHere <- rules.specAll(consLength, List(x, w))
      aboveCons <- successorIsAbove(
        logic, theory, consLengthHere, consed, i, lengthOfW, assumedAbove, held)
      leftIsPad <- rules
        .specAll(held.nthAbove, List(consed, successorOfI))
        .flatMap(rules.mp(_, aboveCons))
      aboveValue <- Conv.sym(rightIsPad).flatMap(Conv.trans(leftIsPad, _))

      middle <- held.classical.excludedMiddleAt(guardTerm)
      settled <- rules.disjElim(middle, insideValue, aboveValue)
      result <- rules.genAll(settled, List(x, w, i))
    } yield result
  }

  /**
   * `G |- ~(NUM_LT (SUC i) (WORD_LENGTH consed))`, from `G |- ~(NUM_LT i (WORD_LENGTH w))`.
   *
   * The cons is one longer than `w`, so an index past `w` is, one place further along, past the
   * cons. What carries it is [[successorsCancel]], and that lemma is derived here rather than taken
   * by name because `Peano` has no `SUC i < SUC n <==> i < n`: it has the cancellation for a sum,
   * and a successor is a sum with `SUC ZERO` on the left.
   */
  private def successorIsAbove(
    logic: Logic,
    theory: Theory,
    consLength: Kernel.Thm,
    consed: Term,
    i: Term,
    lengthOfW: Term,
    assumedAbove: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      successor <- LogicError.lift(theory.constant(Natural.NumberSuccessor, successorType))
      successorOfI <- LogicError.lift(Term.app(successor, i))
      lengthOfConsed <- LogicError.lift(Term.app(lengthConstant, consed))

      claim <- LogicError.lift(Term.appAll(strictOrder, List(successorOfI, lengthOfConsed)))
      supposed <- LogicError.lift(Kernel.assume(claim))

      below <- LogicError.lift(Term.app(strictOrder, successorOfI))
      atSuccessors <- Conv
        .apTerm(below, consLength)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, supposed)))

      cancelled <- successorsCancel(logic, theory, i, lengthOfW, held)
      inside <- rules.mp(cancelled, atSuccessors)
      absurd <- rules.notElim(assumedAbove, inside)
      result <- rules.notIntro(claim, absurd)
    } yield result
  }

  /**
   * `|- NUM_LT (SUC i) (SUC n) ==> NUM_LT i n`, built rather than taken by name.
   *
   * `Peano` publishes the cancellation for a sum, `NUM_LT (p + m) (p + n) ==> NUM_LT m n`, and not
   * the one for a successor. The two are the same fact at `p := SUC ZERO`, because
   * `SUC ZERO + m = SUC m` by `NUM_SUC_ADD` and `NUM_ZERO_ADD`; the work is carrying that equation
   * into both arguments of the order, which is one `apTerm` for the left and one for the right.
   *
   * It is not published. A consumer wanting it wants it about `num` and not about a list, so the
   * place for it is `Peano`, and putting it there is a change to that file rather than a fact this
   * development may declare on its behalf.
   */
  private def successorsCancel(
    logic: Logic,
    theory: Theory,
    i: Term,
    n: Term,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      successor <- LogicError.lift(theory.constant(Natural.NumberSuccessor, successorType))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      one <- LogicError.lift(Term.app(successor, zero))

      atI <- oneMore(logic, theory, i, held)
      atN <- oneMore(logic, theory, n, held)
      sumWithI <- LogicError.lift(Term.appAll(plus, List(one, i)))
      successorOfI <- LogicError.lift(Term.app(successor, i))
      successorOfN <- LogicError.lift(Term.app(successor, n))

      // `NUM_LT (SUC ZERO + i) (SUC ZERO + n) = NUM_LT (SUC i) (SUC n)`, in two steps.
      onTheLeft <- Conv.apTerm(strictOrder, atI).flatMap(Conv.apThm(_, successorOfN))
      partial <- LogicError.lift(Term.app(strictOrder, sumWithI))
      onTheRight <- Conv.apTerm(partial, atN)
      sameClaim <- Conv.trans(onTheRight, onTheLeft)

      claim <- LogicError.lift(Term.appAll(strictOrder, List(successorOfI, successorOfN)))
      supposed <- LogicError.lift(Kernel.assume(claim))
      asSum <- Conv
        .sym(sameClaim)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, supposed)))
      inside <- rules
        .specAll(held.addCancelsStrictOrder, List(one, i, n))
        .flatMap(rules.mp(_, asSum))
      result <- rules.disch(claim, inside)
    } yield result
  }

  /** `|- NUM_ADD (SUC ZERO) n = SUC n`, which is `NUM_SUC_ADD` and then `NUM_ZERO_ADD`. */
  private def oneMore(
    logic: Logic,
    theory: Theory,
    n: Term,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      successor <- LogicError.lift(theory.constant(Natural.NumberSuccessor, successorType))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      stepped <- rules.specAll(held.successorPlus, List(zero, n))
      collapsed <- rules.spec(n, held.zeroPlus)
      result <- Conv.apTerm(successor, collapsed).flatMap(Conv.trans(stepped, _))
    } yield result
  }

  /**
   * [[ConsNotEmpty]]: the lengths settle it, because `SUC n` is never `ZERO`.
   *
   * The equation gives `SUC (WORD_LENGTH w) = ZERO` by congruence on [[ConsLength]] and
   * `WORD_EMPTY_LENGTH`, which `NUM_SUC_NOT_ZERO` refuses.
   */
  private def aConsIsNotEmpty(
    logic: Logic,
    theory: Theory,
    consLength: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", Element)
    val w = Term.variable("w", Words)

    for {
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      empty <- LogicError.lift(theory.constant(Concatenation.Empty, Words))
      consConstant <- LogicError.lift(theory.constant(Cons, consType))
      consed <- LogicError.lift(Term.appAll(consConstant, List(x, w)))

      claim <- LogicError.lift(Term.eq(consed, empty))
      supposed <- LogicError.lift(Kernel.assume(claim))

      lengthsEqual <- Conv.apTerm(lengthConstant, supposed)
      atCons <- rules.specAll(consLength, List(x, w))
      successorIsZero <- Conv
        .sym(atCons)
        .flatMap(Conv.trans(_, lengthsEqual))
        .flatMap(Conv.trans(_, held.emptyLength))

      lengthOfW <- LogicError.lift(Term.app(lengthConstant, w))
      refused <- rules.spec(lengthOfW, held.successorNotZero)
      absurd <- rules.notElim(refused, successorIsZero)
      negated <- rules.notIntro(claim, absurd)
      result <- rules.genAll(negated, List(x, w))
    } yield result
  }

  /**
   * `|- WORD_LENGTH (LIST_TAIL w) = n` and `|- !i. i < n ==> WORD_NTH (LIST_TAIL w) i = WORD_NTH w (SUC i)`,
   * given `|- WORD_LENGTH w = SUC n`.
   *
   * The two facts every consumer of [[Tail]] below this line needs, and the only place the tail's
   * body is taken apart. The premise is a length of the form `SUC n` rather than
   * `~(WORD_LENGTH w = ZERO)`, and that is what keeps `PRE` out of everything downstream: at
   * `SUC n` the predecessor is `n` by `NUM_PRE_SUC` and no case split arises, where the negated
   * form would have to produce the `n` before it could say anything.
   *
   * **Nothing is rewritten under the binder.** The size `PRE (WORD_LENGTH w)` occurs twice, once as
   * `WORD_MAKE`'s first argument and once inside the guard of the conditional, and a rewrite of the
   * second would have to go under the lambda. Both laws of `WORD_MAKE` are taken at the term as it
   * stands and the equation `PRE (WORD_LENGTH w) = n` is applied afterwards, to the length in one
   * case and to the guard the caller supplies in the other.
   */
  private def theTail(
    logic: Logic,
    theory: Theory,
    tailDefinition: Kernel.Thm,
    subject: Term,
    size: Term,
    measured: Kernel.Thm,
    held: Held
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules

    for {
      opened <- Conv.unfold(tailDefinition, List(subject))
      made <- rightOf(opened)
      parts <- destructureMake(made)
      (bound, entries) = parts

      padding <- conditionalPadding(logic, theory, held.condFalse, made)
      madeLength <- rules
        .specAll(held.makeLength, List(bound, entries))
        .flatMap(rules.mp(_, padding))
      madeNth <- rules
        .specAll(held.makeNth, List(bound, entries))
        .flatMap(rules.mp(_, padding))

      predecessor <- LogicError.lift(theory.constant(Peano.Predecessor, predecessorType))
      atSuccessor <- rules.spec(size, held.preAtSuccessor)
      preIsSize <- Conv.apTerm(predecessor, measured).flatMap(Conv.trans(_, atSuccessor))

      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      tailLength <- Conv
        .apTerm(lengthConstant, opened)
        .flatMap(Conv.trans(_, madeLength))
        .flatMap(Conv.trans(_, preIsSize))

      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      index = Conv.freshVariable(
        "i",
        Numbers,
        Term.freeVariables(subject) ++ Term.freeVariables(size)
      )
      guard <- LogicError.lift(Term.appAll(strictOrder, List(index, size)))
      assumed <- LogicError.lift(Kernel.assume(guard))
      belowBound <- Conv
        .sym(preIsSize)
        .flatMap(equation => carryRight(strictOrder, index, equation, assumed))

      atIndex <- Conv.apTerm(nthConstant, opened).flatMap(Conv.apThm(_, index))
      viaMade <- Conv.apThm(madeNth, index)
      betaed <- rightOf(viaMade).flatMap(Conv.betaRoot).flatMap(Conv.trans(viaMade, _))
      conditional <- rightOf(betaed)
      branches <- destructureCond(conditional)
      (yes, no) = branches
      condGuard <- destructureCondGuard(conditional)
      chosen <- rules
        .specAll(held.condTrue, List(condGuard, yes, no))
        .flatMap(rules.mp(_, belowBound))
      value <- Conv.trans(atIndex, betaed).flatMap(Conv.trans(_, chosen))
      tailNth <- rules.disch(guard, value).flatMap(rules.gen(index, _))
    } yield (tailLength, tailNth)
  }

  /**
   * [[TailOfCons]]: [[theTail]] at a cons, then extensionality against the word that was consed on.
   *
   * The cons's length is `SUC (WORD_LENGTH w)` by [[ConsLength]], which is the premise [[theTail]]
   * asks for with `n := WORD_LENGTH w`, so the tail has `w`'s length and reads `WORD_NTH (cons) (SUC i)`
   * at `i`, which [[ConsNth]] says is `WORD_NTH w i`. Two words of one length agreeing below it are
   * one word.
   */
  private def tailOfACons(
    logic: Logic,
    theory: Theory,
    tailDefinition: Kernel.Thm,
    consLength: Kernel.Thm,
    consNth: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", Element)
    val w = Term.variable("w", Words)

    for {
      consConstant <- LogicError.lift(theory.constant(Cons, consType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      tailConstant <- LogicError.lift(theory.constant(Tail, tailType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      successor <- LogicError.lift(theory.constant(Natural.NumberSuccessor, successorType))

      consed <- LogicError.lift(Term.appAll(consConstant, List(x, w)))
      lengthOfW <- LogicError.lift(Term.app(lengthConstant, w))
      measured <- rules.specAll(consLength, List(x, w))

      both <- theTail(logic, theory, tailDefinition, consed, lengthOfW, measured, held)
      (tailLength, tailNth) = both
      tailed <- LogicError.lift(Term.app(tailConstant, consed))

      index = Conv.freshVariable("i", Numbers, Set(x, w).flatMap(Term.freeVariables))
      lengthOfTail <- LogicError.lift(Term.app(lengthConstant, tailed))
      guard <- LogicError.lift(Term.appAll(strictOrder, List(index, lengthOfTail)))
      assumed <- LogicError.lift(Kernel.assume(guard))
      belowW <- carryRight(strictOrder, index, tailLength, assumed)

      fromTail <- rules.spec(index, tailNth).flatMap(rules.mp(_, belowW))
      fromCons <- rules.specAll(consNth, List(x, w, index))
      entry <- Conv.trans(fromTail, fromCons)
      agreement <- rules.disch(guard, entry).flatMap(rules.gen(index, _))

      lengths <- Right(tailLength)
      conjoined <- rules.conjIntro(lengths, agreement)
      equal <- rules.specAll(held.extensional, List(tailed, w)).flatMap(rules.mp(_, conjoined))
      result <- rules.genAll(equal, List(x, w))
    } yield result
  }

  /**
   * [[ConsInjective]]: the head and the tail read the two arguments back off one equation.
   *
   * Congruence on the equation gives `LIST_HEAD (cons x w) = LIST_HEAD (cons y v)`, which
   * [[HeadOfCons]] reads as `x = y` at both ends, and the same with [[TailOfCons]] for the tails.
   */
  private def aConsIsInjective(
    logic: Logic,
    theory: Theory,
    headOfCons: Kernel.Thm,
    tailOfCons: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", Element)
    val w = Term.variable("w", Words)
    val y = Term.variable("y", Element)
    val v = Term.variable("v", Words)

    for {
      consConstant <- LogicError.lift(theory.constant(Cons, consType))
      headConstant <- LogicError.lift(theory.constant(Head, headType))
      tailConstant <- LogicError.lift(theory.constant(Tail, tailType))

      left <- LogicError.lift(Term.appAll(consConstant, List(x, w)))
      right <- LogicError.lift(Term.appAll(consConstant, List(y, v)))
      claim <- LogicError.lift(Term.eq(left, right))
      supposed <- LogicError.lift(Kernel.assume(claim))

      headsEqual <- Conv.apTerm(headConstant, supposed)
      leftHead <- rules.specAll(headOfCons, List(x, w))
      rightHead <- rules.specAll(headOfCons, List(y, v))
      letters <- Conv
        .sym(leftHead)
        .flatMap(Conv.trans(_, headsEqual))
        .flatMap(Conv.trans(_, rightHead))

      tailsEqual <- Conv.apTerm(tailConstant, supposed)
      leftTail <- rules.specAll(tailOfCons, List(x, w))
      rightTail <- rules.specAll(tailOfCons, List(y, v))
      words <- Conv
        .sym(leftTail)
        .flatMap(Conv.trans(_, tailsEqual))
        .flatMap(Conv.trans(_, rightTail))

      conjoined <- rules.conjIntro(letters, words)
      discharged <- rules.disch(claim, conjoined)
      result <- rules.genAll(discharged, List(x, w, y, v))
    } yield result
  }

  /**
   * `|- w = LIST_CONS (LIST_HEAD w) (LIST_TAIL w)`, given `|- WORD_LENGTH w = SUC n`.
   *
   * The decomposition both [[Cases]] and [[Induct]] run on, and the one derivation here that needs
   * a case split on an **index**. Extensionality asks for the lengths and for the entries below
   * them; `NUM_CASES` splits an index into zero and a successor, which is exactly the split the two
   * constructors make: at zero the cons answers with its head, which is `w`'s own entry at zero by
   * the definition of [[Head]], and at `SUC m` it answers with its tail's entry at `m`, which is
   * `w`'s at `SUC m` by [[theTail]] once `SUC m < SUC n` has been cancelled to `m < n`.
   */
  private def rebuilt(
    logic: Logic,
    theory: Theory,
    tailDefinition: Kernel.Thm,
    headDefinition: Kernel.Thm,
    consLength: Kernel.Thm,
    consNth: Kernel.Thm,
    headOfCons: Kernel.Thm,
    subject: Term,
    size: Term,
    measured: Kernel.Thm,
    held: Held
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules

    for {
      consConstant <- LogicError.lift(theory.constant(Cons, consType))
      headConstant <- LogicError.lift(theory.constant(Head, headType))
      tailConstant <- LogicError.lift(theory.constant(Tail, tailType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      successor <- LogicError.lift(theory.constant(Natural.NumberSuccessor, successorType))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))

      both <- theTail(logic, theory, tailDefinition, subject, size, measured, held)
      (tailLength, tailNth) = both

      headOfSubject <- LogicError.lift(Term.app(headConstant, subject))
      tailOfSubject <- LogicError.lift(Term.app(tailConstant, subject))
      joined <- LogicError.lift(Term.appAll(consConstant, List(headOfSubject, tailOfSubject)))

      // The lengths: the cons is one longer than the tail, and the tail is `n` long.
      consLengthHere <- rules.specAll(consLength, List(headOfSubject, tailOfSubject))
      liftedTail <- Conv.apTerm(successor, tailLength)
      joinedLength <- Conv.trans(consLengthHere, liftedTail)
      lengths <- Conv.sym(joinedLength).flatMap(Conv.trans(measured, _))

      // The entries, below the subject's own length.
      lengthOfSubject <- LogicError.lift(Term.app(lengthConstant, subject))
      index = Conv.freshVariable(
        "i",
        Numbers,
        Term.freeVariables(subject) ++ Term.freeVariables(size)
      )
      guard <- LogicError.lift(Term.appAll(strictOrder, List(index, lengthOfSubject)))
      assumedBelow <- LogicError.lift(Kernel.assume(guard))

      nthOfSubject <- LogicError.lift(Term.app(nthConstant, subject))
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))

      split <- rules.spec(index, held.zeroOrSuccessor)
      halves <- logic.destDisj(split.conclusion).toRight(
        NotOfForm("a disjunction", split.conclusion)
      )
      (isZero, isSuccessor) = halves

      atZero <- LogicError.lift(Kernel.assume(isZero)).flatMap { assumed =>
        entryAtZero(
          logic, theory, headDefinition, headOfCons,
          (subject, joined, headOfSubject, tailOfSubject, index),
          assumed
        )
      }

      atSuccessor <- LogicError.lift(Kernel.assume(isSuccessor)).flatMap { assumed =>
        entryAtASuccessor(
          logic, theory, consNth, tailNth,
          (subject, joined, headOfSubject, tailOfSubject, index, size),
          (assumedBelow, assumed, measured),
          held
        )
      }

      settled <- rules.disjElim(split, atZero, atSuccessor)
      agreement <- rules.disch(guard, settled).flatMap(rules.gen(index, _))

      conjoined <- rules.conjIntro(lengths, agreement)
      equal <- rules.specAll(held.extensional, List(subject, joined)).flatMap(rules.mp(_, conjoined))
    } yield (tailLength, equal)
  }

  /** At index zero the cons answers with its head, which is the subject's own entry at zero. */
  private def entryAtZero(
    logic: Logic,
    theory: Theory,
    headDefinition: Kernel.Thm,
    headOfCons: Kernel.Thm,
    terms: (Term, Term, Term, Term, Term),
    isZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (subject, joined, headOfSubject, tailOfSubject, index) = terms

    for {
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      nthOfSubject <- LogicError.lift(Term.app(nthConstant, subject))
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))

      // `WORD_NTH joined ZERO = LIST_HEAD joined = LIST_HEAD subject = WORD_NTH subject ZERO`
      headOfJoined <- Conv.unfold(headDefinition, List(joined))
      joinedHead <- rules.specAll(headOfCons, List(headOfSubject, tailOfSubject))
      headOfW <- Conv.unfold(headDefinition, List(subject))
      atZero <- Conv
        .sym(headOfJoined)
        .flatMap(Conv.trans(_, joinedHead))
        .flatMap(Conv.trans(_, headOfW))

      // Carried back to the index the claim is about.
      onTheLeft <- Conv.apTerm(nthOfSubject, isZero)
      onTheRight <- Conv.apTerm(nthOfJoined, isZero)
      bridge <- Conv.sym(atZero)
      stepped <- Conv.trans(onTheLeft, bridge)
      result <- Conv.sym(onTheRight).flatMap(Conv.trans(stepped, _))
    } yield result
  }

  /** Past zero the cons answers with its tail, which reads the subject one place further along. */
  private def entryAtASuccessor(
    logic: Logic,
    theory: Theory,
    consNth: Kernel.Thm,
    tailNth: Kernel.Thm,
    terms: (Term, Term, Term, Term, Term, Term),
    facts: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (subject, joined, headOfSubject, tailOfSubject, index, size) = terms
    val (assumedBelow, isSuccessor, measured) = facts

    for {
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      successor <- LogicError.lift(theory.constant(Natural.NumberSuccessor, successorType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      nthOfSubject <- LogicError.lift(Term.app(nthConstant, subject))
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))

      predicate <- logic
        .destExistsPredicate(isSuccessor.conclusion)
        .toRight(NotOfForm("an existential quantification", isSuccessor.conclusion))
      witness = Conv.freshVariable(
        "m",
        Numbers,
        Term.freeVariables(subject) ++ Term.freeVariables(size) ++ Term.freeVariables(index)
      )
      applied <- LogicError.lift(Term.app(predicate, witness))
      contraction <- Conv.betaRoot(applied)
      equationTerm <- rightOf(contraction)
      assumedEquation <- LogicError.lift(Kernel.assume(equationTerm))
      successorOfWitness <- LogicError.lift(Term.app(successor, witness))

      // `m < n`, from `i < WORD_LENGTH subject`, `i = SUC m` and `WORD_LENGTH subject = SUC n`.
      lengthOfSubject <- LogicError.lift(Term.app(lengthConstant, subject))
      atSuccessors <- carryRight(strictOrder, index, measured, assumedBelow)
      successorOfSize <- LogicError.lift(Term.app(successor, size))
      moved <- Conv
        .apTerm(strictOrder, assumedEquation)
        .flatMap(Conv.apThm(_, successorOfSize))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atSuccessors)))
      cancelled <- successorsCancel(logic, theory, witness, size, held)
      inside <- rules.mp(cancelled, moved)

      // The two entries at `SUC m`, joined through the tail.
      fromTail <- rules.spec(witness, tailNth).flatMap(rules.mp(_, inside))
      fromCons <- rules.specAll(consNth, List(headOfSubject, tailOfSubject, witness))
      atWitness <- Conv.trans(fromCons, fromTail)

      onTheLeft <- Conv.apTerm(nthOfSubject, assumedEquation)
      onTheRight <- Conv.apTerm(nthOfJoined, assumedEquation)
      bridge <- Conv.sym(atWitness)
      stepped <- Conv.trans(onTheLeft, bridge)
      value <- Conv.sym(onTheRight).flatMap(Conv.trans(stepped, _))

      result <- rules.existsElim(isSuccessor, witness, value)
    } yield result
  }

  /**
   * [[Cases]]: `NUM_CASES` at the length, with [[rebuilt]] on the successor side.
   *
   * A word whose length is zero is `WORD_EMPTY`, which is `Concatenation.LengthZero`; a word whose
   * length is `SUC n` is its head consed onto its tail. The two are exhaustive because the lengths
   * are, and they are exclusive because of [[ConsNotEmpty]], which is not needed here and is what a
   * consumer reaches for when it wants only one of them to hold.
   */
  private def theCases(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    tailDefinition: Kernel.Thm,
    headDefinition: Kernel.Thm,
    consLength: Kernel.Thm,
    consNth: Kernel.Thm,
    headOfCons: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      goal <- Parser.proposition(theory, notation, Statements.toMap.apply(Cases))
      stripped <- Logic.stripForall(goal)
      subject <- stripped._1.headOption.toRight(NotOfForm("a claim about every word", goal))
      halves <- logic.destDisj(stripped._2).toRight(NotOfForm("a disjunction", stripped._2))
      (isEmpty, isCons) = halves

      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      lengthOfSubject <- LogicError.lift(Term.app(lengthConstant, subject))
      split <- rules.spec(lengthOfSubject, held.zeroOrSuccessor)
      sides <- logic.destDisj(split.conclusion).toRight(
        NotOfForm("a disjunction", split.conclusion)
      )
      (lengthIsZero, lengthIsSuccessor) = sides

      // Length zero: the word is the empty one.
      assumedZero <- LogicError.lift(Kernel.assume(lengthIsZero))
      empty <- rules.spec(subject, held.lengthZero).flatMap(rules.mp(_, assumedZero))
      leftCase <- rules.disjIntro1(isCons, empty)

      // Length a successor: the word is its head consed onto its tail.
      assumedSuccessor <- LogicError.lift(Kernel.assume(lengthIsSuccessor))
      predicate <- logic
        .destExistsPredicate(lengthIsSuccessor)
        .toRight(NotOfForm("an existential quantification", lengthIsSuccessor))
      witness = Conv.freshVariable("n", Numbers, Term.freeVariables(goal))
      applied <- LogicError.lift(Term.app(predicate, witness))
      contraction <- Conv.betaRoot(applied)
      measuredTerm <- rightOf(contraction)
      measured <- LogicError.lift(Kernel.assume(measuredTerm))

      decomposed <- rebuilt(
        logic, theory, tailDefinition, headDefinition,
        consLength, consNth, headOfCons, subject, witness, measured, held)
      (_, equal) = decomposed
      injected <- rules.disjIntro2(isEmpty, equal)
      rightCase <- rules.existsElim(assumedSuccessor, witness, injected)

      settled <- rules.disjElim(split, leftCase, rightCase)
      result <- rules.gen(subject, settled)
      _ <-
        if (result.conclusion == goal) Right(())
        else Left(NotOfForm("the cases as they are written", result.conclusion))
    } yield result
  }

  /**
   * [[Induct]], by induction on the length with [[rebuilt]] supplying the step's decomposition.
   *
   * The predicate handed to `Natural.Induction` is `\n. !w. WORD_LENGTH w = n ==> P w`, which is
   * `Concatenation.rightwardInduction`'s shape and is the only one available: `word` is a defined
   * type and the recursion principle it was carved with is `num`'s. What differs from that mirror
   * is where the decomposition comes from -- there it is built inside the step and published
   * nowhere, here it is [[Head]] and [[Tail]], which are constants because [[Recursion]] above this
   * line needs to name them.
   */
  private def consInduction(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    tailDefinition: Kernel.Thm,
    headDefinition: Kernel.Thm,
    consLength: Kernel.Thm,
    consNth: Kernel.Thm,
    headOfCons: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      goal <- Parser.proposition(theory, notation, Statements.toMap.apply(Induct))
      stripped <- Logic.stripForall(goal)
      predicate <- stripped._1.headOption.toRight(NotOfForm("a claim about every predicate", goal))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (hypothesis, conclusion) = parts
      assumed <- LogicError.lift(Kernel.assume(hypothesis))
      atEmpty <- rules.conjElim1(assumed)
      stepRule <- rules.conjElim2(assumed)

      // `\n. !w. WORD_LENGTH w = n ==> P w`
      taken = Term.freeVariables(goal) + predicate
      size = Conv.freshVariable("n", Numbers, taken)
      subject = Conv.freshVariable("w", Words, taken + size)
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      lengthOfSubject <- LogicError.lift(Term.app(lengthConstant, subject))
      measuredTerm <- LogicError.lift(Term.eq(lengthOfSubject, size))
      heldAt <- LogicError.lift(Term.app(predicate, subject))
      claim <- logic.mkImp(measuredTerm, heldAt)
      claimAt <- logic.mkForall(subject, claim)
      abstracted <- LogicError.lift(Term.abs(size, claimAt))

      instance <- rules.spec(abstracted, held.induction)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      pair <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = pair

      base <- atLengthZero(logic, baseTerm, atEmpty, held)
      step <- atOneLonger(
        logic, theory, stepTerm, stepRule, tailDefinition, headDefinition,
        consLength, consNth, headOfCons, held)

      everywhere <- rules.conjIntro(base, step).flatMap(rules.mp(opened, _))
      finalWord = Conv.freshVariable("w", Words, taken)
      lengthOfFinal <- LogicError.lift(Term.app(lengthConstant, finalWord))
      reached <- rules
        .spec(lengthOfFinal, everywhere)
        .flatMap(rules.spec(finalWord, _))
        .flatMap(rules.mp(_, Conv.refl(lengthOfFinal)))
      general <- rules.gen(finalWord, reached)
      discharged <- rules.disch(hypothesis, general)
      result <- rules.gen(predicate, discharged)
      _ <-
        if (result.conclusion == goal) Right(())
        else Left(NotOfForm("the induction as it is written", result.conclusion))
    } yield result
  }

  /** The base: a word of length zero is `WORD_EMPTY`, so the predicate at the empty word is it. */
  private def atLengthZero(
    logic: Logic,
    baseTerm: Term,
    atEmpty: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      stripped <- Logic.stripForall(baseTerm)
      subject <- stripped._1.headOption.toRight(NotOfForm("a claim about every word", baseTerm))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (measured, heldAt) = parts
      assumed <- LogicError.lift(Kernel.assume(measured))

      equal <- rules.spec(subject, held.lengthZero).flatMap(rules.mp(_, assumed))
      transported <- Conv.apTerm(headOfApplication(heldAt), equal)
      reached <- Conv
        .sym(transported)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atEmpty)))
      discharged <- rules.disch(measured, reached)
      result <- rules.gen(subject, discharged)
    } yield result
  }

  /** The step: a word of length `SUC n` is its head consed onto a tail of length `n`. */
  private def atOneLonger(
    logic: Logic,
    theory: Theory,
    stepTerm: Term,
    stepRule: Kernel.Thm,
    tailDefinition: Kernel.Thm,
    headDefinition: Kernel.Thm,
    consLength: Kernel.Thm,
    consNth: Kernel.Thm,
    headOfCons: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      stripped <- Logic.stripForall(stepTerm)
      size <- stripped._1.headOption.toRight(NotOfForm("a claim about every number", stepTerm))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (hypothesisTerm, conclusionTerm) = parts
      hypothesis <- LogicError.lift(Kernel.assume(hypothesisTerm))

      inner <- Logic.stripForall(conclusionTerm)
      subject <- inner._1.headOption.toRight(NotOfForm("a claim about every word", conclusionTerm))
      innerParts <- logic.destImp(inner._2).toRight(NotOfForm("an implication", inner._2))
      (measuredTerm, heldAt) = innerParts
      measured <- LogicError.lift(Kernel.assume(measuredTerm))

      headConstant <- LogicError.lift(theory.constant(Head, headType))
      tailConstant <- LogicError.lift(theory.constant(Tail, tailType))
      headOfSubject <- LogicError.lift(Term.app(headConstant, subject))
      tailOfSubject <- LogicError.lift(Term.app(tailConstant, subject))

      decomposed <- rebuilt(
        logic, theory, tailDefinition, headDefinition,
        consLength, consNth, headOfCons, subject, size, measured, held)
      (tailLength, equal) = decomposed

      shorter <- rules.spec(tailOfSubject, hypothesis).flatMap(rules.mp(_, tailLength))
      lifted <- rules
        .specAll(stepRule, List(headOfSubject, tailOfSubject))
        .flatMap(rules.mp(_, shorter))

      transported <- Conv.apTerm(headOfApplication(heldAt), equal)
      reached <- Conv
        .sym(transported)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, lifted)))
      discharged <- rules.disch(measuredTerm, reached).flatMap(rules.gen(subject, _))
      result <- rules.disch(hypothesisTerm, discharged).flatMap(rules.gen(size, _))
    } yield result
  }

  /**
   * [[RecursionTheorem]]: `Recursion.theorem` at the result type `word('a) -> 'b`, read at the
   * length.
   *
   * The auxiliary function is `F : num -> word('a) -> 'b` with `F ZERO = \w. a` and
   * `F (SUC n) = \w. g (LIST_HEAD w) (LIST_TAIL w) (F n (LIST_TAIL w))`, and the function the
   * theorem asserts is `\w. F (WORD_LENGTH w) w`. **The type substitution is the one place to read
   * carefully**: the recursion theorem's own variable is `'a` and so is the element type of
   * `word('a)`, and what makes writing `'a := word('a) -> 'b` right rather than a collision is that
   * type substitution is simultaneous and does not walk into what it substitutes.
   * `Word.atEncoding` does exactly this and says so.
   *
   * **No induction happens here**, which is worth saying because the statement looks like it should
   * need one. The empty word's length is `ZERO` by `WORD_EMPTY_LENGTH`, so `F`'s first equation
   * fires; a cons's length is `SUC (WORD_LENGTH w)` by [[ConsLength]], so `F`'s second equation
   * fires once, and [[HeadOfCons]] and [[TailOfCons]] turn what it produced into `g x w (f w)`.
   * The induction is inside `Recursion.theorem` and is spent there.
   *
   * Everything is built at the variables the parsed statement binds rather than at variables named
   * here, for [[theCases]]'s reason: `existsIntro` compares against the predicate's own
   * beta-contraction, so a proof about a differently-named word is refused rather than accepted.
   */
  private def structuralRecursion(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    consLength: Kernel.Thm,
    headOfCons: Kernel.Thm,
    tailOfCons: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      goal <- Parser.proposition(theory, notation, Statements.toMap.apply(RecursionTheorem))
      stripped <- Logic.stripForall(goal)
      start <- stripped._1.headOption.toRight(
        NotOfForm("a claim about every starting value", goal)
      )
      stepper <- stripped._1.drop(1).headOption.toRight(
        NotOfForm("a claim about every step", goal)
      )
      predicate <- logic
        .destExistsPredicate(stripped._2)
        .toRight(NotOfForm("an existential quantification", stripped._2))

      headConstant <- LogicError.lift(theory.constant(Head, headType))
      tailConstant <- LogicError.lift(theory.constant(Tail, tailType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      consConstant <- LogicError.lift(theory.constant(Cons, consType))
      empty <- LogicError.lift(theory.constant(Concatenation.Empty, Words))

      results = Term.typeOf(start)
      functions = Type.fun(Words, results)

      // The variables the statement BINDS, not only those free in it: the goal is closed, so what
      // is free in it is empty, and a variable chosen fresh against that set is free to collide
      // with a binder the statement already spent.
      taken = Term.freeVariables(goal) ++ stripped._1.toSet

      // `\w. a` and `\p. \n. \w. g (LIST_HEAD w) (LIST_TAIL w) (p (LIST_TAIL w))`, which are the
      // two arguments `Recursion.theorem` takes. The step ignores the index, because a list's
      // recursive call is at its own tail rather than at a smaller number the caller can see.
      ignored = Conv.freshVariable("w", Words, taken)
      startFunction <- LogicError.lift(Term.abs(ignored, start))

      previous = Conv.freshVariable("p", functions, taken)
      index = Conv.freshVariable("n", Numbers, taken + previous)
      subject = Conv.freshVariable("w", Words, taken + previous + index)
      headOfSubject <- LogicError.lift(Term.app(headConstant, subject))
      tailOfSubject <- LogicError.lift(Term.app(tailConstant, subject))
      recursiveCall <- LogicError.lift(Term.app(previous, tailOfSubject))
      stepBody <- LogicError.lift(
        Term.appAll(stepper, List(headOfSubject, tailOfSubject, recursiveCall))
      )
      stepFunction <- LogicError.lift(
        Term.absAll(List(previous, index, subject), stepBody)
      )

      atFunctions = Kernel.instType(Map(Classical.TypeVariable -> functions), held.recursion)
      instance <- rules.specAll(atFunctions, List(startFunction, stepFunction))
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))

      // The auxiliary function, assumed to satisfy the two equations `Recursion.theorem` gives.
      auxiliary = Conv.freshVariable("F", Type.fun(Numbers, functions), taken)
      auxiliaryPredicate <- logic
        .destExistsPredicate(opened.conclusion)
        .toRight(NotOfForm("an existential quantification", opened.conclusion))
      applied <- LogicError.lift(Term.app(auxiliaryPredicate, auxiliary))
      contraction <- Conv.betaRoot(applied)
      bodyTerm <- rightOf(contraction)
      assumed <- LogicError.lift(Kernel.assume(bodyTerm))
      atZero <- rules.conjElim1(assumed)
      atStep <- rules.conjElim2(assumed)

      // The function the theorem asserts: read the auxiliary at the word's own length.
      witnessWord = Conv.freshVariable("w", Words, taken + auxiliary)
      lengthOfWitnessWord <- LogicError.lift(Term.app(lengthConstant, witnessWord))
      readOff <- LogicError.lift(
        Term.appAll(auxiliary, List(lengthOfWitnessWord, witnessWord))
      )
      witness <- LogicError.lift(Term.abs(witnessWord, readOff))

      // What `existsIntro` will compare against, taken apart so that the two halves are built at
      // exactly the terms it expects rather than at terms rebuilt from the statement by hand.
      wanted <- LogicError.lift(Term.app(predicate, witness)).flatMap(Conv.betaRoot).flatMap(rightOf)
      halves <- logic.destConj(wanted).toRight(NotOfForm("a conjunction", wanted))
      (atEmptyTarget, atConsTarget) = halves

      base <- valueAtTheEmptyList(witness, empty, auxiliary, atZero, held)
      _ <-
        if (base.conclusion == atEmptyTarget) Right(())
        else Left(NotOfForm("the value at the empty list as it is written", base.conclusion))

      stepStripped <- Logic.stripForall(atConsTarget)
      letter <- stepStripped._1.headOption.toRight(
        NotOfForm("a claim about every letter", atConsTarget)
      )
      word <- stepStripped._1.drop(1).headOption.toRight(
        NotOfForm("a claim about every word", atConsTarget)
      )
      stepValue <- valueAtACons(
        logic, witness, (auxiliary, stepper, consConstant, lengthConstant),
        (letter, word), atStep, consLength, headOfCons, tailOfCons)
      step <- rules.genAll(stepValue, List(letter, word))
      _ <-
        if (step.conclusion == atConsTarget) Right(())
        else Left(NotOfForm("the value at a cons as it is written", step.conclusion))

      conjoined <- rules.conjIntro(base, step)
      built <- rules.existsIntro(predicate, witness, conjoined)
      closed <- rules.existsElim(opened, auxiliary, built)
      result <- rules.genAll(closed, List(start, stepper))
      _ <-
        if (result.conclusion == goal) Right(())
        else Left(NotOfForm("the recursion as it is written", result.conclusion))
    } yield result
  }

  /**
   * `|- (\w. F (WORD_LENGTH w) w) WORD_EMPTY = a`, from `|- F ZERO = \w. a`.
   *
   * The application is left unreduced on the left, because that is the form `existsIntro` compares
   * against: it contracts the predicate at the witness and reduces the root only, so an inner
   * redex it did not touch has to survive in what is handed to it.
   */
  private def valueAtTheEmptyList(
    witness: Term,
    empty: Term,
    auxiliary: Term,
    atZero: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] =
    for {
      unfolded <- LogicError.lift(Term.app(witness, empty)).flatMap(Conv.betaRoot)
      atLengthZero <- Conv.apTerm(auxiliary, held.emptyLength).flatMap(Conv.apThm(_, empty))
      chosen <- Conv.apThm(atZero, empty)
      value <- rightOf(chosen).flatMap(Conv.betaRoot).flatMap(Conv.trans(chosen, _))
      result <- Conv
        .trans(unfolded, atLengthZero)
        .flatMap(Conv.trans(_, value))
    } yield result

  /**
   * `|- (\w. F (WORD_LENGTH w) w) (LIST_CONS x w) = g x w ((\w. F (WORD_LENGTH w) w) w)`.
   *
   * The whole of the recursion's step, and it is three rewrites over one equation of `F`. The
   * cons's length is `SUC (WORD_LENGTH w)`, so `F`'s successor equation applies and produces
   * `g (LIST_HEAD (cons x w)) (LIST_TAIL (cons x w)) (F (WORD_LENGTH w) (LIST_TAIL (cons x w)))`;
   * the head is `x` and the two tails are `w`, and the recursive call is then `F (WORD_LENGTH w) w`,
   * which is the witness at `w` read backwards.
   *
   * The congruences are built by hand rather than by the rewriter because the tail occurs twice in
   * one term and the two occurrences are reached from different operators, so what a rewrite pass
   * would do here is what these five steps do and it would do it without saying where.
   */
  private def valueAtACons(
    logic: Logic,
    witness: Term,
    constants: (Term, Term, Term, Term),
    arguments: (Term, Term),
    atStep: Kernel.Thm,
    consLength: Kernel.Thm,
    headOfCons: Kernel.Thm,
    tailOfCons: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (auxiliary, stepper, consConstant, lengthConstant) = constants
    val (letter, word) = arguments

    for {
      consed <- LogicError.lift(Term.appAll(consConstant, List(letter, word)))
      unfolded <- LogicError.lift(Term.app(witness, consed)).flatMap(Conv.betaRoot)

      measured <- rules.specAll(consLength, List(letter, word))
      movedIndex <- Conv.apTerm(auxiliary, measured).flatMap(Conv.apThm(_, consed))

      lengthOfWord <- LogicError.lift(Term.app(lengthConstant, word))
      stepped <- rules.spec(lengthOfWord, atStep).flatMap(Conv.apThm(_, consed))
      produced <- rightOf(stepped).flatMap(Conv.betaRoot).flatMap(Conv.trans(stepped, _))

      headEquation <- rules.specAll(headOfCons, List(letter, word))
      tailEquation <- rules.specAll(tailOfCons, List(letter, word))
      tailOfConsed <- leftOf(tailEquation)
      atLength <- LogicError.lift(Term.app(auxiliary, lengthOfWord))
      call <- LogicError.lift(Term.app(atLength, tailOfConsed))
      applied <- LogicError.lift(Term.app(stepper, letter))
      both <- LogicError.lift(Term.appAll(stepper, List(letter, word)))

      // `g <head> <tail> = g x w`, in two congruences, then carried to the recursive call.
      outer <- Conv
        .apTerm(stepper, headEquation)
        .flatMap(Conv.apThm(_, tailOfConsed))
        .flatMap(step => Conv.apTerm(applied, tailEquation).flatMap(Conv.trans(step, _)))
      carried <- Conv.apThm(outer, call)

      // `F (WORD_LENGTH w) <tail> = F (WORD_LENGTH w) w`, which is the witness at `w` backwards.
      inner <- Conv.apTerm(atLength, tailEquation)
      movedCall <- Conv.apTerm(both, inner)
      folded <- LogicError.lift(Term.app(witness, word))
        .flatMap(Conv.betaRoot)
        .flatMap(Conv.sym)
        .flatMap(Conv.apTerm(both, _))

      result <- Conv
        .trans(unfolded, movedIndex)
        .flatMap(Conv.trans(_, produced))
        .flatMap(Conv.trans(_, carried))
        .flatMap(Conv.trans(_, movedCall))
        .flatMap(Conv.trans(_, folded))
    } yield result
  }

  /**
   * [[RecursionUnique]]: [[Induct]] on `\w. f w = h w`, then function extensionality.
   *
   * The base is that both sides are the same `a` at the empty word, which is one `Conv.sym` and one
   * `Conv.trans`; the step rewrites the recursive call under `g` with the induction hypothesis, and
   * is where the hypothesis is genuinely spent. `Classical.ext` is taken against **this**
   * development's logic rather than the classical one, because eta has to be specialised at the
   * function type and `Classical.standard` has never heard of `word`.
   */
  private def recursionIsUnique(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    induct: Kernel.Thm,
    held: Held
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      goal <- Parser.proposition(theory, notation, Statements.toMap.apply(RecursionUnique))
      stripped <- Logic.stripForall(goal)
      variables = stripped._1
      stepper <- variables.drop(1).headOption.toRight(NotOfForm("a claim about every step", goal))
      first <- variables.drop(2).headOption.toRight(NotOfForm("a claim about a function", goal))
      second <- variables.drop(3).headOption.toRight(NotOfForm("a claim about a function", goal))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (hypothesisTerm, conclusionTerm) = parts
      assumed <- LogicError.lift(Kernel.assume(hypothesisTerm))
      firstHalf <- rules.conjElim1(assumed)
      secondHalf <- rules.conjElim2(assumed)
      firstAtEmpty <- rules.conjElim1(firstHalf)
      firstAtCons <- rules.conjElim2(firstHalf)
      secondAtEmpty <- rules.conjElim1(secondHalf)
      secondAtCons <- rules.conjElim2(secondHalf)

      consConstant <- LogicError.lift(theory.constant(Cons, consType))
      empty <- LogicError.lift(theory.constant(Concatenation.Empty, Words))

      // `\w. f w = h w`, the predicate the induction runs on. `taken` is what the statement binds
      // rather than what is free in it, for the reason [[structuralRecursion]] gives.
      taken = Term.freeVariables(goal) ++ variables.toSet
      subject = Conv.freshVariable("w", Words, taken)
      onTheLeft <- LogicError.lift(Term.app(first, subject))
      onTheRight <- LogicError.lift(Term.app(second, subject))
      agreement <- LogicError.lift(Term.eq(onTheLeft, onTheRight))
      predicate <- LogicError.lift(Term.abs(subject, agreement))

      instance <- rules.spec(predicate, induct)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      // The base: both are `a` at the empty word, so they are each other.
      base <- Conv.sym(secondAtEmpty).flatMap(Conv.trans(firstAtEmpty, _))
      _ <-
        if (base.conclusion == baseTerm) Right(())
        else Left(NotOfForm("the two functions agreeing at the empty list", base.conclusion))

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

      leftAtCons <- rules.specAll(firstAtCons, List(letter, word))
      rightAtCons <- rules.specAll(secondAtCons, List(letter, word))
      applied <- LogicError.lift(Term.appAll(stepper, List(letter, word)))
      underG <- Conv.apTerm(applied, hypothesis)
      reached <- Conv
        .trans(leftAtCons, underG)
        .flatMap(step => Conv.sym(rightAtCons).flatMap(Conv.trans(step, _)))
      step <- rules
        .disch(stepParts._1, reached)
        .flatMap(rules.genAll(_, List(letter, word)))

      everywhere <- rules.conjIntro(base, step).flatMap(rules.mp(opened, _))
      equal <- held.classical.ext(logic, everywhere)
      _ <-
        if (equal.conclusion == conclusionTerm) Right(())
        else Left(NotOfForm("the two functions being one", equal.conclusion))

      discharged <- rules.disch(hypothesisTerm, equal)
      result <- rules.genAll(discharged, variables.toList)
      _ <-
        if (result.conclusion == goal) Right(())
        else Left(NotOfForm("the uniqueness as it is written", result.conclusion))
    } yield result
  }

  /* ------------------------------------------------------------------- internals */

  /**
   * `|- !i. ~(i < k) ==> f i = WORD_PAD` for a `WORD_MAKE k f` whose `f` is a conditional guarded
   * by `i < k`.
   *
   * The premise `WORD_MAKE`'s two laws carry, discharged by `COND_FALSE` alone. It mirrors
   * `Concatenation`'s private helper of the same shape and is not shared with it: the thing it is
   * about is `WORD_MAKE`'s premise, so the home for one copy is `Word`, and moving it there is a
   * change to that file rather than something this development may do on its behalf. Two call
   * sites is where that becomes worth doing; this is the second.
   */
  private def conditionalPadding(
    logic: Logic,
    theory: Theory,
    condFalse: Kernel.Thm,
    made: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val index = Conv.freshVariable("i", Numbers, Term.freeVariables(made))

    for {
      parts <- destructureMake(made)
      (size, entries) = parts

      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      isBelow <- LogicError.lift(Term.appAll(strictOrder, List(index, size)))
      notBelow <- logic.mkNot(isBelow)
      assumed <- LogicError.lift(Kernel.assume(notBelow))

      applied <- LogicError.lift(Term.app(entries, index))
      beta <- Conv.betaRoot(applied)
      conditional <- rightOf(beta)
      branches <- destructureCond(conditional)
      (yes, no) = branches

      isPad <- rules
        .specAll(condFalse, List(isBelow, yes, no))
        .flatMap(rules.mp(_, assumed))
        .flatMap(Conv.trans(beta, _))
      result <- rules.disch(notBelow, isPad).flatMap(rules.gen(index, _))
    } yield result
  }

  /** `|- R a c` from `|- a = b` -- read the other way -- and `|- R a b`. */
  private def carryRight(
    relation: Term,
    left: Term,
    equation: Kernel.Thm,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- LogicError.lift(Term.app(relation, left))
      moved <- Conv.apTerm(partial, equation)
      result <- LogicError.lift(Kernel.eqMp(moved, fact))
    } yield result

  /** `WORD_MAKE k f`, taken apart into its two arguments. */
  private def destructureMake(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(Const(Word.Make, _), size), entries) => Right((size, entries))
    case other => Left(NotOfForm("an application of WORD_MAKE to two arguments", other))
  }

  /** `COND p a b`, taken apart into its two branches. */
  private def destructureCond(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(App(Const(Classical.Conditional, _), _), yes), no) => Right((yes, no))
    case other => Left(NotOfForm("an application of COND to three arguments", other))
  }

  /** The guard of a `COND`. */
  private def destructureCondGuard(term: Term): Either[LogicError, Term] = term match {
    case App(App(App(Const(Classical.Conditional, _), guard), _), _) => Right(guard)
    case other => Left(NotOfForm("an application of COND to three arguments", other))
  }

  /** The operator of an application. */
  private def headOfApplication(term: Term): Term = term match {
    case App(operator, _) => operator
    case other => other
  }

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))


  /**
   * The facts this file needs from the developments below it, collected once and named.
   *
   * Reaching for each through `fact` at the point of use would put the failure of a missing name in
   * the middle of a derivation instead of at the top, which is `Concatenation.Numeric`'s argument
   * for the same shape.
   */
  private final case class Held(
    classical: Classical,
    emptyLength: Kernel.Thm,
    lengthZero: Kernel.Thm,
    singletonLength: Kernel.Thm,
    singletonNth: Kernel.Thm,
    concatLength: Kernel.Thm,
    concatNthLeft: Kernel.Thm,
    concatNthRight: Kernel.Thm,
    nthAbove: Kernel.Thm,
    makeLength: Kernel.Thm,
    makeNth: Kernel.Thm,
    extensional: Kernel.Thm,
    condTrue: Kernel.Thm,
    condFalse: Kernel.Thm,
    induction: Kernel.Thm,
    zeroPlus: Kernel.Thm,
    successorPlus: Kernel.Thm,
    successorPositive: Kernel.Thm,
    successorNotZero: Kernel.Thm,
    addCancelsStrictOrder: Kernel.Thm,
    preAtSuccessor: Kernel.Thm,
    notBelowZero: Kernel.Thm,
    zeroOrSuccessor: Kernel.Thm,
    recursion: Kernel.Thm
  )

  private object Held {
    def of(
      peano: Peano,
      concatenation: Concatenation,
      classical: Classical
    ): Either[LogicError, Held] =
      for {
        emptyLength <- concatenation.fact(Concatenation.EmptyLength)
        lengthZero <- concatenation.fact(Concatenation.LengthZero)
        singletonLength <- concatenation.fact(Concatenation.SingletonLength)
        singletonNth <- concatenation.fact(Concatenation.SingletonNth)
        concatLength <- concatenation.fact(Concatenation.Length)
        concatNthLeft <- concatenation.fact(Concatenation.NthLeft)
        concatNthRight <- concatenation.fact(Concatenation.NthRight)
        nthAbove <- concatenation.word.fact(Word.NthAbove)
        makeLength <- concatenation.word.fact(Word.MakeLength)
        makeNth <- concatenation.word.fact(Word.MakeNth)
        extensional <- concatenation.word.fact(Word.Extensionality)
        condTrue <- classical.fact(Classical.CondTrue)
        condFalse <- classical.fact(Classical.CondFalse)
        induction <- peano.naturals.fact(Natural.Induction)
        zeroPlus <- peano.fact(Peano.ZeroPlus)
        successorPlus <- peano.fact(Peano.SuccessorPlus)
        successorPositive <- peano.fact(Peano.SuccessorPositive)
        successorNotZero <- peano.naturals.fact(Natural.SuccessorNotZero)
        addCancelsStrictOrder <- peano.fact(Peano.AddCancelsStrictOrder)
        preAtSuccessor <- peano.fact(Peano.PreAtSuccessor)
        notBelowZero <- peano.fact(Peano.NotBelowZero)
        zeroOrSuccessor <- peano.naturals.fact(Natural.ZeroOrSuccessor)
        recursion <- peano.naturals.recursion
      } yield Held(
        classical,
        emptyLength,
        lengthZero,
        singletonLength,
        singletonNth,
        concatLength,
        concatNthLeft,
        concatNthRight,
        nthAbove,
        makeLength,
        makeNth,
        extensional,
        condTrue,
        condFalse,
        induction,
        zeroPlus,
        successorPlus,
        successorPositive,
        successorNotZero,
        addCancelsStrictOrder,
        preAtSuccessor,
        notBelowZero,
        zeroOrSuccessor,
        recursion
      )
  }
}
