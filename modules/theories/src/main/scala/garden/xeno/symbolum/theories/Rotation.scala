package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Rotating a finite word, which is what the gap audit asked for and could not have.
 *
 * The operation is `WORD_ROTATE j w`, whose entry at `i` is `w ((i + j) mod k)` for `k` the length.
 * It is the first thing anybody wants of a word that stands for a cyclic sequence, and it was the
 * one item of the audit's A3 that stayed open after `Word` landed.
 *
 * == Why it is a development of its own ==
 *
 * `Word` cannot hold it. [[Word.standard]] is built over `Chain.standard.peano`, which is below
 * `Modular`, so `NUM_MOD` is not in its signature at all; the chain's `word` has it, because the
 * chain puts `Modular` first. A rotation defined inside `Word` would therefore build in one of the
 * two and refuse in the other, which is not a development, it is a development and a hole. So this
 * sits above both, exactly as `Matrix` sits above `Product` and `Ring`, and it declares what it
 * needs by taking it.
 *
 * == What was actually missing, which was not `NUM_MOD` ==
 *
 * `Word`'s own docstring worked this out and then recorded the wrong conclusion, and the correction
 * is worth keeping rather than tidying away. Defining a remainder was never the obstacle: a term
 * naming something that exists is `select` of a predicate, and `Magnitude` makes the general point.
 * What was missing was everything one could then prove about it, because
 * `Modular.Division` gives EXISTENCE of a quotient and remainder and existence alone does not make
 * "the remainder" denote. [[Modular.DivisionUnique]] is the lemma that does, and with it
 * [[Modular.DivisionBelow]] says `i < k ==> i mod k = i`, which is the whole of [[AtZero]] below.
 *
 * == What this does not do ==
 *
 * **No composition.** `WORD_ROTATE j (WORD_ROTATE k w) = WORD_ROTATE (NUM_ADD k j) w` is true and
 * is not here. It is a different proof: the three below are about one application of `NUM_MOD` and
 * that one is about two, so it needs `NUM_MOD (NUM_ADD (NUM_MOD a n) b) n = NUM_MOD (NUM_ADD a b) n`,
 * which is congruence arithmetic rather than the division theorem. `Modular` has the congruences it
 * would be built from ([[Modular.CongAdd]], [[Modular.CongModulus]]); nothing has asked for it yet,
 * and this file states the absence rather than guessing at the statement a consumer will want.
 *
 * **No inverse.** `WORD_ROTATE (NUM_SUB k j) (WORD_ROTATE j w) = w` needs the composition first and
 * then an argument about truncated subtraction, which is the only subtraction `num` has.
 */
final class Rotation private (
  val word: Word,
  val modular: Modular,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = word.product.classical.logic
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

object Rotation {

  /** `WORD_ROTATE j w` is the word whose entry at `i` is `w ((i + j) mod k)`. */
  val Name: String = "WORD_ROTATE"

  /** `|- !j w. WORD_LENGTH (WORD_ROTATE j w) = WORD_LENGTH w` — rotating moves nothing. */
  val Length: String = "WORD_ROTATE_LENGTH"

  /**
   * `|- !j w i. i < WORD_LENGTH w ==> WORD_NTH (WORD_ROTATE j w) i = WORD_NTH w ((i + j) mod k)`
   *
   * Guarded, and the guard is not bookkeeping. Above the length both sides are `WORD_PAD` and the
   * statement is true there too, but it is true for a different reason, and a consumer reading the
   * unguarded form would be entitled to conclude that the right side is an entry of `w` at every
   * index, which it is not.
   */
  val Nth: String = "WORD_ROTATE_NTH"

  /** `|- !w. WORD_ROTATE 0 w = w` — and it needs no guard on the length; see the docstring. */
  val AtZero: String = "WORD_ROTATE_ZERO"

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Element: Type = TyVar("a")
  private val Words: Type = TyApp(Word.TypeName, List(Element))

  /**
   * The body, which is `WORD_MAKE` over a function that pads itself.
   *
   * [[Word.Make]] takes a function that is **already** padded, so the caller does the padding, and
   * until 2026-09-12 nothing anywhere defined a conditional to do it with. `Classical.COND` is what
   * closed that, and this is the first use of it outside the file that defines it.
   */
  private val Body: String =
    "\\j:num. \\w:word('a). WORD_MAKE (WORD_LENGTH w) " +
      "(\\i:num. COND (NUM_LT i (WORD_LENGTH w)) " +
      "(WORD_NTH w (NUM_MOD (NUM_ADD i j) (WORD_LENGTH w))) (WORD_PAD:'a))"

  /** Everything this development proves, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    Length -> "!j:num. !w:word('a). WORD_LENGTH (WORD_ROTATE j w) = WORD_LENGTH w",
    Nth ->
      ("!j:num. !w:word('a). !i:num. NUM_LT i (WORD_LENGTH w) ==> " +
        "WORD_NTH (WORD_ROTATE j w) i = WORD_NTH w (NUM_MOD (NUM_ADD i j) (WORD_LENGTH w))"),
    AtZero -> "!w:word('a). WORD_ROTATE 0 w = w"
  )


  /**
   * The standard development, which is **the chain's own** and not a second one beside it.
   *
   * `Word.standard` and `Product.standard` each build a second development over a narrower theory,
   * and each carries a docstring saying why that is worth the cost: a caller with a development of
   * its own reaches for it, and `docs/adr/0008` makes the two refuse to mix rather than mix
   * silently. Neither argument reaches this file. Nothing is built on top of a rotation -- no
   * development in this repository takes one, which is a stronger statement than the "it is the
   * last link" this sentence carried until 2026-09-17, with sixteen entries of `Chain` after it
   * -- so a second one would have no caller, and it would put a second `WORD_ROTATE` of a different
   * origin into the world for a consumer to trip over. So this is a lookup.
   */
  lazy val standard: Rotation = Chain.standard.rotation

  /**
   * The development over a word and a modular arithmetic that are in one signature.
   *
   * Both, and the second is not decoration: `WORD_ROTATE` mentions `NUM_MOD` inside its own
   * definition, so a signature holding only the first cannot even state it. That is checked by
   * being used rather than asserted, since the parse of [[Body]] against `base` is what refuses if
   * the two were built beside each other rather than one over the other.
   *
   * `base` is the theory to extend and is not `word.theory`: this is the LAST link, so what it
   * extends is `Matrix`'s. A development that extended `word.theory` inside a chain whose last link
   * was `matrix` would declare its constant into a side branch, and every link below would be
   * unable to see it -- which is the defect this repository has already paid for once, and is why
   * the five developments that used to sit beside the chain are in it.
   */
  def construct(word: Word, modular: Modular, base: Theory): Either[LogicError, Rotation] = {
    val classical = word.product.classical
    val notation = word.notation

    for {
      body <- Parser.term(base, notation, Body)
      defined <- LogicError.lift(Kernel.defineConstant(base, Name, body))
      (theory, definition) = defined

      logic <- classical.logic.over(theory)

      lengthLaw <- word.fact(Word.MakeLength)
      nthLaw <- word.fact(Word.MakeNth)
      extensional <- word.fact(Word.Extensionality)
      condTrue <- classical.fact(Classical.CondTrue)
      condFalse <- classical.fact(Classical.CondFalse)
      addAtZero <- word.peano.fact(Peano.AddAtZero)
      below <- modular.fact(Modular.DivisionBelow)

      laws <- shapeOf(
        logic,
        theory,
        notation,
        definition,
        (lengthLaw, nthLaw, condTrue, condFalse)
      )
      (lengthResult, nthResult) = laws

      atZero <- identityAtZero(
        logic, theory, notation, lengthResult, nthResult, extensional, addAtZero, below)
    } yield new Rotation(
      word,
      modular,
      theory,
      notation,
      Map(Name -> definition),
      Map(Length -> lengthResult, Nth -> nthResult, AtZero -> atZero)
    )
  }

  /**
   * [[Length]] and [[Nth]], which are [[Word.MakeLength]] and [[Word.MakeNth]] with one premise
   * discharged.
   *
   * Both of those carry "what you handed me was already padded", and this definition pads with
   * `COND`, so the premise is [[Classical.CondFalse]] at each index above the length and nothing
   * else. Proving it once and using it twice is why the two laws are derived together rather than
   * in a function each.
   */
  private def shapeOf(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definition: Kernel.Thm,
    rules0: (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm)
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val (lengthLaw, nthLaw, condTrue, condFalse) = rules0

    val j = Term.variable("j", Numbers)
    val w = Term.variable("w", Words)
    val i = Term.variable("i", Numbers)

    for {
      unfolded <- Conv.unfold(definition, List(j, w))
      made <- rightOf(unfolded)
      parts <- destructure(made)
      (length, padded) = parts

      // The premise both laws carry: above the length the function is `WORD_PAD`, which is the
      // false branch of the conditional and nothing more.
      strictOrder <- LogicError.lift(
        theory.constant(Peano.StrictOrder, Type.fun(Numbers, Type.fun(Numbers, Type.Bool)))
      )
      isBelow <- LogicError.lift(Term.appAll(strictOrder, List(i, length)))
      notBelow <- logic.mkNot(isBelow)
      assumedAbove <- LogicError.lift(Kernel.assume(notBelow))

      applied <- LogicError.lift(Term.app(padded, i))
      beta <- Conv.betaRoot(applied)
      conditional <- rightOf(beta)
      branches <- destructureCond(conditional)
      (entry, pad) = branches

      falseCase <- rules.specAll(condFalse, List(isBelow, entry, pad))
      isPad <- rules.mp(falseCase, assumedAbove).flatMap(Conv.trans(beta, _))
      premise <- rules.disch(notBelow, isPad).flatMap(rules.gen(i, _))

      lengthAt <- rules.specAll(lengthLaw, List(length, padded))
      lengthIs <- rules.mp(lengthAt, premise)
      lengthOf <- headOf(lengthIs)
      lengthResult <- Conv
        .apTerm(lengthOf, unfolded)
        .flatMap(Conv.trans(_, lengthIs))
        .flatMap(rules.genAll(_, List(j, w)))

      nthAt <- rules.specAll(nthLaw, List(length, padded))
      nthIs <- rules.mp(nthAt, premise)
      nthOf <- headOf(nthIs)
      atIndex <- Conv.apThm(nthIs, i)
      assumedBelow <- LogicError.lift(Kernel.assume(isBelow))
      trueCase <- rules.specAll(condTrue, List(isBelow, entry, pad))
      isEntry <- rules.mp(trueCase, assumedBelow)
      through <- Conv
        .apTerm(nthOf, unfolded)
        .flatMap(equation => Conv.apThm(equation, i))
        .flatMap(Conv.trans(_, atIndex))
        .flatMap(Conv.trans(_, beta))
        .flatMap(Conv.trans(_, isEntry))
      nthResult <- rules
        .disch(isBelow, through)
        .flatMap(rules.gen(i, _))
        .flatMap(rules.genAll(_, List(j, w)))
    } yield (lengthResult, nthResult)
  }

  /**
   * [[AtZero]], by extensionality, and it needs no guard on the length.
   *
   * At length zero there is no index below the length, so the second premise of
   * [[Word.Extensionality]] is discharged from a proof that never used it, and the two words are
   * equal because both are empty. That is the honest reading of an empty word rather than a case
   * anybody has to split on, and it is the reason this statement is unconditional where a reader
   * might expect `0 < WORD_LENGTH w`.
   *
   * The work is one rewrite in two steps: `(i + 0) mod k` is `i mod k` by [[Peano.AddAtZero]] and
   * then `i` by [[Modular.DivisionBelow]], whose hypothesis is the one the goal already carries.
   */
  private def identityAtZero(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    lengthResult: Kernel.Thm,
    nthResult: Kernel.Thm,
    extensional: Kernel.Thm,
    addAtZero: Kernel.Thm,
    below: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val w = Term.variable("w", Words)
    val i = Term.variable("i", Numbers)

    for {
      zero <- Parser.term(theory, notation, "0:num")
      rotate <- LogicError.lift(
        theory.constant(Name, Type.fun(Numbers, Type.fun(Words, Words)))
      )
      rotated <- LogicError.lift(Term.appAll(rotate, List(zero, w)))

      lengths <- rules.specAll(lengthResult, List(zero, w))
      lengthOf <- headOf(lengths)
      lengthHere <- LogicError.lift(Term.app(lengthOf, rotated))

      strictOrder <- LogicError.lift(
        theory.constant(Peano.StrictOrder, Type.fun(Numbers, Type.fun(Numbers, Type.Bool)))
      )
      belowRotated <- LogicError.lift(Term.appAll(strictOrder, List(i, lengthHere)))
      assumed <- LogicError.lift(Kernel.assume(belowRotated))

      // The bound in the premise is the ROTATED word's length, and every lemma below is about the
      // original's. They are equal by `lengths`, so the assumption is carried across rather than
      // every lemma being restated at the other bound.
      partial <- LogicError.lift(Term.app(strictOrder, i))
      carried <- Conv
        .apTerm(partial, lengths)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed)))

      entryAt <- rules.specAll(nthResult, List(zero, w, i)).flatMap(rules.mp(_, carried))
      sum <- rules.spec(i, addAtZero)
      residueOf <- rightOf(entryAt).flatMap {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("an entry of the word", other))
      }
      modulus <- residueOf match {
        case App(App(_, _), modulus) => Right(modulus)
        case other => Left(NotOfForm("a remainder", other))
      }
      modOf <- residueOf match {
        case App(App(operator, _), _) => Right(operator)
        case other => Left(NotOfForm("a remainder", other))
      }
      simplerResidue <- Conv.apTerm(modOf, sum).flatMap(Conv.apThm(_, modulus))

      atIndex <- rules.specAll(below, List(i, modulus)).flatMap(rules.mp(_, carried))
      remainder <- rules.conjElim2(atIndex)
      residueIsIndex <- Conv.trans(simplerResidue, remainder)

      entryOf <- rightOf(entryAt).flatMap {
        case App(operator, _) => Right(operator)
        case other => Left(NotOfForm("an entry of the word", other))
      }
      sameEntry <- Conv
        .apTerm(entryOf, residueIsIndex)
        .flatMap(Conv.trans(entryAt, _))

      agreement <- rules.disch(belowRotated, sameEntry).flatMap(rules.gen(i, _))
      both <- rules.conjIntro(lengths, agreement)
      equal <- rules.specAll(extensional, List(rotated, w)).flatMap(rules.mp(_, both))
      result <- rules.gen(w, equal)
    } yield result
  }

  /** `WORD_MAKE k f`, taken apart into the length and the padded function. */
  private def destructure(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(Const(Word.Make, _), length), padded) => Right((length, padded))
    case other => Left(NotOfForm("an application of WORD_MAKE to two arguments", other))
  }

  /** `COND p a b`, taken apart into its two branches. */
  private def destructureCond(term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(App(Const(Classical.Conditional, _), _), yes), no) => Right((yes, no))
    case other => Left(NotOfForm("an application of COND to three arguments", other))
  }

  /** The operator of an application read off a theorem's left side. */
  private def headOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1) match {
      case Some(App(operator, _)) => Right(operator)
      case _ => Left(NotOfForm("an equation whose left side is an application", theorem.conclusion))
    }

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
