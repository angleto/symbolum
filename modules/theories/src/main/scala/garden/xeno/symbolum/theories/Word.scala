package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A finite word: a length and a function that is only consulted below it.
 *
 * The second half of what the gap audit asked for and the first thing `Product` was built for. A
 * consumer wanting lists, finite words or an index type was told item A10, that none of them is
 * statable; a word is a length together with a function, so it is a pair, and with `prod` in the
 * signature it is a type that can be carved out.
 *
 * == Why a pair is not already a word, and what the padding is for ==
 *
 * `prod(num, num -> 'a)` holds two encodings of every word: the length is honest and the function
 * is only pinned below it, so `PAIR (SUC ZERO) f` and `PAIR (SUC ZERO) g` are different terms
 * whenever `f` and `g` differ anywhere at all, including at indices no reader of the word can see.
 * A type whose equality is that of its encoding would then have two words that are equal in every
 * observable way and not equal, and every lemma about words would have to carry a side condition
 * saying which encoding was meant.
 *
 * So the type is the **padded** encodings: those whose function is [[Word.Pad]] at every index at
 * or above the length. That makes the encoding canonical, which is what buys
 * [[Word.Extensionality]] — two words of one length agreeing below it **are** one word — and that
 * theorem is the whole reason the type is worth defining rather than working with pairs directly.
 *
 * `WORD_PAD` is `select (\x. T)`, some element of `'a` and no particular one. Nothing here proves
 * anything about it and nothing needs to: what the definition uses is that it is **one** term, so
 * that two padded encodings pad identically. It costs the choice axiom, which this development
 * already holds through `Product`'s projections.
 *
 * == Rotation is not here, and this is exactly what stops it ==
 *
 * The operation the consumer asked for is `rotate j w`, whose entry at `i` is `w ((i + j) mod k)`.
 * There is no `NUM_MOD` on `num`, and the interesting part is that **defining one is not what is
 * missing**. `Magnitude` makes the general point for `max`: a term naming something that exists is
 * `select` of a predicate, so
 * `NUM_MOD n m = select (\r. ?q. m = NUM_ADD (NUM_MUL n q) r /\ NUM_LT r n)` is a definition this
 * signature can already write, exactly the way `FST` above is.
 *
 * What was missing was everything one could then prove about it, and that changed hours after this
 * file was written, so the paragraph is kept with its correction rather than rewritten into
 * hindsight. `Modular.Division` is `!n m. NUM_LT ZERO n ==> ?q r. m = n * q + r /\ r < n`, which is
 * **existence and not uniqueness**, and that file said so in as many words: "the remainder" did not
 * denote. From existence alone the selected `r` is *a* remainder; `NUM_LT i k ==> i mod k = i`
 * needs it to be **the** remainder, and without that not one law of rotation goes through.
 *
 * [[Modular.DivisionUnique]] is that lemma and it is proved:
 * `n * q1 + r1 = n * q2 + r2 /\ r1 < n /\ r2 < n ==> q1 = q2 /\ r1 = r2`, with no positivity
 * guard because `r1 < n` already carries it.
 *
 * **So rotation is now one definition and one derivation away rather than one lemma away**, and
 * those are different kinds of gap.
 *
 * The paragraph that stood here said the definition was still a decision about the signature,
 * because `NUM_MOD` and `NUM_DIV` did not exist. **They do**, in `Modular`, which landed the same
 * day this was written, and this file went on saying otherwise. `WordSpec` asserts their absence
 * off the code rather than off a comment, which is why the sentence survived: the assertion is
 * about [[Word.standard]], built over `Chain.standard.peano` and therefore BELOW `Modular`, where
 * both really are absent. The `word` of the chain, which is the one `Library.of` collects and the
 * one a consumer reaches for, has both in signature. A verdict that is right about a population
 * nobody chose, which is the shape this repository has met three times now, and the spec says so
 * beside the assertion rather than being deleted.
 *
 * **A second thing this development does not offer, and that one is a scope decision rather than a
 * limit.** [[Word.Make]] takes a function that is **already** padded rather than padding one for the
 * caller. A constructor that normalised an arbitrary function would be
 * `\i. COND (NUM_LT i k) (f i) WORD_PAD`, and until 2026-09-12 nothing anywhere defined `COND`.
 * **It does now**: `Classical` defines it from the choice operator, with `COND_TRUE` and
 * `COND_FALSE`, so this signature names it and the term above is one a caller can write. The
 * missing half of this is therefore no longer the constant but the constructor: a padding
 * `WORD_MAKE` has to be proved to agree with the function it was handed below the length and to be
 * `WORD_PAD` above it, which is where the two equations get used rather than merely be available.
 * What it would buy is a caller that no longer has to discharge the premise the two laws below
 * carry.
 */
final class Word private (
  val product: Product,
  val peano: Peano,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = product.classical.logic
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

object Word {

  /** The element the function takes at and above the length. */
  val Pad: String = "WORD_PAD"

  /** The type of finite words over `'a`. */
  val TypeName: String = "word"

  /** The two halves of the bijection, as `Kernel.defineType` names them. */
  val Abstraction: String = "mk_word"
  val RepresentationFunction: String = "dest_word"

  /** The length, the index, and the constructor from an already-padded function. */
  val Length: String = "WORD_LENGTH"
  val Nth: String = "WORD_NTH"
  val Make: String = "WORD_MAKE"

  /** The two theorems `Kernel.defineType` returns. */
  val AbstractionOfRepresentation: String = "WORD_ABS_REP"
  val Characterisation: String = "WORD_REP_ABS"

  /** `|- !w i. ~(NUM_LT i (WORD_LENGTH w)) ==> WORD_NTH w i = WORD_PAD`. */
  val NthAbove: String = "WORD_NTH_PAD"

  /** What [[Make]] builds, given that what it was handed was padded. */
  val MakeLength: String = "WORD_MAKE_LENGTH"
  val MakeNth: String = "WORD_MAKE_NTH"

  /** `|- !v w. same length /\ same entries below it ==> v = w`. */
  val Extensionality: String = "WORD_EXTENSIONALITY"

  /** The element type, which is the classical extension's first type variable. */
  val Element: Type = TyVar(Classical.TypeVariable)

  /** `num`, `num -> 'a`, `prod(num, num->'a)` and `word('a)`. */
  val Numbers: Type = TyApp(Natural.TypeName, Nil)
  val Entries: Type = Type.fun(Numbers, Element)
  val Encoding: Type = TyApp(Product.TypeName, List(Numbers, Entries))
  val Words: Type = TyApp(TypeName, List(Element))

  /**
   * The predicate the type is the image of, as text.
   *
   * **The parentheses around the negated guard are not decoration.** `~` takes the widest argument
   * this notation allows, so `~(NUM_LT i (FST p)) ==> q` reads as `~((NUM_LT i (FST p)) ==> q)`,
   * which is a different predicate and defines a different type. The same trap `Classical.Statements`
   * documents for the two De Morgan entries, met again here.
   */
  val RepresentationBody: String =
    "\\p:prod(num,num->'a). !i:num. (~(NUM_LT i (FST p))) ==> SND p i = WORD_PAD"

  /** The bodies of the four definitions, as text, in the order they are introduced. */
  val Definitions: Vector[(String, String)] = Vector(
    Pad -> "select (\\x:'a. T)",
    Length -> "\\w:word('a). FST (dest_word w)",
    Nth -> "\\w:word('a). SND (dest_word w)",
    Make -> "\\k:num. \\f:num->'a. mk_word (PAIR k f)"
  )

  /**
   * The empty word, which is the witness that makes the type inhabited.
   *
   * `WORD_PAD` carries its own annotation, and it is the only place in this file that needs one.
   * The constant is polymorphic at `'a` with nothing else in the term to pin it: every other
   * occurrence sits beside an entry of the function and takes its type from there, and here there
   * is no function to take it from. The parser refuses rather than inventing a type variable, which
   * is `Parser`'s stated design and is how this was found.
   */
  val WitnessBody: String = "PAIR ZERO (\\i:num. (WORD_PAD:'a))"

  /** The premise [[Make]] and its two laws carry: what was handed over is already padded. */
  val PaddedPremise: String =
    "!i:num. (~(NUM_LT i (k:num))) ==> (f:num->'a) i = WORD_PAD"

  /**
   * What every derived fact says, as text, in the order they are derived.
   *
   * Compared as terms rather than as printed text, for the reason `Product.Statements` gives: a
   * type variable is written `'a` and printed `a`, so a printed polymorphic statement does not read
   * back.
   */
  val Statements: Vector[(String, String)] = Vector(
    NthAbove ->
      "!w:word('a). !i:num. (~(NUM_LT i (WORD_LENGTH w))) ==> WORD_NTH w i = WORD_PAD",
    MakeLength ->
      ("!k:num. !f:num->'a. (!i:num. (~(NUM_LT i k)) ==> f i = WORD_PAD) ==> " +
        "WORD_LENGTH (WORD_MAKE k f) = k"),
    MakeNth ->
      ("!k:num. !f:num->'a. (!i:num. (~(NUM_LT i k)) ==> f i = WORD_PAD) ==> " +
        "WORD_NTH (WORD_MAKE k f) = f"),
    Extensionality ->
      ("!v:word('a). !w:word('a). WORD_LENGTH v = WORD_LENGTH w /\\ " +
        "(!i:num. NUM_LT i (WORD_LENGTH v) ==> WORD_NTH v i = WORD_NTH w i) ==> v = w")
  )

  /**
   * The standard development, built beside the chain rather than taken from it.
   *
   * `Chain.standard.word` is the one a caller almost always wants since 2026-09-12: it is in the
   * signature everything else is in, and it is the one `Library.of` collects and `docs/lemmas.md`
   * lists. This builds a **second** one, over the narrower theory, and it is kept because the
   * specs of this file are about what this development does on its own and because a caller with a
   * development of its own reaches for it.
   *
   * The two are not interchangeable and the kernel says so rather than letting them mix: a constant
   * defined here and a constant of the same name defined in the chain have different origins, which
   * `docs/adr/0008` is about, so a rule built from one is refused against the other. Loud, and not
   * silent.
   */
  lazy val standard: Word =
    construct(Chain.standard.peano).fold(
      error => throw new IllegalStateException(s"the words do not build: ${error.message}"),
      identity
    )

  /**
   * The development over a `Peano` of one's own, with its own `Product` built on top.
   *
   * The product is built here rather than taken as a parameter because it has to be the one over
   * **this** theory: a `Product` built beside the naturals rather than over them declares a `PAIR`
   * that is a different constant, and `docs/adr/0008` is why the two would not combine.
   */
  def construct(peano: Peano): Either[LogicError, Word] =
    Product
      .construct(peano.naturals.classical, peano.theory, peano.notation)
      .flatMap(construct(peano, _))

  /**
   * The same, over a `Product` the caller already built.
   *
   * The chain entry point, added on 2026-09-12 when the five developments beside `Chain` went into
   * it. The constraint the one-argument version encodes has not moved: the product has to be the
   * one over **this** theory, because a `PAIR` declared beside the naturals is a different constant
   * from a `PAIR` declared over them and `docs/adr/0008` is why the two would not combine. What
   * changed is who checks it. A chain that built a product for its own signature and then let this
   * build a second one would hold two `prod` type operators with one name, which `Theory` refuses
   * outright, so the failure would be loud rather than silent. It would also be a chain paying
   * twice for a development it already has.
   *
   * The base this extends is `product.theory` rather than `peano.theory`: the product is where the
   * pair came from and everything below it is still there.
   */
  def construct(peano: Peano, product: Product): Either[LogicError, Word] = {
    val classical = peano.naturals.classical
    val notation = peano.notation

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
      pad <- define(product.theory, Pad, Definitions(0)._2)
      (withPad, padDefinition) = pad

      predicate <- Parser.term(withPad, notation, RepresentationBody)
      empty <- Parser.term(withPad, notation, WitnessBody)
      narrow <- classical.logic.over(withPad)
      witness <- emptyIsPadded(narrow, withPad, product, predicate, empty)

      typed <- LogicError.lift(
        Kernel.defineType(withPad, TypeName, Abstraction, RepresentationFunction, witness)
      )
      (withType, bijection) = typed

      length <- define(withType, Length, Definitions(1)._2)
      (withLength, lengthDefinition) = length
      nth <- define(withLength, Nth, Definitions(2)._2)
      (withNth, nthDefinition) = nth
      make <- define(withNth, Make, Definitions(3)._2)
      (complete, makeDefinition) = make

      wider <- classical.logic.over(complete)

      above <- nthAbove(wider, complete, bijection, lengthDefinition, nthDefinition)
      built <- makeLaws(
        wider,
        complete,
        notation,
        product,
        predicate,
        bijection._2,
        (lengthDefinition, nthDefinition, makeDefinition)
      )
      extensional <- extensionality(
        classical,
        wider,
        complete,
        notation,
        product,
        bijection._1,
        (lengthDefinition, nthDefinition),
        above
      )

      facts = Map(
        AbstractionOfRepresentation -> bijection._1,
        Characterisation -> bijection._2,
        NthAbove -> above,
        MakeLength -> built._1,
        MakeNth -> built._2,
        Extensionality -> extensional
      )

      // Each statement checked against the text a person reads it by, here rather than in the spec:
      // a development that built something other than what it says it built must not be handed out.
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { (acc, entry) =>
        val (name, text) = entry
        for {
          _ <- acc
          expected <- Parser.proposition(complete, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Word(
      product,
      peano,
      complete,
      notation,
      Map(
        Pad -> padDefinition,
        Length -> lengthDefinition,
        Nth -> nthDefinition,
        Make -> makeDefinition
      ),
      facts
    )
  }

  /* --------------------------------------------------------------- the derivations */

  /**
   * `|- P (PAIR ZERO (\i. WORD_PAD))`: the empty word, which is what makes the type inhabited.
   *
   * The shortest derivation here and the one without which nothing else is allowed to happen. The
   * guard is never used: the function is `WORD_PAD` at **every** index, so it is padded above zero
   * for the reason that it is padded everywhere, and the implication is discharged from a proof that
   * did not assume it. That is `Rules.disch`'s behaviour and the honest reading of this word.
   */
  private def emptyIsPadded(
    logic: Logic,
    theory: Theory,
    product: Product,
    predicate: Term,
    empty: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      applied <- LogicError.lift(Term.app(predicate, empty))
      contraction <- Conv.betaRoot(applied)
      goal <- rightOf(contraction)
      stripped <- Logic.stripForall(goal)
      index <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", goal))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (guard, conclusion) = parts

      pairing <- LogicError.lift(theory.constant(Product.Pairing, pairingType))
      components <- destPair(pairing, empty)
      (zero, function) = components

      secondLaw <- product.fact(Product.SecondOfPair).map(atEncoding)
      atPair <- rules.specAll(secondLaw, List(zero, function))
      atIndex <- Conv.apThm(atPair, index)
      inside <- LogicError.lift(Term.app(function, index))
      reduced <- Conv.betaRoot(inside)
      value <- Conv.trans(atIndex, reduced)

      _ <-
        if (value.conclusion == conclusion) Right(())
        else Left(NotOfForm("the entry as the predicate states it", value.conclusion))

      body <- rules.disch(guard, value).flatMap(rules.gen(index, _))
      result <- Conv.sym(contraction).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, body)))
    } yield result
  }

  /**
   * `|- !w i. ~(NUM_LT i (WORD_LENGTH w)) ==> WORD_NTH w i = WORD_PAD`.
   *
   * The defining property of the type, read back off the characterisation and restated in the
   * language a consumer has. `mk_word (dest_word w) = w` gives
   * `dest_word (mk_word (dest_word w)) = dest_word w` in one congruence step, which is the
   * right-hand side of the characterisation at `dest_word w`, so the predicate holds there; and the
   * predicate at `dest_word w` **is** this statement with `FST (dest_word w)` where
   * `WORD_LENGTH w` stands and `SND (dest_word w) i` where `WORD_NTH w i` stands. The rest is the
   * two definitions carried across an equation, once in the guard and once in the conclusion.
   */
  private def nthAbove(
    logic: Logic,
    theory: Theory,
    bijection: (Kernel.Thm, Kernel.Thm),
    lengthDefinition: Kernel.Thm,
    nthDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (abstraction, characterisation) = bijection
    val w = Term.variable("w", Words)
    val i = Term.variable("i", Numbers)

    for {
      takeApart <- LogicError.lift(theory.constant(RepresentationFunction, Type.fun(Words, Encoding)))
      lessThan <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      below <- LogicError.lift(Term.app(lessThan, i))

      atWord <- LogicError.lift(Kernel.inst(Map(Term.variable("a", Words) -> w), abstraction))
      representative <- LogicError.lift(Term.app(takeApart, w))
      carried <- Conv.apTerm(takeApart, atWord)
      at <- LogicError.lift(
        Kernel.inst(Map(Term.variable("r", Encoding) -> representative), characterisation)
      )
      holds <- Conv.sym(at).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, carried)))
      opened <- Conv
        .betaRoot(holds.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, holds)))
      instance <- rules.spec(i, opened)

      lengthAt <- Conv.unfold(lengthDefinition, List(w))
      guardEquation <- Conv.apTerm(below, lengthAt)
      negated <- Conv.apTerm(logic.negation, guardEquation)
      wanted <- leftOf(negated)
      assumed <- LogicError.lift(Kernel.assume(wanted))
      raw <- LogicError.lift(Kernel.eqMp(negated, assumed))
      value <- rules.mp(instance, raw)

      nthAt <- Conv.unfold(nthDefinition, List(w))
      applied <- Conv.apThm(nthAt, i)
      entry <- Conv.trans(applied, value)
      result <- rules.disch(wanted, entry).flatMap(rules.genAll(_, List(w, i)))
    } yield result
  }

  /**
   * The two laws of the constructor, which say what it built when what it was handed was padded.
   *
   * One function for both, because they share everything up to the last step: the premise gives
   * `P (PAIR k f)`, the characterisation turns that into `dest_word (WORD_MAKE k f) = PAIR k f`,
   * and then the length is `FST` of that and the entries are `SND` of it. Deriving them apart would
   * derive the shared five-sixths twice.
   *
   * **The premise is not removable.** Without it `WORD_MAKE k f` is `mk_word` of an encoding that
   * may not be in the image, and `mk_word` off the image is a value about which the type definition
   * says nothing at all — not a contradiction, just silence. A constructor that padded the function
   * itself would need a conditional, and there is none.
   */
  private def makeLaws(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    product: Product,
    predicate: Term,
    characterisation: Kernel.Thm,
    definitions: (Kernel.Thm, Kernel.Thm, Kernel.Thm)
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val (lengthDefinition, nthDefinition, makeDefinition) = definitions
    val k = Term.variable("k", Numbers)
    val f = Term.variable("f", Entries)

    for {
      pairing <- LogicError.lift(theory.constant(Product.Pairing, pairingType))
      takeApart <- LogicError.lift(theory.constant(RepresentationFunction, Type.fun(Words, Encoding)))
      encoded <- LogicError.lift(Term.appAll(pairing, List(k, f)))

      premise <- Parser.proposition(theory, notation, PaddedPremise)
      padded <- LogicError.lift(Kernel.assume(premise))
      holds <- encodes(logic, theory, product, predicate, encoded, padded)

      at <- LogicError.lift(
        Kernel.inst(Map(Term.variable("r", Encoding) -> encoded), characterisation)
      )
      inImage <- LogicError.lift(Kernel.eqMp(at, holds))

      built <- Conv.unfold(makeDefinition, List(k, f))
      representative <- Conv.apTerm(takeApart, built).flatMap(Conv.trans(_, inImage))

      firstLaw <- product.fact(Product.FirstOfPair).map(atEncoding)
      secondLaw <- product.fact(Product.SecondOfPair).map(atEncoding)
      word <- leftOf(built)

      lengthAt <- Conv.unfold(lengthDefinition, List(word))
      firstOf <- LogicError.lift(theory.constant(Product.First, firstType))
      lengthIs <- Conv
        .apTerm(firstOf, representative)
        .flatMap(Conv.trans(lengthAt, _))
        .flatMap(step => rules.specAll(firstLaw, List(k, f)).flatMap(Conv.trans(step, _)))
      lengthResult <- rules.disch(premise, lengthIs).flatMap(rules.genAll(_, List(k, f)))

      nthAt <- Conv.unfold(nthDefinition, List(word))
      secondOf <- LogicError.lift(theory.constant(Product.Second, secondType))
      nthIs <- Conv
        .apTerm(secondOf, representative)
        .flatMap(Conv.trans(nthAt, _))
        .flatMap(step => rules.specAll(secondLaw, List(k, f)).flatMap(Conv.trans(step, _)))
      nthResult <- rules.disch(premise, nthIs).flatMap(rules.genAll(_, List(k, f)))
    } yield (lengthResult, nthResult)
  }

  /**
   * `|- !v w. WORD_LENGTH v = WORD_LENGTH w /\ (!i. i < WORD_LENGTH v ==> WORD_NTH v i = WORD_NTH w i) ==> v = w`.
   *
   * The theorem the padding exists for, and the one a consumer needs: two words are equal when they
   * agree on what can be observed of them. It is the only derivation here that needs a case split,
   * and the split is where the padding does its work — below the length the premise supplies the
   * entry, at or above it both words are `WORD_PAD` and the premise is not needed. The second half
   * is why the encoding was made canonical: without the padding the two functions could differ
   * above the length and the words would be different terms.
   *
   * **The statement is read from text and every piece is taken off it**, which is `Natural`'s
   * pattern for the induction principle and is here for the same two reasons: the quantifiers are at
   * types the classical logic has never heard of, and the text is what a person checks the theorem
   * by.
   *
   * `Classical.ext` is what turns the pointwise agreement into an equation between the two entry
   * functions, so this is the one fact in the development that reaches the eta axiom.
   */
  private def extensionality(
    classical: Classical,
    logic: Logic,
    theory: Theory,
    notation: Notation,
    product: Product,
    abstraction: Kernel.Thm,
    definitions: (Kernel.Thm, Kernel.Thm),
    above: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (lengthDefinition, nthDefinition) = definitions

    for {
      goal <- Parser.proposition(theory, notation, Statements(3)._2)
      stripped <- Logic.stripForall(goal)
      (variables, body) = stripped
      v <- variables.headOption.toRight(NotOfForm("a claim about every word", goal))
      w <- variables.drop(1).headOption.toRight(NotOfForm("a claim about two words", goal))
      parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (hypothesis, conclusion) = parts

      assumed <- LogicError.lift(Kernel.assume(hypothesis))
      lengths <- rules.conjElim1(assumed)
      entries <- rules.conjElim2(assumed)

      lessThan <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      i = Conv.freshVariable("i", Numbers, Term.freeVariables(hypothesis))
      below <- LogicError.lift(Term.app(lessThan, i))
      lengthOfFirst <- leftOf(lengths)
      guard <- LogicError.lift(Term.app(below, lengthOfFirst))

      // Below the length: the premise says the entries agree, and that is the whole branch.
      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      positive <- rules.spec(i, entries).flatMap(rules.mp(_, assumedGuard))

      // At or above it: both are the pad. The guard has to be moved to the second word first,
      // which is the only use the equality of the lengths gets in this branch.
      negatedGuard <- logic.mkNot(guard)
      assumedNegated <- LogicError.lift(Kernel.assume(negatedGuard))
      atFirst <- rules.specAll(above, List(v, i)).flatMap(rules.mp(_, assumedNegated))
      transferred <- Conv.apTerm(below, lengths).flatMap(Conv.apTerm(logic.negation, _))
      negatedThere <- LogicError.lift(Kernel.eqMp(transferred, assumedNegated))
      atSecond <- rules.specAll(above, List(w, i)).flatMap(rules.mp(_, negatedThere))
      negative <- Conv.sym(atSecond).flatMap(Conv.trans(atFirst, _))

      middle <- classical.excludedMiddleAt(guard)
      pointwise <- rules.disjElim(middle, positive, negative)
      generalised <- rules.gen(i, pointwise)
      functions <- classical.ext(logic, generalised)

      // The two components of the encoding, each stated over `dest_word` rather than over the
      // definitions, which is the language `PAIR_SURJECTIVE` rebuilds the encoding in.
      lengthOfV <- Conv.unfold(lengthDefinition, List(v))
      lengthOfW <- Conv.unfold(lengthDefinition, List(w))
      firstHalf <- Conv
        .sym(lengthOfV)
        .flatMap(Conv.trans(_, lengths))
        .flatMap(Conv.trans(_, lengthOfW))
      nthOfV <- Conv.unfold(nthDefinition, List(v))
      nthOfW <- Conv.unfold(nthDefinition, List(w))
      secondHalf <- Conv
        .sym(nthOfV)
        .flatMap(Conv.trans(_, functions))
        .flatMap(Conv.trans(_, nthOfW))

      takeApart <- LogicError.lift(theory.constant(RepresentationFunction, Type.fun(Words, Encoding)))
      makeWord <- LogicError.lift(theory.constant(Abstraction, Type.fun(Encoding, Words)))
      pairing <- LogicError.lift(theory.constant(Product.Pairing, pairingType))
      surjective <- product.fact(Product.Surjective).map(atEncoding)
      representativeV <- LogicError.lift(Term.app(takeApart, v))
      representativeW <- LogicError.lift(Term.app(takeApart, w))
      expandV <- rules.spec(representativeV, surjective)
      expandW <- rules.spec(representativeW, surjective)

      rebuilt <- Conv.apTerm(pairing, firstHalf).flatMap(partial =>
        LogicError.lift(Kernel.mkComb(partial, secondHalf))
      )
      representatives <- Conv
        .trans(expandV, rebuilt)
        .flatMap(step => Conv.sym(expandW).flatMap(Conv.trans(step, _)))

      lifted <- Conv.apTerm(makeWord, representatives)
      atV <- LogicError.lift(Kernel.inst(Map(Term.variable("a", Words) -> v), abstraction))
      atW <- LogicError.lift(Kernel.inst(Map(Term.variable("a", Words) -> w), abstraction))
      equal <- Conv
        .sym(atV)
        .flatMap(Conv.trans(_, lifted))
        .flatMap(Conv.trans(_, atW))

      _ <-
        if (equal.conclusion == conclusion) Right(())
        else Left(NotOfForm("the two words equal", equal.conclusion))
      result <- rules.disch(hypothesis, equal).flatMap(rules.genAll(_, List(v, w)))
      _ <-
        if (result.conclusion == goal) Right(())
        else Left(NotOfForm("extensionality as it is written", result.conclusion))
    } yield result
  }

  /* ------------------------------------------------------------------- internals */

  /**
   * `G |- P (PAIR k f)`, from `G |- !i. ~(i < k) ==> f i = WORD_PAD`.
   *
   * The bridge between the premise a caller can state and the predicate the type was carved by. The
   * two differ only in that the predicate reads the length and the entries through `FST` and `SND`
   * of the encoding, so the derivation is the two projection laws used once each, in the guard and
   * in the conclusion.
   */
  private def encodes(
    logic: Logic,
    theory: Theory,
    product: Product,
    predicate: Term,
    encoded: Term,
    padded: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      pairing <- LogicError.lift(theory.constant(Product.Pairing, pairingType))
      components <- destPair(pairing, encoded)
      (k, f) = components
      lessThan <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))

      applied <- LogicError.lift(Term.app(predicate, encoded))
      contraction <- Conv.betaRoot(applied)
      goal <- rightOf(contraction)
      stripped <- Logic.stripForall(goal)
      index <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", goal))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (guard, conclusion) = parts

      firstLaw <- product.fact(Product.FirstOfPair).map(atEncoding)
      secondLaw <- product.fact(Product.SecondOfPair).map(atEncoding)
      lengthIs <- rules.specAll(firstLaw, List(k, f))
      entriesAre <- rules.specAll(secondLaw, List(k, f))

      below <- LogicError.lift(Term.app(lessThan, index))
      guardEquation <- Conv.apTerm(below, lengthIs).flatMap(Conv.apTerm(logic.negation, _))
      assumed <- LogicError.lift(Kernel.assume(guard))
      narrowed <- LogicError.lift(Kernel.eqMp(guardEquation, assumed))
      value <- rules.spec(index, padded).flatMap(rules.mp(_, narrowed))

      atIndex <- Conv.apThm(entriesAre, index)
      entry <- Conv.trans(atIndex, value)
      _ <-
        if (entry.conclusion == conclusion) Right(())
        else Left(NotOfForm("the entry as the predicate states it", entry.conclusion))

      body <- rules.disch(guard, entry).flatMap(rules.gen(index, _))
      result <- Conv.sym(contraction).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, body)))
    } yield result
  }

  /**
   * A theorem of `Product` at the instance this development uses it at.
   *
   * `'a` becomes `num` and `'b` becomes `num -> 'a`, and the `'a` inside that second replacement is
   * **this** development's element type rather than the one being replaced: type substitution is
   * simultaneous and does not walk into what it substitutes, which is what makes writing the two in
   * one map right rather than a collision.
   */
  private def atEncoding(theorem: Kernel.Thm): Kernel.Thm =
    Kernel.instType(
      Map(
        Classical.TypeVariable -> Numbers,
        Classical.CodomainVariable -> Entries
      ),
      theorem
    )

  /** The two arguments of a `PAIR`, refused when the term is not one. */
  private def destPair(pairing: Term, term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(head, first), second) if head == pairing => Right((first, second))
    case other => Left(NotOfForm("a pair built by PAIR", other))
  }

  /** `num -> num -> bool`, `prod(num,num->'a) -> num` and `prod(num,num->'a) -> (num -> 'a)`. */
  private def orderType: Type = Type.fun(Numbers, Type.fun(Numbers, Type.Bool))
  private def firstType: Type = Type.fun(Encoding, Numbers)
  private def secondType: Type = Type.fun(Encoding, Entries)
  private def pairingType: Type = Type.fun(Numbers, Type.fun(Entries, Encoding))

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
