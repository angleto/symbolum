package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Putting two finite words end to end, and the three relations that are nothing but that.
 *
 * `Word` gave the type a length, an index, a constructor and an extensionality, and `Rotation` gave
 * it the one operation a cyclic sequence wants. Neither gave it the operation a **word** wants. So
 * of a factor -- a stretch of a word, with something possibly before it and something possibly
 * after -- nothing could be said here, and the gap was not that the proof was hard: the sentence
 * could not be written down, because `?x y. w = x u y` needs a `WORD_CONCAT` and there was none.
 *
 * == What is declared, and why the empty word and the one-letter word are here ==
 *
 * Six constants. [[Name]] is the operation; [[Prefix]], [[Suffix]] and [[Factor]] are defined
 * **from** it rather than each on its own, which is what makes `WORD_FACTOR_LENGTH` one lemma
 * instead of three; and [[Empty]] and [[Singleton]] are the two words the first four cannot be
 * stated without.
 *
 * Putting those last two in `Word.scala`, where the type is, was the alternative and it was
 * rejected on the rule this repository already applies to `COND`: a constant is unreachable from
 * every link below the one that declares it, so the question is whether anything below needs it,
 * and nothing does. `Word` builds the empty encoding already, as the witness that makes the type
 * inhabited, and never names it; what turns that witness into a constant worth having is being the
 * unit of an operation, and the operation is here. The one-letter word is narrower still: it exists
 * so that [[Induction]] can say "one letter longer", and it has no other consumer.
 *
 * == Why this is not a paragraph of `Word.scala` ==
 *
 * `Rotation` is a development of its own because it **must** be: `WORD_ROTATE` mentions `NUM_MOD`,
 * `Word.standard` is built below `Modular`, and a rotation written inside `Word` would build in the
 * chain and refuse beside it. That argument does not reach this file, and saying so matters,
 * because it is the argument a reader will assume. Everything here needs is `NUM_ADD`, `NUM_SUB`,
 * `NUM_LT` and `COND`, and all four are in `Word.standard`'s own signature; this could have lived
 * there and would have built.
 *
 * What decided it instead is size and subject. This is six constants and sixteen derived facts
 * against `Word`'s four and six, and what it is about is an algebra over the type rather than the
 * type. `Rotation`'s one constant and three facts were given a file on a weaker argument than that.
 *
 * == The operation is not spelled `*`, and that is `docs/adr/0018` rather than taste ==
 *
 * The card that asked for this wrote a factor as `?x y. w = x * u * y`, which is how the literature
 * writes it. That record's criterion for overloading a symbol is that the candidates name **the
 * same operation**, and it refuses `-` and `/` over `num` on exactly that ground. Concatenation is
 * not multiplication: it is not commutative, where both of the `*`s already in the notation are,
 * and `NUM_MUL` and `WORD_CONCAT` do not share a shape either, one being `num -> num -> num` and
 * the other polymorphic in the element. So the prefix form stands, and `WORD_CONCAT u v` is what a
 * reader writes.
 *
 * == What the guard on [[Nth]] is, and what it is not ==
 *
 * [[Rotation.Nth]] carries a bound and `RotationSpec` says the unguarded version of it is **false**.
 * This one is different and the difference is worth having in front of a reader who has met that
 * file: above the total length both sides here are `WORD_PAD`, the first by [[Word.NthAbove]] and
 * the second because the index into the right-hand word is above **its** length too, so the
 * unguarded statement is true. It is not proved, because nothing wants it: [[NthLeft]] and
 * [[NthRight]] are what a consumer reaches for, both are below a length by construction, and the
 * one place the raw shape is used is inside this file's own associativity.
 *
 * == What is here and what is not ==
 *
 * [[Induction]] is the one a consumer asked for by name, and it adds **on the right**: the card
 * that produced this file wants to go from `/f0^i f` to `/f0^(i+1) f`, which is a word one letter
 * longer at the end, and an induction on the length alone does not give a proof that shape. It is
 * derived rather than assumed, by ordinary induction on the length with the decomposition of a
 * non-empty word into its front and its last letter built inside the step.
 *
 * == Specialising by position here, and what makes it safe ==
 *
 * Every derivation in this file specialises by position, `Rules.specAll` and not `Rules.specTo`,
 * and two of the lemmas it does that to have **two leading binders of one type**:
 * `WORD_EXTENSIONALITY` takes two words and this file's own entry laws take two. That is exactly
 * the hazard this repository has recorded, where a reversed pair gives a theorem that is true and
 * is not the one the caller meant, and the type checker cannot see it.
 *
 * What makes it safe is not care, it is the check at the bottom of [[construct]]: every one of the
 * sixteen facts is compared against the text in [[Statements]] before the development is handed
 * out, and every intermediate step in this file is on a path that ends at one of them. A reversed
 * pair anywhere reaches a conclusion that is not what the text says and the construction refuses.
 * So the guard is the same one `Word` and `Rotation` already carry, and it is named here because a
 * reader who knows the convention will otherwise stop at the first `specAll`.
 *
 * **There is no cancellation and no decidable equality.** `WORD_CONCAT u v = WORD_CONCAT u w ==> v = w`
 * is true and is not here; nothing has needed it, and this file states the absence rather than
 * guessing at the shape a consumer will want, which is what `Rotation` does about composition.
 * **And a factor is stated and not decided**: `WORD_FACTOR u w` is an existential over all words,
 * so deciding it is a bounded search, which is the card `55c586b0` is about and is not this one.
 * [[FactorRefused]] is what refuses by the one argument that costs nothing, which is length.
 */
final class Concatenation private (
  val word: Word,
  val peano: Peano,
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

object Concatenation {

  /* ------------------------------------------------------------------- names */

  /** The word of no letters, which is the unit of [[Name]] on both sides. */
  val Empty: String = "WORD_EMPTY"

  /** `WORD_SINGLETON x` is the word whose only letter is `x`. */
  val Singleton: String = "WORD_SINGLETON"

  /** `WORD_CONCAT u v` is `u` followed by `v`. */
  val Name: String = "WORD_CONCAT"

  /** `WORD_PREFIX u w` is `?y. w = WORD_CONCAT u y`. */
  val Prefix: String = "WORD_PREFIX"

  /** `WORD_SUFFIX u w` is `?x. w = WORD_CONCAT x u`. */
  val Suffix: String = "WORD_SUFFIX"

  /**
   * `WORD_FACTOR u w` is `?x y. w = WORD_CONCAT (WORD_CONCAT x u) y`.
   *
   * Defined through the concatenation and not beside it, which is what makes [[PrefixIsFactor]] and
   * [[SuffixIsFactor]] two short derivations rather than two more definitions to keep in step. A
   * prefix is a factor with nothing in front and a suffix is one with nothing behind, and "nothing"
   * is [[Empty]] in both cases.
   */
  val Factor: String = "WORD_FACTOR"

  /** `|- WORD_LENGTH WORD_EMPTY = ZERO`. */
  val EmptyLength: String = "WORD_EMPTY_LENGTH"

  /**
   * `|- !w. WORD_LENGTH w = ZERO ==> w = WORD_EMPTY`, which is [[EmptyLength]] read backwards.
   *
   * Published on 2026-09-16 and derived here since the induction landed, inside its base case: a
   * word of length zero agrees with `WORD_EMPTY` at every index below zero, of which there are
   * none, so extensionality settles it from a premise it never reads. It is a fact of its own now
   * because a second consumer arrived, and a derivation living inside the one proof that first
   * needed it is a derivation the next caller writes again.
   *
   * What wanted it: a step of a rewriting system splits a word into a context, a left-hand side
   * and a tail, and the argument about the tail divides on whether the tail is there. `NUM_CASES`
   * answers that about the tail's **length**, and nothing turned a length of zero back into the
   * empty word, so the case where the rule applies at the very end could not be closed.
   */
  val LengthZero: String = "WORD_LENGTH_ZERO"

  /** `|- !x. WORD_LENGTH (WORD_SINGLETON x) = SUC ZERO`. */
  val SingletonLength: String = "WORD_SINGLETON_LENGTH"

  /** `|- !x. WORD_NTH (WORD_SINGLETON x) ZERO = x`, which is what makes the name honest. */
  val SingletonNth: String = "WORD_SINGLETON_NTH"

  /** `|- !u v. WORD_LENGTH (WORD_CONCAT u v) = NUM_ADD (WORD_LENGTH u) (WORD_LENGTH v)`. */
  val Length: String = "WORD_CONCAT_LENGTH"

  /**
   * `|- !u v i. i < |u| + |v| ==> WORD_NTH (WORD_CONCAT u v) i = COND (i < |u|) ...`
   *
   * The raw shape, with the conditional left standing, and the file's docstring says why the guard
   * is here and how it differs from [[Rotation.Nth]]'s. A consumer wants [[NthLeft]] or
   * [[NthRight]] instead; this is what both are derived from and what the associativity reads.
   */
  val Nth: String = "WORD_CONCAT_NTH"

  /** `|- !u v i. i < |u| ==> WORD_NTH (WORD_CONCAT u v) i = WORD_NTH u i`. */
  val NthLeft: String = "WORD_CONCAT_NTH_LEFT"

  /** `|- !u v i. i < |v| ==> WORD_NTH (WORD_CONCAT u v) (|u| + i) = WORD_NTH v i`. */
  val NthRight: String = "WORD_CONCAT_NTH_RIGHT"

  /** `|- !w. WORD_CONCAT WORD_EMPTY w = w`. */
  val EmptyLeft: String = "WORD_CONCAT_EMPTY_LEFT"

  /** `|- !w. WORD_CONCAT w WORD_EMPTY = w`. */
  val EmptyRight: String = "WORD_CONCAT_EMPTY_RIGHT"

  /**
   * `|- !u v w. WORD_CONCAT (WORD_CONCAT u v) w = WORD_CONCAT u (WORD_CONCAT v w)`.
   *
   * The longest derivation here by a wide margin, and every one of its obligations is arithmetic
   * rather than about words: an index below the total length is in the first block, in the second or
   * in the third, and saying which needs the difference `i - |u|` to be placed. Three facts about
   * `num` were missing in front of it and are now in `Peano`, named where they are derived:
   * `NUM_ADD_LT_CANCEL`, `NUM_LE_OF_NOT_LT` and `NUM_SUB_SUB`. The last is the one that decides
   * the third case, where `(i - |u|) - |v|` and `i - (|u| + |v|)` have to be the same number.
   */
  val Associative: String = "WORD_CONCAT_ASSOC"

  /** `|- !u w. WORD_PREFIX u w ==> WORD_FACTOR u w`, with [[Empty]] as the witness in front. */
  val PrefixIsFactor: String = "WORD_PREFIX_FACTOR"

  /** `|- !u w. WORD_SUFFIX u w ==> WORD_FACTOR u w`, with [[Empty]] as the witness behind. */
  val SuffixIsFactor: String = "WORD_SUFFIX_FACTOR"

  /**
   * `|- !u w. WORD_FACTOR u w ==> NUM_LE (WORD_LENGTH u) (WORD_LENGTH w)`.
   *
   * The first statement that **uses** the predicate rather than defining it, which is the test of
   * whether the predicate is usable at all.
   */
  val FactorLength: String = "WORD_FACTOR_LENGTH"

  /**
   * `|- !u w. NUM_LT (WORD_LENGTH w) (WORD_LENGTH u) ==> ~(WORD_FACTOR u w)`.
   *
   * The predicate saying no, which is the half a definition does not give you. A relation that has
   * never been derived to fail is one nobody has shown to be a relation rather than the constant
   * true, and `ConcatenationSpec` spends this on a concrete pair: a one-letter word is not a factor
   * of the empty one.
   */
  val FactorRefused: String = "WORD_FACTOR_REFUSED"

  /**
   * `|- !P. P WORD_EMPTY /\ (!w x. P w ==> P (WORD_CONCAT w (WORD_SINGLETON x))) ==> !w. P w`
   *
   * Induction that extends **on the right**, which is the shape a consumer walking a word from its
   * front needs and which induction on the length alone does not give. Derived from
   * `Natural.Induction` over `\n. !w. WORD_LENGTH w = n ==> P w`, with the decomposition of a word
   * of length `SUC n` into its first `n` letters and its last one built inside the step rather than
   * published: naming the front would be a seventh constant, and nothing outside this proof has
   * asked for one.
   */
  /**
   * `|- !f x y. NUM_SUM (\i. f i (WORD_NTH (WORD_CONCAT x y) i)) (WORD_LENGTH (WORD_CONCAT x y)) =
   * NUM_SUM (\i. f i (WORD_NTH x i)) (WORD_LENGTH x) +
   * NUM_SUM (\i. f (WORD_LENGTH x + i) (WORD_NTH y i)) (WORD_LENGTH y)`
   *
   * A tally over the positions of a word, split where the word is. It is the fact anything that
   * counts or weighs letters needs, and nothing that counts letters can be said without it: the
   * number of times a letter occurs, a potential that weighs a letter by where it sits, a cost
   * that depends on both. Each is this lemma at a different `f`.
   *
   * `f` takes the index as well as the letter, and that is not generality for its own sake. A
   * tally that only saw letters could not express a measure that weighs a letter by its distance
   * from the start, which is the one this repository wanted it for, and the shifted summand on the
   * right is exactly the correction such a measure needs: the letters of `y` sit `WORD_LENGTH x`
   * further along than they do in `y` alone.
   *
   * Three facts do the work and each covers one part. [[Length]] turns the bound into a sum so
   * that `NUM_SUM_SPLIT` applies. [[NthLeft]] says the left half reads the same in the whole,
   * below `WORD_LENGTH x`. [[NthRight]] says the right half reads the same at `WORD_LENGTH x + i`,
   * which is the shifted summand `NUM_SUM_SPLIT` produces, so the two meet without an adapter.
   */
  val Tally: String = "WORD_CONCAT_TALLY"

  val Induction: String = "WORD_INDUCTION"

  /* ------------------------------------------------------------------- types */

  private val Element: Type = TyVar(Classical.TypeVariable)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Words: Type = TyApp(Word.TypeName, List(Element))
  private val Entries: Type = Type.fun(Numbers, Element)

  private def binaryNumbers: Type = Type.fun(Numbers, Type.fun(Numbers, Numbers))
  private def orderType: Type = Type.fun(Numbers, Type.fun(Numbers, Type.Bool))
  private def lengthType: Type = Type.fun(Words, Numbers)
  private def nthType: Type = Type.fun(Words, Entries)
  private def concatType: Type = Type.fun(Words, Type.fun(Words, Words))

  /* --------------------------------------------------------------- the bodies */

  /**
   * The six definitions, as text, in the order they are introduced.
   *
   * [[Name]]'s body has **two** conditionals nested and only the outer one is bookkeeping. The outer
   * is what makes the function `WORD_PAD` above the total length, which is the premise
   * [[Word.Make]] carries and nothing more; the inner is the operation. Writing the inner one alone
   * would hand `WORD_MAKE` a function that is `WORD_NTH v (i - |u|)` at every index above the
   * total, and above `|v|` that is `WORD_PAD` anyway -- so the word would be right and the premise
   * would be unprovable without [[Word.NthAbove]] and an argument about the difference. The outer
   * conditional buys that argument for one `COND_FALSE`.
   */
  val Definitions: Vector[(String, String)] = Vector(
    Empty -> "WORD_MAKE ZERO (\\i:num. (WORD_PAD:'a))",
    Singleton ->
      ("\\x:'a. WORD_MAKE (SUC ZERO) " +
        "(\\i:num. COND (NUM_LT i (SUC ZERO)) x (WORD_PAD:'a))"),
    Name ->
      ("\\u:word('a). \\v:word('a). " +
        "WORD_MAKE (NUM_ADD (WORD_LENGTH u) (WORD_LENGTH v)) " +
        "(\\i:num. COND (NUM_LT i (NUM_ADD (WORD_LENGTH u) (WORD_LENGTH v))) " +
        "(COND (NUM_LT i (WORD_LENGTH u)) (WORD_NTH u i) " +
        "(WORD_NTH v (NUM_SUB i (WORD_LENGTH u)))) (WORD_PAD:'a))"),
    Prefix -> "\\u:word('a). \\w:word('a). ?y:word('a). w = WORD_CONCAT u y",
    Suffix -> "\\u:word('a). \\w:word('a). ?x:word('a). w = WORD_CONCAT x u",
    Factor ->
      ("\\u:word('a). \\w:word('a). ?x:word('a). ?y:word('a). " +
        "w = WORD_CONCAT (WORD_CONCAT x u) y")
  )

  /**
   * Everything this development proves, as the text a person checks it by.
   *
   * Compared as terms rather than as printed text, for the reason `Word.Statements` gives: a type
   * variable is written `'a` and printed `a`, so a printed polymorphic statement does not read back.
   */
  val Statements: Vector[(String, String)] = Vector(
    EmptyLength -> "WORD_LENGTH (WORD_EMPTY:word('a)) = ZERO",
    LengthZero -> "!w:word('a). WORD_LENGTH w = ZERO ==> w = WORD_EMPTY",
    SingletonLength -> "!x:'a. WORD_LENGTH (WORD_SINGLETON x) = SUC ZERO",
    SingletonNth -> "!x:'a. WORD_NTH (WORD_SINGLETON x) ZERO = x",
    Length ->
      ("!u:word('a). !v:word('a). WORD_LENGTH (WORD_CONCAT u v) = " +
        "NUM_ADD (WORD_LENGTH u) (WORD_LENGTH v)"),
    Nth ->
      ("!u:word('a). !v:word('a). !i:num. " +
        "NUM_LT i (NUM_ADD (WORD_LENGTH u) (WORD_LENGTH v)) ==> " +
        "WORD_NTH (WORD_CONCAT u v) i = " +
        "COND (NUM_LT i (WORD_LENGTH u)) (WORD_NTH u i) " +
        "(WORD_NTH v (NUM_SUB i (WORD_LENGTH u)))"),
    NthLeft ->
      ("!u:word('a). !v:word('a). !i:num. NUM_LT i (WORD_LENGTH u) ==> " +
        "WORD_NTH (WORD_CONCAT u v) i = WORD_NTH u i"),
    NthRight ->
      ("!u:word('a). !v:word('a). !i:num. NUM_LT i (WORD_LENGTH v) ==> " +
        "WORD_NTH (WORD_CONCAT u v) (NUM_ADD (WORD_LENGTH u) i) = WORD_NTH v i"),
    Tally ->
      ("!f:num -> 'a -> num. !u:word('a). !v:word('a). " +
        "NUM_SUM (\\i:num. f i (WORD_NTH (WORD_CONCAT u v) i)) " +
        "(WORD_LENGTH (WORD_CONCAT u v)) = " +
        "NUM_ADD (NUM_SUM (\\i:num. f i (WORD_NTH u i)) (WORD_LENGTH u)) " +
        "(NUM_SUM (\\i:num. f (NUM_ADD (WORD_LENGTH u) i) (WORD_NTH v i)) (WORD_LENGTH v))"),
    EmptyLeft -> "!w:word('a). WORD_CONCAT WORD_EMPTY w = w",
    EmptyRight -> "!w:word('a). WORD_CONCAT w WORD_EMPTY = w",
    Associative ->
      ("!u:word('a). !v:word('a). !w:word('a). " +
        "WORD_CONCAT (WORD_CONCAT u v) w = WORD_CONCAT u (WORD_CONCAT v w)"),
    PrefixIsFactor -> "!u:word('a). !w:word('a). WORD_PREFIX u w ==> WORD_FACTOR u w",
    SuffixIsFactor -> "!u:word('a). !w:word('a). WORD_SUFFIX u w ==> WORD_FACTOR u w",
    FactorLength ->
      ("!u:word('a). !w:word('a). WORD_FACTOR u w ==> " +
        "NUM_LE (WORD_LENGTH u) (WORD_LENGTH w)"),
    FactorRefused ->
      ("!u:word('a). !w:word('a). NUM_LT (WORD_LENGTH w) (WORD_LENGTH u) ==> " +
        "(~(WORD_FACTOR u w))"),
    Induction ->
      ("!P:word('a)->bool. P WORD_EMPTY /\\ " +
        "(!w:word('a). !x:'a. P w ==> P (WORD_CONCAT w (WORD_SINGLETON x))) ==> " +
        "!w:word('a). P w")
  )

  /* ---------------------------------------------------------------- building */

  /**
   * The standard development, which is **the chain's own** and not a second one beside it.
   *
   * The same lookup `Rotation.standard` is, and for the same reason: nothing is built on top of
   * this, so a second development over a narrower theory would have no caller and would put a
   * second `WORD_CONCAT` of a different origin into the world for a consumer to trip over.
   */
  lazy val standard: Concatenation = Chain.standard.concatenation

  /**
   * The development over a `Word`, a `Peano` in the same signature, and the theory to extend.
   *
   * `base` is the theory to extend and is not `word.theory`: this is the last link, so what it
   * extends is whatever the chain's end is, for the reason `Rotation.construct`'s comment gives. A
   * development that extended `word.theory` would declare its six constants into a side branch, and
   * every link above would be unable to see them.
   *
   * The `Peano` is separate from the base and is the one the base was built over: the fourteen
   * facts about `num` this file takes by name are theorems of that theory and so of every extension
   * of it.
   */
  def construct(word: Word, peano: Peano, base: Theory): Either[LogicError, Concatenation] = {
    val classical = word.product.classical
    val notation = word.notation

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
      first <- define(base, Empty, Definitions(0)._2)
      (withEmpty, emptyDefinition) = first
      second <- define(withEmpty, Singleton, Definitions(1)._2)
      (withSingleton, singletonDefinition) = second
      third <- define(withSingleton, Name, Definitions(2)._2)
      (withConcat, concatDefinition) = third
      fourth <- define(withConcat, Prefix, Definitions(3)._2)
      (withPrefix, prefixDefinition) = fourth
      fifth <- define(withPrefix, Suffix, Definitions(4)._2)
      (withSuffix, suffixDefinition) = fifth
      sixth <- define(withSuffix, Factor, Definitions(5)._2)
      (theory, factorDefinition) = sixth

      logic <- classical.logic.over(theory)

      makeLength <- word.fact(Word.MakeLength)
      makeNth <- word.fact(Word.MakeNth)
      extensional <- word.fact(Word.Extensionality)
      condTrue <- classical.fact(Classical.CondTrue)
      condFalse <- classical.fact(Classical.CondFalse)
      induction <- peano.naturals.fact(Natural.Induction)

      numbers <- Numeric.of(peano)

      emptyLength <- emptyIsEmpty(logic, theory, emptyDefinition, makeLength, makeNth)
      lengthZero <- nothingIsEmpty(logic, theory, emptyLength, extensional, numbers)
      singleton <- oneLetter(
        logic, theory, singletonDefinition, makeLength, makeNth, condTrue, condFalse, numbers)
      (singletonLength, singletonNth) = singleton

      joined <- concatLaws(
        logic, theory, concatDefinition, makeLength, makeNth, condTrue, condFalse)
      (length, nth) = joined

      nthLeft <- entriesOnTheLeft(logic, theory, nth, condTrue, numbers)
      nthRight <- entriesOnTheRight(logic, theory, nth, condFalse, numbers)

      emptyLeft <- unitOnTheLeft(
        logic, theory, length, nthRight, emptyLength, extensional, numbers)
      emptyRight <- unitOnTheRight(
        logic, theory, length, nthLeft, emptyLength, extensional, numbers)

      associative <- associativity(
        logic, theory, classical, length, nth, nthLeft, nthRight, condFalse, extensional, numbers)

      prefixIsFactor <- oneSideIsAFactor(
        logic, theory, prefixDefinition, factorDefinition, emptyLeft, inFront = true)
      suffixIsFactor <- oneSideIsAFactor(
        logic, theory, suffixDefinition, factorDefinition, emptyRight, inFront = false)

      factorLength <- aFactorIsNoLonger(logic, theory, factorDefinition, length, numbers)
      factorRefused <- tooLongToBeAFactor(logic, theory, factorDefinition, factorLength, numbers)

      inductive <- rightwardInduction(
        logic,
        theory,
        notation,
        induction,
        lengthZero,
        (emptyLength, singletonLength, singletonNth),
        (length, nthLeft, nthRight),
        (makeLength, makeNth, extensional, condTrue, condFalse),
        numbers
      )

      split <- peano.fact(Peano.PartialSumSplit)
      congruence <- peano.fact(Peano.PartialSumCongruenceBelow)
      tally <- tallyOverAConcatenation(
        logic, theory, notation, split, congruence, length, nthLeft, nthRight)

      facts = Map(
        EmptyLength -> emptyLength,
        LengthZero -> lengthZero,
        SingletonLength -> singletonLength,
        SingletonNth -> singletonNth,
        Length -> length,
        Nth -> nth,
        NthLeft -> nthLeft,
        NthRight -> nthRight,
        EmptyLeft -> emptyLeft,
        EmptyRight -> emptyRight,
        Associative -> associative,
        PrefixIsFactor -> prefixIsFactor,
        SuffixIsFactor -> suffixIsFactor,
        FactorLength -> factorLength,
        FactorRefused -> factorRefused,
        Induction -> inductive,
        Tally -> tally
      )

      // Each statement checked against the text a person reads it by, here rather than in the spec:
      // a development that built something other than what it says it built must not be handed out.
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { (acc, entry) =>
        val (name, text) = entry
        for {
          _ <- acc
          expected <- Parser.proposition(theory, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Concatenation(
      word,
      peano,
      theory,
      notation,
      Map(
        Empty -> emptyDefinition,
        Singleton -> singletonDefinition,
        Name -> concatDefinition,
        Prefix -> prefixDefinition,
        Suffix -> suffixDefinition,
        Factor -> factorDefinition
      ),
      facts
    )
  }

  /**
   * [[Tally]]: `NUM_SUM_SPLIT` at the length of the first half, with both halves re-read.
   *
   * No induction of its own. `Peano` does the splitting and this supplies the three word facts that
   * make the pieces line up, which is the whole of it:
   *
   *  - [[Length]] turns `WORD_LENGTH (WORD_CONCAT u v)` into a sum, which is the shape the split
   *    is stated at. Without it the split does not apply at all.
   *  - below `WORD_LENGTH u` the whole reads as `u` does, so the first summand is congruent to the
   *    tally over `u`, by [[NthLeft]] under `NUM_SUM_CONGRUENCE_BELOW`.
   *  - the split's shifted summand is at `WORD_LENGTH u + i`, and [[NthRight]] is stated at exactly
   *    that index, so the second summand is congruent to the tally over `v`.
   *
   * The two congruences are the only work and they are the same shape twice: build the pointwise
   * agreement below the bound, discharge the order hypothesis from the bound itself, and hand it to
   * the congruence. They are not written once and used twice, because the agreement each proves is
   * about a different pair of functions and only the assembly is shared.
   *
   * == It does not compose with itself through the rewriter, and a consumer will meet that ==
   *
   * A word with a factor in the middle is `x (m y)`, so the decomposition a rewriting step wants is
   * this lemma applied **twice**. Put it to `Rewrite.rewrite` as a rule on such a term and it
   * refuses, with a transitivity failure naming the once-applied term against the twice-applied
   * one. The cause is in the right side above: it introduces a lambda for the shifted weight, and
   * the second application has to match under that lambda, so the two ends of the chain differ by
   * the beta redex the first application left.
   *
   * Measured on 2026-09-16, through `Rewrite.rewrite` directly and through `Peano.normalisation`,
   * with the same refusal from both — and after a probe had first confirmed the rule fires
   * perfectly well **once**, on a two-part word, which is what makes this a statement about
   * composition rather than about the pattern. A higher-order left side is not the obstacle and was
   * the first guess.
   *
   * What a consumer should do instead is apply it at the root twice, giving each application a term
   * the other has not touched: the whole word, then the second summand of what came back, joined by
   * the kernel's congruence. That is more work than a rule set and it is the work that succeeds.
   */
  private def tallyOverAConcatenation(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    split: Kernel.Thm,
    congruence: Kernel.Thm,
    length: Kernel.Thm,
    nthLeft: Kernel.Thm,
    nthRight: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      statement <- Statements
        .collectFirst { case (name, text) if name == Tally => text }
        .toRight(MissingDefinition(Tally))
        .flatMap(text => Parser.proposition(theory, notation, text))

      stripped <- Logic.stripForall(statement)
      (binders, body) = stripped
      weight <- binders.lift(0).toRight(NotOfForm("a weight", body))
      left <- binders.lift(1).toRight(NotOfForm("a first half", body))
      right <- binders.lift(2).toRight(NotOfForm("a second half", body))

      sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
      (statedLeft, statedRight) = sides

      // The length fact and the split, as rewrites. They carry the left side of the statement to
      // `A + B`, where `A` and `B` are tallies over the WHOLE word at the two ranges. The two
      // congruences cannot join them: each carries a hypothesis about an index, so a rewriter has
      // nothing to do with it.
      conversions <- Peano.normalisation(logic, Vector(length, split), Vector.empty)
      splitting <- conversions._1(statedLeft)
      afterSplit <- Term.destEq(splitting.conclusion).map(_._2).toRight(
        NotOfForm("an equation", splitting.conclusion))

      wholeParts <- summands(logic, afterSplit)
      (wholeLeft, wholeRight) = wholeParts
      wantedParts <- summands(logic, statedRight)
      (wantedLeft, wantedRight) = wantedParts

      // Below `WORD_LENGTH u` the whole reads as `u` does.
      leftAgrees <- reReadUnder(logic, congruence, nthLeft, wholeLeft, wantedLeft, List(left, right))
      // And at `WORD_LENGTH u + i`, below `WORD_LENGTH v`, it reads as `v` does.
      rightAgrees <- reReadUnder(logic, congruence, nthRight, wholeRight, wantedRight, List(left, right))

      // `a = a'` and `b = b'` give `a + b = a' + b'`: the kernel's own congruence, once to carry
      // the addition over the first and once to apply the result to the second.
      addition <- additionOf(logic, afterSplit)
      partial <- Conv.apTerm(addition, leftAgrees)
      joined <- LogicError.lift(Kernel.mkComb(partial, rightAgrees))

      whole <- Conv.trans(splitting, joined)
      result <- rules.gen(right, whole).flatMap(rules.gen(left, _)).flatMap(rules.gen(weight, _))
    } yield result
  }

  /** The two summands of `NUM_ADD a b`. */
  private def summands(logic: Logic, term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(_, first), second) => Right((first, second))
    case other => Left(NotOfForm("a sum of two tallies", other))
  }

  /** `NUM_ADD` itself, taken off a sum rather than rebuilt from the theory. */
  private def additionOf(logic: Logic, term: Term): Either[LogicError, Term] = term match {
    case App(App(head, _), _) => Right(head)
    case other => Left(NotOfForm("a sum", other))
  }

  /**
   * One tally re-read through a fact about where the letters come from.
   *
   * `NUM_SUM f n = NUM_SUM g n` where `f` and `g` differ only in which word they read, given a
   * fact of the form `index < bound ==> WORD_NTH <one> <index> = WORD_NTH <other> <index'>`. The
   * agreement is built pointwise at a fresh index, the order hypothesis is discharged from the
   * bound the sum already carries, and `NUM_SUM_CONGRUENCE_BELOW` does the rest.
   *
   * Both summands go through here and the only difference is which fact arrives, which is why the
   * shift is nowhere in this function: `WORD_CONCAT_NTH_RIGHT` is already stated at the shifted
   * index, so what it proves at a fresh `i` is already the equation the shifted summand needs.
   */
  private def reReadUnder(
    logic: Logic,
    congruence: Kernel.Thm,
    nthFact: Kernel.Thm,
    from: Term,
    to: Term,
    halves: List[Term]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      fromParts <- sumParts(logic, from)
      (fromFunction, bound) = fromParts
      toParts <- sumParts(logic, to)
      (toFunction, _) = toParts

      index = Conv.freshVariable(
        "i",
        TyApp(Natural.TypeName, Nil),
        Term.freeVariables(from) ++ Term.freeVariables(to))

      // The fact at this pair of halves and this index: `i < bound ==> nth ... = nth ...`.
      atHalves <- rules.specAll(nthFact, halves :+ index)
      condition <- logic.destImp(atHalves.conclusion).map(_._1).toRight(
        NotOfForm("an implication", atHalves.conclusion))
      assumed <- LogicError.lift(Kernel.assume(condition))
      letters <- rules.mp(atHalves, assumed)

      // Both sides applied at the index and beta reduced, so what is compared is what the sum adds.
      fromAt <- LogicError.lift(Term.app(fromFunction, index)).flatMap(Conv.betaRoot)
      toAt <- LogicError.lift(Term.app(toFunction, index)).flatMap(Conv.betaRoot)
      fromValue <- Term.destEq(fromAt.conclusion).map(_._2).toRight(
        NotOfForm("an equation", fromAt.conclusion))

      weighted <- weightOf(fromValue).toRight(NotOfForm("a weighted letter", fromValue))
      carried <- Conv.apTerm(weighted, letters)
      pointwise <- Conv.trans(fromAt, carried).flatMap(Conv.trans(_, Conv.sym(toAt).getOrElse(toAt)))

      agreement <- rules.disch(condition, pointwise).flatMap(rules.gen(index, _))
      instance <- rules.specAll(congruence, List(fromFunction, toFunction, bound))
      result <- rules.mp(instance, agreement)
    } yield result
  }

  /** The summand function and the bound of `NUM_SUM f n`. */
  private def sumParts(logic: Logic, term: Term): Either[LogicError, (Term, Term)] = term match {
    case App(App(_, function), bound) => Right((function, bound))
    case other => Left(NotOfForm("a partial sum", other))
  }

  /** `f i` out of `f i (WORD_NTH w i)`, which is what the letter is carried under. */
  private def weightOf(term: Term): Option[Term] = term match {
    case App(head, _) => Some(head)
    case _ => None
  }

  /**
   * The facts about `num` this file needs, collected once and named.
   *
   * Fourteen of them, and reaching for each through `peano.fact` at the point of use would put the
   * failure of a missing name in the middle of a derivation instead of at the top. Three of the
   * fourteen did not exist before this file was written and are named in [[Associative]]'s
   * docstring.
   */
  private final case class Numeric(
    addAtZero: Kernel.Thm,
    zeroPlus: Kernel.Thm,
    addAtSuccessor: Kernel.Thm,
    addAssociative: Kernel.Thm,
    addCommutative: Kernel.Thm,
    atMostSum: Kernel.Thm,
    addMonotone: Kernel.Thm,
    addStrictlyMonotone: Kernel.Thm,
    addCancelsOrder: Kernel.Thm,
    addCancelsStrictOrder: Kernel.Thm,
    atMostFromNotBelow: Kernel.Thm,
    belowExcludesAtMost: Kernel.Thm,
    belowThenAtMost: Kernel.Thm,
    transitive: Kernel.Thm,
    minusThenPlus: Kernel.Thm,
    subTwice: Kernel.Thm,
    sumMinus: Kernel.Thm,
    notBelowZero: Kernel.Thm,
    belowSuccessorCases: Kernel.Thm,
    successorPositive: Kernel.Thm
  )

  private object Numeric {
    def of(peano: Peano): Either[LogicError, Numeric] =
      for {
        addAtZero <- peano.fact(Peano.AddAtZero)
        zeroPlus <- peano.fact(Peano.ZeroPlus)
        addAtSuccessor <- peano.fact(Peano.AddAtSuccessor)
        addAssociative <- peano.fact(Peano.AddAssociative)
        addCommutative <- peano.fact(Peano.AddCommutative)
        atMostSum <- peano.fact(Peano.AtMostSum)
        addMonotone <- peano.fact(Peano.AddMonotone)
        addStrictlyMonotone <- peano.fact(Peano.AddStrictlyMonotone)
        addCancelsOrder <- peano.fact(Peano.AddCancelsOrder)
        addCancelsStrictOrder <- peano.fact(Peano.AddCancelsStrictOrder)
        atMostFromNotBelow <- peano.fact(Peano.AtMostFromNotBelow)
        belowExcludesAtMost <- peano.fact(Peano.BelowExcludesAtMost)
        belowThenAtMost <- peano.fact(Peano.BelowThenAtMost)
        transitive <- peano.fact(Peano.Transitive)
        minusThenPlus <- peano.fact(Peano.MinusThenPlus)
        subTwice <- peano.fact(Peano.SubTwice)
        sumMinus <- peano.fact(Peano.SumMinus)
        notBelowZero <- peano.fact(Peano.NotBelowZero)
        belowSuccessorCases <- peano.fact(Peano.BelowSuccessorCases)
        successorPositive <- peano.fact(Peano.SuccessorPositive)
      } yield Numeric(
        addAtZero,
        zeroPlus,
        addAtSuccessor,
        addAssociative,
        addCommutative,
        atMostSum,
        addMonotone,
        addStrictlyMonotone,
        addCancelsOrder,
        addCancelsStrictOrder,
        atMostFromNotBelow,
        belowExcludesAtMost,
        belowThenAtMost,
        transitive,
        minusThenPlus,
        subTwice,
        sumMinus,
        notBelowZero,
        belowSuccessorCases,
        successorPositive
      )
  }

  /* ------------------------------------------------------- the constructor's two laws */

  /**
   * `|- WORD_LENGTH t = k` and `|- WORD_NTH t = f`, from `|- t = WORD_MAKE k f` and the padding.
   *
   * The shared five-sixths of every law in this file. [[Word.MakeLength]] and [[Word.MakeNth]] each
   * carry "what you handed me was already padded", so a caller that has proved that once gets both.
   */
  private def madeLaws(
    logic: Logic,
    unfolded: Kernel.Thm,
    padding: Kernel.Thm,
    makeLength: Kernel.Thm,
    makeNth: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules

    for {
      made <- rightOf(unfolded)
      parts <- destructureMake(made)
      (size, entries) = parts

      lengthIs <- rules.specAll(makeLength, List(size, entries)).flatMap(rules.mp(_, padding))
      lengthOf <- headOf(lengthIs)
      lengthResult <- Conv.apTerm(lengthOf, unfolded).flatMap(Conv.trans(_, lengthIs))

      nthIs <- rules.specAll(makeNth, List(size, entries)).flatMap(rules.mp(_, padding))
      nthOf <- headOf(nthIs)
      nthResult <- Conv.apTerm(nthOf, unfolded).flatMap(Conv.trans(_, nthIs))
    } yield (lengthResult, nthResult)
  }

  /**
   * `|- !i. ~(i < k) ==> f i = WORD_PAD`, where `f` is `\i. COND (i < k) e WORD_PAD`.
   *
   * The premise both of [[Word]]'s constructor laws carry, and for a body that pads itself with a
   * conditional it is [[Classical.CondFalse]] and nothing else. This is `Rotation.shapeOf`'s first
   * block, taken out of it because three definitions here have that shape instead of one.
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

  /**
   * The same for a body that is `WORD_PAD` at **every** index rather than only above the length.
   *
   * The empty word's function, and the guard is never used: the beta contraction alone proves the
   * conclusion, and the implication is discharged from a proof that did not assume it. That is the
   * shape `Word.emptyIsPadded` already has for the same encoding one level down.
   */
  private def constantPadding(
    logic: Logic,
    theory: Theory,
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

      applied <- LogicError.lift(Term.app(entries, index))
      beta <- Conv.betaRoot(applied)
      result <- rules.disch(notBelow, beta).flatMap(rules.gen(index, _))
    } yield result
  }

  /* ------------------------------------------------------------- the two small words */

  /** `|- WORD_LENGTH WORD_EMPTY = ZERO`. */
  private def emptyIsEmpty(
    logic: Logic,
    theory: Theory,
    definition: Kernel.Thm,
    makeLength: Kernel.Thm,
    makeNth: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      unfolded <- Conv.unfold(definition, Nil)
      made <- rightOf(unfolded)
      padding <- constantPadding(logic, theory, made)
      laws <- madeLaws(logic, unfolded, padding, makeLength, makeNth)
    } yield laws._1

  /** `|- !x. WORD_LENGTH (WORD_SINGLETON x) = SUC ZERO` and `|- !x. WORD_NTH ... ZERO = x`. */
  private def oneLetter(
    logic: Logic,
    theory: Theory,
    definition: Kernel.Thm,
    makeLength: Kernel.Thm,
    makeNth: Kernel.Thm,
    condTrue: Kernel.Thm,
    condFalse: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val letter = Term.variable("x", Element)

    for {
      unfolded <- Conv.unfold(definition, List(letter))
      made <- rightOf(unfolded)
      padding <- conditionalPadding(logic, theory, condFalse, made)
      laws <- madeLaws(logic, unfolded, padding, makeLength, makeNth)
      (lengthIs, nthIs) = laws
      lengthResult <- rules.gen(letter, lengthIs)

      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      atZero <- Conv.apThm(nthIs, zero)
      opened <- rightOf(atZero).flatMap(Conv.betaRoot).flatMap(Conv.trans(atZero, _))
      conditional <- rightOf(opened)
      branches <- destructureCond(conditional)
      (yes, no) = branches
      guard <- destructureCondGuard(conditional)
      below <- rules.spec(zero, numbers.successorPositive)
      _ <-
        if (below.conclusion == guard) Right(())
        else Left(NotOfForm("zero below one", below.conclusion))
      isLetter <- rules
        .specAll(condTrue, List(guard, yes, no))
        .flatMap(rules.mp(_, below))
        .flatMap(Conv.trans(opened, _))
      nthResult <- rules.gen(letter, isLetter)
    } yield (lengthResult, nthResult)
  }

  /* ------------------------------------------------------------- the two laws of the join */

  /** [[Length]] and [[Nth]], which is [[madeLaws]] with the outer conditional opened for [[Nth]]. */
  private def concatLaws(
    logic: Logic,
    theory: Theory,
    definition: Kernel.Thm,
    makeLength: Kernel.Thm,
    makeNth: Kernel.Thm,
    condTrue: Kernel.Thm,
    condFalse: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val v = Term.variable("v", Words)
    val i = Term.variable("i", Numbers)

    for {
      unfolded <- Conv.unfold(definition, List(u, v))
      made <- rightOf(unfolded)
      padding <- conditionalPadding(logic, theory, condFalse, made)
      laws <- madeLaws(logic, unfolded, padding, makeLength, makeNth)
      (lengthIs, nthIs) = laws
      lengthResult <- rules.genAll(lengthIs, List(u, v))

      atIndex <- Conv.apThm(nthIs, i)
      opened <- rightOf(atIndex).flatMap(Conv.betaRoot).flatMap(Conv.trans(atIndex, _))
      conditional <- rightOf(opened)
      guard <- destructureCondGuard(conditional)
      branches <- destructureCond(conditional)
      (yes, no) = branches

      assumed <- LogicError.lift(Kernel.assume(guard))
      inside <- rules
        .specAll(condTrue, List(guard, yes, no))
        .flatMap(rules.mp(_, assumed))
        .flatMap(Conv.trans(opened, _))
      nthResult <- rules
        .disch(guard, inside)
        .flatMap(rules.gen(i, _))
        .flatMap(rules.genAll(_, List(u, v)))
    } yield (lengthResult, nthResult)
  }

  /** [[NthLeft]]: [[Nth]] with the bound widened to the total and the conditional taken true. */
  private def entriesOnTheLeft(
    logic: Logic,
    theory: Theory,
    nth: Kernel.Thm,
    condTrue: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val v = Term.variable("v", Words)
    val i = Term.variable("i", Numbers)

    for {
      sizes <- lengthsOf(theory, List(u, v))
      List(lu, lv) = sizes
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      guard <- LogicError.lift(Term.appAll(strictOrder, List(i, lu)))
      assumed <- LogicError.lift(Kernel.assume(guard))

      total <- sum(theory, lu, lv)
      inTotal <- widened(logic, i, lu, total, assumed, numbers)

      general <- rules.specAll(nth, List(u, v, i)).flatMap(rules.mp(_, inTotal))
      conditional <- rightOf(general)
      branches <- destructureCond(conditional)
      (yes, no) = branches
      innerGuard <- destructureCondGuard(conditional)
      entry <- rules
        .specAll(condTrue, List(innerGuard, yes, no))
        .flatMap(rules.mp(_, assumed))
        .flatMap(Conv.trans(general, _))
      result <- rules
        .disch(guard, entry)
        .flatMap(rules.gen(i, _))
        .flatMap(rules.genAll(_, List(u, v)))
    } yield result
  }

  /**
   * [[NthRight]]: [[Nth]] at `|u| + i`, where the conditional is false and the difference collapses.
   *
   * Two obligations and neither is bookkeeping. That `|u| + i` is not below `|u|` is `NUM_LE_ADD`
   * against `NUM_LT_NOT_LE`; and that `(|u| + i) - |u|` is `i` is `NUM_ADD_SUB`, which takes away
   * the **second** summand, so the sum is commuted before it applies.
   */
  private def entriesOnTheRight(
    logic: Logic,
    theory: Theory,
    nth: Kernel.Thm,
    condFalse: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val v = Term.variable("v", Words)
    val i = Term.variable("i", Numbers)

    for {
      sizes <- lengthsOf(theory, List(u, v))
      List(lu, lv) = sizes
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      guard <- LogicError.lift(Term.appAll(strictOrder, List(i, lv)))
      assumed <- LogicError.lift(Kernel.assume(guard))

      index <- sum(theory, lu, i)
      inTotal <- rules
        .specAll(numbers.addStrictlyMonotone, List(lu, i, lv))
        .flatMap(rules.mp(_, assumed))
      notBelowLeft <- notBelowTheSummand(logic, theory, lu, i, numbers)

      general <- rules.specAll(nth, List(u, v, index)).flatMap(rules.mp(_, inTotal))
      conditional <- rightOf(general)
      branches <- destructureCond(conditional)
      (yes, no) = branches
      innerGuard <- destructureCondGuard(conditional)
      entry <- rules
        .specAll(condFalse, List(innerGuard, yes, no))
        .flatMap(rules.mp(_, notBelowLeft))
        .flatMap(Conv.trans(general, _))

      collapses <- differenceCollapses(logic, theory, lu, i, numbers)
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      nthOfRight <- LogicError.lift(Term.app(nthConstant, v))
      moved <- Conv.apTerm(nthOfRight, collapses).flatMap(Conv.trans(entry, _))

      result <- rules
        .disch(guard, moved)
        .flatMap(rules.gen(i, _))
        .flatMap(rules.genAll(_, List(u, v)))
    } yield result
  }

  /* ----------------------------------------------------------------- the two units */

  /** [[EmptyLeft]], by extensionality, with [[NthRight]] at a shift of zero. */
  private def unitOnTheLeft(
    logic: Logic,
    theory: Theory,
    length: Kernel.Thm,
    nthRight: Kernel.Thm,
    emptyLength: Kernel.Thm,
    extensional: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val w = Term.variable("w", Words)

    for {
      empty <- LogicError.lift(theory.constant(Empty, Words))
      joined <- concat(theory, empty, w)
      sizes <- lengthsOf(theory, List(empty, w))
      List(_, size) = sizes
      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))

      total <- rules.specAll(length, List(empty, w))
      atZero <- Conv.apTerm(plus, emptyLength).flatMap(Conv.apThm(_, size))
      collapsed <- rules.spec(size, numbers.zeroPlus)
      lengths <- Conv.trans(total, atZero).flatMap(Conv.trans(_, collapsed))

      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      index = Conv.freshVariable("i", Numbers, Term.freeVariables(joined))
      agreement <- agreesBelow(logic, theory, joined, index) { (i, guarded) =>
        for {
          // The bound in the premise is the JOINED word's length and every lemma below is about
          // `w`'s. They are equal by `lengths`, so the assumption is carried across once rather
          // than every lemma being restated at the other bound; `Rotation.identityAtZero` makes
          // the same move and `Rules.mp` is why it is not optional, since an antecedent that does
          // not match is left standing as a hypothesis instead of being refused.
          below <- carryRight(strictOrder, i, lengths, guarded)
          shifted <- rules.specAll(nthRight, List(empty, w, i)).flatMap(rules.mp(_, below))
          moved <- Conv.apTerm(plus, emptyLength).flatMap(Conv.apThm(_, i))
          collapses <- rules.spec(i, numbers.zeroPlus).flatMap(Conv.trans(moved, _))
          restated <- Conv.sym(collapses).flatMap(Conv.apTerm(nthOfJoined, _))
          result <- Conv.trans(restated, shifted)
        } yield result
      }

      both <- rules.conjIntro(lengths, agreement)
      equal <- rules.specAll(extensional, List(joined, w)).flatMap(rules.mp(_, both))
      result <- rules.gen(w, equal)
    } yield result
  }

  /** [[EmptyRight]], by extensionality, with [[NthLeft]] doing the whole of the agreement. */
  private def unitOnTheRight(
    logic: Logic,
    theory: Theory,
    length: Kernel.Thm,
    nthLeft: Kernel.Thm,
    emptyLength: Kernel.Thm,
    extensional: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val w = Term.variable("w", Words)

    for {
      empty <- LogicError.lift(theory.constant(Empty, Words))
      joined <- concat(theory, w, empty)
      sizes <- lengthsOf(theory, List(w, empty))
      List(size, _) = sizes
      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      partial <- LogicError.lift(Term.app(plus, size))

      total <- rules.specAll(length, List(w, empty))
      atZero <- Conv.apTerm(partial, emptyLength)
      collapsed <- rules.spec(size, numbers.addAtZero)
      lengths <- Conv.trans(total, atZero).flatMap(Conv.trans(_, collapsed))

      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      index = Conv.freshVariable("i", Numbers, Term.freeVariables(joined))
      agreement <- agreesBelow(logic, theory, joined, index) { (i, guarded) =>
        carryRight(strictOrder, i, lengths, guarded)
          .flatMap(below => rules.specAll(nthLeft, List(w, empty, i)).flatMap(rules.mp(_, below)))
      }

      both <- rules.conjIntro(lengths, agreement)
      equal <- rules.specAll(extensional, List(joined, w)).flatMap(rules.mp(_, both))
      result <- rules.gen(w, equal)
    } yield result
  }

  /**
   * [[LengthZero]], by extensionality over an empty range.
   *
   * The second premise of `WORD_EXTENSIONALITY` is an agreement at every index below the length,
   * and the length is zero, so the range is empty and the branch is closed from the absurdity of
   * `i < ZERO` rather than from anything about the two words. That is the whole proof, and it is
   * why the lemma costs nothing beyond what extensionality costs.
   */
  private def nothingIsEmpty(
    logic: Logic,
    theory: Theory,
    emptyLength: Kernel.Thm,
    extensional: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val w = Term.variable("w", Words)

    for {
      empty <- LogicError.lift(theory.constant(Empty, Words))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))

      lengthOfW <- LogicError.lift(Term.app(lengthConstant, w))
      measured <- LogicError.lift(Term.eq(lengthOfW, zero))
      assumed <- LogicError.lift(Kernel.assume(measured))
      lengths <- Conv.sym(emptyLength).flatMap(Conv.trans(assumed, _))

      index = Conv.freshVariable("i", Numbers, Term.freeVariables(w))
      agreement <- agreesBelow(logic, theory, w, index) { (i, below) =>
        for {
          nothing <- rules.spec(i, numbers.notBelowZero)
          carried <- carryRight(strictOrder, i, assumed, below)
          absurd <- rules.notElim(nothing, carried)
          leftEntry <- LogicError.lift(Term.appAll(nthConstant, List(w, i)))
          rightEntry <- LogicError.lift(Term.appAll(nthConstant, List(empty, i)))
          wanted <- LogicError.lift(Term.eq(leftEntry, rightEntry))
          result <- rules.falsityElim(wanted, absurd)
        } yield result
      }

      both <- rules.conjIntro(lengths, agreement)
      equal <- rules.specAll(extensional, List(w, empty)).flatMap(rules.mp(_, both))
      result <- rules.disch(measured, equal).flatMap(rules.gen(w, _))
    } yield result
  }

  /* ---------------------------------------------------------------- associativity */

  /**
   * [[Associative]], by extensionality, with the entries split three ways.
   *
   * The lengths are one application of `NUM_ADD_ASSOC`. The entries are the work: an index below the
   * total is in `u`, in `v` or in `w`, and which of the three it is comes from two nested excluded
   * middles, on `i < |u|` and then on `i < |u| + |v|`. Between them the three branches spend all
   * three of the `Peano` facts this file needed added.
   */
  private def associativity(
    logic: Logic,
    theory: Theory,
    classical: Classical,
    length: Kernel.Thm,
    nth: Kernel.Thm,
    nthLeft: Kernel.Thm,
    nthRight: Kernel.Thm,
    condFalse: Kernel.Thm,
    extensional: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val v = Term.variable("v", Words)
    val w = Term.variable("w", Words)

    for {
      uv <- concat(theory, u, v)
      vw <- concat(theory, v, w)
      left <- concat(theory, uv, w)
      right <- concat(theory, u, vw)

      sizes <- lengthsOf(theory, List(u, v, w))
      List(lu, lv, lw) = sizes
      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      minus <- LogicError.lift(theory.constant(Peano.Subtraction, binaryNumbers))
      partialU <- LogicError.lift(Term.app(plus, lu))

      lengthUV <- rules.specAll(length, List(u, v))
      lengthVW <- rules.specAll(length, List(v, w))

      // `|(u v) w| = (|u| + |v|) + |w|` and `|u (v w)| = |u| + (|v| + |w|)`.
      lengthLeft <- rules
        .specAll(length, List(uv, w))
        .flatMap(step =>
          Conv.apTerm(plus, lengthUV).flatMap(Conv.apThm(_, lw)).flatMap(Conv.trans(step, _))
        )
      lengthRight <- rules
        .specAll(length, List(u, vw))
        .flatMap(step => Conv.apTerm(partialU, lengthVW).flatMap(Conv.trans(step, _)))
      shape <- rules.specAll(numbers.addAssociative, List(lu, lv, lw))
      lengths <- Conv
        .trans(lengthLeft, shape)
        .flatMap(step => Conv.sym(lengthRight).flatMap(Conv.trans(step, _)))

      totalUV <- sum(theory, lu, lv)

      index = Conv.freshVariable(
        "i",
        Numbers,
        Term.freeVariables(left) ++ Term.freeVariables(right)
      )
      agreement <- agreesBelow(logic, theory, left, index) { (i, belowTotal) =>
        for {
          totalLeft <- carryRight(strictOrder, i, lengthLeft, belowTotal)
          belowU <- LogicError.lift(Term.appAll(strictOrder, List(i, lu)))
          belowUV <- LogicError.lift(Term.appAll(strictOrder, List(i, totalUV)))
          difference <- LogicError.lift(Term.appAll(minus, List(i, lu)))

          insideU <- LogicError.lift(Kernel.assume(belowU))
          branchFirst <- inTheFirstBlock(
            logic, theory, Blocks(u, v, w, uv, vw, left, right), i, insideU, lengthUV, nthLeft, numbers)

          notInsideU <- logic.mkNot(belowU)
          assumedNotU <- LogicError.lift(Kernel.assume(notInsideU))
          atLeastU <- rules
            .specAll(numbers.atMostFromNotBelow, List(i, lu))
            .flatMap(rules.mp(_, assumedNotU))
          shift <- shiftedBy(logic, i, lu, atLeastU, numbers)

          insideUV <- LogicError.lift(Kernel.assume(belowUV))
          branchSecond <- inTheSecondBlock(
            logic,
            theory,
            Blocks(u, v, w, uv, vw, left, right),
            (i, difference),
            (insideUV, shift),
            (lengthUV, lengthVW),
            (nthLeft, nthRight),
            numbers
          )

          notInsideUV <- logic.mkNot(belowUV)
          assumedNotUV <- LogicError.lift(Kernel.assume(notInsideUV))
          branchThird <- inTheThirdBlock(
            logic,
            theory,
            Blocks(u, v, w, uv, vw, left, right),
            (i, difference),
            (assumedNotUV, assumedNotU, shift, totalLeft),
            (lengthUV, lengthVW, shape),
            (nth, condFalse),
            numbers
          )

          innerCases <- classical.excludedMiddleAt(belowUV)
          afterU <- rules.disjElim(innerCases, branchSecond, branchThird)
          outerCases <- classical.excludedMiddleAt(belowU)
          settled <- rules.disjElim(outerCases, branchFirst, afterU)
        } yield settled
      }

      both <- rules.conjIntro(lengths, agreement)
      equal <- rules.specAll(extensional, List(left, right)).flatMap(rules.mp(_, both))
      result <- rules.genAll(equal, List(u, v, w))
    } yield result
  }

  /** The index is inside `u`: both sides are `WORD_NTH u i`, by [[NthLeft]] three times. */
  private def inTheFirstBlock(
    logic: Logic,
    theory: Theory,
    words: Blocks,
    i: Term,
    insideU: Kernel.Thm,
    lengthUV: Kernel.Thm,
    nthLeft: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    import words.{u, v, w, uv, vw}

    for {
      sizes <- lengthsOf(theory, List(u, v))
      List(lu, lv) = sizes
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))

      total <- sum(theory, lu, lv)
      belowTotal <- widened(logic, i, lu, total, insideU, numbers)
      belowUV <- Conv
        .sym(lengthUV)
        .flatMap(equation => carryRight(strictOrder, i, equation, belowTotal))

      outer <- rules.specAll(nthLeft, List(uv, w, i)).flatMap(rules.mp(_, belowUV))
      inner <- rules.specAll(nthLeft, List(u, v, i)).flatMap(rules.mp(_, insideU))
      onTheLeft <- Conv.trans(outer, inner)
      onTheRight <- rules.specAll(nthLeft, List(u, vw, i)).flatMap(rules.mp(_, insideU))
      result <- Conv.sym(onTheRight).flatMap(Conv.trans(onTheLeft, _))
    } yield result
  }

  /** The index is inside `v`: both sides are `WORD_NTH v (i - |u|)`. */
  private def inTheSecondBlock(
    logic: Logic,
    theory: Theory,
    words: Blocks,
    indices: (Term, Term),
    facts: (Kernel.Thm, Kernel.Thm),
    lengthsOfPairs: (Kernel.Thm, Kernel.Thm),
    laws: (Kernel.Thm, Kernel.Thm),
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    import words.{u, v, w, uv, vw, right}
    val (i, j) = indices
    val (insideUV, shift) = facts
    val (lengthUV, lengthVW) = lengthsOfPairs
    val (nthLeft, nthRight) = laws

    for {
      sizes <- lengthsOf(theory, List(u, v, w))
      List(lu, lv, lw) = sizes
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      totalUV <- sum(theory, lu, lv)

      // `i = |u| + j` with `j = i - |u|`, so `|u| + j < |u| + |v|` cancels to `j < |v|`.
      restated <- carryLeft(strictOrder, shift, totalUV, insideUV)
      belowV <- rules
        .specAll(numbers.addCancelsStrictOrder, List(lu, j, lv))
        .flatMap(rules.mp(_, restated))

      belowUV <- Conv
        .sym(lengthUV)
        .flatMap(equation => carryRight(strictOrder, i, equation, insideUV))

      outerLeft <- rules.specAll(nthLeft, List(uv, w, i)).flatMap(rules.mp(_, belowUV))
      nthOfUV <- LogicError.lift(Term.app(nthConstant, uv))
      movedLeft <- Conv.sym(shift).flatMap(Conv.apTerm(nthOfUV, _))
      innerLeft <- rules.specAll(nthRight, List(u, v, j)).flatMap(rules.mp(_, belowV))
      onTheLeft <- Conv.trans(outerLeft, movedLeft).flatMap(Conv.trans(_, innerLeft))

      totalVW <- sum(theory, lv, lw)
      belowTotalVW <- widened(logic, j, lv, totalVW, belowV, numbers)
      belowVW <- Conv
        .sym(lengthVW)
        .flatMap(equation => carryRight(strictOrder, j, equation, belowTotalVW))

      nthOfRight <- LogicError.lift(Term.app(nthConstant, right))
      movedRight <- Conv.sym(shift).flatMap(Conv.apTerm(nthOfRight, _))
      outerRight <- rules.specAll(nthRight, List(u, vw, j)).flatMap(rules.mp(_, belowVW))
      innerRight <- rules.specAll(nthLeft, List(v, w, j)).flatMap(rules.mp(_, belowV))
      onTheRight <- Conv.trans(movedRight, outerRight).flatMap(Conv.trans(_, innerRight))

      result <- Conv.sym(onTheRight).flatMap(Conv.trans(onTheLeft, _))
    } yield result
  }

  /**
   * The index is inside `w`, which is where `NUM_SUB_SUB` decides the two differences agree.
   *
   * The left side reaches `WORD_NTH w (i - (|u| + |v|))` by taking the outer conditional false once;
   * the right side reaches `WORD_NTH w ((i - |u|) - |v|)` by taking it false twice. Nothing but
   * `NUM_SUB_SUB` says those are the same index, and that lemma did not exist before this file.
   */
  private def inTheThirdBlock(
    logic: Logic,
    theory: Theory,
    words: Blocks,
    indices: (Term, Term),
    facts: (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm),
    lengthsOfPairs: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    laws: (Kernel.Thm, Kernel.Thm),
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    import words.{u, v, w, uv, vw}
    val (i, j) = indices
    val (assumedNotUV, assumedNotU, shift, totalLeft) = facts
    val (lengthUV, lengthVW, shape) = lengthsOfPairs
    val (nth, condFalse) = laws

    for {
      sizes <- lengthsOf(theory, List(u, v, w))
      List(lu, lv, lw) = sizes
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      atMost <- LogicError.lift(theory.constant(Peano.NonStrictOrder, orderType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      minus <- LogicError.lift(theory.constant(Peano.Subtraction, binaryNumbers))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      nthOfW <- LogicError.lift(Term.app(nthConstant, w))
      partialU <- LogicError.lift(Term.app(plus, lu))
      takeAway <- LogicError.lift(Term.app(minus, i))
      totalUV <- sum(theory, lu, lv)
      totalVW <- sum(theory, lv, lw)

      // ---- the left side: the index is past `u v`, so the entry is `w`'s at `i - (|u| + |v|)`.
      notBelowLengthUV <- Conv
        .sym(lengthUV)
        .flatMap(equation => carryRightNegated(logic, strictOrder, i, equation, assumedNotUV))
      boundOfLeft <- Conv
        .sym(lengthUV)
        .flatMap(equation => Conv.apTerm(plus, equation).flatMap(Conv.apThm(_, lw)))
        .flatMap(equation => carryRight(strictOrder, i, equation, totalLeft))
      generalLeft <- rules.specAll(nth, List(uv, w, i)).flatMap(rules.mp(_, boundOfLeft))
      entryLeft <- takeTheFalseBranch(logic, generalLeft, notBelowLengthUV, condFalse)
      atUV <- Conv.apTerm(takeAway, lengthUV)
      onTheLeft <- Conv.apTerm(nthOfW, atUV).flatMap(Conv.trans(entryLeft, _))

      // ---- the right side: past `u`, and then past `v` inside `v w`.
      boundOfRight <- Conv
        .sym(lengthVW)
        .flatMap(Conv.apTerm(partialU, _))
        .flatMap(Conv.trans(shape, _))
        .flatMap(equation => carryRight(strictOrder, i, equation, totalLeft))
      generalRight <- rules.specAll(nth, List(u, vw, i)).flatMap(rules.mp(_, boundOfRight))
      entryRight <- takeTheFalseBranch(logic, generalRight, assumedNotU, condFalse)

      // `|v| <= j`, so the index is past `v` too; and `j < |v| + |w|`, so it is inside `v w`.
      atLeastUV <- rules
        .specAll(numbers.atMostFromNotBelow, List(i, totalUV))
        .flatMap(rules.mp(_, assumedNotUV))
      atLeastShifted <- Conv
        .sym(shift)
        .flatMap(equation => carryRight(atMost, totalUV, equation, atLeastUV))
      atLeastV <- rules
        .specAll(numbers.addCancelsOrder, List(lu, lv, j))
        .flatMap(rules.mp(_, atLeastShifted))
      notBelowV <- refuses(logic, strictOrder, j, lv, atLeastV, numbers)

      grouped <- carryRight(strictOrder, i, shape, totalLeft)
      totalOfRight <- sum(theory, lu, totalVW)
      shifted <- carryLeft(strictOrder, shift, totalOfRight, grouped)
      belowTotalVW <- rules
        .specAll(numbers.addCancelsStrictOrder, List(lu, j, totalVW))
        .flatMap(rules.mp(_, shifted))
      insideVW <- rules.specAll(nth, List(v, w, j)).flatMap(rules.mp(_, belowTotalVW))
      entryInner <- takeTheFalseBranch(logic, insideVW, notBelowV, condFalse)

      twice <- rules.specAll(numbers.subTwice, List(i, lu, lv))
      sameEntry <- Conv.apTerm(nthOfW, twice)
      onTheRight <- Conv.trans(entryRight, entryInner).flatMap(Conv.trans(_, sameEntry))

      result <- Conv.sym(onTheRight).flatMap(Conv.trans(onTheLeft, _))
    } yield result
  }

  /**
   * The five words the associativity is about, named rather than positional.
   *
   * A seven-tuple was what this was first, and two of the three branch functions ignored two of its
   * slots, which is the shape that makes a reader count commas. The same reason `Numeric` above is
   * a record: what a branch needs is a subset, and a subset of named fields costs nothing to read.
   */
  private final case class Blocks(
    u: Term,
    v: Term,
    w: Term,
    uv: Term,
    vw: Term,
    left: Term,
    right: Term
  )

  /* --------------------------------------------------------------- the predicates */

  /**
   * [[PrefixIsFactor]] or [[SuffixIsFactor]], which differ only in which side the empty word goes.
   *
   * One function for both, because everything but the witness is shared: open the one-sided
   * existential, put the empty word on the other side through the unit law, and close the two
   * existentials the factor is.
   */
  private def oneSideIsAFactor(
    logic: Logic,
    theory: Theory,
    sideDefinition: Kernel.Thm,
    factorDefinition: Kernel.Thm,
    unit: Kernel.Thm,
    inFront: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val w = Term.variable("w", Words)

    for {
      empty <- LogicError.lift(theory.constant(Empty, Words))
      joinConstant <- LogicError.lift(theory.constant(Name, concatType))
      opened <- Conv.unfold(sideDefinition, List(u, w))
      premise <- leftOf(opened)
      assumed <- LogicError.lift(Kernel.assume(premise))
      existential <- LogicError.lift(Kernel.eqMp(opened, assumed))
      predicate <- rightOf(opened).flatMap(predicateOf(logic, _))

      witness = Conv.freshVariable(
        if (inFront) "y" else "x",
        Words,
        Term.freeVariables(existential.conclusion) + u + w
      )
      instanceTerm <- LogicError
        .lift(Term.app(predicate, witness))
        .flatMap(Conv.betaRoot)
        .flatMap(rightOf)
      instance <- LogicError.lift(Kernel.assume(instanceTerm))

      factor <- Conv.unfold(factorDefinition, List(u, w))
      outerPredicate <- rightOf(factor).flatMap(predicateOf(logic, _))

      front = if (inFront) empty else (witness: Term)
      back = if (inFront) (witness: Term) else empty

      // `w = u y` becomes `w = (EMPTY u) y`, or `w = x u` becomes `w = (x u) EMPTY`.
      rebuilt <-
        if (inFront)
          rules
            .spec(u, unit)
            .flatMap(Conv.sym)
            .flatMap(Conv.apTerm(joinConstant, _))
            .flatMap(Conv.apThm(_, witness))
            .flatMap(Conv.trans(instance, _))
        else
          concat(theory, witness, u)
            .flatMap(rules.spec(_, unit))
            .flatMap(Conv.sym)
            .flatMap(Conv.trans(instance, _))

      innerBody <- LogicError
        .lift(Term.app(outerPredicate, front))
        .flatMap(Conv.betaRoot)
        .flatMap(rightOf)
      innerPredicate <- predicateOf(logic, innerBody)
      inner <- rules.existsIntro(innerPredicate, back, rebuilt)
      outer <- rules.existsIntro(outerPredicate, front, inner)
      concluded <- Conv
        .sym(factor)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, outer)))

      closed <- rules.existsElim(existential, witness, concluded)
      result <- rules.disch(premise, closed).flatMap(rules.genAll(_, List(u, w)))
    } yield result
  }

  /** [[FactorLength]]: `|w|` is `(|x| + |u|) + |y|`, and a summand is at most its sum, twice. */
  private def aFactorIsNoLonger(
    logic: Logic,
    theory: Theory,
    factorDefinition: Kernel.Thm,
    length: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val w = Term.variable("w", Words)

    for {
      opened <- Conv.unfold(factorDefinition, List(u, w))
      premise <- leftOf(opened)
      assumed <- LogicError.lift(Kernel.assume(premise))
      existential <- LogicError.lift(Kernel.eqMp(opened, assumed))
      outerPredicate <- rightOf(opened).flatMap(predicateOf(logic, _))

      taken = Term.freeVariables(existential.conclusion) + u + w
      front = Conv.freshVariable("x", Words, taken)
      innerBody <- LogicError
        .lift(Term.app(outerPredicate, front))
        .flatMap(Conv.betaRoot)
        .flatMap(rightOf)
      innerExistential <- LogicError.lift(Kernel.assume(innerBody))
      innerPredicate <- predicateOf(logic, innerBody)
      back = Conv.freshVariable("y", Words, taken + front)
      instanceTerm <- LogicError
        .lift(Term.app(innerPredicate, back))
        .flatMap(Conv.betaRoot)
        .flatMap(rightOf)
      instance <- LogicError.lift(Kernel.assume(instanceTerm))

      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      atMost <- LogicError.lift(theory.constant(Peano.NonStrictOrder, orderType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      sizes <- lengthsOf(theory, List(u, front, back))
      List(lu, lx, ly) = sizes

      frontJoined <- concat(theory, front, u)
      wholeLength <- Conv.apTerm(lengthConstant, instance)
      outerSum <- rules.specAll(length, List(frontJoined, back))
      innerSum <- rules.specAll(length, List(front, u))
      shaped <- Conv.apTerm(plus, innerSum).flatMap(Conv.apThm(_, ly))
      chain <- Conv.trans(wholeLength, outerSum).flatMap(Conv.trans(_, shaped))

      // `|u| <= |x| + |u|`, which is the sum the other way round, and then `<= (|x| + |u|) + |y|`.
      middle <- sum(theory, lx, lu)
      total <- sum(theory, middle, ly)
      commuted <- rules.specAll(numbers.addCommutative, List(lu, lx))
      atMostFlipped <- rules.specAll(numbers.atMostSum, List(lu, lx))
      atMostMiddle <- carryRight(atMost, lu, commuted, atMostFlipped)
      atMostWhole <- rules.specAll(numbers.atMostSum, List(middle, ly))
      together <- rules.conjIntro(atMostMiddle, atMostWhole)
      chained <- rules
        .specAll(numbers.transitive, List(lu, middle, total))
        .flatMap(rules.mp(_, together))
      reached <- Conv
        .sym(chain)
        .flatMap(equation => carryRight(atMost, lu, equation, chained))

      withoutBack <- rules.existsElim(innerExistential, back, reached)
      withoutFront <- rules.existsElim(existential, front, withoutBack)
      result <- rules.disch(premise, withoutFront).flatMap(rules.genAll(_, List(u, w)))
    } yield result
  }

  /** [[FactorRefused]]: the contrapositive of [[FactorLength]] against `NUM_LT_NOT_LE`. */
  private def tooLongToBeAFactor(
    logic: Logic,
    theory: Theory,
    factorDefinition: Kernel.Thm,
    factorLength: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val w = Term.variable("w", Words)

    for {
      sizes <- lengthsOf(theory, List(u, w))
      List(lu, lw) = sizes
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      premise <- LogicError.lift(Term.appAll(strictOrder, List(lw, lu)))
      assumed <- LogicError.lift(Kernel.assume(premise))

      opened <- Conv.unfold(factorDefinition, List(u, w))
      claim <- leftOf(opened)
      supposed <- LogicError.lift(Kernel.assume(claim))
      bound <- rules.specAll(factorLength, List(u, w)).flatMap(rules.mp(_, supposed))
      excluded <- rules
        .specAll(numbers.belowExcludesAtMost, List(lw, lu))
        .flatMap(rules.mp(_, assumed))
      absurd <- rules.notElim(excluded, bound)
      refused <- rules.notIntro(claim, absurd)
      result <- rules.disch(premise, refused).flatMap(rules.genAll(_, List(u, w)))
    } yield result
  }

  /* ---------------------------------------------------------------- the induction */

  /**
   * [[Induction]], by induction on the length with the decomposition built inside the step.
   *
   * The predicate handed to `Natural.Induction` is `\n. !w. WORD_LENGTH w = n ==> P w`, which is the
   * standard way to induct on a structure whose size is a number and is the only way available here,
   * because `word` is a defined type and the recursion principle it was carved with is `num`'s.
   *
   * The base is the empty word and nothing else: a word of length zero agrees with `WORD_EMPTY` at
   * every index below zero, of which there are none, so extensionality settles it from a proof that
   * never used its second premise. That is the same reading of an empty range `Rotation.AtZero`
   * relies on, met again.
   */
  private def rightwardInduction(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    induction: Kernel.Thm,
    lengthZero: Kernel.Thm,
    small: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    joins: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    tools: (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm),
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (emptyLength, singletonLength, singletonNth) = small
    val (length, nthLeft, nthRight) = joins
    val (makeLength, makeNth, extensional, condTrue, condFalse) = tools

    for {
      goal <- Parser.proposition(theory, notation, Statements.toMap.apply(Induction))
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
      measured <- LogicError.lift(Term.eq(lengthOfSubject, size))
      held <- LogicError.lift(Term.app(predicate, subject))
      claim <- logic.mkImp(measured, held)
      claimAt <- logic.mkForall(subject, claim)
      abstracted <- LogicError.lift(Term.abs(size, claimAt))

      instance <- rules.spec(abstracted, induction)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      base <- atLengthZero(logic, baseTerm, atEmpty, lengthZero)
      step <- atOneMore(
        logic,
        theory,
        stepTerm,
        stepRule,
        (singletonLength, singletonNth),
        (length, nthLeft, nthRight),
        (makeLength, makeNth, extensional, condTrue, condFalse),
        numbers
      )

      everywhere <- rules.conjIntro(base, step).flatMap(rules.mp(opened, _))
      finalWord = Conv.freshVariable("w", Words, taken)
      lengthOfFinal <- LogicError.lift(Term.app(lengthConstant, finalWord))
      reached <- rules
        .spec(lengthOfFinal, everywhere)
        .flatMap(rules.spec(finalWord, _))
        .flatMap(rules.mp(_, Conv.refl(lengthOfFinal)))
      general <- rules.gen(finalWord, reached)
      _ <-
        if (general.conclusion == conclusion) Right(())
        else Left(NotOfForm("what the induction concludes", general.conclusion))
      discharged <- rules.disch(hypothesis, general)
      result <- rules.gen(predicate, discharged)
      _ <-
        if (result.conclusion == goal) Right(())
        else Left(NotOfForm("the induction as it is written", result.conclusion))
    } yield result
  }

  /**
   * The base: a word of length zero is `WORD_EMPTY`, so the predicate at the empty word is it.
   *
   * The extensionality argument that used to be written out here is [[LengthZero]] since
   * 2026-09-16, and this is what is left of the base once it is spent: specialise, detach, and
   * carry the predicate across the equation.
   */
  private def atLengthZero(
    logic: Logic,
    baseTerm: Term,
    atEmpty: Kernel.Thm,
    lengthZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      stripped <- Logic.stripForall(baseTerm)
      subject <- stripped._1.headOption.toRight(NotOfForm("a claim about every word", baseTerm))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (measured, held) = parts
      assumed <- LogicError.lift(Kernel.assume(measured))

      equal <- rules.spec(subject, lengthZero).flatMap(rules.mp(_, assumed))
      transported <- Conv.apTerm(headOfApplication(held), equal)
      reached <- Conv
        .sym(transported)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atEmpty)))
      discharged <- rules.disch(measured, reached)
      result <- rules.gen(subject, discharged)
    } yield result
  }

  /**
   * The step: a word of length `SUC n` is its first `n` letters with its last one on the end.
   *
   * The front is `WORD_MAKE n (\i. COND (i < n) (WORD_NTH w i) WORD_PAD)`, built here rather than
   * declared: a constant for it would be a seventh in a file that has six, and nothing outside this
   * proof has asked to name the front of a word. If one ever does, that is the constant to add, and
   * the two laws [[frontAndLast]] proves are what it would be published with.
   */
  private def atOneMore(
    logic: Logic,
    theory: Theory,
    stepTerm: Term,
    stepRule: Kernel.Thm,
    small: (Kernel.Thm, Kernel.Thm),
    joins: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    tools: (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm),
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (singletonLength, singletonNth) = small
    val (length, nthLeft, nthRight) = joins
    val (makeLength, makeNth, extensional, condTrue, condFalse) = tools

    for {
      stripped <- Logic.stripForall(stepTerm)
      size <- stripped._1.headOption.toRight(NotOfForm("a claim about every number", stepTerm))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (hypothesisTerm, conclusionTerm) = parts
      hypothesis <- LogicError.lift(Kernel.assume(hypothesisTerm))

      inner <- Logic.stripForall(conclusionTerm)
      subject <- inner._1.headOption.toRight(NotOfForm("a claim about every word", conclusionTerm))
      innerParts <- logic.destImp(inner._2).toRight(NotOfForm("an implication", inner._2))
      (measured, held) = innerParts
      assumed <- LogicError.lift(Kernel.assume(measured))

      pieces <- frontAndLast(logic, theory, subject, size, condFalse, makeLength, makeNth)
      (front, lastLetter, frontLength, frontNth) = pieces

      shorter <- rules.spec(front, hypothesis).flatMap(rules.mp(_, frontLength))
      lifted <- rules.specAll(stepRule, List(front, lastLetter)).flatMap(rules.mp(_, shorter))

      rebuilt <- theWordIsItsFrontAndLast(
        logic,
        theory,
        (subject, front, lastLetter, size),
        (assumed, frontLength, frontNth),
        (singletonLength, singletonNth),
        (length, nthLeft, nthRight),
        (extensional, condTrue),
        numbers
      )

      transported <- Conv.apTerm(headOfApplication(held), rebuilt)
      reached <- Conv
        .sym(transported)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, lifted)))
      _ <-
        if (reached.conclusion == held) Right(())
        else Left(NotOfForm("the claim at the longer word", reached.conclusion))
      discharged <- rules.disch(measured, reached).flatMap(rules.gen(subject, _))
      result <- rules.disch(hypothesisTerm, discharged).flatMap(rules.gen(size, _))
    } yield result
  }

  /** The front of `w` at `n`, its letter at `n`, and the two laws of the front. */
  private def frontAndLast(
    logic: Logic,
    theory: Theory,
    subject: Term,
    size: Term,
    condFalse: Kernel.Thm,
    makeLength: Kernel.Thm,
    makeNth: Kernel.Thm
  ): Either[LogicError, (Term, Term, Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules

    for {
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      makeConstant <- LogicError.lift(
        theory.constant(Word.Make, Type.fun(Numbers, Type.fun(Entries, Words)))
      )
      pad <- LogicError.lift(theory.constant(Word.Pad, Element))
      conditional <- LogicError.lift(
        theory.constant(
          Classical.Conditional,
          Type.fun(Type.Bool, Type.fun(Element, Type.fun(Element, Element)))
        )
      )
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))

      index = Conv.freshVariable(
        "i",
        Numbers,
        Term.freeVariables(subject) ++ Term.freeVariables(size)
      )
      entry <- LogicError.lift(Term.appAll(nthConstant, List(subject, index)))
      guard <- LogicError.lift(Term.appAll(strictOrder, List(index, size)))
      branch <- LogicError.lift(Term.appAll(conditional, List(guard, entry, pad)))
      entries <- LogicError.lift(Term.abs(index, branch))
      front <- LogicError.lift(Term.appAll(makeConstant, List(size, entries)))
      lastLetter <- LogicError.lift(Term.appAll(nthConstant, List(subject, size)))

      padding <- conditionalPadding(logic, theory, condFalse, front)
      frontLength <- rules.specAll(makeLength, List(size, entries)).flatMap(rules.mp(_, padding))
      frontNth <- rules.specAll(makeNth, List(size, entries)).flatMap(rules.mp(_, padding))
    } yield (front, lastLetter, frontLength, frontNth)
  }

  /** `|- w = WORD_CONCAT front (WORD_SINGLETON (WORD_NTH w n))`, by extensionality. */
  private def theWordIsItsFrontAndLast(
    logic: Logic,
    theory: Theory,
    terms: (Term, Term, Term, Term),
    facts: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    small: (Kernel.Thm, Kernel.Thm),
    joins: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    tools: (Kernel.Thm, Kernel.Thm),
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (subject, front, lastLetter, size) = terms
    val (measured, frontLength, frontNth) = facts
    val (singletonLength, singletonNth) = small
    val (length, nthLeft, nthRight) = joins
    val (extensional, condTrue) = tools

    for {
      singletonConstant <- LogicError.lift(theory.constant(Singleton, Type.fun(Element, Words)))
      tail <- LogicError.lift(Term.app(singletonConstant, lastLetter))
      joined <- concat(theory, front, tail)
      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(Numbers, Numbers))
      )
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      lengthOfTail <- LogicError.lift(Term.app(lengthConstant, tail))

      tailLength <- rules.spec(lastLetter, singletonLength)
      total <- rules.specAll(length, List(front, tail))
      lengths <- lengthOfTheRebuild(
        logic,
        (total, frontLength, tailLength, measured),
        (plus, successor, zero, size, lengthOfTail),
        numbers
      )

      index = Conv.freshVariable(
        "i",
        Numbers,
        Term.freeVariables(subject) ++ Term.freeVariables(joined)
      )
      agreement <- agreesBelow(logic, theory, subject, index) { (i, below) =>
        for {
          belowSuccessor <- carryRight(strictOrder, i, measured, below)
          cases <- rules
            .specAll(numbers.belowSuccessorCases, List(size, i))
            .flatMap(rules.mp(_, belowSuccessor))
          split <- logic.destDisj(cases.conclusion).toRight(
            NotOfForm("a disjunction", cases.conclusion)
          )
          (belowSize, atSize) = split

          insideFront <- LogicError.lift(Kernel.assume(belowSize))
          fromFront <- entryInsideTheFront(
            logic, theory, front, tail, i, insideFront, frontLength, frontNth, nthLeft, condTrue)

          atTheEnd <- LogicError.lift(Kernel.assume(atSize))
          fromEnd <- entryAtTheLastLetter(
            logic,
            theory,
            (subject, front, tail, joined, lastLetter, size),
            i,
            atTheEnd,
            (frontLength, tailLength, singletonNth),
            nthRight,
            numbers
          )

          settled <- rules.disjElim(cases, fromFront, fromEnd)
        } yield settled
      }

      both <- rules.conjIntro(lengths, agreement)
      result <- rules.specAll(extensional, List(subject, joined)).flatMap(rules.mp(_, both))
    } yield result
  }

  /** `|- WORD_LENGTH (WORD_CONCAT front tail) = WORD_LENGTH w`, which is `n + 1 = SUC n`. */
  private def lengthOfTheRebuild(
    logic: Logic,
    facts: (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm),
    terms: (Term, Term, Term, Term, Term),
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (total, frontLength, tailLength, measured) = facts
    val (plus, successor, zero, size, lengthOfTail) = terms

    for {
      withFront <- Conv.apTerm(plus, frontLength).flatMap(Conv.apThm(_, lengthOfTail))
      partial <- LogicError.lift(Term.app(plus, size))
      withTail <- Conv.apTerm(partial, tailLength)
      shaped <- Conv.trans(total, withFront).flatMap(Conv.trans(_, withTail))

      // `n + SUC ZERO = SUC (n + ZERO) = SUC n`.
      opened <- rules.specAll(numbers.addAtSuccessor, List(size, zero))
      collapsed <- rules.spec(size, numbers.addAtZero)
      lifted <- Conv.apTerm(successor, collapsed).flatMap(Conv.trans(opened, _))
      reached <- Conv.trans(shaped, lifted)

      // `WORD_LENGTH w = WORD_LENGTH (front tail)` and not the other way round, because that is the
      // order `Word.Extensionality` states its first premise in and `Rules.mp` compares antecedents
      // by equality rather than up to symmetry: the reversed equation leaves the whole conjunction
      // standing as a hypothesis and the failure surfaces three steps later, at the generalisation.
      result <- Conv.sym(reached).flatMap(Conv.trans(measured, _))
    } yield result
  }

  /** Below `n` the rebuilt word answers with the front, and the front answers with `w`. */
  private def entryInsideTheFront(
    logic: Logic,
    theory: Theory,
    front: Term,
    tail: Term,
    i: Term,
    insideFront: Kernel.Thm,
    frontLength: Kernel.Thm,
    frontNth: Kernel.Thm,
    nthLeft: Kernel.Thm,
    condTrue: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      belowFront <- Conv
        .sym(frontLength)
        .flatMap(equation => carryRight(strictOrder, i, equation, insideFront))
      outer <- rules.specAll(nthLeft, List(front, tail, i)).flatMap(rules.mp(_, belowFront))

      atIndex <- Conv.apThm(frontNth, i)
      opened <- rightOf(atIndex).flatMap(Conv.betaRoot).flatMap(Conv.trans(atIndex, _))
      conditional <- rightOf(opened)
      branches <- destructureCond(conditional)
      (yes, no) = branches
      guard <- destructureCondGuard(conditional)
      entry <- rules
        .specAll(condTrue, List(guard, yes, no))
        .flatMap(rules.mp(_, insideFront))
        .flatMap(Conv.trans(opened, _))
      onTheRight <- Conv.trans(outer, entry)
      result <- Conv.sym(onTheRight)
    } yield result
  }

  /** At `n` the rebuilt word answers with the one-letter word, whose only letter is `w`'s last. */
  private def entryAtTheLastLetter(
    logic: Logic,
    theory: Theory,
    words: (Term, Term, Term, Term, Term, Term),
    i: Term,
    atTheEnd: Kernel.Thm,
    small: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    nthRight: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (subject, front, tail, joined, lastLetter, size) = words
    val (frontLength, tailLength, singletonNth) = small

    for {
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      plus <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, nthType))
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))
      nthOfSubject <- LogicError.lift(Term.app(nthConstant, subject))

      // `0 < |tail|`, which is `0 < SUC ZERO` with the length read off the singleton's law.
      positive <- rules.spec(zero, numbers.successorPositive)
      belowTail <- Conv
        .sym(tailLength)
        .flatMap(equation => carryRight(strictOrder, zero, equation, positive))

      shifted <- rules.specAll(nthRight, List(front, tail, zero)).flatMap(rules.mp(_, belowTail))
      atZero <- rules.spec(lastLetter, singletonNth)
      entry <- Conv.trans(shifted, atZero)

      // The index that law answers at is `|front| + 0`, which is `n`, which is `i`.
      withFront <- Conv.apTerm(plus, frontLength).flatMap(Conv.apThm(_, zero))
      collapsed <- rules.spec(size, numbers.addAtZero)
      atIndex <- Conv
        .trans(withFront, collapsed)
        .flatMap(step => Conv.sym(atTheEnd).flatMap(Conv.trans(step, _)))
      moved <- Conv.sym(atIndex).flatMap(Conv.apTerm(nthOfJoined, _)).flatMap(Conv.trans(_, entry))

      // And `i` is `n`, so the entry of `w` at `i` is the very letter the tail carries.
      sameEntry <- Conv.apTerm(nthOfSubject, atTheEnd)
      result <- Conv.sym(moved).flatMap(Conv.trans(sameEntry, _))
    } yield result
  }

  /* ------------------------------------------------------------------- internals */

  /**
   * The second premise of [[Word.Extensionality]], built by a caller that proves one entry.
   *
   * The bound is the **first** word's length, and every lemma a branch reaches for is about
   * something else, so the guard is assumed here once rather than in each caller.
   */
  private def agreesBelow(
    logic: Logic,
    theory: Theory,
    first: Term,
    index: FVar
  )(
    entry: (Term, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      lengthOfFirst <- LogicError.lift(Term.app(lengthConstant, first))
      guard <- LogicError.lift(Term.appAll(strictOrder, List(index, lengthOfFirst)))
      assumed <- LogicError.lift(Kernel.assume(guard))
      proved <- entry(index, assumed)
      result <- rules.disch(guard, proved).flatMap(rules.gen(index, _))
    } yield result
  }

  /** `|- NUM_LT i total` from `|- NUM_LT i part` and `part` being a summand of `total`. */
  private def widened(
    logic: Logic,
    i: Term,
    part: Term,
    total: Term,
    below: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      other <- total match {
        case App(App(_, _), second) => Right(second)
        case _ => Left(NotOfForm("a sum", total))
      }
      atMost <- rules.specAll(numbers.atMostSum, List(part, other))
      both <- rules.conjIntro(below, atMost)
      result <- rules.specAll(numbers.belowThenAtMost, List(i, part, total)).flatMap(rules.mp(_, both))
    } yield result
  }

  /** The false branch of a conditional taken, given the negation of its guard. */
  private def takeTheFalseBranch(
    logic: Logic,
    general: Kernel.Thm,
    negated: Kernel.Thm,
    condFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      conditional <- rightOf(general)
      branches <- destructureCond(conditional)
      (yes, no) = branches
      guard <- destructureCondGuard(conditional)
      result <- rules
        .specAll(condFalse, List(guard, yes, no))
        .flatMap(rules.mp(_, negated))
        .flatMap(Conv.trans(general, _))
    } yield result
  }

  /**
   * `|- R a c` from `|- b = c` and `|- R a b`, for any binary relation `R`.
   *
   * The move a derivation makes constantly here, and it is one function rather than one per
   * relation: a comparison is an application like any other, so rewriting its second argument is
   * `Conv.apTerm` under the partially applied relation. Both orders on `num` and the negated forms
   * below all go through it.
   */
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

  /**
   * `|- R b c` from `|- b = a` and `|- R a c`.
   *
   * The other argument, and it takes `c` where [[carryRight]] does not have to: rewriting the first
   * argument leaves the second to be supplied, because a relation is not an equation and there is
   * nothing to read it off.
   */
  private def carryLeft(
    relation: Term,
    equation: Kernel.Thm,
    other: Term,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      reversed <- Conv.sym(equation)
      moved <- Conv.apTerm(relation, reversed).flatMap(Conv.apThm(_, other))
      result <- LogicError.lift(Kernel.eqMp(moved, fact))
    } yield result

  /** `|- ~(R i b)` from `|- a = b` and `|- ~(R i a)`. */
  private def carryRightNegated(
    logic: Logic,
    relation: Term,
    i: Term,
    equation: Kernel.Thm,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- LogicError.lift(Term.app(relation, i))
      moved <- Conv.apTerm(partial, equation).flatMap(Conv.apTerm(logic.negation, _))
      result <- LogicError.lift(Kernel.eqMp(moved, fact))
    } yield result

  /** `|- ~(NUM_LT (NUM_ADD k i) k)`, which is `NUM_LE_ADD` against `NUM_LT_NOT_LE`. */
  private def notBelowTheSummand(
    logic: Logic,
    theory: Theory,
    summand: Term,
    other: Term,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, orderType))
      total <- sum(theory, summand, other)
      holds <- rules.specAll(numbers.atMostSum, List(summand, other))
      result <- refuses(logic, strictOrder, total, summand, holds, numbers)
    } yield result
  }

  /** `|- ~(NUM_LT a b)` from `|- NUM_LE b a`. */
  private def refuses(
    logic: Logic,
    order: Term,
    smaller: Term,
    larger: Term,
    atLeast: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      claim <- LogicError.lift(Term.appAll(order, List(smaller, larger)))
      supposed <- LogicError.lift(Kernel.assume(claim))
      excluded <- rules
        .specAll(numbers.belowExcludesAtMost, List(smaller, larger))
        .flatMap(rules.mp(_, supposed))
      absurd <- rules.notElim(excluded, atLeast)
      result <- rules.notIntro(claim, absurd)
    } yield result
  }

  /** `|- NUM_SUB (NUM_ADD k i) k = i`, which is `NUM_ADD_SUB` with the sum commuted first. */
  private def differenceCollapses(
    logic: Logic,
    theory: Theory,
    summand: Term,
    other: Term,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      minus <- LogicError.lift(theory.constant(Peano.Subtraction, binaryNumbers))
      commuted <- rules.specAll(numbers.addCommutative, List(summand, other))
      moved <- Conv.apTerm(minus, commuted).flatMap(Conv.apThm(_, summand))
      collapsed <- rules.specAll(numbers.sumMinus, List(other, summand))
      result <- Conv.trans(moved, collapsed)
    } yield result
  }

  /** `|- NUM_ADD k (NUM_SUB i k) = i`, from `|- NUM_LE k i`. */
  private def shiftedBy(
    logic: Logic,
    i: Term,
    summand: Term,
    atLeast: Kernel.Thm,
    numbers: Numeric
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      restored <- rules.specAll(numbers.minusThenPlus, List(i, summand)).flatMap(rules.mp(_, atLeast))
      difference <- leftOf(restored).flatMap {
        case App(App(_, first), _) => Right(first)
        case other => Left(NotOfForm("a sum", other))
      }
      commuted <- rules.specAll(numbers.addCommutative, List(difference, summand))
      result <- Conv.sym(commuted).flatMap(Conv.trans(_, restored))
    } yield result
  }

  /** `WORD_CONCAT a b`, as a term. */
  private def concat(theory: Theory, first: Term, second: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(Name, concatType))
      applied <- LogicError.lift(Term.appAll(constant, List(first, second)))
    } yield applied

  /** `NUM_ADD a b`, as a term. */
  private def sum(theory: Theory, first: Term, second: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(Peano.Addition, binaryNumbers))
      applied <- LogicError.lift(Term.appAll(constant, List(first, second)))
    } yield applied

  /** `WORD_LENGTH w`, as a term, for each of the words given. */
  private def lengthsOf(theory: Theory, words: List[Term]): Either[LogicError, List[Term]] =
    for {
      constant <- LogicError.lift(theory.constant(Word.Length, lengthType))
      applied <- words.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, each) =>
        for {
          reached <- acc
          one <- LogicError.lift(Term.app(constant, each))
        } yield reached :+ one
      }
    } yield applied

  private def predicateOf(logic: Logic, term: Term): Either[LogicError, Term] =
    logic.destExistsPredicate(term).toRight(NotOfForm("an existential quantification", term))

  /** `WORD_MAKE k f`, taken apart into the length and the padded function. */
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

  /** The operator of an application read off a theorem's left side. */
  private def headOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1) match {
      case Some(App(operator, _)) => Right(operator)
      case _ => Left(NotOfForm("an equation whose left side is an application", theorem.conclusion))
    }

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
