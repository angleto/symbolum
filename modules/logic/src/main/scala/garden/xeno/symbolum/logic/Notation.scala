package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * How constants are written and read: which symbol stands for which constant, at what precedence,
 * and which way it associates.
 *
 * This is not part of the theory and deliberately not part of the kernel. A theory says which
 * constants exist and at what type; how they are spelled changes nothing about what is provable,
 * and putting a precedence table in the trusted base would mean the trusted base grows every time
 * someone wants to write `+` infix.
 *
 * It exists because of what comes next. A theory of arithmetic is twenty axioms that a person has
 * to read against a source, and `(!x. (!y. ((+ x) y = (+ y) x)))` is not something anyone checks;
 * `!x y. x + y = y + x` is.
 */
final class Notation private (
  val infix: Vector[Infix],
  val prefix: Vector[Prefix],
  val binders: Vector[BinderNotation],
  val numerals: Vector[NumeralNotation]
) {

  /** This notation with an infix operator for `constant`. */
  def withInfix(
    symbol: String,
    constant: String,
    precedence: Int,
    rightAssociative: Boolean = false,
    fixedType: Option[Type] = None
  ): Notation =
    new Notation(
      infix :+ Infix(symbol, constant, precedence, rightAssociative, fixedType),
      prefix,
      binders,
      numerals
    )

  /**
   * This notation with a mirror spelling for `constant`: `a symbol b` reads as `constant b a`.
   *
   * For reading only. [[infixOf]] never returns a flipped operator, so nothing is ever printed
   * this way and the printed form of a term stays the one form that reads back to it. That is the
   * whole discipline: the surface may accept two spellings, the settled form is one.
   */
  def withFlippedInfix(symbol: String, constant: String, precedence: Int): Notation =
    new Notation(
      infix :+ Infix(symbol, constant, precedence, rightAssociative = false, None, flipped = true),
      prefix,
      binders,
      numerals
    )

  /** This notation with a prefix operator for `constant`. */
  def withPrefix(symbol: String, constant: String, precedence: Int): Notation =
    new Notation(infix, prefix :+ Prefix(symbol, constant, precedence), binders, numerals)

  /** This notation with a binder for `constant`, written `<symbol>x. body`. */
  def withBinder(symbol: String, constant: String): Notation =
    new Notation(infix, prefix, binders :+ BinderNotation(symbol, Some(constant)), numerals)

  /**
   * This notation with digit strings read as numerals in binary.
   *
   * The four constants are named rather than fixed because they belong to a theory: the logic has
   * no numbers, and the theory that introduces them decides what they are called and what type
   * they have.
   *
   * More than one encoding may be declared, and since 2026-09-12 the chain declares two: the reals'
   * and `num`'s. They are kept as a sequence rather than a map keyed by type because a `Notation`
   * has no theory to ask what type a constant was declared at; the parser, which does, picks the
   * encoding whose `one` matches the type the numeral's context forced. Nothing here is allowed to
   * pick by position, and [[valueOfNumeral]] does not need to: the four names of one encoding are
   * the names of no other, so at most one of them can read a given term.
   */
  def withNumerals(zero: String, one: String, bit0: String, bit1: String): Notation =
    new Notation(infix, prefix, binders, numerals :+ NumeralNotation(zero, one, bit0, bit1))

  /** The value `term` denotes under whichever declared encoding reads it, if any does. */
  def valueOfNumeral(term: Term): Option[BigInt] =
    numerals.iterator.flatMap(_.valueOf(term)).nextOption()

  /**
   * Every operator written with this symbol, in the order they were declared.
   *
   * Plural because one symbol may stand for more than one constant, which `docs/adr/0018` decides
   * and the parser resolves: `+` is the reals' addition and `num`'s, and which one a text means is
   * settled by unification rather than here. This table still has no way to ask what anything
   * means, which is the property that record keeps: it hands back every candidate, and the caller
   * that holds a theory is the one that decides.
   */
  def infixesFor(symbol: String): Vector[Infix] = infix.filter(_.symbol == symbol)

  /**
   * The first operator written with this symbol.
   *
   * For a caller that wants a symbol's precedence or associativity, which every candidate for one
   * symbol shares: `Parser` refuses a notation where they do not, because two precedences for one
   * symbol is an ambiguous grammar rather than an overload. A caller that wants to know which
   * constant a symbol means cannot use this and wants [[infixesFor]].
   */
  def infixFor(symbol: String): Option[Infix] = infix.find(_.symbol == symbol)
  def prefixFor(symbol: String): Option[Prefix] = prefix.find(_.symbol == symbol)
  def binderFor(symbol: String): Option[BinderNotation] = binders.find(_.symbol == symbol)

  /**
   * The symbol a constant is printed with, if it has one.
   *
   * Flipped spellings are skipped rather than merely ordered after the plain one, because a
   * printer that picked one would produce a term that reads back to its own mirror image.
   */
  def infixOf(constant: String): Option[Infix] =
    infix.find(operator => operator.constant == constant && !operator.flipped)
  def prefixOf(constant: String): Option[Prefix] = prefix.find(_.constant == constant)
  def binderOf(constant: String): Option[BinderNotation] =
    binders.find(_.constant.contains(constant))

  /**
   * Every symbol the lexer must recognise, longest first.
   *
   * Longest first is not a preference: with `=` before `==>`, the text `p ==> q` lexes as `p`,
   * `=`, `=`, `>`, and the error surfaces somewhere else entirely.
   */
  lazy val symbols: List[String] =
    (Notation.Structural ++ infix.map(_.symbol) ++ prefix.map(_.symbol) ++ binders.map(_.symbol))
      .distinct
      .sortBy(-_.length)
      .toList
}

/**
 * How a numeral is spelled: `12` is `BIT0 (BIT0 (BIT1 1))`, which is `1100` read from the right.
 *
 * The encoding is binary rather than a sequence of successors because the size of the term has to
 * grow with the number of digits and not with the value. `1000000` in unary is a term with a
 * million nodes; in binary it is twenty.
 *
 * [[valueOf]] is the inverse of the expansion the parser performs, and a property test asserts
 * that the two are inverse rather than leaving it to inspection.
 */
final case class NumeralNotation(zero: String, one: String, bit0: String, bit1: String) {

  /**
   * The number a term denotes, if it is a numeral in this encoding.
   *
   * Only the canonical spelling counts: a chain of bits ends at `1`, and `0` stands alone. `BIT0
   * 0` denotes zero as well, and is not a numeral here on purpose, because two terms printing as
   * `0` would make printing lose information and the round trip through the parser would stop
   * being an identity. Such a term prints as the application it is, which is honest about being a
   * numeral that has not been reduced to one.
   */
  def valueOf(term: Term): Option[BigInt] = term match {
    case Const(name, _) if name == zero => Some(BigInt(0))
    case other => positiveValueOf(other)
  }

  private def positiveValueOf(term: Term): Option[BigInt] = term match {
    case Const(name, _) if name == one => Some(BigInt(1))
    case App(Const(name, _), inner) if name == bit0 => positiveValueOf(inner).map(_ * 2)
    case App(Const(name, _), inner) if name == bit1 => positiveValueOf(inner).map(_ * 2 + 1)
    case _ => None
  }
}

/**
 * An infix operator: `left symbol right` is `constant left right`, or `constant right left` when
 * the spelling is flipped.
 *
 * Flipping is how a relation gets its mirror spelling without the theory gaining a constant.
 * `a > b` is not a second relation to be axiomatised, it is `<` read from the other end, so the
 * term the parser builds is the same term `b < a` builds, to the node. A theory that added a
 * `>` constant would owe an axiom relating it to `<` and would double every lemma about the order.
 */
final case class Infix(
  symbol: String,
  constant: String,
  precedence: Int,
  rightAssociative: Boolean,
  fixedType: Option[Type],
  flipped: Boolean = false
)

/** A prefix operator: `symbol argument` is `constant argument`. */
final case class Prefix(symbol: String, constant: String, precedence: Int)

/** A binder: `symbol x:ty. body` is `constant (\x:ty. body)`, or a lambda when there is none. */
final case class BinderNotation(symbol: String, constant: Option[String])

object Notation {

  /** Symbols the grammar needs whatever notation is declared. */
  val Structural: Vector[String] = Vector("(", ")", ".", ",", ":", "->")

  /**
   * The precedences of the logical connectives.
   *
   * Spaced out so that a theory can put its own operators between them without renumbering these.
   * Negation sits below equality on purpose: `~x = y` is `~(x = y)`, which is how it is read on
   * paper, and above conjunction so that `~p /\ q` is `(~p) /\ q`.
   */
  val ImplicationPrecedence: Int = 10
  val DisjunctionPrecedence: Int = 20
  val ConjunctionPrecedence: Int = 30
  val NegationPrecedence: Int = 35
  val EqualityPrecedence: Int = 40

  /** Application binds tighter than any declared operator. */
  val ApplicationPrecedence: Int = 1000

  private val booleanEquality: Type =
    Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool))

  /** The notation of the logic alone: connectives, quantifiers and lambda. */
  val standard: Notation =
    new Notation(Vector.empty, Vector.empty, Vector(BinderNotation("\\", None)), Vector.empty)
      .withInfix("==>", Logic.Implication, ImplicationPrecedence, rightAssociative = true)
      .withInfix("\\/", Logic.Disjunction, DisjunctionPrecedence, rightAssociative = true)
      .withInfix("/\\", Logic.Conjunction, ConjunctionPrecedence, rightAssociative = true)
      // `=` first, so that it is the spelling a term prints with; `<=>` is the same constant with
      // its type fixed, which is what makes `p <=> q` unambiguous where `p = q` is not.
      .withInfix("=", Term.EqualityName, EqualityPrecedence)
      .withInfix("<=>", Term.EqualityName, EqualityPrecedence, fixedType = Some(booleanEquality))
      .withPrefix("~", Logic.Negation, NegationPrecedence)
      .withBinder("!", Logic.Universal)
      .withBinder("?", Logic.Existential)
}
