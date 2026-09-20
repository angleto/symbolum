package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The integers, as the classes of pairs of naturals under the difference relation.
 *
 * == Why a fifth type operator at all ==
 *
 * The chain had four — `num`, `real`, `prod` and `word` — and no signed ring, and that absence
 * blocked two open formalisations in two **different** ways, which is the reason it is a type
 * missing rather than a file in the wrong place:
 *
 *  - `Divisibility` is over the reals, where every non-zero element divides everything.
 *    `DIVIDES_NONZERO` is that, derived rather than left to be discovered, so a divisibility
 *    hypothesis over `real` is stated and discharged **vacuously**.
 *  - `NUM_DIVIDES` is over `num` and cannot state the condition at all, because the coefficients a
 *    lattice argument divides are signed.
 *
 * Neither is repaired by moving a development. What repairs both is an ordered ring in which a
 * quantity can be negative and the divisors of a quantity are finitely many.
 *
 * == The construction, and what it is not ==
 *
 * A pair `(a, b)` stands for `a - b`, and two pairs stand for the same integer exactly when
 * `a + d = c + b`, which is `a - b = c - d` written so that no subtraction appears. That relation
 * is [[Integer.SameName]], the type is `Quotient.define` applied to it, and the arithmetic is
 * lifted through `Quotient.liftBinary` and `Quotient.liftUnary`.
 *
 * **It is not `docs/adr/0007`'s step 4 arriving early.** That record wants the integers as a stage
 * on the way to constructing the reals, and under that framing they are estimated as the large
 * piece and never start. What is here is the prerequisite on its own: a signed ring with a
 * divisibility over it, which stands up without anything above it being built and without any of
 * the sixteen becoming a theorem. When the construction does happen this development moves below
 * `Real` rather than being rewritten, because nothing in it reaches for a real.
 *
 * **Canonical representatives were the obvious alternative and `docs/adr/0016` already rejected
 * them**, in the general form: a pair with one component zero needs no quotient builder at all, and
 * the same trick for the rationals needs lowest terms, which needs the greatest common divisor,
 * which would put `Modular` below `Real`. The reason is about the next quotient rather than this
 * one, which is why it is worth repeating here: this file could have been written the cheap way.
 *
 * == The operators keep a prefix spelling, deliberately ==
 *
 * `docs/adr/0018` lets a symbol stand for more than one constant and `+`, `*`, `<` and `<=` already
 * stand for two, the reals' and `num`'s. Adding a third candidate to each is not a line in
 * `Notation`: the elaborator refuses a text nothing determines, so every existing statement
 * carrying one of those symbols would gain a way of being ambiguous, and 135 statements moved the
 * last time a type joined the overloading. That is a change with a measurement of its own in front
 * of it, and it is not this one. So the operations here are written `INT_ADD a b`, the way `num`'s
 * truncated subtraction keeps a prefix form for a different reason.
 *
 * == How the ring laws are proved, which is one route and not eleven ==
 *
 * Every equation between integers below is settled the same way and by one function. Both sides are
 * written at **carrier** variables, `INT_OF_PAIR x` and not `a:int`; the lifted equations and the
 * two projections of a pair are a rewrite rule set that brings each side to a single
 * `INT_OF_PAIR (PAIR … …)`; the two pairs are related by `Semiring`, which decides identities of
 * the commutative semiring on `num` and costs no axiom of the reals; the central fact of the
 * quotient turns that relation into an equation between classes; and the result is put back over
 * `int` by specialising at a representative and rewriting `INT_OF_PAIR (INT_OF_PAIR_repr a)` to
 * `a`.
 *
 * What that buys is that associativity, commutativity, both units, the additive inverse and
 * distributivity are one function applied to a pair of texts each, and that a further law costs a
 * line. What it costs is that a law which is **not** a semiring identity after projection does not
 * go through this route at all, and the two in the file that are not — the respectfulness of
 * multiplication and the injectivity of the embedding — say so where they are written.
 */
final class Integer private (
  val classical: Classical,
  val theory: Theory,
  val notation: Notation,
  /** The quotient this development is, kept so a consumer can project and lift against it. */
  val quotient: Quotient,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = classical.logic
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

object Integer {

  /* ------------------------------------------------------------------ the names */

  /** The type operator, and the two halves of the bijection the kernel returns for it. */
  val TypeName: String = "int"
  val Abstraction: String = "mk_int"
  val Representation: String = "dest_int"

  /**
   * `INT_SAME p q` — the two pairs stand for the same integer.
   *
   * `FST p + SND q = FST q + SND p`, which is `a - b = c - d` with no subtraction in it. Written
   * this way because `num`'s subtraction is truncated, so the reading with a `NUM_SUB` in it is a
   * different relation and is not an equivalence.
   */
  val SameName: String = "INT_SAME"

  /** `INT_OF_PAIR p` — the integer the pair stands for. */
  val Projection: String = "INT_OF_PAIR"

  /** `INT_OF_NUM n` — the natural `n` as an integer. */
  val OfNatural: String = "INT_OF_NUM"

  /** `INT_ADD a b` — the sum. */
  val Addition: String = "INT_ADD"

  /** `INT_NEG a` — the additive inverse, which is the whole reason for a signed ring. */
  val Negation: String = "INT_NEG"

  /** `INT_MUL a b` — the product. */
  val Multiplication: String = "INT_MUL"

  /** `INT_ZERO` — the additive unit. */
  val Zero: String = "INT_ZERO"

  /** `INT_ONE` — the multiplicative unit. */
  val One: String = "INT_ONE"

  /** `|- !p. INT_SAME p p` */
  val SameReflexive: String = "INT_SAME_REFL"

  /** `|- !p q. INT_SAME p q ==> INT_SAME q p` */
  val SameSymmetric: String = "INT_SAME_SYM"

  /** `|- !p q r. INT_SAME p q ==> INT_SAME q r ==> INT_SAME p r` */
  val SameTransitive: String = "INT_SAME_TRANS"

  /**
   * `|- !p q. (INT_OF_PAIR p = INT_OF_PAIR q) = INT_SAME p q`
   *
   * The fact the type is defined for, republished here under a name of this development rather than
   * left in the quotient's own map. A fact reachable from no library is in no document either,
   * which is the argument `Chain`'s own comment makes about the five developments that sat beside
   * it until 2026-09-12.
   */
  val Equal: String = "INT_EQ_PAIRS"

  /** `|- !a. ?p. a = INT_OF_PAIR p` — every integer is some pair's. */
  val Cases: String = "INT_CASES"

  /**
   * `|- !a b d. INT_MUL a (INT_OF_NUM (SUC d)) = INT_MUL b (INT_OF_NUM (SUC d)) ==> a = b`
   *
   * Cancelling a factor that cannot be zero, in the restricted form `docs/adr/0036` asks for and
   * not in the general one. The general law is `~(c = INT_ZERO) ==> a * c = b * c ==> a = b`, and
   * what stands in front of it is the absence of zero divisors, which this development does not
   * hold; the successor of a natural cannot be zero for a reason the pair representation already
   * carries, so this form goes through `INT_MUL_PAIRS`, `INT_EQ_PAIRS`, one semiring rearrangement
   * and `Peano.NUM_MUL_CANCEL_LEFT`, all of which exist.
   *
   * **What wants it is the rationals.** Their relation on `prod(int, num)` reads the denominator of
   * `(a, d)` as `INT_OF_NUM (SUC d)`, and its transitivity is this cancellation: that is the whole
   * of why the carrier can be the pairs themselves rather than a carved subtype, which is the
   * decision `docs/adr/0036` records.
   */
  val CancelsPositive: String = "INT_MUL_CANCEL_NUM"

  /** `|- !p q. INT_ADD (INT_OF_PAIR p) (INT_OF_PAIR q) = INT_OF_PAIR (…)`, the lift. */
  val AddPairs: String = "INT_ADD_PAIRS"

  /** `|- !p. INT_NEG (INT_OF_PAIR p) = INT_OF_PAIR (PAIR (SND p) (FST p))`, the lift. */
  val NegPair: String = "INT_NEG_PAIR"

  /** `|- !p q. INT_MUL (INT_OF_PAIR p) (INT_OF_PAIR q) = INT_OF_PAIR (…)`, the lift. */
  val MulPairs: String = "INT_MUL_PAIRS"

  val AddCommutative: String = "INT_ADD_SYM"
  val AddAssociative: String = "INT_ADD_ASSOC"
  val AddAtZero: String = "INT_ADD_ZERO"

  /** `|- !a. INT_ADD a (INT_NEG a) = INT_ZERO`, which is what `num` has no counterpart of. */
  val AddNegation: String = "INT_ADD_NEG"

  val NegTwice: String = "INT_NEG_NEG"
  val MulCommutative: String = "INT_MUL_SYM"
  val MulAssociative: String = "INT_MUL_ASSOC"
  val MulAtOne: String = "INT_MUL_ONE"
  val MulAtZero: String = "INT_MUL_ZERO"
  val Distributive: String = "INT_MUL_DISTRIBUTE"

  val OfNaturalSum: String = "INT_OF_NUM_ADD"
  val OfNaturalProduct: String = "INT_OF_NUM_MUL"
  val OfNaturalZero: String = "INT_OF_NUM_ZERO"

  /**
   * `|- !m n. (INT_OF_NUM m = INT_OF_NUM n) = (m = n)`
   *
   * The embedding is faithful, and this is the second thing in the development that says the type
   * did not collapse: a one-point `int` satisfies every equation in the file and refutes this one.
   */
  val OfNaturalInjective: String = "INT_OF_NUM_EQ"

  /** `|- !a b. INT_MUL a (INT_NEG b) = INT_NEG (INT_MUL a b)` */
  val MulNegation: String = "INT_MUL_NEG"

  /** `|- !a. INT_MUL INT_ZERO a = INT_ZERO`, which `INT_MUL_ZERO` does not give by itself. */
  val ZeroTimes: String = "INT_ZERO_MUL"

  /**
   * `|- !a b c d e. d * (a * b) + e * (a * c) = a * (d * b + e * c)`
   *
   * The one law here that exists for a consumer rather than for the ring: it is the whole of what
   * [[DividesLinear]] needs, and it is a law rather than five steps inside that derivation because
   * this development has **no decision procedure of its own**. `Divisibility` closes each of its
   * steps with `Ring`, which decides identities over the reals; nothing decides identities over
   * `int`, so every regrouping a derivation wants has to be a named fact somebody proved.
   */
  val Combine: String = "INT_COMBINE"

  /** `INT_DIVIDES a b` — `b` is `a` times an integer. */
  val Divides: String = "INT_DIVIDES"

  val DividesIntro: String = "INT_DIVIDES_INTRO"
  val DividesElim: String = "INT_DIVIDES_ELIM"
  val DividesReflexive: String = "INT_DIVIDES_REFL"
  val DividesTransitive: String = "INT_DIVIDES_TRANS"
  val DividesZero: String = "INT_DIVIDES_ZERO"
  val DividesMultiple: String = "INT_DIVIDES_MUL"
  val DividesNegation: String = "INT_DIVIDES_NEG"

  /**
   * `|- !a b c x y. INT_DIVIDES a b ==> INT_DIVIDES a c ==> INT_DIVIDES a (x * b + y * c)`
   *
   * The one a consumer reaches for, and the reason the card that asked for this file names
   * `Divisibility` as the thing it could not use: this statement is **true and empty** over a
   * field, where every non-zero `a` divides everything, and it is a real condition here.
   */
  val DividesLinear: String = "INT_DIVIDES_LINEAR"

  /** `|- !b. INT_DIVIDES INT_ZERO b ==> b = INT_ZERO` */
  val ZeroDividesOnly: String = "INT_ZERO_DIVIDES"

  /**
   * `|- !m n. INT_DIVIDES (INT_OF_NUM m) (INT_OF_NUM n) = NUM_DIVIDES m n`
   *
   * The embedding is faithful for divisibility, and it is one fact rather than two for the reason
   * [[AtMostOfNatural]] is one: what a caller wants of an embedding is that the question gets the
   * same answer on either side, and an implication answers half of it. It is also what carries
   * `num`'s arithmetic of divisors up here, which is the whole of how [[TwoDoesNotDivide]] is
   * derived and the reason that one is six steps.
   */
  val DividesOfNatural: String = "INT_DIVIDES_OF_NUM"

  /**
   * `|- ~(INT_DIVIDES (INT_OF_NUM 2) (INT_OF_NUM 1))`
   *
   * The witness this development exists for: a non-divisibility at a divisor that is **not** zero,
   * which is what `Divisibility` cannot supply. Over the reals `DIVIDES_NONZERO` makes every
   * non-zero element divide everything, so the only refusal available there is at zero, and
   * [[ZeroDividesOnly]] is that one and holds over a field as well.
   */
  val TwoDoesNotDivide: String = "INT_TWO_NOT_DIVIDES_ONE"

  /**
   * `INT_LE a b` — the order, and the one construct here that the quotient builder does not lift.
   *
   * A relation of **two** quotient arguments is not `liftPredicate`, which takes one, and not
   * `liftBinary`, whose obligation relates the two results and so needs them in the carrier. So it
   * is defined through the chosen representatives directly and [[AtMostPairs]] is the fact that
   * makes that definition usable, proved from a respectfulness lemma of its own.
   */
  val AtMost: String = "INT_LE"

  /** `|- !p q. INT_LE (INT_OF_PAIR p) (INT_OF_PAIR q) = NUM_LE (FST p + SND q) (FST q + SND p)` */
  val AtMostPairs: String = "INT_LE_PAIRS"

  val AtMostReflexive: String = "INT_LE_REFL"
  val AtMostTransitive: String = "INT_LE_TRANS"
  val AtMostAntisymmetric: String = "INT_LE_ANTISYM"

  /** `|- !a b. INT_LE a b \/ INT_LE b a`, which is what makes it an order and not a partial one. */
  val AtMostTotal: String = "INT_LE_TOTAL"

  /** `|- !a b c. INT_LE a b ==> INT_LE (INT_ADD c a) (INT_ADD c b)`: the ring is **ordered**. */
  val AddMonotone: String = "INT_ADD_LE_MONOTONE"

  /** `|- !m n. INT_LE (INT_OF_NUM m) (INT_OF_NUM n) = NUM_LE m n`: the embedding is an order map. */
  val AtMostOfNatural: String = "INT_LE_OF_NUM"

  /* ------------------------------------------------------------------ the types */

  /** `num`, spelled here rather than borrowed from a development that keeps it private. */
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /** `prod(num,num)`, the carrier. */
  val Pairs: Type = TyApp(Product.TypeName, List(numbers, numbers))

  /** `int`, the classes. */
  val Classes: Type = TyApp(TypeName, Nil)

  /** `prod(num,num) -> prod(num,num) -> bool`, the relation's type. */
  val Relation: Type = Type.fun(Pairs, Type.fun(Pairs, Type.Bool))

  /** `num -> num -> num`, which is what the carrier's arithmetic is written in. */
  private val binary: Type = Type.fun(numbers, Type.fun(numbers, numbers))

  /** `prod(num,num) -> num`, which is what a projection of the carrier is. */
  private val component: Type = Type.fun(Pairs, numbers)

  /** The four names the quotient builder introduces, all of them this development's. */
  val Names: Quotient.Names =
    Quotient.Names(
      typeName = TypeName,
      abstraction = Abstraction,
      representation = Representation,
      projection = Projection
    )

  private val SameBody: String =
    "\\p:prod(num,num). \\q:prod(num,num). NUM_ADD (FST p) (SND q) = NUM_ADD (FST q) (SND p)"

  private val AdditionBody: String =
    "\\p:prod(num,num). \\q:prod(num,num). " +
      "PAIR (NUM_ADD (FST p) (FST q)) (NUM_ADD (SND p) (SND q))"

  private val NegationBody: String =
    "\\p:prod(num,num). PAIR (SND p) (FST p)"

  /**
   * `(a - b) * (c - d) = (ac + bd) - (ad + bc)`, written with no subtraction in it.
   *
   * The one operation whose respectfulness is not the premises rearranged, because the conclusion's
   * equation is the premise **multiplied** by the other argument's components rather than added to
   * anything. [[productMoves]] is that step and it is used twice.
   */
  private val MultiplicationBody: String =
    "\\p:prod(num,num). \\q:prod(num,num). " +
      "PAIR (NUM_ADD (NUM_MUL (FST p) (FST q)) (NUM_MUL (SND p) (SND q))) " +
      "(NUM_ADD (NUM_MUL (FST p) (SND q)) (NUM_MUL (SND p) (FST q)))"

  private val ZeroBody: String = "INT_OF_PAIR (PAIR ZERO ZERO)"
  private val OneBody: String = "INT_OF_PAIR (PAIR (SUC ZERO) ZERO)"
  private val OfNaturalBody: String = "\\n:num. INT_OF_PAIR (PAIR n ZERO)"

  private val DividesBody: String = "\\a:int. \\b:int. ?k:int. b = INT_MUL a k"

  /**
   * Everything this development proves, as the text a person checks it by.
   *
   * Read as a term rather than compared as printed text, which is the reading `RotationSpec`
   * argues for: what a reader wants to compare against the informal claim is a statement that
   * parses back to the theorem, and the parse is the stronger comparison of the two.
   */
  val Statements: Vector[(String, String)] = Vector(
    SameReflexive -> "!p:prod(num,num). INT_SAME p p",
    SameSymmetric -> "!p:prod(num,num) q:prod(num,num). INT_SAME p q ==> INT_SAME q p",
    SameTransitive ->
      ("!p:prod(num,num) q:prod(num,num) r:prod(num,num). " +
        "INT_SAME p q ==> INT_SAME q r ==> INT_SAME p r"),
    Equal ->
      "!p:prod(num,num) q:prod(num,num). (INT_OF_PAIR p = INT_OF_PAIR q) = INT_SAME p q",
    Cases -> "!a:int. ?p:prod(num,num). a = INT_OF_PAIR p",
    CancelsPositive ->
      ("!a:int. !b:int. !d:num. " +
        "INT_MUL a (INT_OF_NUM (SUC d)) = INT_MUL b (INT_OF_NUM (SUC d)) ==> a = b"),
    AddPairs ->
      ("!p:prod(num,num) q:prod(num,num). INT_ADD (INT_OF_PAIR p) (INT_OF_PAIR q) = " +
        "INT_OF_PAIR (PAIR (NUM_ADD (FST p) (FST q)) (NUM_ADD (SND p) (SND q)))"),
    NegPair ->
      "!p:prod(num,num). INT_NEG (INT_OF_PAIR p) = INT_OF_PAIR (PAIR (SND p) (FST p))",
    MulPairs ->
      ("!p:prod(num,num) q:prod(num,num). INT_MUL (INT_OF_PAIR p) (INT_OF_PAIR q) = " +
        "INT_OF_PAIR (PAIR (NUM_ADD (NUM_MUL (FST p) (FST q)) (NUM_MUL (SND p) (SND q))) " +
        "(NUM_ADD (NUM_MUL (FST p) (SND q)) (NUM_MUL (SND p) (FST q))))"),
    AddCommutative -> "!a:int b:int. INT_ADD a b = INT_ADD b a",
    AddAssociative ->
      "!a:int b:int c:int. INT_ADD (INT_ADD a b) c = INT_ADD a (INT_ADD b c)",
    AddAtZero -> "!a:int. INT_ADD a INT_ZERO = a",
    AddNegation -> "!a:int. INT_ADD a (INT_NEG a) = INT_ZERO",
    NegTwice -> "!a:int. INT_NEG (INT_NEG a) = a",
    MulCommutative -> "!a:int b:int. INT_MUL a b = INT_MUL b a",
    MulAssociative ->
      "!a:int b:int c:int. INT_MUL (INT_MUL a b) c = INT_MUL a (INT_MUL b c)",
    MulAtOne -> "!a:int. INT_MUL a INT_ONE = a",
    MulAtZero -> "!a:int. INT_MUL a INT_ZERO = INT_ZERO",
    Distributive ->
      ("!a:int b:int c:int. INT_MUL a (INT_ADD b c) = " +
        "INT_ADD (INT_MUL a b) (INT_MUL a c)"),
    OfNaturalSum ->
      ("!m:num n:num. INT_OF_NUM (NUM_ADD m n) = " +
        "INT_ADD (INT_OF_NUM m) (INT_OF_NUM n)"),
    OfNaturalProduct ->
      ("!m:num n:num. INT_OF_NUM (NUM_MUL m n) = " +
        "INT_MUL (INT_OF_NUM m) (INT_OF_NUM n)"),
    OfNaturalZero -> "INT_OF_NUM ZERO = INT_ZERO",
    OfNaturalInjective -> "!m:num n:num. (INT_OF_NUM m = INT_OF_NUM n) = (m = n)",
    MulNegation -> "!a:int b:int. INT_MUL a (INT_NEG b) = INT_NEG (INT_MUL a b)",
    ZeroTimes -> "!a:int. INT_MUL INT_ZERO a = INT_ZERO",
    Combine ->
      ("!a:int b:int c:int d:int e:int. " +
        "INT_ADD (INT_MUL d (INT_MUL a b)) (INT_MUL e (INT_MUL a c)) = " +
        "INT_MUL a (INT_ADD (INT_MUL d b) (INT_MUL e c))"),
    DividesIntro -> "!a:int b:int k:int. b = INT_MUL a k ==> INT_DIVIDES a b",
    DividesElim -> "!a:int b:int. INT_DIVIDES a b ==> (?k:int. b = INT_MUL a k)",
    DividesReflexive -> "!a:int. INT_DIVIDES a a",
    DividesTransitive ->
      "!a:int b:int c:int. INT_DIVIDES a b ==> INT_DIVIDES b c ==> INT_DIVIDES a c",
    DividesZero -> "!a:int. INT_DIVIDES a INT_ZERO",
    DividesMultiple ->
      "!a:int b:int c:int. INT_DIVIDES a b ==> INT_DIVIDES a (INT_MUL b c)",
    DividesNegation -> "!a:int b:int. INT_DIVIDES a b ==> INT_DIVIDES a (INT_NEG b)",
    DividesLinear ->
      ("!a:int b:int c:int x:int y:int. INT_DIVIDES a b ==> INT_DIVIDES a c ==> " +
        "INT_DIVIDES a (INT_ADD (INT_MUL x b) (INT_MUL y c))"),
    ZeroDividesOnly -> "!b:int. INT_DIVIDES INT_ZERO b ==> b = INT_ZERO",
    DividesOfNatural ->
      "!m:num n:num. INT_DIVIDES (INT_OF_NUM m) (INT_OF_NUM n) = NUM_DIVIDES m n",
    TwoDoesNotDivide -> "~(INT_DIVIDES (INT_OF_NUM 2) (INT_OF_NUM 1))",
    AtMostPairs ->
      ("!p:prod(num,num) q:prod(num,num). INT_LE (INT_OF_PAIR p) (INT_OF_PAIR q) = " +
        "NUM_LE (NUM_ADD (FST p) (SND q)) (NUM_ADD (FST q) (SND p))"),
    AtMostReflexive -> "!a:int. INT_LE a a",
    AtMostTransitive -> "!a:int b:int c:int. INT_LE a b ==> INT_LE b c ==> INT_LE a c",
    AtMostAntisymmetric -> "!a:int b:int. INT_LE a b ==> INT_LE b a ==> a = b",
    AtMostTotal -> "!a:int b:int. INT_LE a b \\/ INT_LE b a",
    AddMonotone ->
      "!a:int b:int c:int. INT_LE a b ==> INT_LE (INT_ADD c a) (INT_ADD c b)",
    AtMostOfNatural -> "!m:num n:num. INT_LE (INT_OF_NUM m) (INT_OF_NUM n) = NUM_LE m n"
  )

  /**
   * The standard development, which is the chain's own and not a second one beside it.
   *
   * A lookup rather than a second construction, for the reason `Inductive.standard` gives: a second
   * one would put a second `int` of a different origin into the world, and `docs/adr/0008` is what
   * says two constants of one name and two origins are two constants.
   */
  lazy val standard: Integer = Chain.standard.integers

  /**
   * The development, over whatever the last link of the chain is.
   *
   * `base` is the theory to **extend** and is not the whole of what this needs: `peano` supplies
   * the arithmetic of `num` the carrier's equations are settled by and `product` the pair. The two
   * orders are different things, which is the distinction `Rotation.construct`'s comment draws.
   *
   * `modular` and `successor` are the two the embedding's divisibility needs and nothing else here
   * does. [[DividesOfNatural]] is an equation between a proposition of this development and one of
   * `Modular`'s, so that development's own facts are what the right-hand side is reasoned with;
   * and [[TwoDoesNotDivide]] is written at numerals, which reach `Modular.DividesOne`'s `SUC ZERO`
   * only through `Successor`. Neither costs an extension: both are developments already below this
   * one in the chain, so what is added is a lookup and not a prerequisite.
   */
  def construct(
    classical: Classical,
    peano: Peano,
    product: Product,
    modular: Modular,
    successor: Successor,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Integer] =
    for {
      semiring <- Semiring.construct(peano)

      sameBody <- Parser.term(base, notation, SameBody)
      sameDefined <- LogicError.lift(Kernel.defineConstant(base, SameName, sameBody))
      (withSame, sameDefinition) = sameDefined

      carrier <- Carrier.over(classical, semiring, product, withSame, notation, sameDefinition)

      reflexive <- sameReflexive(carrier)
      symmetric <- sameSymmetric(carrier)
      transitive <- sameTransitive(carrier, peano)

      quotient <- Quotient.define(
        classical,
        withSame,
        notation,
        Names,
        Quotient.Equivalence(carrier.relation, reflexive, symmetric, transitive)
      )

      additionRespects <- addRespects(carrier)
      withAddition <- quotient.liftBinary(Addition, carrier.pairAdd, additionRespects)
      (afterAddition, addPairs) = withAddition

      negationRespects <- negRespects(carrier)
      withNegation <- afterAddition.liftUnary(Negation, carrier.pairNeg, negationRespects)
      (afterNegation, negPair) = withNegation

      multiplicationRespects <- mulRespects(carrier, transitive)
      withMultiplication <- afterNegation.liftBinary(
        Multiplication,
        carrier.pairMul,
        multiplicationRespects
      )
      (complete, mulPairs) = withMultiplication

      zeroBody <- Parser.term(complete.theory, notation, ZeroBody)
      zeroDefined <- LogicError.lift(Kernel.defineConstant(complete.theory, Zero, zeroBody))
      (withZero, zeroDefinition) = zeroDefined

      oneBody <- Parser.term(withZero, notation, OneBody)
      oneDefined <- LogicError.lift(Kernel.defineConstant(withZero, One, oneBody))
      (withOne, oneDefinition) = oneDefined

      ofNaturalBody <- Parser.term(withOne, notation, OfNaturalBody)
      ofNaturalDefined <- LogicError.lift(Kernel.defineConstant(withOne, OfNatural, ofNaturalBody))
      (theory, ofNaturalDefinition) = ofNaturalDefined

      logic <- classical.logic.over(theory)
      equal <- complete.fact(Quotient.ProjectionEqual)
      cases <- complete.fact(Quotient.ProjectionOnto)
      representative <- complete.fact(Quotient.ProjectionOfRepresentative)

      laws <- Laws.over(
        carrier,
        complete,
        theory,
        notation,
        logic,
        equal,
        representative,
        Vector(addPairs, negPair, mulPairs),
        Vector(zeroDefinition, oneDefinition),
        ofNaturalDefinition
      )

      proved <- laws.prove

      dividesBody <- Parser.term(theory, notation, DividesBody)
      dividesDefined <- LogicError.lift(Kernel.defineConstant(theory, Divides, dividesBody))
      (whole, dividesDefinition) = dividesDefined
      widest <- classical.logic.over(whole)
      dividing <- Dividing.over(widest, whole, dividesDefinition, proved)
      divisibility <- dividing.prove

      ordered <- Order.over(
        classical,
        carrier,
        complete,
        peano,
        whole,
        equal,
        laws.representative,
        addPairs,
        laws.tidying
      )
      (entire, order, atMostDefinition) = ordered
      comparison <- order.prove

      // Last, and over `entire` rather than over `whole`: nothing here needs the order, and taking
      // the constants from the theory the development ends at is what keeps every term in the file
      // built from one origin, which is the argument `Carrier` makes about `docs/adr/0008`.
      embedded <- Embedded.over(
        classical, carrier, modular, successor, entire, notation, proved, divisibility,
        equal, cases, mulPairs, ofNaturalDefinition
      )
      faithful <- embedded.prove

      // Last of all, and over `entire` for the reason the embedding gives: what this needs is the
      // multiplication of the ring and the embedding of a natural, both of which are behind it.
      whole1 <- classical.logic.over(entire)
      cancelling <- cancelsPositive(
        whole1, carrier, complete, peano, entire, notation, equal, laws.representative,
        mulPairs, ofNaturalDefinition)
    } yield new Integer(
      classical,
      entire,
      notation,
      complete,
      Map(
        SameName -> sameDefinition,
        Zero -> zeroDefinition,
        One -> oneDefinition,
        OfNatural -> ofNaturalDefinition,
        Divides -> dividesDefinition,
        AtMost -> atMostDefinition
      ) ++ complete.definitions,
      Map(
        SameReflexive -> reflexive,
        SameSymmetric -> symmetric,
        SameTransitive -> transitive,
        Equal -> equal,
        Cases -> cases,
        AddPairs -> addPairs,
        NegPair -> negPair,
        MulPairs -> mulPairs,
        CancelsPositive -> cancelling
      ) ++ proved ++ divisibility ++ comparison ++ faithful
    )

  /* ------------------------------------------------------------------ the carrier */

  private val x: FVar = Term.variable("x", Pairs)
  private val y: FVar = Term.variable("y", Pairs)
  private val u: FVar = Term.variable("u", Pairs)
  private val v: FVar = Term.variable("v", Pairs)
  private val z: FVar = Term.variable("z", Pairs)
  private val w: FVar = Term.variable("w", Pairs)
  private val t: FVar = Term.variable("t", Pairs)
  private val p: FVar = Term.variable("p", Pairs)
  private val q: FVar = Term.variable("q", Pairs)
  private val r: FVar = Term.variable("r", Pairs)

  /** The left-hand side of an equation a step produced. */
  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term
      .destEq(theorem.conclusion)
      .map(_._1)
      .toRight(NotOfForm("an equation", theorem.conclusion))

  /** The right-hand side of an equation a step produced. */
  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term
      .destEq(theorem.conclusion)
      .map(_._2)
      .toRight(NotOfForm("an equation", theorem.conclusion))

  private def sidesOf(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
    for {
      body <- rightOf(theorem)
      sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
    } yield sides

  /**
   * Everything the derivations below share, held together rather than fetched in each of them.
   *
   * Every constant is taken from the one theory the relation was defined in. A lemma that took the
   * addition from a different theory would build a term the kernel refuses for its origin, which is
   * `docs/adr/0008`; the alternative to holding them is a dozen copies of the same lookup.
   */
  private final class Carrier private (
    val logic: Logic,
    val semiring: Semiring,
    val definition: Kernel.Thm,
    val relation: Term,
    val addition: Term,
    val multiplication: Term,
    val first: Term,
    val second: Term,
    val pairing: Term,
    /** `ZERO`, which the embedding's pairs are built with. */
    val zero: Term,
    /** `FST (PAIR a b) = a` and `SND (PAIR a b) = b`, which every unfolding below needs. */
    val projections: Vector[Rewrite.Rule],
    val pairAdd: Term,
    val pairNeg: Term,
    val pairMul: Term
  ) {

    val rules: Rules = logic.rules

    /** `INT_SAME s t`, as a term. */
    def related(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(relation, List(left, right)))

    /**
     * `|- INT_SAME s t = (… = …)`, with `FST (PAIR a b)` already reduced away.
     *
     * The reduction is here and not at the call sites because every unfolding at a **built** pair
     * needs it and no unfolding at a variable is changed by it: the rules cannot fire on `FST p`.
     */
    def unfoldedAt(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      for {
        unfolded <- Conv.unfold(definition, List(left, right))
        reduced <- Rewrite.inTheorem(projections, unfolded)
      } yield reduced

    /** `s + t`, as a term. */
    def sum(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(addition, List(left, right)))

    /** `s * t`, as a term. */
    def product(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(multiplication, List(left, right)))

    /** `FST t` and `SND t`, as terms. */
    def firstOf(pair: Term): Either[LogicError, Term] = LogicError.lift(Term.app(first, pair))
    def secondOf(pair: Term): Either[LogicError, Term] = LogicError.lift(Term.app(second, pair))

    /** `PAIR s t`, as a term, built from the constant this development's relation was defined over. */
    def pairOf(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(pairing, List(left, right)))

    /**
     * An operation applied and beta-contracted, which is what the quotient builder does to it.
     *
     * The same call the builder makes, deliberately: the obligation it checks is built from its own
     * application of the operation, so a caller that applied it any other way would hand over a
     * theorem about a term that is equal to the one wanted and is not it.
     */
    def applied(operation: Term, arguments: List[Term]): Either[LogicError, Term] =
      for {
        built <- LogicError.lift(Term.appAll(operation, arguments))
        equation <- Conv.betaNormalise(built)
        result <- rightOf(equation)
      } yield result

    /**
     * `|- INT_SAME s t` from an equation the caller has already derived.
     *
     * The equation has to be the very one the unfolding produces; anything else is refused by
     * `Kernel.eqMp` rather than absorbed.
     */
    def fold(unfolded: Kernel.Thm, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        back <- Conv.sym(unfolded)
        folded <- LogicError.lift(Kernel.eqMp(back, equation))
      } yield folded

    /**
     * The premises' equation carried to the conclusion's by the semiring, both sides at once.
     *
     * `combined` relates two sums the premises give; `target` is the unfolded conclusion. What this
     * asserts is that each side of the one is the corresponding side of the other **as a semiring
     * identity**, which is where a wrong construction fails: `Semiring.prove` refuses rather than
     * searching, so a conclusion that does not follow comes back as a refusal naming the two normal
     * forms.
     */
    def bridge(target: Kernel.Thm, combined: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        wanted <- sidesOf(target)
        chained <- rearranged(wanted._1, wanted._2, combined)
        folded <- fold(target, chained)
      } yield folded

    /**
     * `|- left = right`, where `combined` is an equation the semiring rearranges into it on both
     * sides.
     *
     * The half of [[bridge]] that does not fold, published because the order's respectfulness needs
     * the equation and not the relation: its conclusion is an order, so there is nothing to fold
     * back into.
     */
    def rearranged(
      left: Term,
      right: Term,
      combined: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        combinedLeft <- leftOf(combined)
        combinedRight <- rightOf(combined)
        toCombined <- semiring.prove(left, combinedLeft)
        fromCombined <- semiring.prove(combinedRight, right)
        halfway <- Conv.trans(toCombined, combined)
        chained <- Conv.trans(halfway, fromCombined)
      } yield chained

    /** `|- INT_SAME s t` where the equation under it is an identity of the semiring outright. */
    def relate(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      for {
        unfolded <- unfoldedAt(left, right)
        sides <- sidesOf(unfolded)
        identity <- semiring.prove(sides._1, sides._2)
        folded <- fold(unfolded, identity)
      } yield folded

    /** `x + y` swapped to `y + x`, as a term, for a sum this built. */
    def commuted(term: Term): Either[LogicError, Term] =
      term match {
        case App(App(_, left), right) => sum(right, left)
        case _ => Left(NotOfForm("a sum of two terms", term))
      }
  }

  private object Carrier {

    def over(
      classical: Classical,
      semiring: Semiring,
      product: Product,
      theory: Theory,
      notation: Notation,
      definition: Kernel.Thm
    ): Either[LogicError, Carrier] =
      for {
        logic <- classical.logic.over(theory)
        relation <- LogicError.lift(theory.constant(SameName, Relation))
        addition <- LogicError.lift(theory.constant(Peano.Addition, binary))
        multiplication <- LogicError.lift(theory.constant(Peano.Multiplication, binary))
        first <- LogicError.lift(theory.constant(Product.First, component))
        second <- LogicError.lift(theory.constant(Product.Second, component))
        pairing <- LogicError.lift(
          theory.constant(Product.Pairing, Type.fun(numbers, Type.fun(numbers, Pairs)))
        )
        zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
        firstOfPair <- product.fact(Product.FirstOfPair)
        secondOfPair <- product.fact(Product.SecondOfPair)
        projections <- Rewrite.Rule.all(logic, Vector(firstOfPair, secondOfPair))
        pairAdd <- Parser.term(theory, notation, AdditionBody)
        pairNeg <- Parser.term(theory, notation, NegationBody)
        pairMul <- Parser.term(theory, notation, MultiplicationBody)
      } yield new Carrier(
        logic,
        semiring,
        definition,
        relation,
        addition,
        multiplication,
        first,
        second,
        pairing,
        zero,
        projections,
        pairAdd,
        pairNeg,
        pairMul
      )
  }

  /* ------------------------------------------------------------------ the equivalence */

  /**
   * `|- !p. INT_SAME p p`.
   *
   * The unfolded relation at one pair is an equation between a term and itself, so what proves it
   * is reflexivity of equality and nothing about `num` at all.
   */
  private def sameReflexive(carrier: Carrier): Either[LogicError, Kernel.Thm] =
    for {
      unfolded <- carrier.unfoldedAt(p, p)
      sides <- sidesOf(unfolded)
      reflexivity = Conv.refl(sides._1)
      folded <- carrier.fold(unfolded, reflexivity)
      result <- carrier.rules.gen(p, folded)
    } yield result

  /**
   * `|- !p q. INT_SAME p q ==> INT_SAME q p`.
   *
   * Symmetry of the relation is symmetry of the equation under it: `FST p + SND q = FST q + SND p`
   * reversed **is** the unfolding at the swapped pair, with nothing in between.
   */
  private def sameSymmetric(carrier: Carrier): Either[LogicError, Kernel.Thm] =
    for {
      forwards <- carrier.unfoldedAt(p, q)
      backwards <- carrier.unfoldedAt(q, p)
      premise <- leftOf(forwards)
      assumed <- LogicError.lift(Kernel.assume(premise))
      equation <- LogicError.lift(Kernel.eqMp(forwards, assumed))
      flipped <- Conv.sym(equation)
      folded <- carrier.fold(backwards, flipped)
      discharged <- carrier.rules.disch(premise, folded)
      result <- carrier.rules.genAll(discharged, List(p, q))
    } yield result

  /**
   * `|- !p q r. INT_SAME p q ==> INT_SAME q r ==> INT_SAME p r`.
   *
   * The one step of the three that is arithmetic. With `p = (a,b)`, `q = (c,d)` and `r = (e,f)` the
   * two premises are `a + d = c + b` and `c + f = e + d` and the conclusion is `a + f = e + b`.
   * Adding the premises gives `(a + d) + (c + f) = (c + b) + (e + d)`, both sides of which the
   * semiring rearranges to put `c + d` in front, and then `NUM_ADD_CANCEL_LEFT` takes it off.
   *
   * **Cancellation is where the naturals are actually spent**, and it is the step with no
   * counterpart in the relation itself: reflexivity and symmetry are about equality, and this one
   * is about `num` being cancellative. A carrier that was not would not give an equivalence here,
   * and this derivation is where that would show.
   */
  private def sameTransitive(
    carrier: Carrier,
    peano: Peano
  ): Either[LogicError, Kernel.Thm] =
    for {
      first <- carrier.unfoldedAt(p, q)
      second <- carrier.unfoldedAt(q, r)
      target <- carrier.unfoldedAt(p, r)

      firstPremise <- leftOf(first)
      secondPremise <- leftOf(second)
      firstAssumed <- LogicError.lift(Kernel.assume(firstPremise))
      secondAssumed <- LogicError.lift(Kernel.assume(secondPremise))
      firstEquation <- LogicError.lift(Kernel.eqMp(first, firstAssumed))
      secondEquation <- LogicError.lift(Kernel.eqMp(second, secondAssumed))

      combined <- addEquations(carrier, firstEquation, secondEquation)

      wanted <- sidesOf(target)
      (conclusionLeft, conclusionRight) = wanted

      // `c + d`, read off the premises rather than spelled again. Read off because the alternative
      // is writing `NUM_ADD (FST q) (SND q)` here and hoping it is the term the unfolding built.
      firstSides <- sidesOf(first)
      secondSides <- sidesOf(second)
      d <- secondArgument(firstSides._1)
      c <- firstArgument(secondSides._1)
      common <- carrier.sum(c, d)

      leftShape <- carrier.sum(common, conclusionLeft)
      rightShape <- carrier.sum(common, conclusionRight)
      combinedLeft <- leftOf(combined)
      combinedRight <- rightOf(combined)
      toShape <- carrier.semiring.prove(leftShape, combinedLeft)
      fromShape <- carrier.semiring.prove(combinedRight, rightShape)
      halfway <- Conv.trans(toShape, combined)
      shaped <- Conv.trans(halfway, fromShape)

      cancellation <- peano.fact(Peano.AddCancelsLeft)
      instance <- carrier.rules.specAll(
        cancellation,
        List(conclusionLeft, conclusionRight, common)
      )
      cancelled <- carrier.rules.mp(instance, shaped)

      folded <- carrier.fold(target, cancelled)
      dischargedSecond <- carrier.rules.disch(secondPremise, folded)
      dischargedFirst <- carrier.rules.disch(firstPremise, dischargedSecond)
      result <- carrier.rules.genAll(dischargedFirst, List(p, q, r))
    } yield result

  /**
   * [[CancelsPositive]], at the pairs and then over the classes.
   *
   * The multiplier is `INT_OF_NUM (SUC d)`, which is `INT_OF_PAIR (PAIR (SUC d) ZERO)` once its
   * definition is unfolded, so both sides of the hypothesis go through `INT_MUL_PAIRS` and the
   * equation between two classes becomes `INT_SAME` between two built pairs. Unfolded, that is one
   * equation on `num`, and the semiring is what puts it in the shape the cancellation reads:
   * `SUC d * (FST p + SND q) = SUC d * (FST q + SND p)`, where the two sides are what the raw
   * equation rearranges to. `Peano.NUM_MUL_CANCEL_LEFT` takes the factor off, and what is left is
   * `INT_SAME p q` folded back and read through `INT_EQ_PAIRS`.
   *
   * **The rearrangement is where a wrong construction would fail rather than pass**, which is the
   * argument `Carrier.rearranged` makes about itself: `Semiring.prove` refuses instead of
   * searching, so a multiplier whose pair were built differently comes back as two normal forms
   * that do not meet rather than as a theorem about something else.
   */
  private def cancelsPositive(
    logic: Logic,
    carrier: Carrier,
    quotient: Quotient,
    peano: Peano,
    theory: Theory,
    notation: Notation,
    equal: Kernel.Thm,
    representative: Rewrite.Rule,
    mulPairs: Kernel.Thm,
    ofNatural: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val d = Term.variable("d", numbers)
    val leftClass = Term.variable("a", Classes)
    val rightClass = Term.variable("b", Classes)

    for {
      successor <- Parser.term(theory, notation, "SUC (d:num)", numbers)
      multiplier <- Parser.term(theory, notation, "INT_OF_NUM (SUC (d:num))", Classes)
      projection <- LogicError.lift(
        quotient.theory.constant(quotient.names.projection, Type.fun(Pairs, Classes))
      )
      times <- LogicError.lift(
        theory.constant(Multiplication, Type.fun(Classes, Type.fun(Classes, Classes)))
      )

      // The multiplier as a pair, which is the one step that needs the embedding's definition.
      asPair <- Conv.unfold(ofNatural, List(successor))
      pairOfMultiplier <- rightOf(asPair).flatMap {
        case App(_, pair) => Right(pair)
        case other => Left(NotOfForm("a projected pair", other))
      }

      // Both sides of the hypothesis, as classes of built pairs.
      leftProduct <- rules
        .specAll(mulPairs, List(p, pairOfMultiplier))
        .flatMap(Rewrite.inTheorem(carrier.projections, _))
      rightProduct <- rules
        .specAll(mulPairs, List(q, pairOfMultiplier))
        .flatMap(Rewrite.inTheorem(carrier.projections, _))
      leftPair <- rightOf(leftProduct).flatMap {
        case App(_, pair) => Right(pair)
        case other => Left(NotOfForm("a projected pair", other))
      }
      rightPair <- rightOf(rightProduct).flatMap {
        case App(_, pair) => Right(pair)
        case other => Left(NotOfForm("a projected pair", other))
      }

      projectedLeft <- LogicError.lift(Term.app(projection, p))
      projectedRight <- LogicError.lift(Term.app(projection, q))
      premiseLeft <- LogicError.lift(Term.appAll(times, List(projectedLeft, multiplier)))
      premiseRight <- LogicError.lift(Term.appAll(times, List(projectedRight, multiplier)))
      premise <- LogicError.lift(Term.eq(premiseLeft, premiseRight))
      assumed <- LogicError.lift(Kernel.assume(premise))

      // `INT_MUL (INT_OF_PAIR p) (INT_OF_NUM (SUC d))` rewritten to the class of a built pair, on
      // each side of the assumption.
      folding <- Rewrite.Rule.all(logic, Vector(asPair, leftProduct, rightProduct))
      betweenPairs <- Rewrite.inTheorem(folding, assumed)

      related <- rules
        .specAll(equal, List(leftPair, rightPair))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, betweenPairs)))
      unfolded <- carrier.unfoldedAt(leftPair, rightPair)
      raw <- LogicError.lift(Kernel.eqMp(unfolded, related))

      // The shape the cancellation reads, which the semiring is what produces.
      firstOfP <- carrier.firstOf(p)
      secondOfP <- carrier.secondOf(p)
      firstOfQ <- carrier.firstOf(q)
      secondOfQ <- carrier.secondOf(q)
      leftSum <- carrier.sum(firstOfP, secondOfQ)
      rightSum <- carrier.sum(firstOfQ, secondOfP)
      leftScaled <- carrier.product(successor, leftSum)
      rightScaled <- carrier.product(successor, rightSum)
      scaled <- carrier.rearranged(leftScaled, rightScaled, raw)

      positive <- peano.fact(Peano.SuccessorPositive).flatMap(rules.spec(d, _))
      cancelled <- peano
        .fact(Peano.MulCancelsLeft)
        .flatMap(rules.specAll(_, List(successor, leftSum, rightSum)))
        .flatMap(rules.mp(_, positive))
        .flatMap(rules.mp(_, scaled))

      sameUnfolded <- carrier.unfoldedAt(p, q)
      same <- carrier.fold(sameUnfolded, cancelled)
      central <- rules.specAll(equal, List(p, q))
      back <- Conv.sym(central)
      classesEqual <- LogicError.lift(Kernel.eqMp(back, same))

      discharged <- rules.disch(premise, classesEqual)

      // `d` is generalised **after** the classes and not before, which is where the first
      // assembly of this went wrong: `overRepresentatives` specialises the two leading binders at
      // the representatives, and a theorem already carrying `!d` in front of them hands it three
      // quantifiers and two arguments. So the index stays free through that step and the order the
      // statement publishes, `!a b d`, is restored by putting it back inside afterwards.
      overClasses <- overRepresentatives(
        logic, quotient, representative, discharged, List(p, q), List(leftClass, rightClass))
      atClasses <- rules.specAll(overClasses, List(leftClass, rightClass))
      inside <- rules.gen(d, atClasses)
      result <- rules.genAll(inside, List(leftClass, rightClass))
    } yield result
  }

  /**
   * A fact proved at carrier variables, put back over `int`.
   *
   * Specialising at `INT_OF_PAIR_repr a` and rewriting `INT_OF_PAIR (INT_OF_PAIR_repr a)` to `a` is
   * the whole of it, and it needs no existential: `PROJ_REPR` is an equation with nothing assumed,
   * where going through `PROJ_ONTO` would open a witness per variable and close it again.
   *
   * It takes a **theorem** and not two texts, which is the one thing worth saying about the shape:
   * the ring's laws are equations and the order's are implications and a disjunction, and none of
   * that reaches this step. What it needs is that every occurrence of each carrier variable sits
   * under the projection, which is the caller's to arrange and is not checked here — a variable
   * left outside one comes back generalised over a class and applied to a pair, and the kernel
   * refuses it rather than this.
   */
  private def overRepresentatives(
    logic: Logic,
    quotient: Quotient,
    representative: Rewrite.Rule,
    proved: Kernel.Thm,
    carrierVariables: List[FVar],
    classVariables: List[FVar]
  ): Either[LogicError, Kernel.Thm] =
    for {
      general <- logic.rules.genAll(proved, carrierVariables)
      chooser <- LogicError.lift(
        quotient.theory.constant(quotient.names.representative, Type.fun(Classes, Pairs))
      )
      chosen <- classVariables.foldLeft(Right(List.empty[Term]): Either[LogicError, List[Term]]) {
        (accumulated, variable) =>
          for {
            so <- accumulated
            applied <- LogicError.lift(Term.app(chooser, variable))
          } yield so :+ applied
      }
      instance <- logic.rules.specAll(general, chosen)
      rewritten <- Rewrite.inTheorem(Vector(representative), instance)
      result <- logic.rules.genAll(rewritten, classVariables)
    } yield result

  /** The first argument of a two-argument application. */
  private def firstArgument(term: Term): Either[LogicError, Term] =
    term match {
      case App(App(_, left), _) => Right(left)
      case _ => Left(NotOfForm("an application of two arguments", term))
    }

  /** The second argument of an application. */
  private def secondArgument(term: Term): Either[LogicError, Term] =
    term match {
      case App(_, right) => Right(right)
      case _ => Left(NotOfForm("an application", term))
    }

  /**
   * From `|- s = t` and `|- w = z`, the theorem `|- s + w = t + z`.
   *
   * Two congruences and a transitivity, which is what the kernel's rules give: there is no rule
   * taking two equations to one, because the equation between the two applications is built one
   * argument at a time.
   */
  private def addEquations(
    carrier: Carrier,
    left: Kernel.Thm,
    right: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- Conv.apTerm(carrier.addition, left)
      rightArgument <- leftOf(right)
      firstStep <- Conv.apThm(partial, rightArgument)
      head <- rightOf(left)
      applied <- LogicError.lift(Term.app(carrier.addition, head))
      secondStep <- Conv.apTerm(applied, right)
      result <- Conv.trans(firstStep, secondStep)
    } yield result

  /* ------------------------------------------------------------------ the three obligations */

  /**
   * `|- !x y u v. INT_SAME x u ==> INT_SAME y v ==> INT_SAME (x + y) (u + v)`, at pairs.
   *
   * The premises added side by side **are** the conclusion, rearranged: `(x1 + u2) + (y1 + v2) =
   * (u1 + x2) + (v1 + y2)` and `(x1 + y1) + (u2 + v2) = (u1 + v1) + (x2 + y2)` have the same four
   * summands on each side. So nothing is multiplied and nothing is cancelled, which is why this one
   * is four lines where the product's is a page.
   */
  private def addRespects(carrier: Carrier): Either[LogicError, Kernel.Thm] =
    for {
      left <- carrier.applied(carrier.pairAdd, List(x, y))
      right <- carrier.applied(carrier.pairAdd, List(u, v))

      first <- carrier.unfoldedAt(x, u)
      second <- carrier.unfoldedAt(y, v)
      target <- carrier.unfoldedAt(left, right)

      firstPremise <- leftOf(first)
      secondPremise <- leftOf(second)
      firstEquation <- LogicError
        .lift(Kernel.assume(firstPremise))
        .flatMap(assumed => LogicError.lift(Kernel.eqMp(first, assumed)))
      secondEquation <- LogicError
        .lift(Kernel.assume(secondPremise))
        .flatMap(assumed => LogicError.lift(Kernel.eqMp(second, assumed)))

      combined <- addEquations(carrier, firstEquation, secondEquation)
      folded <- carrier.bridge(target, combined)

      dischargedSecond <- carrier.rules.disch(secondPremise, folded)
      dischargedFirst <- carrier.rules.disch(firstPremise, dischargedSecond)
      result <- carrier.rules.genAll(dischargedFirst, List(x, y, u, v))
    } yield result

  /**
   * `|- !x y. INT_SAME x y ==> INT_SAME (neg x) (neg y)`, at pairs.
   *
   * Negation swaps the components, so the conclusion's equation is the premise **reversed** and
   * then commuted on each side: the premise is `FST x + SND y = FST y + SND x` and what is wanted
   * is `SND x + FST y = SND y + FST x`, whose left side is the premise's right one. So the equation
   * handed over is `Conv.sym` of the premise and not the premise, and the semiring does the rest.
   * Handing over the premise itself type-checks, builds a term, and asks `Semiring` to prove that
   * two different sums of two different atoms are equal, which it refuses.
   */
  private def negRespects(carrier: Carrier): Either[LogicError, Kernel.Thm] =
    for {
      left <- carrier.applied(carrier.pairNeg, List(x))
      right <- carrier.applied(carrier.pairNeg, List(y))

      premiseUnfolded <- carrier.unfoldedAt(x, y)
      target <- carrier.unfoldedAt(left, right)

      premise <- leftOf(premiseUnfolded)
      equation <- LogicError
        .lift(Kernel.assume(premise))
        .flatMap(assumed => LogicError.lift(Kernel.eqMp(premiseUnfolded, assumed)))

      reversed <- Conv.sym(equation)
      folded <- carrier.bridge(target, reversed)
      discharged <- carrier.rules.disch(premise, folded)
      result <- carrier.rules.genAll(discharged, List(x, y))
    } yield result

  /**
   * `|- !x y u v. INT_SAME x u ==> INT_SAME y v ==> INT_SAME (x * y) (u * v)`, at pairs.
   *
   * **The one obligation that is not the premises rearranged**, and the reason it is not is worth
   * a line: the conclusion's equation is the premise multiplied by the other argument's components,
   * and no amount of commuting and associating produces a product from a sum. So it goes one
   * argument at a time — `x * y` to `u * y` using the first premise, then `u * y` to `u * v` using
   * the second — and the two are joined by the transitivity of the relation, which this file has
   * already proved. That is the reason [[sameTransitive]] is a published fact rather than something
   * the quotient builder consumed and discarded.
   */
  private def mulRespects(
    carrier: Carrier,
    transitive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      xy <- carrier.applied(carrier.pairMul, List(x, y))
      uy <- carrier.applied(carrier.pairMul, List(u, y))
      uv <- carrier.applied(carrier.pairMul, List(u, v))

      first <- carrier.unfoldedAt(x, u)
      second <- carrier.unfoldedAt(y, v)
      firstPremise <- leftOf(first)
      secondPremise <- leftOf(second)
      firstEquation <- LogicError
        .lift(Kernel.assume(firstPremise))
        .flatMap(assumed => LogicError.lift(Kernel.eqMp(first, assumed)))
      secondEquation <- LogicError
        .lift(Kernel.assume(secondPremise))
        .flatMap(assumed => LogicError.lift(Kernel.eqMp(second, assumed)))

      // The argument that does not move, by its two components: `y` in the first step and `u` in
      // the second.
      firstFixed <- carrier.firstOf(y)
      secondFixed <- carrier.secondOf(y)
      thirdFixed <- carrier.firstOf(u)
      fourthFixed <- carrier.secondOf(u)

      leftTarget <- carrier.unfoldedAt(xy, uy)
      rightTarget <- carrier.unfoldedAt(uy, uv)

      leftStep <- productMoves(carrier, firstEquation, (firstFixed, secondFixed), leftTarget)
      rightStep <- productMoves(carrier, secondEquation, (thirdFixed, fourthFixed), rightTarget)

      instance <- carrier.rules.specAll(transitive, List(xy, uy, uv))
      once <- carrier.rules.mp(instance, leftStep)
      joined <- carrier.rules.mp(once, rightStep)

      dischargedSecond <- carrier.rules.disch(secondPremise, joined)
      dischargedFirst <- carrier.rules.disch(firstPremise, dischargedSecond)
      result <- carrier.rules.genAll(dischargedFirst, List(x, y, u, v))
    } yield result

  /**
   * One argument of a product moved, the other held fixed.
   *
   * `premise` is `|- P = Q` with `P` and `Q` both sums; `multipliers` are the two components of the
   * argument that does not move. What the conclusion needs is `m1 * P + m2 * Q' = m1 * Q + m2 * P'`
   * where the primes are the sums with their summands swapped, and that is the premise multiplied
   * twice and added. The swap is derived from the premise by the semiring rather than assumed,
   * which is why there is no second hypothesis here.
   */
  private def productMoves(
    carrier: Carrier,
    premise: Kernel.Thm,
    multipliers: (Term, Term),
    target: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      left <- leftOf(premise)
      right <- rightOf(premise)
      swappedLeft <- carrier.commuted(left)
      swappedRight <- carrier.commuted(right)

      toSwapped <- carrier.semiring.prove(swappedRight, right)
      back <- Conv.sym(premise)
      fromSwapped <- carrier.semiring.prove(left, swappedLeft)
      halfway <- Conv.trans(toSwapped, back)
      swapped <- Conv.trans(halfway, fromSwapped)

      firstMultiplier <- LogicError.lift(Term.app(carrier.multiplication, multipliers._1))
      secondMultiplier <- LogicError.lift(Term.app(carrier.multiplication, multipliers._2))
      firstScaled <- Conv.apTerm(firstMultiplier, premise)
      secondScaled <- Conv.apTerm(secondMultiplier, swapped)

      combined <- addEquations(carrier, firstScaled, secondScaled)
      result <- carrier.bridge(target, combined)
    } yield result

  /* ------------------------------------------------------------------ the ring laws */

  /**
   * The rewriting that brings an equation between integers down to one between pairs, and back.
   *
   * Held as a value because every law below is the same four steps over a different pair of texts,
   * and because the rule set has to be assembled once: it is the three lifted equations, the two
   * projections of a pair and the three definitions, and a law proved against a subset of it would
   * be a law proved about a different normal form.
   */
  private final class Laws private (
    val carrier: Carrier,
    val quotient: Quotient,
    val theory: Theory,
    val notation: Notation,
    val logic: Logic,
    val equal: Kernel.Thm,
    val rules: Vector[Rewrite.Rule],
    val representative: Rewrite.Rule,
    /** `INT_OF_PAIR (PAIR k ZERO)` folded back to `INT_OF_NUM k`, and `k + ZERO` to `k`. */
    val tidying: Vector[Rewrite.Rule]
  ) {

    /** `a`, `b` and `c` over `int`, which is what a published law is stated at. */
    private val a: FVar = Term.variable("a", Classes)
    private val b: FVar = Term.variable("b", Classes)
    private val c: FVar = Term.variable("c", Classes)

    private val d: FVar = Term.variable("d", Classes)
    private val e: FVar = Term.variable("e", Classes)

    private val m: FVar = Term.variable("m", numbers)
    private val n: FVar = Term.variable("n", numbers)

    /**
     * Every law of the ring, by the one route.
     *
     * The texts are written at `INT_OF_PAIR x` rather than at `a:int` because the route needs a
     * carrier to rewrite to: a law stated at class variables has nothing under it for the semiring
     * to decide. The generalisation at the end is what puts the statement back over `int`.
     */
    def prove: Either[LogicError, Map[String, Kernel.Thm]] =
      for {
        addCommutative <- overClasses(
          AddCommutative,
          "INT_ADD (INT_OF_PAIR x) (INT_OF_PAIR y)",
          "INT_ADD (INT_OF_PAIR y) (INT_OF_PAIR x)",
          List(x, y),
          List(a, b)
        )
        addAssociative <- overClasses(
          AddAssociative,
          "INT_ADD (INT_ADD (INT_OF_PAIR x) (INT_OF_PAIR y)) (INT_OF_PAIR z)",
          "INT_ADD (INT_OF_PAIR x) (INT_ADD (INT_OF_PAIR y) (INT_OF_PAIR z))",
          List(x, y, z),
          List(a, b, c)
        )
        addAtZero <- overClasses(
          AddAtZero,
          "INT_ADD (INT_OF_PAIR x) INT_ZERO",
          "INT_OF_PAIR x",
          List(x),
          List(a)
        )
        addNegation <- overClasses(
          AddNegation,
          "INT_ADD (INT_OF_PAIR x) (INT_NEG (INT_OF_PAIR x))",
          "INT_ZERO",
          List(x),
          List(a)
        )
        negTwice <- overClasses(
          NegTwice,
          "INT_NEG (INT_NEG (INT_OF_PAIR x))",
          "INT_OF_PAIR x",
          List(x),
          List(a)
        )
        mulCommutative <- overClasses(
          MulCommutative,
          "INT_MUL (INT_OF_PAIR x) (INT_OF_PAIR y)",
          "INT_MUL (INT_OF_PAIR y) (INT_OF_PAIR x)",
          List(x, y),
          List(a, b)
        )
        mulAssociative <- overClasses(
          MulAssociative,
          "INT_MUL (INT_MUL (INT_OF_PAIR x) (INT_OF_PAIR y)) (INT_OF_PAIR z)",
          "INT_MUL (INT_OF_PAIR x) (INT_MUL (INT_OF_PAIR y) (INT_OF_PAIR z))",
          List(x, y, z),
          List(a, b, c)
        )
        mulAtOne <- overClasses(
          MulAtOne,
          "INT_MUL (INT_OF_PAIR x) INT_ONE",
          "INT_OF_PAIR x",
          List(x),
          List(a)
        )
        mulAtZero <- overClasses(
          MulAtZero,
          "INT_MUL (INT_OF_PAIR x) INT_ZERO",
          "INT_ZERO",
          List(x),
          List(a)
        )
        distributive <- overClasses(
          Distributive,
          "INT_MUL (INT_OF_PAIR x) (INT_ADD (INT_OF_PAIR y) (INT_OF_PAIR z))",
          "INT_ADD (INT_MUL (INT_OF_PAIR x) (INT_OF_PAIR y)) " +
            "(INT_MUL (INT_OF_PAIR x) (INT_OF_PAIR z))",
          List(x, y, z),
          List(a, b, c)
        )

        ofNaturalSum <- overNaturals(
          OfNaturalSum,
          "INT_OF_NUM (NUM_ADD m n)",
          "INT_ADD (INT_OF_NUM m) (INT_OF_NUM n)",
          List(m, n)
        )
        ofNaturalProduct <- overNaturals(
          OfNaturalProduct,
          "INT_OF_NUM (NUM_MUL m n)",
          "INT_MUL (INT_OF_NUM m) (INT_OF_NUM n)",
          List(m, n)
        )
        ofNaturalZero <- overNaturals(OfNaturalZero, "INT_OF_NUM ZERO", "INT_ZERO", Nil)
        ofNaturalInjective <- injective

        mulNegation <- overClasses(
          MulNegation,
          "INT_MUL (INT_OF_PAIR x) (INT_NEG (INT_OF_PAIR y))",
          "INT_NEG (INT_MUL (INT_OF_PAIR x) (INT_OF_PAIR y))",
          List(x, y),
          List(a, b)
        )
        zeroTimes <- overClasses(
          ZeroTimes,
          "INT_MUL INT_ZERO (INT_OF_PAIR x)",
          "INT_ZERO",
          List(x),
          List(a)
        )
        combine <- overClasses(
          Combine,
          "INT_ADD (INT_MUL (INT_OF_PAIR w) (INT_MUL (INT_OF_PAIR x) (INT_OF_PAIR y))) " +
            "(INT_MUL (INT_OF_PAIR t) (INT_MUL (INT_OF_PAIR x) (INT_OF_PAIR z)))",
          "INT_MUL (INT_OF_PAIR x) (INT_ADD (INT_MUL (INT_OF_PAIR w) (INT_OF_PAIR y)) " +
            "(INT_MUL (INT_OF_PAIR t) (INT_OF_PAIR z)))",
          List(x, y, z, w, t),
          List(a, b, c, d, e)
        )
      } yield Map(
        MulNegation -> mulNegation,
        ZeroTimes -> zeroTimes,
        Combine -> combine,
        AddCommutative -> addCommutative,
        AddAssociative -> addAssociative,
        AddAtZero -> addAtZero,
        AddNegation -> addNegation,
        NegTwice -> negTwice,
        MulCommutative -> mulCommutative,
        MulAssociative -> mulAssociative,
        MulAtOne -> mulAtOne,
        MulAtZero -> mulAtZero,
        Distributive -> distributive,
        OfNaturalSum -> ofNaturalSum,
        OfNaturalProduct -> ofNaturalProduct,
        OfNaturalZero -> ofNaturalZero,
        OfNaturalInjective -> ofNaturalInjective
      )

    /** The two sides brought to one projection each, and the two pairs related by the semiring. */
    private def equation(leftText: String, rightText: String): Either[LogicError, Kernel.Thm] =
      for {
        left <- Parser.term(theory, notation, leftText, Classes)
        right <- Parser.term(theory, notation, rightText, Classes)
        leftNormal <- normalise(left)
        rightNormal <- normalise(right)
        leftProjected <- rightOf(leftNormal)
        rightProjected <- rightOf(rightNormal)
        leftPair <- projected(leftProjected)
        rightPair <- projected(rightProjected)
        related <- carrier.relate(leftPair, rightPair)
        instance <- logic.rules.specAll(equal, List(leftPair, rightPair))
        back <- Conv.sym(instance)
        bridge <- LogicError.lift(Kernel.eqMp(back, related))
        halfway <- Conv.trans(leftNormal, bridge)
        undo <- Conv.sym(rightNormal)
        result <- Conv.trans(halfway, undo)
      } yield result

    /**
     * The rewriting, with the question `Rewrite.finished` exists for asked where it belongs.
     *
     * Asked **after** the normal form turns out not to be a projection, never before: on the path
     * where it is one the answer changes nothing, and the refusal a reader wants names which of the
     * two it was — a rule set that did not settle, or a term the rules have nothing to say about.
     */
    private def normalise(term: Term): Either[LogicError, Kernel.Thm] =
      Rewrite.rewrite(rules, term)

    /** The pair under a projection, or a refusal naming what was found instead. */
    private def projected(term: Term): Either[LogicError, Term] =
      term match {
        case App(Const(Projection, _), pair) => Right(pair)
        case other =>
          Rewrite.finished(rules, other).flatMap { settled =>
            if (settled)
              Left(NotOfForm(s"a term the rules bring to one $Projection", other))
            else
              Left(NotOfForm("a term the rules settle within their step limit", other))
          }
      }

    /**
     * A law proved at carrier variables, put back over `int`.
     *
     * Specialising at `INT_OF_PAIR_repr a` and rewriting `INT_OF_PAIR (INT_OF_PAIR_repr a)` to `a`
     * is the whole of it, and it needs no existential: `PROJ_REPR` is an equation with nothing
     * assumed, where going through `PROJ_ONTO` would open a witness per variable and close it
     * again.
     */
    private def overClasses(
      name: String,
      leftText: String,
      rightText: String,
      carrierVariables: List[FVar],
      classVariables: List[FVar]
    ): Either[LogicError, Kernel.Thm] =
      blaming(name, leftText, proveOverClasses(leftText, rightText, carrierVariables, classVariables))

    /**
     * A refusal with the law's name in front of it.
     *
     * Every law below is the same four steps over a different pair of texts, so a refusal from any
     * of them reads identically: `Semiring` names two normal forms and nothing says which law was
     * being proved. Since the whole construction is one for-comprehension, the first failure aborts
     * the chain and a reader gets one message for seventeen candidates. This is what makes that
     * message answer the question a reader arrives with.
     */
    private def blaming(
      name: String,
      text: String,
      result: Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      result.left.flatMap { error =>
        Parser
          .term(theory, notation, text, Classes)
          .flatMap(term =>
            Left(NotOfForm(s"$name, which is ${error.message}, over", term))
              : Either[LogicError, Kernel.Thm]
          )
      }

    private def proveOverClasses(
      leftText: String,
      rightText: String,
      carrierVariables: List[FVar],
      classVariables: List[FVar]
    ): Either[LogicError, Kernel.Thm] =
      equation(leftText, rightText).flatMap(
        overRepresentatives(
          logic,
          quotient,
          representative,
          _,
          carrierVariables,
          classVariables
        )
      )

    /** A law whose variables are naturals, which needs no representative and no generalisation. */
    private def overNaturals(
      name: String,
      leftText: String,
      rightText: String,
      variables: List[FVar]
    ): Either[LogicError, Kernel.Thm] =
      blaming(name, leftText, equation(leftText, rightText).flatMap(logic.rules.genAll(_, variables)))

    /**
     * `|- !m n. (INT_OF_NUM m = INT_OF_NUM n) = (m = n)`.
     *
     * Not an equation between integers, so not the route above: it is the central fact at two pairs
     * of the embedding's shape, with the `+ ZERO` on each side taken off and the projection folded
     * back into `INT_OF_NUM`. The folding direction is what makes the rule set here different from
     * the one the laws use, and it is the only place in the file that rewrites a projection into a
     * constant rather than out of one.
     */
    private def injective: Either[LogicError, Kernel.Thm] =
      for {
        leftPair <- Parser.term(theory, notation, "PAIR m ZERO", Pairs)
        rightPair <- Parser.term(theory, notation, "PAIR n ZERO", Pairs)
        instance <- logic.rules.specAll(equal, List(leftPair, rightPair))
        unfolded <- carrier.unfoldedAt(leftPair, rightPair)
        opened <- Conv.trans(instance, unfolded)
        tidied <- Rewrite.inTheorem(tidying, opened)
        result <- logic.rules.genAll(tidied, List(m, n))
      } yield result

  }

  private object Laws {

    def over(
      carrier: Carrier,
      quotient: Quotient,
      theory: Theory,
      notation: Notation,
      logic: Logic,
      equal: Kernel.Thm,
      representative: Kernel.Thm,
      lifts: Vector[Kernel.Thm],
      constants: Vector[Kernel.Thm],
      ofNatural: Kernel.Thm
    ): Either[LogicError, Laws] =
      for {
        liftRules <- Rewrite.Rule.all(logic, lifts)
        ofNaturalRule <- equationRule(logic, ofNatural, List(Term.variable("k", numbers)))
        constantRules <- Rewrite.Rule.all(logic, constants)
        representativeRule <- Rewrite.Rule.of(logic, representative)
        folding <- foldingRule(logic, ofNaturalRule)
        zeroAtSum <- sumAtZeroRule(logic, carrier)
      } yield new Laws(
        carrier,
        quotient,
        theory,
        notation,
        logic,
        equal,
        liftRules ++ carrier.projections ++ constantRules :+ ofNaturalRule,
        representativeRule,
        Vector(folding, zeroAtSum)
      )

    /** `|- !k. c k = …`, which is a definition put into the shape a rewrite rule is read from. */
    private def equationRule(
      logic: Logic,
      definition: Kernel.Thm,
      variables: List[FVar]
    ): Either[LogicError, Rewrite.Rule] =
      for {
        unfolded <- Conv.unfold(definition, variables.map(variable => variable: Term))
        general <- logic.rules.genAll(unfolded, variables)
        rule <- Rewrite.Rule.of(logic, general)
      } yield rule

    /** The embedding's equation read backwards, which is the one fold in the file. */
    private def foldingRule(
      logic: Logic,
      unfolding: Rewrite.Rule
    ): Either[LogicError, Rewrite.Rule] =
      for {
        reversed <- Conv.sym(unfolding.theorem)
        general <- logic.rules.genAll(reversed, unfolding.variables.toList)
        rule <- Rewrite.Rule.of(logic, general)
      } yield rule

    /** `m + ZERO = m`, taken from `Peano` rather than restated. */
    private def sumAtZeroRule(
      logic: Logic,
      carrier: Carrier
    ): Either[LogicError, Rewrite.Rule] =
      carrier.semiring.peano.fact(Peano.AddAtZero).flatMap(Rewrite.Rule.of(logic, _))
  }



  /* ------------------------------------------------------------------ the order */

  /**
   * `|- !x y u v. INT_SAME x u ==> INT_SAME y v ==> ((FST x + SND y <= FST y + SND x) = (…))`.
   *
   * What the order's definition owes, and the one obligation in the file that is an equation
   * between **propositions** rather than between terms. Two related pairs have to give the same
   * order, in both directions, so it is `Kernel.deductAntisym` over two implications rather than a
   * rearrangement: `Semiring` decides equations and has nothing to say about an order.
   *
   * Each direction is the same three steps. Adding `B'` on the left of the assumed order is
   * `NUM_ADD_MONOTONE`; the two sums so produced are the two the other direction wants, which is
   * the one equation the semiring does prove and it is derived from the premises before either
   * direction starts; and `NUM_ADD_LE_CANCEL` takes the summand off again. That the same equation
   * serves both directions read one way and the other is why this is one lemma and not two.
   */
  private def orderRespects(
    carrier: Carrier,
    peano: Peano,
    logic: Logic,
    atMost: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      firstUnfolded <- carrier.unfoldedAt(x, u)
      secondUnfolded <- carrier.unfoldedAt(y, v)
      firstPremise <- leftOf(firstUnfolded)
      secondPremise <- leftOf(secondUnfolded)
      firstEquation <- LogicError
        .lift(Kernel.assume(firstPremise))
        .flatMap(assumed => LogicError.lift(Kernel.eqMp(firstUnfolded, assumed)))
      secondEquation <- LogicError
        .lift(Kernel.assume(secondPremise))
        .flatMap(assumed => LogicError.lift(Kernel.eqMp(secondUnfolded, assumed)))

      xFirst <- carrier.firstOf(x)
      xSecond <- carrier.secondOf(x)
      yFirst <- carrier.firstOf(y)
      ySecond <- carrier.secondOf(y)
      uFirst <- carrier.firstOf(u)
      uSecond <- carrier.secondOf(u)
      vFirst <- carrier.firstOf(v)
      vSecond <- carrier.secondOf(v)

      lower <- carrier.sum(xFirst, ySecond)
      upper <- carrier.sum(yFirst, xSecond)
      lowerMoved <- carrier.sum(uFirst, vSecond)
      upperMoved <- carrier.sum(vFirst, uSecond)

      // `(lower + upperMoved) = (lowerMoved + upper)`, the premises added and rearranged. Both
      // sides hold the same four summands, which is what makes it the semiring's.
      reversedSecond <- Conv.sym(secondEquation)
      combined <- addEquations(carrier, firstEquation, reversedSecond)
      crossLeft <- carrier.sum(lower, upperMoved)
      crossRight <- carrier.sum(lowerMoved, upper)
      cross <- carrier.rearranged(crossLeft, crossRight, combined)

      // `upperMoved + lower = upper + lowerMoved`, which is the same fact with the summand in the
      // position `NUM_ADD_MONOTONE` and `NUM_ADD_LE_CANCEL` both put it in.
      shiftedLeft <- carrier.sum(upperMoved, lower)
      shiftedRight <- carrier.sum(upper, lowerMoved)
      toCross <- carrier.semiring.prove(shiftedLeft, crossLeft)
      fromCross <- carrier.semiring.prove(crossRight, shiftedRight)
      halfway <- Conv.trans(toCross, cross)
      shifted <- Conv.trans(halfway, fromCross)

      // `upperMoved + upper = upper + upperMoved`, which is commutativity and nothing else.
      bothUpperLeft <- carrier.sum(upperMoved, upper)
      bothUpperRight <- carrier.sum(upper, upperMoved)
      commuted <- carrier.semiring.prove(bothUpperLeft, bothUpperRight)

      forwards <- oneDirection(
        logic,
        peano,
        atMost,
        assumedOrder = (lower, upper),
        summand = upperMoved,
        shifting = shifted,
        commuting = commuted,
        cancelAt = (upper, lowerMoved, upperMoved)
      )
      backwardsShifted <- Conv.sym(shifted)
      backwardsCommuted <- Conv.sym(commuted)
      backwards <- oneDirection(
        logic,
        peano,
        atMost,
        assumedOrder = (lowerMoved, upperMoved),
        summand = upper,
        shifting = backwardsShifted,
        commuting = backwardsCommuted,
        cancelAt = (upperMoved, lower, upper)
      )

      equated = Kernel.deductAntisym(backwards, forwards)
      dischargedSecond <- rules.disch(secondPremise, equated)
      dischargedFirst <- rules.disch(firstPremise, dischargedSecond)
      result <- rules.genAll(dischargedFirst, List(x, y, u, v))
    } yield result
  }

  /**
   * One direction of [[orderRespects]]: an order assumed, a summand added, moved and taken off.
   *
   * Both directions are this function, and the two differ only in which way the two semiring
   * equations are read. Writing it once is what says they are the same argument; writing it twice
   * is how the second one stops being checked when the first is repaired.
   */
  private def oneDirection(
    logic: Logic,
    peano: Peano,
    atMost: Term,
    assumedOrder: (Term, Term),
    summand: Term,
    shifting: Kernel.Thm,
    commuting: Kernel.Thm,
    cancelAt: (Term, Term, Term)
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (lower, upper) = assumedOrder
    val (common, cancelledLower, cancelledUpper) = cancelAt

    for {
      order <- LogicError.lift(Term.appAll(atMost, List(lower, upper)))
      assumed <- LogicError.lift(Kernel.assume(order))

      grown <- peano
        .fact(Peano.AddMonotone)
        .flatMap(rules.specAll(_, List(summand, lower, upper)))
        .flatMap(rules.mp(_, assumed))

      grownRight <- secondArgument(grown.conclusion)
      movedLeft <- acrossFirst(atMost, shifting, grownRight, grown)
      shiftedLeft <- rightOf(shifting)
      moved <- acrossSecond(atMost, shiftedLeft, commuting, movedLeft)

      cancelled <- peano
        .fact(Peano.AddCancelsOrder)
        .flatMap(rules.specAll(_, List(common, cancelledLower, cancelledUpper)))
        .flatMap(rules.mp(_, moved))
    } yield cancelled
  }

  /** `|- f t r` from `|- f s r` and `|- s = t`, by congruence on the head. */
  private def acrossFirst(
    head: Term,
    equation: Kernel.Thm,
    second: Term,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- Conv.apTerm(head, equation)
      congruence <- Conv.apThm(partial, second)
      result <- LogicError.lift(Kernel.eqMp(congruence, theorem))
    } yield result

  /** `|- f l t` from `|- f l s` and `|- s = t`. */
  private def acrossSecond(
    head: Term,
    first: Term,
    equation: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      applied <- LogicError.lift(Term.app(head, first))
      congruence <- Conv.apTerm(applied, equation)
      result <- LogicError.lift(Kernel.eqMp(congruence, theorem))
    } yield result


  /**
   * The order on the classes, and the one construct the quotient builder does not reach.
   *
   * `Quotient` lifts a unary operation, a binary operation and a predicate of **one** argument. A
   * relation of two quotient arguments is none of the three: `liftBinary`'s obligation relates the
   * two results, which needs them in the carrier, and `liftPredicate` takes one argument. So this
   * defines the constant through the chosen representatives itself and derives [[AtMostPairs]],
   * which is what a caller uses and what every fact below goes through. That is the shape a fourth
   * lift would have, measured by writing it once rather than added to the builder ahead of a second
   * consumer, which is the criterion `docs/adr/0016` sets for that file.
   *
   * **The respectfulness lemma is where the work is**, and it is not the pattern the ring's laws
   * follow: what has to be shown is that two related pairs give the same **proposition**, so it is
   * an equation at `bool` proved by `Kernel.deductAntisym` from two implications, each of which
   * adds a summand, rearranges by the semiring and cancels. `Semiring` cannot be handed the
   * conclusion directly, because the conclusion is an order and not an equation.
   */
  private final class Order private (
    val carrier: Carrier,
    val quotient: Quotient,
    val logic: Logic,
    val peano: Peano,
    val definition: Kernel.Thm,
    val equal: Kernel.Thm,
    val representative: Rewrite.Rule,
    val addPairs: Kernel.Thm,
    val tidying: Vector[Rewrite.Rule],
    /** `NUM_LE`, which every step under the projection is about. */
    val atMost: Term,
    /**
     * `INT_LE`, which the last two steps of the monotonicity are about.
     *
     * Two heads and not one, because a congruence carries a theorem across an equation **under a
     * head** and the two are at different types: a step about `NUM_LE (FST p + SND q) …` and a step
     * about `INT_LE (INT_OF_PAIR p) …` are the same move at `num` and at `int`. Passing one where
     * the other belongs builds a term the kernel refuses for its type, which is the refusal rather
     * than the wrong theorem, and is how this was found.
     */
    val compare: Term
  ) {

    val rules: Rules = logic.rules

    private val a: FVar = Term.variable("a", Classes)
    private val b: FVar = Term.variable("b", Classes)
    private val c: FVar = Term.variable("c", Classes)
    private val m: FVar = Term.variable("m", numbers)
    private val n: FVar = Term.variable("n", numbers)

    def prove: Either[LogicError, Map[String, Kernel.Thm]] =
      for {
        pairs <- atPairsFact
        reversed <- reversedRule(pairs)
        reflexive <- reflexiveFact(pairs)
        transitive <- transitiveFact(pairs)
        antisymmetric <- antisymmetricFact(pairs)
        total <- totalFact(pairs, reversed)
        monotone <- monotoneFact(pairs)
        embedded <- embeddedFact(pairs)
      } yield Map(
        AtMostPairs -> pairs,
        AtMostReflexive -> reflexive,
        AtMostTransitive -> transitive,
        AtMostAntisymmetric -> antisymmetric,
        AtMostTotal -> total,
        AddMonotone -> monotone,
        AtMostOfNatural -> embedded
      )

    /* ------------------------------------------------ the fact the definition is for */

    /**
     * `|- !p q. INT_LE (INT_OF_PAIR p) (INT_OF_PAIR q) = NUM_LE (FST p + SND q) (FST q + SND p)`.
     *
     * The definition unfolded at two projections says the order between the **chosen**
     * representatives of those two classes; what a caller wants is the order between the pairs it
     * started with. `REPR_REL` relates each to its class's representative and the respectfulness
     * lemma carries the proposition across both at once.
     */
    private def atPairsFact: Either[LogicError, Kernel.Thm] =
      for {
        respects <- orderRespects(carrier, peano, logic, atMost)
        related <- quotient.fact(Quotient.RelatedToRepresentative)
        projection <- LogicError.lift(
          quotient.theory.constant(quotient.names.projection, Type.fun(Pairs, Classes))
        )
        projectedP <- LogicError.lift(Term.app(projection, p))
        projectedQ <- LogicError.lift(Term.app(projection, q))
        unfolded <- Conv.unfold(definition, List(projectedP, projectedQ))

        relatedAtP <- rules.spec(p, related)
        relatedAtQ <- rules.spec(q, related)
        chosenP <- secondArgument(relatedAtP.conclusion)
        chosenQ <- secondArgument(relatedAtQ.conclusion)

        respectsAt <- rules.specAll(respects, List(p, q, chosenP, chosenQ))
        once <- rules.mp(respectsAt, relatedAtP)
        carried <- rules.mp(once, relatedAtQ)

        back <- Conv.sym(carried)
        result <- Conv.trans(unfolded, back)
        general <- rules.genAll(result, List(p, q))
      } yield general

    /**
     * `NUM_LE (FST p + SND q) (FST q + SND p) = INT_LE (INT_OF_PAIR p) (INT_OF_PAIR q)`, as a rule.
     *
     * The published fact read backwards, which is the direction that **contracts**: the right side
     * is smaller than the left and mentions only what the left binds. Reading an equation backwards
     * into a rule is how this file exhausted a heap once, in `IntegerSpec`, so the direction is
     * checked rather than assumed each time it is done.
     */
    private def reversedRule(pairs: Kernel.Thm): Either[LogicError, Rewrite.Rule] =
      for {
        instance <- rules.specAll(pairs, List(p, q))
        flipped <- Conv.sym(instance)
        general <- rules.genAll(flipped, List(p, q))
        rule <- Rewrite.Rule.of(logic, general)
      } yield rule

    /** The published fact at two pairs, with `FST (PAIR a b)` reduced away. */
    private def at(pairs: Kernel.Thm, left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      rules.specAll(pairs, List(left, right)).flatMap(Rewrite.inTheorem(carrier.projections, _))

    /* ------------------------------------------------ the facts */

    /** `|- !a. INT_LE a a`, which is `NUM_LE_REFL` at the one sum both sides are. */
    private def reflexiveFact(pairs: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        instance <- at(pairs, p, p)
        sides <- comparedIn(instance)
        reflexivity <- peano.fact(Peano.Reflexive).flatMap(rules.spec(sides._1, _))
        folded <- foldThrough(instance, reflexivity)
        result <- overRepresentatives(logic, quotient, representative, folded, List(p), List(a))
      } yield result

    /**
     * `|- !a b c. INT_LE a b ==> INT_LE b c ==> INT_LE a c`.
     *
     * The two premises added side by side put `FST q + SND q` in front of both sides of what is
     * wanted, and `NUM_ADD_LE_CANCEL` takes it off. The same shape as the relation's own
     * transitivity one level down, with an order where that has an equation and a cancellation of
     * the order where that cancels an equation.
     */
    private def transitiveFact(pairs: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        first <- at(pairs, p, q)
        second <- at(pairs, q, r)
        target <- at(pairs, p, r)

        firstPremise <- leftOf(first)
        secondPremise <- leftOf(second)
        firstOrder <- assumedThrough(first, firstPremise)
        secondOrder <- assumedThrough(second, secondPremise)

        firstSides <- comparedIn(first)
        secondSides <- comparedIn(second)
        wanted <- comparedIn(target)

        both <- peano
          .fact(Peano.AddMonotoneBoth)
          .flatMap(
            rules.specAll(
              _,
              List(firstSides._1, firstSides._2, secondSides._1, secondSides._2)
            )
          )
        joined <- rules.conjIntro(firstOrder, secondOrder)
        added <- rules.mp(both, joined)

        // `FST q + SND q`, the summand both sides of the conclusion pick up.
        common <- carrier.firstOf(q).flatMap(head => carrier.secondOf(q).map((head, _)))
        summand <- carrier.sum(common._1, common._2)
        leftShape <- carrier.sum(summand, wanted._1)
        rightShape <- carrier.sum(summand, wanted._2)

        addedLeft <- firstArgument(added.conclusion)
        addedRight <- secondArgument(added.conclusion)
        toLeft <- carrier.semiring.prove(addedLeft, leftShape)
        toRight <- carrier.semiring.prove(addedRight, rightShape)
        shapedLeft <- acrossFirst(toLeft, addedRight, added)
        shaped <- acrossSecond(leftShape, toRight, shapedLeft)

        cancelled <- peano
          .fact(Peano.AddCancelsOrder)
          .flatMap(rules.specAll(_, List(summand, wanted._1, wanted._2)))
          .flatMap(rules.mp(_, shaped))

        folded <- foldThrough(target, cancelled)
        dischargedSecond <- rules.disch(secondPremise, folded)
        dischargedFirst <- rules.disch(firstPremise, dischargedSecond)
        result <- overRepresentatives(
          logic,
          quotient,
          representative,
          dischargedFirst,
          List(p, q, r),
          List(a, b, c)
        )
      } yield result

    /**
     * `|- !a b. INT_LE a b ==> INT_LE b a ==> a = b`.
     *
     * The shortest of the five, because the two orders `NUM_LE_ANTISYM` puts together give exactly
     * the equation the relation under the quotient **is**: `FST p + SND q = FST q + SND p` is
     * `INT_SAME p q` unfolded, and the central fact turns it into an equation between classes with
     * nothing in between.
     */
    private def antisymmetricFact(pairs: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        forwards <- at(pairs, p, q)
        backwards <- at(pairs, q, p)
        firstPremise <- leftOf(forwards)
        secondPremise <- leftOf(backwards)
        firstOrder <- assumedThrough(forwards, firstPremise)
        secondOrder <- assumedThrough(backwards, secondPremise)

        sides <- comparedIn(forwards)
        joined <- rules.conjIntro(firstOrder, secondOrder)
        equation <- peano
          .fact(Peano.AntiSymmetric)
          .flatMap(rules.specAll(_, List(sides._1, sides._2)))
          .flatMap(rules.mp(_, joined))

        sameUnfolded <- carrier.unfoldedAt(p, q)
        related <- carrier.fold(sameUnfolded, equation)
        central <- rules.specAll(equal, List(p, q))
        back <- Conv.sym(central)
        classesEqual <- LogicError.lift(Kernel.eqMp(back, related))

        dischargedSecond <- rules.disch(secondPremise, classesEqual)
        dischargedFirst <- rules.disch(firstPremise, dischargedSecond)
        result <- overRepresentatives(
          logic,
          quotient,
          representative,
          dischargedFirst,
          List(p, q),
          List(a, b)
        )
      } yield result

    /** `|- !a b. INT_LE a b \/ INT_LE b a`, which is `NUM_LE_TOTAL` read through the rule. */
    private def totalFact(
      pairs: Kernel.Thm,
      reversed: Rewrite.Rule
    ): Either[LogicError, Kernel.Thm] =
      for {
        instance <- at(pairs, p, q)
        sides <- comparedIn(instance)
        total <- peano.fact(Peano.Total).flatMap(rules.specAll(_, List(sides._1, sides._2)))
        folded <- Rewrite.inTheorem(Vector(reversed), total)
        result <- overRepresentatives(
          logic,
          quotient,
          representative,
          folded,
          List(p, q),
          List(a, b)
        )
      } yield result

    /**
     * `|- !a b c. INT_LE a b ==> INT_LE (INT_ADD c a) (INT_ADD c b)`.
     *
     * What makes the ring an **ordered** one. The lifted sum is what the conclusion is about, so
     * the last two steps carry the theorem back across the lift's own equation by congruence rather
     * than by rewriting: the lift read backwards grows the term, which is the shape this file has
     * already paid for once.
     */
    private def monotoneFact(pairs: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        leftSum <- carrier.applied(carrier.pairAdd, List(r, p))
        rightSum <- carrier.applied(carrier.pairAdd, List(r, q))

        premiseFact <- at(pairs, p, q)
        target <- at(pairs, leftSum, rightSum)
        premise <- leftOf(premiseFact)
        order <- assumedThrough(premiseFact, premise)

        sides <- comparedIn(premiseFact)
        wanted <- comparedIn(target)

        summandFirst <- carrier.firstOf(r)
        summandSecond <- carrier.secondOf(r)
        summand <- carrier.sum(summandFirst, summandSecond)

        monotone <- peano
          .fact(Peano.AddMonotone)
          .flatMap(rules.specAll(_, List(summand, sides._1, sides._2)))
          .flatMap(rules.mp(_, order))

        movedLeft <- firstArgument(monotone.conclusion)
        movedRight <- secondArgument(monotone.conclusion)
        toLeft <- carrier.semiring.prove(movedLeft, wanted._1)
        toRight <- carrier.semiring.prove(movedRight, wanted._2)
        shapedLeft <- acrossFirst(toLeft, movedRight, monotone)
        shaped <- acrossSecond(wanted._1, toRight, shapedLeft)

        folded <- foldThrough(target, shaped)

        leftLift <- rules.specAll(addPairs, List(r, p))
        rightLift <- rules.specAll(addPairs, List(r, q))
        leftBack <- Conv.sym(leftLift)
        rightBack <- Conv.sym(rightLift)
        projectedRight <- rightOf(rightLift)
        atSum <- Integer.acrossFirst(compare, leftBack, projectedRight, folded)
        liftedLeft <- leftOf(leftLift)
        stated <- Integer.acrossSecond(compare, liftedLeft, rightBack, atSum)

        discharged <- rules.disch(premise, stated)
        result <- overRepresentatives(
          logic,
          quotient,
          representative,
          discharged,
          List(p, q, r),
          List(a, b, c)
        )
      } yield result

    /** `|- !m n. INT_LE (INT_OF_NUM m) (INT_OF_NUM n) = NUM_LE m n`. */
    private def embeddedFact(pairs: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        leftPair <- carrier.pairOf(m, carrier.zero)
        rightPair <- carrier.pairOf(n, carrier.zero)
        instance <- at(pairs, leftPair, rightPair)
        tidied <- Rewrite.inTheorem(tidying, instance)
        result <- rules.genAll(tidied, List(m, n))
      } yield result

    /* ------------------------------------------------ plumbing */

    /**
     * The two integers a published order fact is about, read off the right side of it.
     *
     * **Not `sidesOf`**, which is the helper every other derivation in this file reaches for and is
     * wrong here: that one destructures the right side as an **equation**, which is what an
     * unfolded `INT_SAME` gives, and what `INT_LE_PAIRS` gives is an order. Written out because the
     * two read identically at the call site and the first run of this section failed on it with
     * *expected an equation, found (NUM_LE …)*, which is the refusal doing its job.
     */
    private def comparedIn(equation: Kernel.Thm): Either[LogicError, (Term, Term)] =
      for {
        body <- rightOf(equation)
        first <- firstArgument(body)
        second <- secondArgument(body)
      } yield (first, second)

    /** The premise assumed and carried through the published equation. */
    private def assumedThrough(
      equation: Kernel.Thm,
      premise: Term
    ): Either[LogicError, Kernel.Thm] =
      for {
        assumed <- LogicError.lift(Kernel.assume(premise))
        carried <- LogicError.lift(Kernel.eqMp(equation, assumed))
      } yield carried

    /** The conclusion folded back through the published equation. */
    private def foldThrough(
      equation: Kernel.Thm,
      order: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        back <- Conv.sym(equation)
        folded <- LogicError.lift(Kernel.eqMp(back, order))
      } yield folded

    /** The two congruences, at this development's order rather than at a head a caller names. */
    private def acrossFirst(
      equation: Kernel.Thm,
      second: Term,
      theorem: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      Integer.acrossFirst(atMost, equation, second, theorem)

    private def acrossSecond(
      first: Term,
      equation: Kernel.Thm,
      theorem: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      Integer.acrossSecond(atMost, first, equation, theorem)
  }


  private object Order {

    /** `num -> num -> bool`, which is what the carrier's order is written in. */
    private val comparison: Type = Type.fun(numbers, Type.fun(numbers, Type.Bool))

    /**
     * The body, built as a term rather than parsed from a text.
     *
     * A text would have to spell `INT_OF_PAIR_repr`, which is a name `Quotient.Names` derives from
     * the projection's rather than one this file chooses, so writing it here would be a second
     * place that derivation lives; and an interpolated text is a site `NotationBoundarySpec` has to
     * classify. Six applications and two abstractions cost less than either.
     */
    private def body(
      carrier: Carrier,
      quotient: Quotient,
      theory: Theory,
      atMost: Term
    ): Either[LogicError, Term] = {
      val left = Term.variable("a", Classes)
      val right = Term.variable("b", Classes)

      for {
        chooser <- LogicError.lift(
          theory.constant(quotient.names.representative, Type.fun(Classes, Pairs))
        )
        chosenLeft <- LogicError.lift(Term.app(chooser, left))
        chosenRight <- LogicError.lift(Term.app(chooser, right))
        leftFirst <- carrier.firstOf(chosenLeft)
        leftSecond <- carrier.secondOf(chosenLeft)
        rightFirst <- carrier.firstOf(chosenRight)
        rightSecond <- carrier.secondOf(chosenRight)
        lower <- carrier.sum(leftFirst, rightSecond)
        upper <- carrier.sum(rightFirst, leftSecond)
        compared <- LogicError.lift(Term.appAll(atMost, List(lower, upper)))
        abstracted <- LogicError.lift(Term.absAll(List(left, right), compared))
      } yield abstracted
    }

    def over(
      classical: Classical,
      carrier: Carrier,
      quotient: Quotient,
      peano: Peano,
      base: Theory,
      equal: Kernel.Thm,
      representative: Rewrite.Rule,
      addPairs: Kernel.Thm,
      tidying: Vector[Rewrite.Rule]
    ): Either[LogicError, (Theory, Order, Kernel.Thm)] =
      for {
        atMost <- LogicError.lift(base.constant(Peano.NonStrictOrder, comparison))
        built <- body(carrier, quotient, base, atMost)
        defined <- LogicError.lift(Kernel.defineConstant(base, AtMost, built))
        (theory, definition) = defined
        logic <- classical.logic.over(theory)
        compare <- LogicError.lift(
          theory.constant(AtMost, Type.fun(Classes, Type.fun(Classes, Type.Bool)))
        )
      } yield (
        theory,
        new Order(
          carrier,
          quotient,
          logic,
          peano,
          definition,
          equal,
          representative,
          addPairs,
          tidying,
          atMost,
          compare
        ),
        definition
      )
  }

  /* ------------------------------------------------------------------ divisibility */

  /** A premise `INT_DIVIDES a b` taken apart: the existential, a witness, and its equation. */
  private final case class Opened(
    premise: Term,
    existential: Kernel.Thm,
    witness: FVar,
    equation: Kernel.Thm
  )

  /**
   * Divisibility over the integers, and the reason every step of it names a law.
   *
   * `Divisibility` closes each of its steps with `Ring`, which decides identities of a commutative
   * ring over the reals. **Nothing decides identities over `int`**, and the route the laws above
   * take is not available here: those rewrite an equation down to the carrier, and the terms a
   * derivation meets under an existential are class variables with no carrier under them. So every
   * regrouping is a published fact specialised, and [[Integer.Combine]] exists for exactly one of
   * them rather than for a reader.
   *
   * == What this is, measured against the file it is named after ==
   *
   * `DIVIDES_NONZERO`, `!a b. ~(a = 0) ==> Divides a b`, is derivable over the reals and is the
   * whole of what that relation says away from zero. It is **not** derivable here, and that is the
   * difference the card asking for this development is about. The witness of that difference is a
   * concrete non-divisibility at a non-zero divisor, and it is **not in this class**: it is
   * [[Integer.TwoDoesNotDivide]], one section down, because what settles it is the embedding
   * rather than anything about `INT_DIVIDES` itself. Nothing here is that witness, and
   * [[Integer.ZeroDividesOnly]] in particular is not: it is about zero and holds over a field.
   */
  private final class Dividing private (
    val logic: Logic,
    val theory: Theory,
    val definition: Kernel.Thm,
    val laws: Map[String, Kernel.Thm],
    val multiplication: Term,
    val negation: Term,
    val addition: Term,
    val zero: Term,
    val one: Term
  ) {

    val rules: Rules = logic.rules

    private val a: FVar = Term.variable("a", Classes)
    private val b: FVar = Term.variable("b", Classes)
    private val c: FVar = Term.variable("c", Classes)
    private val scaleFirst: FVar = Term.variable("x", Classes)
    private val scaleSecond: FVar = Term.variable("y", Classes)
    private val k: FVar = Term.variable("k", Classes)
    private val l: FVar = Term.variable("l", Classes)

    def prove: Either[LogicError, Map[String, Kernel.Thm]] =
      for {
        introduction <- introduce
        elimination <- eliminate
        reflexive <- reflexiveFact(introduction)
        atZero <- zeroFact(introduction)
        transitive <- transitiveFact(introduction)
        multiple <- multipleFact(introduction)
        negated <- negationFact(introduction)
        linear <- linearFact(introduction)
        onlyZero <- zeroOnlyFact
      } yield Map(
        DividesIntro -> introduction,
        DividesElim -> elimination,
        DividesReflexive -> reflexive,
        DividesZero -> atZero,
        DividesTransitive -> transitive,
        DividesMultiple -> multiple,
        DividesNegation -> negated,
        DividesLinear -> linear,
        ZeroDividesOnly -> onlyZero
      )

    /* ------------------------------------------------ the two faces of the definition */

    /** `|- !a b k. b = INT_MUL a k ==> INT_DIVIDES a b` */
    private def introduce: Either[LogicError, Kernel.Thm] =
      for {
        unfolded <- unfoldedAt(a, b)
        folded <- Conv.sym(unfolded)
        predicate <- rightOf(unfolded).flatMap(predicateOf)
        applied <- LogicError.lift(Term.app(predicate, k))
        contraction <- Conv.betaRoot(applied)
        equation <- rightOf(contraction)
        assumed <- LogicError.lift(Kernel.assume(equation))
        witnessed <- rules.existsIntro(predicate, k, assumed)
        related <- LogicError.lift(Kernel.eqMp(folded, witnessed))
        discharged <- rules.disch(equation, related)
        general <- rules.genAll(discharged, List(a, b, k))
      } yield general

    /** `|- !a b. INT_DIVIDES a b ==> (?k. b = INT_MUL a k)` */
    private def eliminate: Either[LogicError, Kernel.Thm] =
      for {
        opened <- open(a, b, k)
        discharged <- rules.disch(opened.premise, opened.existential)
        general <- rules.genAll(discharged, List(a, b))
      } yield general

    /* ------------------------------------------------ the facts */

    /** `|- !a. INT_DIVIDES a a`, with `INT_ONE` as the witness. */
    private def reflexiveFact(introduction: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        atOne <- law(MulAtOne)
        instance <- rules.spec(a, atOne)
        equation <- Conv.sym(instance)
        related <- conclude(introduction, a, a, one, equation)
        general <- rules.gen(a, related)
      } yield general

    /** `|- !a. INT_DIVIDES a INT_ZERO`, with `INT_ZERO` as the witness. */
    private def zeroFact(introduction: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        atZero <- law(MulAtZero)
        instance <- rules.spec(a, atZero)
        equation <- Conv.sym(instance)
        related <- conclude(introduction, a, zero, zero, equation)
        general <- rules.gen(a, related)
      } yield general

    /**
     * `|- !a b c. INT_DIVIDES a b ==> INT_DIVIDES b c ==> INT_DIVIDES a c`.
     *
     * Two witnesses multiplied, and the two eliminations nest with the inner one first. Both side
     * conditions hold for the same reason `Divisibility`'s do: neither witness occurs in the
     * conclusion, and neither occurs in the other's predicate. The other order refuses rather than
     * misleading, since the generalisation finds the outer witness free in a surviving hypothesis.
     */
    private def transitiveFact(introduction: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        outer <- open(a, b, k)
        inner <- open(b, c, l)
        scaled <- scaleOnTheRight(outer.equation, l)
        chained <- Conv.trans(inner.equation, scaled)
        associative <- law(MulAssociative)
        regrouped <- rules.specAll(associative, List(a, k, l))
        equation <- Conv.trans(chained, regrouped)
        witness <- product(k, l)
        related <- conclude(introduction, a, c, witness, equation)
        closedInner <- rules.existsElim(inner.existential, l, related)
        closedOuter <- rules.existsElim(outer.existential, k, closedInner)
        dischargedInner <- rules.disch(inner.premise, closedOuter)
        dischargedOuter <- rules.disch(outer.premise, dischargedInner)
        general <- rules.genAll(dischargedOuter, List(a, b, c))
      } yield general

    /** `|- !a b c. INT_DIVIDES a b ==> INT_DIVIDES a (INT_MUL b c)` */
    private def multipleFact(introduction: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        opened <- open(a, b, k)
        scaled <- scaleOnTheRight(opened.equation, c)
        associative <- law(MulAssociative)
        regrouped <- rules.specAll(associative, List(a, k, c))
        equation <- Conv.trans(scaled, regrouped)
        witness <- product(k, c)
        target <- product(b, c)
        related <- conclude(introduction, a, target, witness, equation)
        closed <- rules.existsElim(opened.existential, k, related)
        discharged <- rules.disch(opened.premise, closed)
        general <- rules.genAll(discharged, List(a, b, c))
      } yield general

    /**
     * `|- !a b. INT_DIVIDES a b ==> INT_DIVIDES a (INT_NEG b)`.
     *
     * The one fact in the file that has no counterpart over `num` at all, which is what having a
     * signed ring buys: the witness is the witness negated, and `num` has nothing to negate it to.
     */
    private def negationFact(introduction: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        opened <- open(a, b, k)
        negated <- Conv.apTerm(negation, opened.equation)
        moved <- law(MulNegation)
        instance <- rules.specAll(moved, List(a, k))
        back <- Conv.sym(instance)
        equation <- Conv.trans(negated, back)
        witness <- LogicError.lift(Term.app(negation, k))
        target <- LogicError.lift(Term.app(negation, b))
        related <- conclude(introduction, a, target, witness, equation)
        closed <- rules.existsElim(opened.existential, k, related)
        discharged <- rules.disch(opened.premise, closed)
        general <- rules.genAll(discharged, List(a, b))
      } yield general

    /**
     * `|- !a b c x y. INT_DIVIDES a b ==> INT_DIVIDES a c ==> INT_DIVIDES a (x * b + y * c)`.
     *
     * The one a consumer reaches for: an invariant that survives a step survives because the new
     * value is a combination of old ones, so this is the step of such an argument that is about
     * divisibility at all. `INT_COMBINE` is the regrouping, and it is a published law rather than
     * five steps here because this development has no decision procedure to close it with.
     */
    private def linearFact(introduction: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        first <- open(a, b, k)
        second <- open(a, c, l)
        scaledFirst <- scaleOnTheLeft(scaleFirst, first.equation)
        scaledSecond <- scaleOnTheLeft(scaleSecond, second.equation)
        added <- addSides(scaledFirst, scaledSecond)
        combining <- law(Combine)
        regrouped <- rules.specAll(combining, List(a, k, l, scaleFirst, scaleSecond))
        equation <- Conv.trans(added, regrouped)
        witnessFirst <- product(scaleFirst, k)
        witnessSecond <- product(scaleSecond, l)
        witness <- sum(witnessFirst, witnessSecond)
        targetFirst <- product(scaleFirst, b)
        targetSecond <- product(scaleSecond, c)
        target <- sum(targetFirst, targetSecond)
        related <- conclude(introduction, a, target, witness, equation)
        closedSecond <- rules.existsElim(second.existential, l, related)
        closedFirst <- rules.existsElim(first.existential, k, closedSecond)
        dischargedSecond <- rules.disch(second.premise, closedFirst)
        dischargedFirst <- rules.disch(first.premise, dischargedSecond)
        general <- rules.genAll(dischargedFirst, List(a, b, c, scaleFirst, scaleSecond))
      } yield general

    /**
     * `|- !b. INT_DIVIDES INT_ZERO b ==> b = INT_ZERO`.
     *
     * The half that is the same over a field and over a ring, and it is here so that the other half
     * is visible by its absence: `Divisibility.ZeroDivides` is an equation because the converse of
     * this is also true there, and `IntegerSpec` spends this one on `~(INT_DIVIDES INT_ZERO
     * INT_ONE)`, which is the file's cheapest statement that divisibility is not everywhere true.
     */
    private def zeroOnlyFact: Either[LogicError, Kernel.Thm] =
      for {
        opened <- open(zero, b, k)
        times <- law(ZeroTimes)
        instance <- rules.spec(k, times)
        equation <- Conv.trans(opened.equation, instance)
        closed <- rules.existsElim(opened.existential, k, equation)
        discharged <- rules.disch(opened.premise, closed)
        general <- rules.gen(b, discharged)
      } yield general

    /* ------------------------------------------------ plumbing */

    private def law(name: String): Either[LogicError, Kernel.Thm] =
      laws.get(name).toRight(MissingDefinition(name))

    private def product(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(multiplication, List(left, right)))

    private def sum(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(addition, List(left, right)))

    /** `|- INT_DIVIDES s t = (?k. t = INT_MUL s k)`, the defining equation at a pair. */
    private def unfoldedAt(divisor: Term, dividend: Term): Either[LogicError, Kernel.Thm] =
      Conv.unfold(definition, List(divisor, dividend))

    private def predicateOf(term: Term): Either[LogicError, Term] =
      logic.destExistsPredicate(term).toRight(NotOfForm("an existential quantification", term))

    /** `|- s * t = u * t`, from `|- s = u`. Congruence and not a rewrite rule. */
    private def scaleOnTheRight(equation: Kernel.Thm, factor: Term): Either[LogicError, Kernel.Thm] =
      Conv.apTerm(multiplication, equation).flatMap(Conv.apThm(_, factor))

    /** `|- t * s = t * u`, from `|- s = u`. */
    private def scaleOnTheLeft(factor: Term, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        partial <- LogicError.lift(Term.app(multiplication, factor))
        congruence <- Conv.apTerm(partial, equation)
      } yield congruence

    /** `|- s + u = t + v`, from `|- s = t` and `|- u = v`. */
    private def addSides(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        partial <- Conv.apTerm(addition, left)
        combined <- LogicError.lift(Kernel.mkComb(partial, right))
      } yield combined

    /** The introduction rule spent: an equation with a witness becomes the relation. */
    private def conclude(
      introduction: Kernel.Thm,
      divisor: Term,
      dividend: Term,
      witness: Term,
      equation: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        instance <- rules.specAll(introduction, List(divisor, dividend, witness))
        related <- rules.mp(instance, equation)
      } yield related

    /**
     * `INT_DIVIDES s t` assumed, with a named witness and the equation it satisfies.
     *
     * The equation comes from contracting the definition's own predicate at the witness, so it is
     * the very term `Rules.existsElim` looks for among the hypotheses. Building it by hand instead
     * is how this fails with "needs a theorem assuming ...".
     */
    private def open(
      divisor: Term,
      dividend: Term,
      witness: FVar
    ): Either[LogicError, Opened] =
      for {
        unfolded <- unfoldedAt(divisor, dividend)
        premise <- leftOf(unfolded)
        assumed <- LogicError.lift(Kernel.assume(premise))
        existential <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
        predicate <- rightOf(unfolded).flatMap(predicateOf)
        applied <- LogicError.lift(Term.app(predicate, witness))
        contraction <- Conv.betaRoot(applied)
        instance <- rightOf(contraction)
        equation <- LogicError.lift(Kernel.assume(instance))
      } yield Opened(premise, existential, witness, equation)
  }

  private object Dividing {

    /** `int -> int -> int`, which is what this development's own arithmetic is written in. */
    private val binaryClasses: Type = Type.fun(Classes, Type.fun(Classes, Classes))

    def over(
      logic: Logic,
      theory: Theory,
      definition: Kernel.Thm,
      laws: Map[String, Kernel.Thm]
    ): Either[LogicError, Dividing] =
      for {
        multiplication <- LogicError.lift(theory.constant(Multiplication, binaryClasses))
        addition <- LogicError.lift(theory.constant(Addition, binaryClasses))
        negation <- LogicError.lift(theory.constant(Negation, Type.fun(Classes, Classes)))
        zero <- LogicError.lift(theory.constant(Zero, Classes))
        one <- LogicError.lift(theory.constant(One, Classes))
      } yield new Dividing(
        logic,
        theory,
        definition,
        laws,
        multiplication,
        negation,
        addition,
        zero,
        one
      )
  }

  /* ------------------------------------------------------ the embedding's divisibility */

  /**
   * What divisibility over the integers says about the naturals, and the refusal it buys.
   *
   * This is the section the card asking for this development is about. Everything above proves
   * that `INT_DIVIDES` is a divisibility; none of it separates that relation from the one over the
   * reals, where `DIVIDES_NONZERO` gives every non-zero element every multiple and the relation
   * says nothing at all away from zero. [[ZeroDividesOnly]] does not separate them either: it is
   * about zero, and it holds over a field.
   *
   * == Where the work is, which is not where `docs/adr/0033` predicted ==
   *
   * That record names the missing fact as `~(INT_DIVIDES 2 1)` and says it wants **the discreteness
   * of the order**, that nothing lies strictly between zero and one. It does not. What settles it
   * is [[DividesOfNatural]], and under that the refusal is `Modular.DividesOne` -- a divisor of one
   * is one -- with two numerals shown apart. The order is not consulted: `INT_LE` does not occur
   * in this section.
   *
   * Two things are worth taking from that rather than only the correction. The arithmetic bounding
   * the divisors of a non-zero number is **already proved**, one type down, and an embedding that
   * is faithful for the relation is how such a fact reaches up; deriving discreteness here would
   * have rebuilt it. And the same equation is what the converse of
   * `NUM_DIVIDES m n ==> INT_DIVIDES (INT_OF_NUM m) (INT_OF_NUM n)` asks for, which that record
   * lists as a second missing item wanting the same lemma: the two are one fact, so its list loses
   * two entries to one derivation.
   *
   * == Why the hard direction goes through the carrier ==
   *
   * The witness of `INT_DIVIDES (INT_OF_NUM m) (INT_OF_NUM n)` is an **integer**, so the obvious
   * route -- read that witness back as a natural -- is the one needing a sign argument, and it is
   * what the prediction above was about. It is avoided by not asking: [[Cases]] writes the witness
   * as some pair, the equation between classes becomes one equation between naturals, and
   * `n + m * b = m * a` gives `NUM_DIVIDES m n` through `Modular.DividesSummand` without anything
   * deciding which of `a` and `b` is the larger. There is no case split in this section.
   */
  private final class Embedded private (
    val logic: Logic,
    val carrier: Carrier,
    val modular: Modular,
    val successor: Successor,
    val laws: Map[String, Kernel.Thm],
    val divisibility: Map[String, Kernel.Thm],
    /** `|- !p q. (INT_OF_PAIR p = INT_OF_PAIR q) = INT_SAME p q`. */
    val equal: Kernel.Thm,
    /** `|- !a. ?p. a = INT_OF_PAIR p`, which is what names the witness's pair. */
    val cases: Kernel.Thm,
    /** `|- !p q. INT_MUL (INT_OF_PAIR p) (INT_OF_PAIR q) = INT_OF_PAIR (...)`, the lift. */
    val mulPairs: Kernel.Thm,
    /** The equation defining `INT_OF_NUM`, which is the only way down to a pair from here. */
    val ofNatural: Kernel.Thm,
    val embedding: Term,
    val multiplication: Term,
    val projection: Term,
    val divides: Term,
    /** `NUM_DIVIDES`, taken from the theory this development ends at and not from `Modular`'s. */
    val dividesNaturals: Term,
    /** The numerals `2` and `1` of `num`, read once at the type their context forces. */
    val two: Term,
    val one: Term
  ) {

    val rules: Rules = logic.rules

    private val m: FVar = Term.variable("m", numbers)
    private val n: FVar = Term.variable("n", numbers)
    private val c: FVar = Term.variable("c", numbers)
    private val k: FVar = Term.variable("k", Classes)

    def prove: Either[LogicError, Map[String, Kernel.Thm]] =
      for {
        faithful <- faithfulFact
        refused <- refusalFact(faithful)
      } yield Map(DividesOfNatural -> faithful, TwoDoesNotDivide -> refused)

    /* ------------------------------------------------ the two directions */

    /**
     * `|- !m n. INT_DIVIDES (INT_OF_NUM m) (INT_OF_NUM n) = NUM_DIVIDES m n`.
     *
     * `Kernel.deductAntisym` rather than two implications joined: each half is derived with the
     * other side's statement standing as a hypothesis, and that rule is what drops exactly those
     * two. The argument order is the equation's order, which is why the half concluding the
     * integers' relation goes first.
     */
    private def faithfulFact: Either[LogicError, Kernel.Thm] =
      for {
        up <- fromTheNaturals
        down <- toTheNaturals
        equated = Kernel.deductAntisym(up, down)
        result <- rules.genAll(equated, List(m, n))
      } yield result

    /**
     * `NUM_DIVIDES m n |- INT_DIVIDES (INT_OF_NUM m) (INT_OF_NUM n)`, the easy half.
     *
     * The witness is the embedded witness and [[OfNaturalProduct]] is the whole of the arithmetic:
     * an embedding that carries a product to a product carries a divisibility to one, since a
     * divisibility is a product with one factor existentially bound.
     */
    private def fromTheNaturals: Either[LogicError, Kernel.Thm] =
      for {
        divisor <- embeddedAt(m)
        dividend <- embeddedAt(n)

        premise <- LogicError.lift(Term.appAll(dividesNaturals, List(m, n)))
        assumed <- LogicError.lift(Kernel.assume(premise))
        existential <- modular
          .fact(Modular.DividesElim)
          .flatMap(rules.specAll(_, List(m, n)))
          .flatMap(rules.mp(_, assumed))
        opened <- openedAt(existential, c)

        embedded <- Conv.apTerm(embedding, opened)
        product <- law(OfNaturalProduct).flatMap(rules.specAll(_, List(m, c)))
        equation <- Conv.trans(embedded, product)

        witness <- embeddedAt(c)
        related <- fact(DividesIntro)
          .flatMap(rules.specAll(_, List(divisor, dividend, witness)))
          .flatMap(rules.mp(_, equation))
        closed <- rules.existsElim(existential, c, related)
      } yield closed

    /**
     * `INT_DIVIDES (INT_OF_NUM m) (INT_OF_NUM n) |- NUM_DIVIDES m n`, which is where the work is.
     *
     * Two witnesses are opened and neither is a natural: the divisibility's own `k`, over `int`,
     * and the pair [[Cases]] writes `k` as. Under both, the equation between classes is one
     * equation between naturals and [[dividesTheDifference]] reads the conclusion off it.
     */
    private def toTheNaturals: Either[LogicError, Kernel.Thm] =
      for {
        divisor <- embeddedAt(m)
        dividend <- embeddedAt(n)

        premise <- LogicError.lift(Term.appAll(divides, List(divisor, dividend)))
        assumed <- LogicError.lift(Kernel.assume(premise))
        existential <- fact(DividesElim)
          .flatMap(rules.specAll(_, List(divisor, dividend)))
          .flatMap(rules.mp(_, assumed))
        atWitness <- openedAt(existential, k)

        pairs <- rules.spec(k, cases)
        isPair <- openedAt(pairs, p)

        scaled <- LogicError
          .lift(Term.app(multiplication, divisor))
          .flatMap(Conv.apTerm(_, isPair))
        atPair <- Conv.trans(atWitness, scaled)

        overNaturals <- betweenNaturals(atPair)
        divided <- dividesTheDifference(overNaturals)

        closedPair <- rules.existsElim(pairs, p, divided)
        closed <- rules.existsElim(existential, k, closedPair)
      } yield closed

    /* ------------------------------------------------ down to the carrier */

    /**
     * `|- n + m * SND p = m * FST p`, from an equation reading
     * `|- INT_OF_NUM n = INT_MUL (INT_OF_NUM m) (INT_OF_PAIR p)`.
     *
     * Both sides are brought to one projection each, the central fact of the quotient turns the
     * equation between classes into the relation, the relation is unfolded, and what is left is the
     * two products by `ZERO` the lift leaves behind. Those go by [[Carrier.rearranged]] and not
     * by a rewrite rule set, because what has to hold is that the equation the unfolding produced and
     * the equation a consumer wants are the same identity, and `Semiring.prove` refuses rather than
     * searching where they are not.
     */
    private def betweenNaturals(equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        dividendPair <- carrier.pairOf(n, carrier.zero)
        divisorPair <- carrier.pairOf(m, carrier.zero)

        dividendNormal <- Conv.unfold(ofNatural, List(n))
        divisorNormal <- Conv.unfold(ofNatural, List(m))

        projected <- LogicError.lift(Term.app(projection, p))
        divisorMoved <- Conv
          .apTerm(multiplication, divisorNormal)
          .flatMap(Conv.apThm(_, projected))
        lifted <- rules.specAll(mulPairs, List(divisorPair, p))
        liftedReduced <- Rewrite.inTheorem(carrier.projections, lifted)
        productNormal <- Conv.trans(divisorMoved, liftedReduced)
        productPair <- rightOf(productNormal).flatMap(underProjection)

        toPairs <- Conv
          .sym(dividendNormal)
          .flatMap(Conv.trans(_, equation))
          .flatMap(Conv.trans(_, productNormal))
        same <- rules
          .specAll(equal, List(dividendPair, productPair))
          .flatMap(instance => LogicError.lift(Kernel.eqMp(instance, toPairs)))

        unfolded <- carrier.unfoldedAt(dividendPair, productPair)
        opened <- LogicError.lift(Kernel.eqMp(unfolded, same))

        first <- carrier.firstOf(p)
        second <- carrier.secondOf(p)
        scaledSecond <- carrier.product(m, second)
        scaledFirst <- carrier.product(m, first)
        wanted <- carrier.sum(n, scaledSecond)
        result <- carrier.rearranged(wanted, scaledFirst, opened)
      } yield result

    /**
     * `|- NUM_DIVIDES m n`, from `|- n + m * SND p = m * FST p`.
     *
     * The one step of the hard direction that is arithmetic rather than plumbing, and it is three
     * published facts of `Modular` in a row: `m` divides each of its own multiples, the equation
     * read the other way says `m * SND p + n` is one of them, and `NUM_DIVIDES_SUMMAND` takes the
     * first summand off. A route through a non-negative witness would have had to decide which of
     * `FST p` and `SND p` is the larger; this decides nothing.
     */
    private def dividesTheDifference(equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        first <- carrier.firstOf(p)
        second <- carrier.secondOf(p)
        scaledSecond <- carrier.product(m, second)
        scaledFirst <- carrier.product(m, first)

        reflexive <- modular.fact(Modular.DividesRefl).flatMap(rules.spec(m, _))
        multiple <- modular.fact(Modular.DividesMul)
        dividesSecond <- rules.specAll(multiple, List(m, m, second)).flatMap(rules.mp(_, reflexive))
        dividesFirst <- rules.specAll(multiple, List(m, m, first)).flatMap(rules.mp(_, reflexive))

        summed <- carrier.sum(scaledSecond, n)
        swapped <- carrier.rearranged(summed, scaledFirst, equation)
        back <- Conv.sym(swapped)
        dividesSum <- LogicError
          .lift(Term.app(dividesNaturals, m))
          .flatMap(Conv.apTerm(_, back))
          .flatMap(carried => LogicError.lift(Kernel.eqMp(carried, dividesFirst)))

        result <- modular
          .fact(Modular.DividesSummand)
          .flatMap(rules.specAll(_, List(m, scaledSecond, n)))
          .flatMap(rules.mp(_, dividesSecond))
          .flatMap(rules.mp(_, dividesSum))
      } yield result

    /* ------------------------------------------------ the refusal */

    /**
     * `|- ~(INT_DIVIDES (INT_OF_NUM 2) (INT_OF_NUM 1))`.
     *
     * Six steps over [[faithfulFact]], and the two that are not bookkeeping are `Modular`'s. The
     * numerals are why `Successor` is here at all: `NUM_DIVIDES_ONE` concludes `d = SUC ZERO` and
     * `2` is `NUM_BIT0 NUM_ONE`, so the two spellings have to be walked between.
     *
     * **The spelling is carried in by congruence and never by rewriting the statement.** A rule
     * taking `NUM_ONE` to `SUC ZERO` fires inside the bit encoding of `2` as well, so a statement
     * rewritten with it comes back about `NUM_BIT0 (SUC ZERO)` and matches nothing: that is the
     * trap `Limit` records meeting at the cosine's exponent and `Collatz` at a letter.
     */
    private def refusalFact(faithful: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        divisor <- embeddedAt(two)
        dividend <- embeddedAt(one)
        premise <- LogicError.lift(Term.appAll(divides, List(divisor, dividend)))
        assumed <- LogicError.lift(Kernel.assume(premise))

        inNaturals <- rules
          .specAll(faithful, List(two, one))
          .flatMap(instance => LogicError.lift(Kernel.eqMp(instance, assumed)))

        spelled <- successor.spell(one)
        atSuccessor <- LogicError
          .lift(Term.app(dividesNaturals, two))
          .flatMap(Conv.apTerm(_, spelled))
          .flatMap(carried => LogicError.lift(Kernel.eqMp(carried, inNaturals)))

        isOne <- modular
          .fact(Modular.DividesOne)
          .flatMap(rules.spec(two, _))
          .flatMap(rules.mp(_, atSuccessor))
        asNumerals <- Conv.sym(spelled).flatMap(Conv.trans(isOne, _))

        apart <- successor.distinct(two, one)
        absurd <- rules.notElim(apart, asNumerals)
        result <- rules.notIntro(premise, absurd)
      } yield result

    /* ------------------------------------------------ plumbing */

    private def law(name: String): Either[LogicError, Kernel.Thm] =
      laws.get(name).toRight(MissingDefinition(name))

    private def fact(name: String): Either[LogicError, Kernel.Thm] =
      divisibility.get(name).toRight(MissingDefinition(name))

    /** `INT_OF_NUM t`, as a term. */
    private def embeddedAt(number: Term): Either[LogicError, Term] =
      LogicError.lift(Term.app(embedding, number))

    /**
     * An existential opened at a named witness: its own body, contracted and assumed.
     *
     * The shape `Dividing.open` uses and for its reason: the equation has to be the very term
     * `Rules.existsElim` looks for among the hypotheses, so it comes from contracting the
     * quantifier's own predicate rather than from building it a second time.
     */
    private def openedAt(existential: Kernel.Thm, witness: FVar): Either[LogicError, Kernel.Thm] =
      for {
        predicate <- logic
          .destExistsPredicate(existential.conclusion)
          .toRight(NotOfForm("an existential quantification", existential.conclusion))
        applied <- LogicError.lift(Term.app(predicate, witness))
        contraction <- Conv.betaRoot(applied)
        instance <- rightOf(contraction)
        assumed <- LogicError.lift(Kernel.assume(instance))
      } yield assumed

    /** The pair under a projection, or a refusal naming what the lift produced instead. */
    private def underProjection(term: Term): Either[LogicError, Term] =
      term match {
        case App(Const(Projection, _), pair) => Right(pair)
        case other => Left(NotOfForm(s"a term under one $Projection", other))
      }
  }

  private object Embedded {

    /** `int -> int -> int`, which is what this development's own arithmetic is written in. */
    private val binaryClasses: Type = Type.fun(Classes, Type.fun(Classes, Classes))

    /** `num -> num -> bool`, which is what `NUM_DIVIDES` is. */
    private val naturalRelation: Type = Type.fun(numbers, Type.fun(numbers, Type.Bool))

    def over(
      classical: Classical,
      carrier: Carrier,
      modular: Modular,
      successor: Successor,
      theory: Theory,
      notation: Notation,
      laws: Map[String, Kernel.Thm],
      divisibility: Map[String, Kernel.Thm],
      equal: Kernel.Thm,
      cases: Kernel.Thm,
      mulPairs: Kernel.Thm,
      ofNatural: Kernel.Thm
    ): Either[LogicError, Embedded] =
      for {
        logic <- classical.logic.over(theory)
        embedding <- LogicError.lift(theory.constant(OfNatural, Type.fun(numbers, Classes)))
        multiplication <- LogicError.lift(theory.constant(Multiplication, binaryClasses))
        projection <- LogicError.lift(theory.constant(Projection, Type.fun(Pairs, Classes)))
        divides <- LogicError.lift(
          theory.constant(Divides, Type.fun(Classes, Type.fun(Classes, Type.Bool)))
        )
        dividesNaturals <- LogicError.lift(
          theory.constant(Modular.DividesName, naturalRelation)
        )

        // Read at an expected type rather than annotated in the text: a digit string determines
        // nothing on its own and the theory reads two encodings, which is `docs/adr/0018`, and the
        // caller is the one that knows. `Parser.term`'s own docstring is where that is argued.
        two <- Parser.term(theory, notation, "2", numbers)
        one <- Parser.term(theory, notation, "1", numbers)
      } yield new Embedded(
        logic,
        carrier,
        modular,
        successor,
        laws,
        divisibility,
        equal,
        cases,
        mulPairs,
        ofNatural,
        embedding,
        multiplication,
        projection,
        divides,
        dividesNaturals,
        two,
        one
      )
  }
}
