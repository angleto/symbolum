package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The rationals, `rat`, as a quotient of `prod(int, num)` where the denominator of `(a, d)` is
 * `SUC d`.
 *
 * **The file is `Fraction` and the type is `rat`, and the name is not a preference.** `Rational`
 * is taken, by the exact arithmetic of `modules/core`, which is a Scala value on the untrusted
 * side and is used across the tree; renaming that to free the word here would be a
 * mechanical change through five modules for a reader's convenience. What the word names in this
 * file is the **carrier**: a fraction is a numerator and a denominator, and `rat` is the quotient
 * of those.
 *
 * `docs/adr/0036` is the decision and the one thing to read before this file. The short form: on
 * pairs of integers the obvious relation, `a * d' = a' * d`, is **not an equivalence relation**,
 * and it fails at a pair anybody can write — `(1,1)` relates to `(0,0)` and `(0,0)` to `(2,3)`,
 * while `(1,1)` to `(2,3)` would be `3 = 2`. `Quotient.define` asks for transitivity over the
 * whole carrier, so that relation cannot be handed to it at all.
 *
 * Reading the second component as a **predecessor** removes the case rather than excluding it: the
 * denominator of `(a, d)` is `INT_OF_NUM (SUC d)`, a successor cannot be zero, and the relation is
 * then an equivalence on every pair there is with no subtype and no side condition. What a reader
 * pays for that is the representation: `(3, 1)` is three halves and not three, and every statement
 * here carries a `SUC` where a reader expects a denominator. It is the same trade `Integer` makes
 * by writing `a + d = c + b` where a reader expects a difference, and for the same reason.
 *
 * == What is here and what is not ==
 *
 * The relation, its three equivalence facts, the type, and since 2026-09-25 **the operations**:
 * `RAT_ADD`, `RAT_NEG` and `RAT_MUL`, lifted from `(a, d) + (b, e) = (a * (e + 1) + b * (d + 1),
 * d * e + d + e)`, `-(a, d) = (-a, d)` and `(a, d) * (b, e) = (a * b, d * e + d + e)`, with the
 * commutativity of the sum and of the product on classes. Until that day there was none, and the
 * reason is worth the paragraph: `Integer` closes every one of its obligations with `Semiring`,
 * which the pair representation of an integer puts within reach, and the carrier here is pairs of
 * **integers**, over which nothing decided an identity. Angelo decided that the procedure be
 * generalised rather than each obligation derived by hand (Mycelium card `fa8737ad`), and
 * `CommutativeRing` is that generalisation: `Integer.ring` decides the algebra of `int`, and
 * `CommutativeRing.consequence` closes an obligation that follows from its premises by
 * substitution, given the coefficient each premise is scaled by. [[Fraction.Denominator]] is the
 * one lemma the obligations share: the index a product of two denominators is stored at, read back
 * as the product.
 *
 * **Since the same day, the rest of a commutative ring**: `RAT_ZERO` and `RAT_ONE` as the classes
 * of `(INT_ZERO, 0)` and `(INT_ONE, 0)`, the two associativities, both units, the additive inverse,
 * the distributive law, and `RAT_ZERO_NOT_ONE`, which is the one of them a one-point type would
 * fail. Each law is a pair-level identity carried to the classes, and `Lifting.laws` says how.
 *
 * **And the order**, `RAT_LE`, defined through the chosen representatives because `Quotient` does
 * not lift a relation of two arguments, with the four laws of a total order and the pair
 * `RAT_ZERO_LE_ONE`, `RAT_NOT_ONE_LE_ZERO` that the trivial relation fails. Under it are two facts
 * about `int` that nothing had needed: a natural factor preserves `INT_LE`, and a positive one
 * comes off it. `Ordering` is the derivation.
 *
 * **And, the same day, the ordered field.** `RAT_INV` is defined over the order's theory as
 * `COND (x = RAT_ZERO) RAT_ZERO (select (\y. RAT_MUL x y = RAT_ONE))`, so the value at zero is a
 * convention the definition writes and `RAT_INV_ZERO` reads it back; `RAT_INVERSE_EXISTS` is what
 * makes the choice say something elsewhere, and `RAT_MUL_INV` is the two together. The pair
 * `(a, d)` holds its numerator as an integer rather than as a sign and a size, so the existence
 * needed the sign first: `INT_OF_NUM_CASES` writes every integer as `n` or `-n`, and the inverse of
 * the class of `(k + 1, d)` is the class of `(d + 1, k)`, with the sign carried to the witness in
 * the negative case. The two laws tying the order to the operations are `RAT_LE_ADD` and
 * `RAT_LE_MUL`; under the second are `INT_NONNEG_OF_NUM`, that a non-negative integer is a natural,
 * and `INT_LE_MUL_NONNEG`. None of them spends anything the rest of the file does not already
 * spend.
 *
 * **And Archimedean and dense, the same day**, which is what the reals as cuts ask beyond the
 * field: `RAT_LT` and `RAT_OF_NUM` are two definitions over it, and `RAT_ARCHIMEDES`,
 * `RAT_ARCHIMEDES_INV` and `RAT_DENSE` are derived in `Density`, mostly on classes through the ring
 * of `rat` rather than at pairs.
 *
 * == The one thing transitivity needs, and where it comes from ==
 *
 * `Integer.INT_MUL_CANCEL_NUM`: a factor `INT_OF_NUM (SUC d)` comes off both sides of a product.
 * It is the restricted cancellation and not the general one, and the reason is in its own
 * docstring: the general law wants the absence of zero divisors and this construction does not
 * hold it. Cancelling is the whole of the arithmetic here, exactly as cancelling an addition is
 * the whole of `Integer`'s own transitivity one level down.
 */
final class Fraction private (
  val classical: Classical,
  val integers: Integer,
  val theory: Theory,
  val notation: Notation,
  val quotient: Quotient,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  val logic: Logic = classical.logic

  /** The relation's definition, and the quotient's own. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A published fact of this development, or a refusal naming it. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).orElse(quotient.facts.get(name)).toRight(MissingDefinition(name))

  /** A proposition read against this development's signature. */
  def proposition(text: String): Either[LogicError, Term] =
    Parser.proposition(theory, notation, text)

  /** A term read against this development's signature. */
  def term(text: String, expected: Type): Either[LogicError, Term] =
    Parser.term(theory, notation, text, expected)

  /** A term as this development prints it. */
  def show(term: Term): String = Show.show(notation, term)

  /** The `rat` instance of `CommutativeRing`, over the laws this development proved about classes. */
  lazy val ring: Either[LogicError, CommutativeRing] = Fraction.ringOver(logic, theory, notation, fact)
}

object Fraction {

  /**
   * The `rat` instance of `CommutativeRing`, over the eight laws `fact` names. A function of the
   * lookup rather than of a finished development because `Density` needs the ring inside the
   * construction, before there is a `Fraction` to ask; `Cut` asks the finished one.
   */
  private[theories] def ringOver(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    fact: String => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, CommutativeRing] = {
    val binary = Type.fun(Classes, Type.fun(Classes, Classes))
    def constant(name: String, ty: Type): Either[LogicError, Term] = Parser.term(theory, notation, name, ty)
    for {
      add <- constant(Addition, binary)
      multiply <- constant(Multiplication, binary)
      negate <- constant(Negation, Type.fun(Classes, Classes))
      zero <- constant(Zero, Classes)
      one <- constant(One, Classes)
      addAssociative <- fact(AddAssociative)
      addCommutative <- fact(AddCommutative)
      addZero <- fact(AddAtZero)
      mulAssociative <- fact(MulAssociative)
      mulCommutative <- fact(MulCommutative)
      mulOne <- fact(MulAtOne)
      distributive <- fact(Distributive)
      inverse <- fact(AddNegation)
      ring <- CommutativeRing.ring(
        logic,
        CommutativeRing.Operations(Classes, add, multiply, zero, one, Some(negate)),
        CommutativeRing.Laws(
          addAssociative, addCommutative, addZero, mulAssociative, mulCommutative, mulOne,
          distributive, None, Some(inverse)
        )
      )
    } yield ring
  }

  /* ------------------------------------------------------------------ the names */

  /** The type operator, and the two halves of the bijection the kernel returns for it. */
  val TypeName: String = "rat"
  val Abstraction: String = "mk_rat"
  val Representation: String = "dest_rat"

  /**
   * `RAT_SAME p q` — the two pairs stand for the same rational.
   *
   * `FST p * SUC (SND q) = FST q * SUC (SND p)`, with each successor embedded into `int`. The
   * cross-multiplication anybody writes, over a denominator that cannot be zero because it is a
   * successor, which is what makes it an equivalence relation everywhere.
   */
  val SameName: String = "RAT_SAME"

  /** `RAT_OF_PAIR p` — the rational the pair stands for. */
  val Projection: String = "RAT_OF_PAIR"

  /** `|- !p. RAT_SAME p p` */
  val SameReflexive: String = "RAT_SAME_REFL"

  /** `|- !p q. RAT_SAME p q ==> RAT_SAME q p` */
  val SameSymmetric: String = "RAT_SAME_SYM"

  /** `|- !p q r. RAT_SAME p q ==> RAT_SAME q r ==> RAT_SAME p r` */
  val SameTransitive: String = "RAT_SAME_TRANS"

  /**
   * `|- !x y z. INT_MUL (INT_MUL x y) z = INT_MUL (INT_MUL x z) y`
   *
   * The rearrangement transitivity needs three times, published because it is used three times
   * and because it is the shape a reader checks the argument by: every step of that proof moves
   * one factor of a triple product past another.
   *
   * It is **not** a fact about the rationals and it is here rather than in `Integer` for one
   * reason: nothing else has needed it. A second consumer moves it down, which is the rule
   * `docs/adr/0008` gives for where a fact belongs.
   */
  val SwapFactors: String = "INT_MUL_SWAP"

  /** `RAT_ADD`, `RAT_NEG` and `RAT_MUL`: the operations, lifted from the pairs. */
  val Addition: String = "RAT_ADD"
  val Negation: String = "RAT_NEG"
  val Multiplication: String = "RAT_MUL"

  /**
   * `|- !d e. INT_OF_NUM (SUC (d * e + d + e)) = INT_MUL (INT_OF_NUM (SUC d)) (INT_OF_NUM (SUC e))`
   *
   * The index a product of two denominators is stored at, read back as the product. It is what
   * `docs/adr/0036` means by "a successor peeled": `SUC d * SUC e` is `SUC (d * e + d + e)`, so the
   * sum and the product of two rationals stay in the carrier without a subtraction, and every
   * obligation about them meets its denominators through this equation.
   */
  val Denominator: String = "RAT_DENOMINATOR"

  /** The three lifts, as `Quotient` returns them: an operation on classes of pairs is its pair form. */
  val AddPairs: String = "RAT_ADD_PAIRS"
  val NegPair: String = "RAT_NEG_PAIR"
  val MulPairs: String = "RAT_MUL_PAIRS"

  /** `|- !x y. RAT_ADD x y = RAT_ADD y x` and the same for the product: the first laws on classes. */
  val AddCommutative: String = "RAT_ADD_SYM"
  val MulCommutative: String = "RAT_MUL_SYM"

  /** `RAT_ZERO` and `RAT_ONE`: the classes of `(INT_ZERO, 0)` and `(INT_ONE, 0)`, `0/1` and `1/1`. */
  val Zero: String = "RAT_ZERO"
  val One: String = "RAT_ONE"

  /**
   * The rest of the commutative ring, on classes: the names are `Integer`'s with `RAT` in front,
   * because they are the same laws one quotient up and a reader looking for one looks for the other.
   */
  val AddAssociative: String = "RAT_ADD_ASSOC"
  val AddAtZero: String = "RAT_ADD_ZERO"
  val AddNegation: String = "RAT_ADD_NEG"
  val MulAssociative: String = "RAT_MUL_ASSOC"
  val MulAtOne: String = "RAT_MUL_ONE"
  val Distributive: String = "RAT_MUL_DISTRIBUTE"

  /**
   * `|- ~(RAT_ZERO = RAT_ONE)`, the guard against a type of one point.
   *
   * Every other law here holds of a one-point type, and a quotient whose relation related everything
   * would be one. `QuotientSpec` says it cannot carry this guard for a quotient in general; for this
   * one it is a theorem, because the relation at the two pairs is `0 = 1` over `int` and that is
   * `ZERO = SUC ZERO` over `num` by the embedding's injectivity.
   */
  val UnitsDistinct: String = "RAT_ZERO_NOT_ONE"

  /**
   * `RAT_LE x y`: the order, defined through the representatives the quotient chose.
   *
   * `Quotient` lifts a relation of one argument and not of two, the reason `Integer` gives for
   * its own `INT_LE`: `liftBinary`'s obligation relates two results and so wants them in the
   * carrier. So the constant reads the chosen pairs directly, and [[Fraction.AtMostPairs]] is the
   * fact that makes it usable at any pair.
   */
  val AtMost: String = "RAT_LE"

  /**
   * `|- !a b n. INT_LE a b ==> INT_LE (INT_MUL a (INT_OF_NUM n)) (INT_MUL b (INT_OF_NUM n))`
   *
   * A natural factor preserves the order of `int`, with no side condition because at `n = 0` both
   * sides are zero. Through the pairs: `INT_LE_PAIRS` makes both orders comparisons of naturals,
   * and the one after the product is the one before it multiplied by `n`, which `NUM_MUL_MONOTONE`
   * gives and `Semiring` rearranges into.
   *
   * It is about `int` and it is here, with the next one, for the reason `INT_MUL_SWAP` is: this is
   * the only consumer so far. A second one moves both down.
   */
  val IntAtMostScaled: String = "INT_LE_MUL_NUM"

  /**
   * `|- !a b d. INT_LE (INT_MUL a (INT_OF_NUM (SUC d))) (INT_MUL b (INT_OF_NUM (SUC d))) ==> INT_LE a b`
   *
   * A positive factor comes off a comparison. No induction and nothing strict: by totality either
   * `a <= b` already, or `b <= a`, which scaled and set against the premise makes the two products
   * equal, and `INT_MUL_CANCEL_NUM` makes `a` and `b` equal.
   */
  val IntAtMostCancels: String = "INT_LE_CANCEL_NUM"

  /**
   * `|- !p q r s. RAT_SAME p r ==> RAT_SAME q s ==> (the order at p q) ==> (the order at r s)`
   *
   * The respectfulness a lifted relation would have owed, stated at the pairs, and the whole of
   * the arithmetic of the order: scale the premise by both of the new denominators, rewrite each
   * side with one of the two premises, and take the product of the old denominators off.
   */
  val AtMostRespects: String = "RAT_LE_RESPECTS"

  /** `|- !p q. RAT_LE (RAT_OF_PAIR p) (RAT_OF_PAIR q) = (the cross-multiplied order at p q)` */
  val AtMostPairs: String = "RAT_LE_PAIRS"

  val AtMostReflexive: String = "RAT_LE_REFL"
  val AtMostTransitive: String = "RAT_LE_TRANS"
  val AtMostAntisymmetric: String = "RAT_LE_ANTISYM"
  val AtMostTotal: String = "RAT_LE_TOTAL"

  /**
   * `|- RAT_LE RAT_ZERO RAT_ONE` and `|- ~(RAT_LE RAT_ONE RAT_ZERO)`: the pair that separates this
   * order from a trivial one. Reflexivity, transitivity, antisymmetry and totality all hold of the
   * relation that relates everything on a one-point type, and of nothing else these two do not.
   */
  val ZeroAtMostOne: String = "RAT_ZERO_LE_ONE"

  /** `RAT_INV x`: the inverse of a non-zero rational, and zero at zero, which the definition writes. */
  val Inverse: String = "RAT_INV"

  /** `|- !a. (?n. a = INT_OF_NUM n) \/ (?n. a = INT_NEG (INT_OF_NUM n))`: the sign of an integer. */
  val IntSign: String = "INT_OF_NUM_CASES"

  /** `|- !a. INT_LE INT_ZERO a ==> ?n. a = INT_OF_NUM n`. */
  val IntNonNegative: String = "INT_NONNEG_OF_NUM"

  /** `|- !a b. INT_LE INT_ZERO a ==> INT_LE INT_ZERO b ==> INT_LE INT_ZERO (INT_MUL a b)`. */
  val IntMulNonNegative: String = "INT_LE_MUL_NONNEG"

  /** `|- !x y z. RAT_LE x y ==> RAT_LE (RAT_ADD x z) (RAT_ADD y z)`: the order with the sum. */
  val AtMostAdd: String = "RAT_LE_ADD"

  /** `|- !x y. RAT_LE RAT_ZERO x ==> RAT_LE RAT_ZERO y ==> RAT_LE RAT_ZERO (RAT_MUL x y)`. */
  val AtMostMul: String = "RAT_LE_MUL"

  /** `|- !x. ~(x = RAT_ZERO) ==> ?y. RAT_MUL x y = RAT_ONE`. */
  val InverseExists: String = "RAT_INVERSE_EXISTS"

  /** `|- !x. ~(x = RAT_ZERO) ==> RAT_MUL x (RAT_INV x) = RAT_ONE`. */
  val MulInverse: String = "RAT_MUL_INV"

  /** `|- RAT_INV RAT_ZERO = RAT_ZERO`. */
  val InverseAtZero: String = "RAT_INV_ZERO"

  /** `RAT_LT x y`, defined as `~(RAT_LE y x)`: the strict order, which on a total order is that. */
  val LessThan: String = "RAT_LT"

  /** `RAT_OF_NUM n`, the class of `(INT_OF_NUM n, 0)`: the naturals inside `rat`. */
  val OfNumber: String = "RAT_OF_NUM"

  /** `|- !x y. RAT_LT x y ==> RAT_LE x y`. */
  val LessWeakens: String = "RAT_LT_LE"

  /** `|- !c x y. RAT_LE RAT_ZERO c ==> RAT_LE x y ==> RAT_LE (RAT_MUL c x) (RAT_MUL c y)`. */
  val MulLeftMonotone: String = "RAT_LE_MUL_LEFT"

  /** `|- !x. RAT_LT RAT_ZERO x ==> RAT_LT RAT_ZERO (RAT_INV x)`. */
  val InversePositive: String = "RAT_INV_POS"

  /** `|- RAT_OF_NUM ZERO = RAT_ZERO`. */
  val OfNumberZero: String = "RAT_OF_NUM_ZERO"

  /** `|- !n. RAT_OF_NUM (SUC n) = RAT_ADD (RAT_OF_NUM n) RAT_ONE`. */
  val OfNumberSuccessor: String = "RAT_OF_NUM_SUC"

  /** `|- !n. RAT_LE RAT_ZERO (RAT_OF_NUM n)`. */
  val OfNumberNonNegative: String = "RAT_OF_NUM_NONNEG"

  /** `|- !x. ?n. RAT_LE x (RAT_OF_NUM n)`: the rationals are Archimedean. */
  val Archimedes: String = "RAT_ARCHIMEDES"

  /** `|- !e. RAT_LT RAT_ZERO e ==> ?n. RAT_LT (RAT_INV (RAT_OF_NUM (SUC n))) e`: the form a cut spends. */
  val ArchimedesInverse: String = "RAT_ARCHIMEDES_INV"

  /** `|- !x y. RAT_LT x y ==> ?z. RAT_LT x z /\ RAT_LT z y`: the rationals are dense. */
  val Dense: String = "RAT_DENSE"

  private val LessBody: String = "\\x:rat. \\y:rat. ~(RAT_LE y x)"
  private val OfNumberBody: String = "\\n:num. RAT_OF_PAIR (PAIR (INT_OF_NUM n) ZERO)"

  private val InverseBody: String =
    "\\x:rat. COND (x = RAT_ZERO) RAT_ZERO (select (\\y:rat. RAT_MUL x y = RAT_ONE))"
  val OneNotAtMostZero: String = "RAT_NOT_ONE_LE_ZERO"

  /** `(a, d) + (b, e) = (a * (e + 1) + b * (d + 1), d * e + d + e)`, over the pair's own projections. */
  private val AddBody: String =
    "\\p:prod(int,num). \\q:prod(int,num). " +
      "PAIR (INT_ADD (INT_MUL (FST p) (INT_OF_NUM (SUC (SND q)))) (INT_MUL (FST q) (INT_OF_NUM (SUC (SND p))))) " +
      "(SND p * SND q + SND p + SND q)"

  /** `(a, d) * (b, e) = (a * b, d * e + d + e)`. */
  private val MulBody: String =
    "\\p:prod(int,num). \\q:prod(int,num). PAIR (INT_MUL (FST p) (FST q)) (SND p * SND q + SND p + SND q)"

  /** `-(a, d) = (-a, d)`. */
  private val NegBody: String = "\\p:prod(int,num). PAIR (INT_NEG (FST p)) (SND p)"

  /** `0/1` and `1/1`, where the stored index `ZERO` is the denominator `SUC ZERO`. */
  private val ZeroBody: String = "RAT_OF_PAIR (PAIR INT_ZERO ZERO)"
  private val OneBody: String = "RAT_OF_PAIR (PAIR INT_ONE ZERO)"

  /** The cross-multiplied order at two pairs, which is the text every statement about it reads. */
  private def crossed(p: String, q: String): String =
    s"INT_LE (INT_MUL (FST $p) (INT_OF_NUM (SUC (SND $q)))) (INT_MUL (FST $q) (INT_OF_NUM (SUC (SND $p))))"

  private val AtMostBody: String =
    "\\x:rat. \\y:rat. " + crossed("(RAT_OF_PAIR_repr x)", "(RAT_OF_PAIR_repr y)")

  val Names: Quotient.Names =
    Quotient.Names(
      typeName = TypeName,
      abstraction = Abstraction,
      representation = Representation,
      projection = Projection
    )

  private val SameBody: String =
    "\\p:prod(int,num). \\q:prod(int,num). " +
      "INT_MUL (FST p) (INT_OF_NUM (SUC (SND q))) = INT_MUL (FST q) (INT_OF_NUM (SUC (SND p)))"

  /** Every statement this development publishes, as the text a reader checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    SwapFactors -> "!x:int. !y:int. !z:int. INT_MUL (INT_MUL x y) z = INT_MUL (INT_MUL x z) y",
    SameReflexive -> "!p:prod(int,num). RAT_SAME p p",
    SameSymmetric -> "!p:prod(int,num). !q:prod(int,num). RAT_SAME p q ==> RAT_SAME q p",
    SameTransitive ->
      ("!p:prod(int,num). !q:prod(int,num). !r:prod(int,num). " +
        "RAT_SAME p q ==> RAT_SAME q r ==> RAT_SAME p r"),
    Denominator ->
      "!d:num. !e:num. INT_OF_NUM (SUC (d * e + d + e)) = INT_MUL (INT_OF_NUM (SUC d)) (INT_OF_NUM (SUC e))",
    AddPairs ->
      ("!p:prod(int,num). !q:prod(int,num). RAT_ADD (RAT_OF_PAIR p) (RAT_OF_PAIR q) = RAT_OF_PAIR " +
        "(PAIR (INT_ADD (INT_MUL (FST p) (INT_OF_NUM (SUC (SND q)))) (INT_MUL (FST q) (INT_OF_NUM (SUC (SND p))))) " +
        "(SND p * SND q + SND p + SND q))"),
    NegPair -> "!p:prod(int,num). RAT_NEG (RAT_OF_PAIR p) = RAT_OF_PAIR (PAIR (INT_NEG (FST p)) (SND p))",
    MulPairs ->
      ("!p:prod(int,num). !q:prod(int,num). RAT_MUL (RAT_OF_PAIR p) (RAT_OF_PAIR q) = RAT_OF_PAIR " +
        "(PAIR (INT_MUL (FST p) (FST q)) (SND p * SND q + SND p + SND q))"),
    AddCommutative -> "!x:rat. !y:rat. RAT_ADD x y = RAT_ADD y x",
    MulCommutative -> "!x:rat. !y:rat. RAT_MUL x y = RAT_MUL y x",
    AddAssociative -> "!x:rat. !y:rat. !z:rat. RAT_ADD (RAT_ADD x y) z = RAT_ADD x (RAT_ADD y z)",
    AddAtZero -> "!x:rat. RAT_ADD x RAT_ZERO = x",
    AddNegation -> "!x:rat. RAT_ADD x (RAT_NEG x) = RAT_ZERO",
    MulAssociative -> "!x:rat. !y:rat. !z:rat. RAT_MUL (RAT_MUL x y) z = RAT_MUL x (RAT_MUL y z)",
    MulAtOne -> "!x:rat. RAT_MUL x RAT_ONE = x",
    Distributive ->
      "!x:rat. !y:rat. !z:rat. RAT_MUL x (RAT_ADD y z) = RAT_ADD (RAT_MUL x y) (RAT_MUL x z)",
    UnitsDistinct -> "~(RAT_ZERO = RAT_ONE)",
    IntAtMostScaled ->
      "!a:int. !b:int. !n:num. INT_LE a b ==> INT_LE (INT_MUL a (INT_OF_NUM n)) (INT_MUL b (INT_OF_NUM n))",
    IntAtMostCancels ->
      ("!a:int. !b:int. !d:num. INT_LE (INT_MUL a (INT_OF_NUM (SUC d))) (INT_MUL b (INT_OF_NUM (SUC d))) " +
        "==> INT_LE a b"),
    AtMostRespects ->
      ("!p:prod(int,num). !q:prod(int,num). !r:prod(int,num). !s:prod(int,num). " +
        "RAT_SAME p r ==> RAT_SAME q s ==> " + crossed("p", "q") + " ==> " + crossed("r", "s")),
    AtMostPairs ->
      ("!p:prod(int,num). !q:prod(int,num). RAT_LE (RAT_OF_PAIR p) (RAT_OF_PAIR q) = " + crossed("p", "q")),
    AtMostReflexive -> "!x:rat. RAT_LE x x",
    AtMostTransitive -> "!x:rat. !y:rat. !z:rat. RAT_LE x y ==> RAT_LE y z ==> RAT_LE x z",
    AtMostAntisymmetric -> "!x:rat. !y:rat. RAT_LE x y ==> RAT_LE y x ==> x = y",
    AtMostTotal -> "!x:rat. !y:rat. RAT_LE x y \\/ RAT_LE y x",
    ZeroAtMostOne -> "RAT_LE RAT_ZERO RAT_ONE",
    OneNotAtMostZero -> "~(RAT_LE RAT_ONE RAT_ZERO)",
    IntSign -> "!a:int. (?n:num. a = INT_OF_NUM n) \\/ (?n:num. a = INT_NEG (INT_OF_NUM n))",
    IntNonNegative -> "!a:int. INT_LE INT_ZERO a ==> (?n:num. a = INT_OF_NUM n)",
    IntMulNonNegative ->
      "!a:int. !b:int. INT_LE INT_ZERO a ==> INT_LE INT_ZERO b ==> INT_LE INT_ZERO (INT_MUL a b)",
    AtMostAdd -> "!x:rat. !y:rat. !z:rat. RAT_LE x y ==> RAT_LE (RAT_ADD x z) (RAT_ADD y z)",
    AtMostMul -> "!x:rat. !y:rat. RAT_LE RAT_ZERO x ==> RAT_LE RAT_ZERO y ==> RAT_LE RAT_ZERO (RAT_MUL x y)",
    InverseExists -> "!x:rat. ~(x = RAT_ZERO) ==> (?y:rat. RAT_MUL x y = RAT_ONE)",
    MulInverse -> "!x:rat. ~(x = RAT_ZERO) ==> RAT_MUL x (RAT_INV x) = RAT_ONE",
    InverseAtZero -> "RAT_INV RAT_ZERO = RAT_ZERO",
    LessWeakens -> "!x:rat. !y:rat. RAT_LT x y ==> RAT_LE x y",
    MulLeftMonotone ->
      "!c:rat. !x:rat. !y:rat. RAT_LE RAT_ZERO c ==> RAT_LE x y ==> RAT_LE (RAT_MUL c x) (RAT_MUL c y)",
    InversePositive -> "!x:rat. RAT_LT RAT_ZERO x ==> RAT_LT RAT_ZERO (RAT_INV x)",
    OfNumberZero -> "RAT_OF_NUM ZERO = RAT_ZERO",
    OfNumberSuccessor -> "!n:num. RAT_OF_NUM (SUC n) = RAT_ADD (RAT_OF_NUM n) RAT_ONE",
    OfNumberNonNegative -> "!n:num. RAT_LE RAT_ZERO (RAT_OF_NUM n)",
    Archimedes -> "!x:rat. ?n:num. RAT_LE x (RAT_OF_NUM n)",
    ArchimedesInverse -> "!e:rat. RAT_LT RAT_ZERO e ==> (?n:num. RAT_LT (RAT_INV (RAT_OF_NUM (SUC n))) e)",
    Dense -> "!x:rat. !y:rat. RAT_LT x y ==> (?z:rat. RAT_LT x z /\\ RAT_LT z y)"
  )

  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val integers: Type = TyApp(Integer.TypeName, Nil)

  /** The carrier: a numerator and the predecessor of a denominator. */
  val Pairs: Type = TyApp(Product.TypeName, List(integers, numbers))

  /** The type this development defines. */
  val Classes: Type = TyApp(TypeName, Nil)

  private val p: FVar = Term.variable("p", Pairs)
  private val q: FVar = Term.variable("q", Pairs)
  private val r: FVar = Term.variable("r", Pairs)

  /* ------------------------------------------------------------------ the construction */

  /** Over the development that holds the integers, which is where the carrier's arithmetic is. */
  def construct(classical: Classical, integer: Integer, product: Product, peano: Peano): Either[LogicError, Fraction] =
    construct(classical, integer, product, peano, integer.theory, integer.notation)

  /**
   * The same, extending a theory that already holds something else, which is the chain's entry
   * point when this development joins it.
   */
  def construct(
    classical: Classical,
    integer: Integer,
    product: Product,
    peano: Peano,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Fraction] =
    for {
      sameBody <- Parser.term(base, notation, SameBody)
      sameDefined <- LogicError.lift(Kernel.defineConstant(base, SameName, sameBody))
      (withSame, sameDefinition) = sameDefined

      logic <- classical.logic.over(withSame)
      projections <- Vector(product.fact(Product.FirstOfPair), product.fact(Product.SecondOfPair))
        .foldRight[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
          case (next, rest) => next.flatMap(one => rest.map(one +: _))
        }
        .flatMap(Rewrite.Rule.all(logic, _))

      swap <- swapFactors(logic, withSame, notation, integer)
      reflexive <- sameReflexive(logic, sameDefinition, projections)
      symmetric <- sameSymmetric(logic, sameDefinition, projections)
      transitive <- sameTransitive(logic, withSame, notation, integer, sameDefinition, projections, swap)

      relation <- LogicError.lift(
        withSame.constant(SameName, Type.fun(Pairs, Type.fun(Pairs, Type.Bool)))
      )
      quotient <- Quotient.define(
        classical,
        withSame,
        notation,
        Names,
        Quotient.Equivalence(relation, reflexive, symmetric, transitive)
      )

      arithmetic <- Lifting.over(logic, withSame, notation, integer, peano, sameDefinition, projections)
      addOperation <- Parser.term(withSame, notation, AddBody)
      negOperation <- Parser.term(withSame, notation, NegBody)
      mulOperation <- Parser.term(withSame, notation, MulBody)

      // With `a * D1 = a1 * D` and `b * E1 = b1 * E` as the premises, the sum's cross-multiplication
      // follows with the coefficients `E * E1` and `D * D1`, and the product's with `b * E1` and
      // `a1 * D`: those are the whole of the arithmetic, and a wrong one is refused by the ring.
      // (Indices rather than primes, because the language census reads a capital and an apostrophe
      // as a truncated accent.)
      addRespects <- arithmetic.binaryRespects(
        addOperation,
        "INT_MUL (INT_OF_NUM (SUC (SND (y:prod(int,num))))) (INT_OF_NUM (SUC (SND (v:prod(int,num)))))",
        "INT_MUL (INT_OF_NUM (SUC (SND (x:prod(int,num))))) (INT_OF_NUM (SUC (SND (u:prod(int,num)))))"
      )
      withAddition <- quotient.liftBinary(Addition, addOperation, addRespects)
      (afterAddition, addPairs) = withAddition
      negRespects <- arithmetic.unaryRespects(negOperation, "INT_NEG INT_ONE")
      withNegation <- afterAddition.liftUnary(Negation, negOperation, negRespects)
      (afterNegation, negPair) = withNegation
      mulRespects <- arithmetic.binaryRespects(
        mulOperation,
        "INT_MUL (FST (y:prod(int,num))) (INT_OF_NUM (SUC (SND (v:prod(int,num)))))",
        "INT_MUL (FST (u:prod(int,num))) (INT_OF_NUM (SUC (SND (x:prod(int,num)))))"
      )
      withMultiplication <- afterNegation.liftBinary(Multiplication, mulOperation, mulRespects)
      (complete, mulPairs) = withMultiplication
      addSymmetric <- arithmetic.commutative(complete, Addition, addOperation, addPairs)
      mulSymmetric <- arithmetic.commutative(complete, Multiplication, mulOperation, mulPairs)

      zeroBody <- Parser.term(complete.theory, notation, ZeroBody)
      zeroDefined <- LogicError.lift(Kernel.defineConstant(complete.theory, Zero, zeroBody))
      (withZero, zeroDefinition) = zeroDefined
      oneBody <- Parser.term(withZero, notation, OneBody)
      oneDefined <- LogicError.lift(Kernel.defineConstant(withZero, One, oneBody))
      (whole, oneDefinition) = oneDefined
      widened <- complete.over(whole)
      laws <- arithmetic.laws(widened, Vector(addPairs, negPair, mulPairs, zeroDefinition, oneDefinition))
      distinct <- arithmetic.unitsDistinct(widened, zeroDefinition, oneDefinition, integer, peano)

      atMostBody <- Parser.term(whole, notation, AtMostBody)
      atMostDefined <- LogicError.lift(Kernel.defineConstant(whole, AtMost, atMostBody))
      (ordered, atMostDefinition) = atMostDefined
      orderedQuotient <- widened.over(ordered)
      ordering = Ordering(orderedQuotient, notation, arithmetic, integer, peano)
      order <- ordering.facts(atMostDefinition, zeroDefinition, oneDefinition, symmetric)

      // The ordered field: the sign of an integer under the order's two compatibilities, then the
      // inverse, which is defined over the order's theory and so needs a quotient over its own.
      atPairsLaw <- order.collectFirst { case (AtMostPairs, law) => law }.toRight(MissingDefinition(AtMostPairs))
      scaledLaw <- order.collectFirst { case (IntAtMostScaled, law) => law }.toRight(MissingDefinition(IntAtMostScaled))
      sign <- ordering.intSign
      nonNegative <- ordering.intNonNegative(sign)
      productNonNegative <- ordering.intMulNonNegative(nonNegative, scaledLaw)
      addMonotone <- ordering.addMonotone(atPairsLaw, scaledLaw, addOperation, addPairs)
      mulNonNegative <- ordering.mulNonNegative(atPairsLaw, zeroDefinition, mulOperation, mulPairs, productNonNegative)
      inverseBody <- Parser.term(ordered, notation, InverseBody)
      inverseDefined <- LogicError.lift(Kernel.defineConstant(ordered, Inverse, inverseBody))
      (fielded, inverseDefinition) = inverseDefined
      fieldQuotient <- orderedQuotient.over(fielded)
      inverses <- Ordering(fieldQuotient, notation, arithmetic, integer, peano)
        .inverse(inverseDefinition, zeroDefinition, oneDefinition, mulOperation, mulPairs, sign)
      (inverseExists, mulInverse, inverseAtZero) = inverses
      field = Vector(
        (IntSign, sign),
        (IntNonNegative, nonNegative),
        (IntMulNonNegative, productNonNegative),
        (AtMostAdd, addMonotone),
        (AtMostMul, mulNonNegative),
        (InverseExists, inverseExists),
        (MulInverse, mulInverse),
        (InverseAtZero, inverseAtZero)
      )

      proved = Vector(
        (SwapFactors, swap),
        (SameReflexive, reflexive),
        (SameSymmetric, symmetric),
        (SameTransitive, transitive),
        (Denominator, arithmetic.denominator),
        (AddPairs, addPairs),
        (NegPair, negPair),
        (MulPairs, mulPairs),
        (AddCommutative, addSymmetric),
        (MulCommutative, mulSymmetric)
      ) ++ laws ++ ((UnitsDistinct, distinct) +: order) ++ field

      // Archimedes and density, over the strict order and the naturals inside `rat`, which are
      // two definitions over the field's theory. `Density` is the derivation.
      lessBody <- Parser.term(fielded, notation, LessBody)
      lessDefined <- LogicError.lift(Kernel.defineConstant(fielded, LessThan, lessBody))
      (withLess, lessDefinition) = lessDefined
      numberBody <- Parser.term(withLess, notation, OfNumberBody)
      numberDefined <- LogicError.lift(Kernel.defineConstant(withLess, OfNumber, numberBody))
      (dense, numberDefinition) = numberDefined
      denseQuotient <- fieldQuotient.over(dense)
      density <- Density(
        denseQuotient, notation, arithmetic, integer, peano, proved.toMap,
        zeroDefinition, oneDefinition, lessDefinition, numberDefinition
      ).facts

      checked <- (proved ++ density).foldRight[Either[LogicError, Vector[(String, Kernel.Thm)]]](Right(Vector.empty)) {
        case ((name, theorem), rest) =>
          for {
            statement <- Parser.proposition(dense, notation, statementOf(name))
            _ <-
              if (theorem.conclusion == statement) Right(())
              else Left(NotOfForm(s"the statement published for $name", theorem.conclusion))
            _ <-
              if (theorem.hypotheses.isEmpty) Right(())
              else Left(NotOfForm(s"$name with nothing assumed", theorem.conclusion))
            more <- rest
          } yield (name, theorem) +: more
      }
    } yield new Fraction(
      classical,
      integer,
      dense,
      notation,
      denseQuotient,
      Map(
        SameName -> sameDefinition,
        Zero -> zeroDefinition,
        One -> oneDefinition,
        AtMost -> atMostDefinition,
        Inverse -> inverseDefinition,
        LessThan -> lessDefinition,
        OfNumber -> numberDefinition
      ) ++
        complete.definitions,
      checked.toMap
    )

  private def statementOf(name: String): String =
    Statements.collectFirst { case (key, text) if key == name => text }.getOrElse(name)

  /* ------------------------------------------------------------------ the equivalence */

  /**
   * `|- !x y z. (x * y) * z = (x * z) * y` over `int`, by associativity and commutativity.
   *
   * Three steps and no procedure, which is the paragraph in this file's opening made concrete:
   * over `num` this is one call to `Semiring` and over the reals one call to `Ring`, and over
   * `int` it is associativity forwards, commutativity under a congruence, and associativity
   * backwards.
   */
  private def swapFactors(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    integer: Integer
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", integers)
    val y = Term.variable("y", integers)
    val z = Term.variable("z", integers)

    for {
      times <- LogicError.lift(
        theory.constant(Integer.Multiplication, Type.fun(integers, Type.fun(integers, integers)))
      )
      associative <- integer.fact(Integer.MulAssociative)
      commutative <- integer.fact(Integer.MulCommutative)

      opened <- rules.specAll(associative, List(x, y, z))
      inner <- rules.specAll(commutative, List(y, z))
      underX <- LogicError.lift(Term.app(times, x)).flatMap(Conv.apTerm(_, inner))
      swapped <- Conv.trans(opened, underX)
      closed <- rules.specAll(associative, List(x, z, y)).flatMap(Conv.sym)
      result <- Conv.trans(swapped, closed).flatMap(rules.genAll(_, List(x, y, z)))
    } yield result
  }

  /** `|- !p. RAT_SAME p p`: the unfolded relation is an equation between a term and itself. */
  private def sameReflexive(
    logic: Logic,
    definition: Kernel.Thm,
    projections: Vector[Rewrite.Rule]
  ): Either[LogicError, Kernel.Thm] =
    for {
      unfolded <- unfoldedAt(definition, projections, p, p)
      sides <- sidesOf(unfolded)
      folded <- fold(unfolded, Conv.refl(sides._1))
      result <- logic.rules.gen(p, folded)
    } yield result

  /** `|- !p q. RAT_SAME p q ==> RAT_SAME q p`: symmetry of the relation is symmetry of the equation. */
  private def sameSymmetric(
    logic: Logic,
    definition: Kernel.Thm,
    projections: Vector[Rewrite.Rule]
  ): Either[LogicError, Kernel.Thm] =
    for {
      forwards <- unfoldedAt(definition, projections, p, q)
      backwards <- unfoldedAt(definition, projections, q, p)
      premise <- leftOf(forwards)
      assumed <- LogicError.lift(Kernel.assume(premise))
      equation <- LogicError.lift(Kernel.eqMp(forwards, assumed))
      flipped <- Conv.sym(equation)
      folded <- fold(backwards, flipped)
      discharged <- logic.rules.disch(premise, folded)
      result <- logic.rules.genAll(discharged, List(p, q))
    } yield result

  /**
   * `|- !p q r. RAT_SAME p q ==> RAT_SAME q r ==> RAT_SAME p r`, and the arithmetic is one
   * cancellation.
   *
   * With `p = (A, a)`, `q = (B, b)` and `r = (C, c)`, and writing `S x` for
   * `INT_OF_NUM (SUC x)`, the premises are `A * S b = B * S a` and `B * S c = C * S b` and the
   * conclusion is `A * S c = C * S a`. Multiplying the first by `S c` and the second by `S a`
   * gives two equations whose middles agree once the factors are swapped, so the chain
   *
   *     (A * S c) * S b = (A * S b) * S c = (B * S a) * S c = (B * S c) * S a
   *                     = (C * S b) * S a = (C * S a) * S b
   *
   * closes it up to the factor `S b`, which `Integer.INT_MUL_CANCEL_NUM` takes off. Every step of
   * it is [[SwapFactors]] or one of the two premises, which is why that lemma is published: a
   * reader checks the argument by reading the chain, and the chain is five rearrangements.
   *
   * **The cancellation is where the denominator being a successor is spent**, and it is the only
   * place in the file where it is: reflexivity and symmetry hold of the cross-multiplication
   * whatever the second component is. That is the sentence `docs/adr/0036` rests on, and this
   * derivation is what would fail if the carrier were pairs of integers.
   */
  private def sameTransitive(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    integer: Integer,
    definition: Kernel.Thm,
    projections: Vector[Rewrite.Rule],
    swap: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      first <- unfoldedAt(definition, projections, p, q)
      second <- unfoldedAt(definition, projections, q, r)
      target <- unfoldedAt(definition, projections, p, r)

      firstPremise <- leftOf(first)
      secondPremise <- leftOf(second)
      firstAssumed <- LogicError.lift(Kernel.assume(firstPremise))
      secondAssumed <- LogicError.lift(Kernel.assume(secondPremise))
      firstEquation <- LogicError.lift(Kernel.eqMp(first, firstAssumed))
      secondEquation <- LogicError.lift(Kernel.eqMp(second, secondAssumed))

      times <- LogicError.lift(
        theory.constant(Integer.Multiplication, Type.fun(integers, Type.fun(integers, integers)))
      )

      // The three denominators, as the terms the premises are written with.
      numeratorOfP <- leftFactorOf(firstEquation)
      denominatorOfQ <- rightFactorOf(firstEquation)
      numeratorOfQ <- secondFactorOfRight(firstEquation)
      denominatorOfP <- rightFactorOfRight(firstEquation)
      numeratorOfR <- secondFactorOfRight(secondEquation)
      denominatorOfR <- rightFactorOf(secondEquation)

      // `(A * S b) * S c = (B * S a) * S c` and `(B * S c) * S a = (C * S b) * S a`.
      firstScaled <- Conv.apTerm(times, firstEquation).flatMap(Conv.apThm(_, denominatorOfR))
      secondScaled <- Conv.apTerm(times, secondEquation).flatMap(Conv.apThm(_, denominatorOfP))

      // The chain, five rearrangements and the two premises.
      openLeft <- rules.specAll(swap, List(numeratorOfP, denominatorOfR, denominatorOfQ))
      middleLeft <- rules.specAll(swap, List(numeratorOfQ, denominatorOfP, denominatorOfR))
      closeRight <- rules.specAll(swap, List(numeratorOfR, denominatorOfQ, denominatorOfP))

      chained <- Conv
        .trans(openLeft, firstScaled)
        .flatMap(Conv.trans(_, middleLeft))
        .flatMap(Conv.trans(_, secondScaled))
        .flatMap(Conv.trans(_, closeRight))

      // `S b` off both sides, which is the only arithmetic in the file.
      index <- indexOf(denominatorOfQ)
      cancelled <- integer
        .fact(Integer.CancelsPositive)
        .flatMap(rules.specAll(_, List(leftOfProduct(chained), rightOfProduct(chained), index)))
        .flatMap(rules.mp(_, chained))

      folded <- fold(target, cancelled)
      dischargedSecond <- rules.disch(secondPremise, folded)
      discharged <- rules.disch(firstPremise, dischargedSecond)
      result <- rules.genAll(discharged, List(p, q, r))
    } yield result
  }

  /* ------------------------------------------------------------------ the small readings */

  /** `|- RAT_SAME s t = (… = …)`, with `FST (PAIR a b)` reduced away where there is one. */
  private def unfoldedAt(
    definition: Kernel.Thm,
    projections: Vector[Rewrite.Rule],
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      unfolded <- Conv.unfold(definition, List(left, right))
      reduced <- Rewrite.inTheorem(projections, unfolded)
    } yield reduced

  /** `|- RAT_SAME s t` from the equation the unfolding produces, and from nothing else. */
  private def fold(unfolded: Kernel.Thm, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv.sym(unfolded).flatMap(back => LogicError.lift(Kernel.eqMp(back, equation)))

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))

  /**
   * The two sides of the equation **under** the relation, which is what the unfolding produces.
   *
   * Not the two sides of the unfolding itself: those are the relation and the equation, and
   * reflexivity of the first is what a caller reaching for this by mistake gets. `Integer` draws
   * the same distinction at the same place and this file got it wrong once before copying it.
   */
  private def sidesOf(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
    for {
      body <- Term
        .destEq(theorem.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", theorem.conclusion))
      sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
    } yield sides

  /** `A` of `A * S b = …`. */
  private def leftFactorOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    theorem.conclusion match {
      case App(App(_, App(App(_, left), _)), _) => Right(left)
      case other => Left(NotOfForm("an equation between two products", other))
    }

  /** `S b` of `A * S b = …`. */
  private def rightFactorOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    theorem.conclusion match {
      case App(App(_, App(App(_, _), right)), _) => Right(right)
      case other => Left(NotOfForm("an equation between two products", other))
    }

  /** `B` of `… = B * S a`. */
  private def secondFactorOfRight(theorem: Kernel.Thm): Either[LogicError, Term] =
    theorem.conclusion match {
      case App(_, App(App(_, left), _)) => Right(left)
      case other => Left(NotOfForm("an equation between two products", other))
    }

  /** `S a` of `… = B * S a`. */
  private def rightFactorOfRight(theorem: Kernel.Thm): Either[LogicError, Term] =
    theorem.conclusion match {
      case App(_, App(App(_, _), right)) => Right(right)
      case other => Left(NotOfForm("an equation between two products", other))
    }

  /** `d` of `INT_OF_NUM (SUC d)`, which is what the cancellation is specialised at. */
  private def indexOf(denominator: Term): Either[LogicError, Term] =
    denominator match {
      case App(_, App(_, index)) => Right(index)
      case other => Left(NotOfForm("an embedded successor", other))
    }

  /** The two products either side of the chain, which the cancellation is about. */
  private def leftOfProduct(theorem: Kernel.Thm): Term =
    theorem.conclusion match {
      case App(App(_, App(App(_, left), _)), _) => left
      case _ => theorem.conclusion
    }

  private def rightOfProduct(theorem: Kernel.Thm): Term =
    theorem.conclusion match {
      case App(_, App(App(_, left), _)) => left
      case _ => theorem.conclusion
    }

  /* ------------------------------------------------------------------ the arithmetic */

  /**
   * The obligations the three lifts owe, closed by the ring of `int`: which is what `Integer.ring`
   * was built for, and the decision of 2026-09-25 (Mycelium card `fa8737ad`) that the procedure be
   * generalised rather than each obligation derived by hand.
   *
   * Every obligation is one shape. Unfold the relation at the two results and read the pairs'
   * projections off; turn the stored denominator `SUC (d * e + d + e)` into the product
   * `SUC d * SUC e` with [[Fraction.Denominator]]; and what is left is an equation of `int` that follows from
   * the premises by substitution, which `CommutativeRing.consequence` decides given the
   * coefficient each premise is scaled by.
   */
  private[theories] final case class Lifting(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definition: Kernel.Thm,
    projections: Vector[Rewrite.Rule],
    denominators: Vector[Rewrite.Rule],
    denominator: Kernel.Thm,
    embeddedOne: Kernel.Thm,
    ring: CommutativeRing
  ) {
    private val rules = logic.rules
    private val x: FVar = Term.variable("x", Pairs)
    private val y: FVar = Term.variable("y", Pairs)
    private val u: FVar = Term.variable("u", Pairs)
    private val v: FVar = Term.variable("v", Pairs)

    private def read(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)

    private def reduced(operation: Term, arguments: Term*): Either[LogicError, Term] =
      for {
        applied <- LogicError.lift(Term.appAll(operation, arguments.toList))
        equation <- Conv.betaNormalise(applied)
        sides <- Term.destEq(equation.conclusion).toRight(NotOfForm("an equation", equation.conclusion))
      } yield sides._2

    /** The premise `RAT_SAME s t`, assumed, and the equation it unfolds to. */
    private def premise(left: Term, right: Term): Either[LogicError, (Term, Kernel.Thm)] =
      for {
        unfolded <- unfoldedAt(definition, projections, left, right)
        statement <- leftOf(unfolded)
        assumed <- LogicError.lift(Kernel.assume(statement))
        equation <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      } yield (statement, equation)

    /** `|- RAT_SAME s t` from the premises, scaled by the coefficients, with denominators read back. */
    def related(left: Term, right: Term, premises: List[(Kernel.Thm, Term)]): Either[LogicError, Kernel.Thm] =
      for {
        target <- unfoldedAt(definition, projections, left, right)
        sides <- sidesOf(target)
        leftRead <- Rewrite.rewrite(denominators, sides._1)
        rightRead <- Rewrite.rewrite(denominators, sides._2)
        leftForm <- rightOfTheorem(leftRead)
        rightForm <- rightOfTheorem(rightRead)
        core <- ring.consequence(leftForm, rightForm, premises)
        equation <- Conv.sym(rightRead).flatMap(back => Conv.trans(leftRead, core).flatMap(Conv.trans(_, back)))
        folded <- fold(target, equation)
      } yield folded

    /** `|- !x y u v. RAT_SAME x u ==> RAT_SAME y v ==> RAT_SAME (f x y) (f u v)`. */
    def binaryRespects(operation: Term, first: String, second: String): Either[LogicError, Kernel.Thm] =
      for {
        firstPremise <- premise(x, u)
        secondPremise <- premise(y, v)
        firstCoefficient <- read(first)
        secondCoefficient <- read(second)
        left <- reduced(operation, x, y)
        right <- reduced(operation, u, v)
        folded <- related(left, right, List(firstPremise._2 -> firstCoefficient, secondPremise._2 -> secondCoefficient))
        discharged <- rules.disch(secondPremise._1, folded).flatMap(rules.disch(firstPremise._1, _))
        result <- rules.genAll(discharged, List(x, y, u, v))
      } yield result

    /** `|- !x y. RAT_SAME x y ==> RAT_SAME (f x) (f y)`. */
    def unaryRespects(operation: Term, coefficient: String): Either[LogicError, Kernel.Thm] =
      for {
        only <- premise(x, y)
        scale <- read(coefficient)
        left <- reduced(operation, x)
        right <- reduced(operation, y)
        folded <- related(left, right, List(only._2 -> scale))
        discharged <- rules.disch(only._1, folded)
        result <- rules.genAll(discharged, List(x, y))
      } yield result

    /**
     * `|- !p q. g p q = g q p` for a lifted operation `g`, from the pair form being symmetric up to
     * the relation: every class is a projection, and two projections are equal exactly where their
     * pairs are related.
     */
    def commutative(quotient: Quotient, name: String, operation: Term, pairs: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val wide = quotient.logic.rules
      val p = Term.variable("p", Classes)
      val q = Term.variable("q", Classes)
      for {
        lifted <- LogicError.lift(quotient.theory.constant(name, Type.fun(Classes, Type.fun(Classes, Classes))))
        onto <- quotient.fact(Quotient.ProjectionOnto)
        equal <- quotient.fact(Quotient.ProjectionEqual)
        atP <- wide.spec(p, onto)
        atQ <- wide.spec(q, onto)
        pIs <- quotient.logic.destExistsPredicate(atP.conclusion).toRight(NotOfForm("an existential", atP.conclusion))
          .flatMap(pred => LogicError.lift(Term.app(pred, x))).flatMap(Conv.betaRoot).flatMap(rightOfTheorem)
        qIs <- quotient.logic.destExistsPredicate(atQ.conclusion).toRight(NotOfForm("an existential", atQ.conclusion))
          .flatMap(pred => LogicError.lift(Term.app(pred, y))).flatMap(Conv.betaRoot).flatMap(rightOfTheorem)
        hp <- LogicError.lift(Kernel.assume(pIs))
        hq <- LogicError.lift(Kernel.assume(qIs))
        forwards <- wide.specAll(pairs, List(x, y))
        backwards <- wide.specAll(pairs, List(y, x))
        left <- reduced(operation, x, y)
        right <- reduced(operation, y, x)
        sameResults <- related(left, right, Nil)
        projectionsEqual <- wide.specAll(equal, List(left, right))
          .flatMap(eqn => Conv.sym(eqn))
          .flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, sameResults)))
        onClasses <- Conv.apTerm(lifted, hp).flatMap(partial => LogicError.lift(Kernel.mkComb(partial, hq)))
        swappedClasses <- Conv.apTerm(lifted, hq).flatMap(partial => LogicError.lift(Kernel.mkComb(partial, hp)))
        chain <- Conv.trans(onClasses, forwards)
          .flatMap(Conv.trans(_, projectionsEqual))
          .flatMap(step => Conv.sym(backwards).flatMap(Conv.trans(step, _)))
          .flatMap(step => Conv.sym(swappedClasses).flatMap(Conv.trans(step, _)))
        openedQ <- wide.existsElim(atQ, y, chain)
        openedP <- wide.existsElim(atP, x, openedQ)
        result <- wide.genAll(openedP, List(p, q))
      } yield result
    }

    /**
     * The laws of the ring on classes, each by the route `Integer.Laws` takes one quotient down.
     *
     * A law is written at `RAT_OF_PAIR p` rather than at a class variable, because the route needs
     * a pair to rewrite to: the three lifts and the two constants' definitions bring each side to
     * `RAT_OF_PAIR` of one pair, the two pairs are related by the ring of `int` with no premise at
     * all, and the quotient's central fact turns the relation into the equation of the classes. The
     * representative the quotient chose for each class is what the pair variables are specialised
     * at in the end, which is what puts the statement back over `rat`.
     *
     * The one law that needs more than the lifts is `x * 1 = x`. A constant stores the index
     * `ZERO`, so the product's denominator reads `SUC d * SUC ZERO`, and the ring treats
     * `INT_OF_NUM (SUC ZERO)` as an atom it knows nothing about: the second rule in `denominators`
     * reads it as `INT_ONE`. Measured on 2026-09-25 with that rule removed: the construction was
     * refused at `RAT_MUL_ONE`, naming the two products, and the four laws built before it held,
     * `x + 0 = x` among them, because there the atom stands on both sides of the cross-multiplication.
     */
    def laws(quotient: Quotient, lifts: Vector[Kernel.Thm]): Either[LogicError, Vector[(String, Kernel.Thm)]] = {
      val wide = quotient.logic
      val p = Term.variable("p", Pairs)
      val q = Term.variable("q", Pairs)
      val r = Term.variable("r", Pairs)
      val x = Term.variable("x", Classes)
      val y = Term.variable("y", Classes)
      val z = Term.variable("z", Classes)
      val one = List(p) -> List(x)
      val three = List(p, q, r) -> List(x, y, z)
      val texts: Vector[(String, String, String, (List[FVar], List[FVar]))] = Vector(
        (AddAssociative,
          "RAT_ADD (RAT_ADD (RAT_OF_PAIR p) (RAT_OF_PAIR q)) (RAT_OF_PAIR r)",
          "RAT_ADD (RAT_OF_PAIR p) (RAT_ADD (RAT_OF_PAIR q) (RAT_OF_PAIR r))", three),
        (AddAtZero, "RAT_ADD (RAT_OF_PAIR p) RAT_ZERO", "RAT_OF_PAIR p", one),
        (AddNegation, "RAT_ADD (RAT_OF_PAIR p) (RAT_NEG (RAT_OF_PAIR p))", "RAT_ZERO", one),
        (MulAssociative,
          "RAT_MUL (RAT_MUL (RAT_OF_PAIR p) (RAT_OF_PAIR q)) (RAT_OF_PAIR r)",
          "RAT_MUL (RAT_OF_PAIR p) (RAT_MUL (RAT_OF_PAIR q) (RAT_OF_PAIR r))", three),
        (MulAtOne, "RAT_MUL (RAT_OF_PAIR p) RAT_ONE", "RAT_OF_PAIR p", one),
        (Distributive,
          "RAT_MUL (RAT_OF_PAIR p) (RAT_ADD (RAT_OF_PAIR q) (RAT_OF_PAIR r))",
          "RAT_ADD (RAT_MUL (RAT_OF_PAIR p) (RAT_OF_PAIR q)) (RAT_MUL (RAT_OF_PAIR p) (RAT_OF_PAIR r))", three)
      )
      for {
        liftRules <- Rewrite.Rule.all(wide, lifts)
        equal <- quotient.fact(Quotient.ProjectionEqual)
        representative <- quotient.fact(Quotient.ProjectionOfRepresentative).flatMap(Rewrite.Rule.of(wide, _))
        chooser <- LogicError.lift(
          quotient.theory.constant(quotient.names.representative, Type.fun(Classes, Pairs))
        )
        proved <- texts.foldLeft[Either[LogicError, Vector[(String, Kernel.Thm)]]](Right(Vector.empty)) {
          case (sofar, (name, leftText, rightText, (pairs, classes))) =>
            for {
              done <- sofar
              theorem <- law(quotient, liftRules ++ projections, equal, representative, chooser, leftText, rightText, pairs, classes)
                .left.flatMap(error => blaming(quotient, name, leftText, error))
            } yield done :+ (name -> theorem)
        }
      } yield proved
    }

    private def law(
      quotient: Quotient,
      rules: Vector[Rewrite.Rule],
      equal: Kernel.Thm,
      representative: Rewrite.Rule,
      chooser: Term,
      leftText: String,
      rightText: String,
      pairs: List[FVar],
      classes: List[FVar]
    ): Either[LogicError, Kernel.Thm] = {
      val wide = quotient.logic.rules
      for {
        left <- Parser.term(quotient.theory, notation, leftText, Classes)
        right <- Parser.term(quotient.theory, notation, rightText, Classes)
        leftNormal <- Rewrite.rewrite(rules, left)
        rightNormal <- Rewrite.rewrite(rules, right)
        leftPair <- rightOfTheorem(leftNormal).flatMap(projected)
        rightPair <- rightOfTheorem(rightNormal).flatMap(projected)
        same <- related(leftPair, rightPair, Nil)
        classesEqual <- wide.specAll(equal, List(leftPair, rightPair))
          .flatMap(Conv.sym)
          .flatMap(back => LogicError.lift(Kernel.eqMp(back, same)))
        chain <- Conv.trans(leftNormal, classesEqual)
          .flatMap(step => Conv.sym(rightNormal).flatMap(Conv.trans(step, _)))
        general <- wide.genAll(chain, pairs)
        chosen <- classes.foldRight[Either[LogicError, List[Term]]](Right(Nil)) { (variable, rest) =>
          rest.flatMap(tail => LogicError.lift(Term.app(chooser, variable)).map(_ :: tail))
        }
        instance <- wide.specAll(general, chosen)
        rewritten <- Rewrite.inTheorem(Vector(representative), instance)
        result <- wide.genAll(rewritten, classes)
      } yield result
    }

    /**
     * A refusal with the law's name in front of it, since every law is the same steps over a
     * different pair of texts and the bare refusal would not say which one was being proved.
     */
    private def blaming(quotient: Quotient, name: String, text: String, error: LogicError): Either[LogicError, Kernel.Thm] =
      Parser.term(quotient.theory, notation, text, Classes).flatMap(term =>
        Left(NotOfForm(s"$name, which is ${error.message}, over", term))
      )

    /** The pair under `RAT_OF_PAIR`, or a refusal naming what the rewriting left instead. */
    private def projected(term: Term): Either[LogicError, Term] =
      term match {
        case App(Const(Projection, _), pair) => Right(pair)
        case other => Left(NotOfForm(s"a term the lifts bring to one $Projection", other))
      }

    /**
     * `|- ~(RAT_ZERO = RAT_ONE)`.
     *
     * The classes are equal exactly where the pairs are related, the relation at `(0, 0)` and
     * `(1, 0)` is `0 * 1 = 1 * 1` over `int` once `SUC ZERO` is read as `INT_ONE`, the ring reads
     * that as `0 = 1`, and the embedding carries it to `ZERO = SUC ZERO`, which the naturals refuse.
     * The steps are equations between propositions joined by transitivity, so the refusal at the end
     * is one `eqMp` and one contradiction.
     */
    def unitsDistinct(
      quotient: Quotient,
      zeroDefinition: Kernel.Thm,
      oneDefinition: Kernel.Thm,
      integer: Integer,
      peano: Peano
    ): Either[LogicError, Kernel.Thm] = {
      val wide = quotient.logic.rules
      for {
        zeroPair <- read("PAIR INT_ZERO ZERO")
        onePair <- read("PAIR INT_ONE ZERO")
        zeroInt <- read("INT_ZERO")
        oneInt <- read("INT_ONE")
        zeroNum <- read("ZERO")
        equal <- quotient.fact(Quotient.ProjectionEqual)
        asRelation <- wide.specAll(equal, List(zeroPair, onePair))
        unfolded <- unfoldedAt(definition, projections, zeroPair, onePair)
        relation <- rightOfTheorem(unfolded)
        readBack <- Rewrite.rewrite(denominators, relation)
        sides <- rightOfTheorem(readBack).flatMap(t => Term.destEq(t).toRight(NotOfForm("an equation", t)))
        leftIsZero <- ring.prove(sides._1, zeroInt)
        rightIsOne <- ring.prove(sides._2, oneInt)
        onInts <- Conv.apTerm(Term.equalityAt(integers), leftIsZero)
          .flatMap(partial => LogicError.lift(Kernel.mkComb(partial, rightIsOne)))
        zeroEmbedded <- integer.fact(Integer.OfNaturalZero).flatMap(Conv.sym)
        oneEmbedded <- Conv.sym(embeddedOne)
        embedded <- Conv.apTerm(Term.equalityAt(integers), zeroEmbedded)
          .flatMap(partial => LogicError.lift(Kernel.mkComb(partial, oneEmbedded)))
        successorZero <- read("SUC ZERO")
        injective <- integer.fact(Integer.OfNaturalInjective).flatMap(wide.specAll(_, List(zeroNum, successorZero)))
        pairsToNaturals <- Vector(unfolded, readBack, onInts, embedded, injective)
          .foldLeft[Either[LogicError, Kernel.Thm]](Right(asRelation))((sofar, next) => sofar.flatMap(Conv.trans(_, next)))
        constants <- Conv.apTerm(Term.equalityAt(Classes), zeroDefinition)
          .flatMap(partial => LogicError.lift(Kernel.mkComb(partial, oneDefinition)))
        whole <- Conv.trans(constants, pairsToNaturals)
        premise <- leftOf(whole)
        assumed <- LogicError.lift(Kernel.assume(premise))
        naturalsEqual <- LogicError.lift(Kernel.eqMp(whole, assumed))
        flipped <- Conv.sym(naturalsEqual)
        never <- peano.naturals.fact(Natural.SuccessorNotZero).flatMap(wide.spec(zeroNum, _))
        clash <- wide.notElim(never, flipped)
        result <- wide.notIntro(premise, clash)
      } yield result
    }
  }

  private object Lifting {

    /**
     * Over the theory that holds the relation. [[Fraction.Denominator]] is proved first: over `num`,
     * `SUC n = n + SUC 0` for each successor puts both sides in `Semiring`'s fragment, and
     * `INT_OF_NUM_MUL` carries the product into `int`.
     */
    def over(
      logic: Logic,
      theory: Theory,
      notation: Notation,
      integer: Integer,
      peano: Peano,
      definition: Kernel.Thm,
      projections: Vector[Rewrite.Rule]
    ): Either[LogicError, Lifting] = {
      val rules = logic.rules
      val d = Term.variable("d", numbers)
      val e = Term.variable("e", numbers)
      for {
        ring <- integer.ring
        semiring <- Semiring.construct(peano)
        successor <- LogicError.lift(theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers)))
        times <- LogicError.lift(theory.constant(Peano.Multiplication, Type.fun(numbers, Type.fun(numbers, numbers))))
        ofNatural <- LogicError.lift(theory.constant(Integer.OfNatural, Type.fun(numbers, integers)))
        zero <- Parser.term(theory, notation, "0", numbers)
        addSuccessor <- peano.fact(Peano.AddAtSuccessor)
        addZero <- peano.fact(Peano.AddAtZero)
        // `SUC n = n + SUC 0`, from `n + SUC 0 = SUC (n + 0)` and `n + 0 = n`
        asSum = (n: Term) =>
          for {
            stepped <- rules.specAll(addSuccessor, List(n, zero))
            inner <- rules.spec(n, addZero).flatMap(Conv.apTerm(successor, _))
            joined <- Conv.trans(stepped, inner)
            result <- Conv.sym(joined)
          } yield result
        stored <- Parser.term(theory, notation, "d:num * e:num + d + e", numbers)
        atStored <- asSum(stored)
        atD <- asSum(d)
        atE <- asSum(e)
        factors <- Conv.apTerm(times, atD).flatMap(partial => LogicError.lift(Kernel.mkComb(partial, atE)))
        storedSum <- rightOfTheorem(atStored)
        factorsSum <- rightOfTheorem(factors)
        core <- semiring.prove(storedSum, factorsSum)
        onNum <- Conv.sym(factors).flatMap(back => Conv.trans(atStored, core).flatMap(Conv.trans(_, back)))
        embedded <- Conv.apTerm(ofNatural, onNum)
        successorD <- LogicError.lift(Term.app(successor, d))
        successorE <- LogicError.lift(Term.app(successor, e))
        product <- integer.fact(Integer.OfNaturalProduct).flatMap(rules.specAll(_, List(successorD, successorE)))
        joined <- Conv.trans(embedded, product)
        denominator <- rules.genAll(joined, List(d, e))

        // `INT_OF_NUM (SUC ZERO) = INT_ONE`, both sides unfolded to `INT_OF_PAIR (PAIR (SUC ZERO) ZERO)`.
        // It is what the denominator of a constant stored at `ZERO` reads as, and nothing else here
        // produces a `SUC ZERO`: every other stored index is a variable or a sum of them.
        ofNaturalDefinition <- integer.definition(Integer.OfNatural)
        integerOne <- integer.definition(Integer.One)
        successorZero <- LogicError.lift(Term.app(successor, zero))
        unfoldedOne <- Conv.unfold(ofNaturalDefinition, List(successorZero))
        embeddedOne <- Conv.sym(integerOne).flatMap(Conv.trans(unfoldedOne, _))

        denominators <- Rewrite.Rule.all(logic, Vector(denominator, embeddedOne))
      } yield Lifting(logic, theory, notation, definition, projections, denominators, denominator, embeddedOne, ring)
    }
  }

  /* ------------------------------------------------------------------ the order */

  /**
   * The order: two facts about `int` under it, the respectfulness at the pairs, the fact that makes
   * the constant usable at any pair, the four laws of a total order on classes, and the pair of
   * facts that says the order is not the trivial one.
   *
   * Every law is proved at pairs, where it is a statement about `int`, and put on classes the way
   * the ring laws are: the cross-multiplied order is folded back into `RAT_LE` of two projections,
   * and the pair variables are specialised at the representatives the quotient chose.
   */
  private final case class Ordering(
    quotient: Quotient,
    notation: Notation,
    lifting: Lifting,
    integer: Integer,
    peano: Peano
  ) {
    private val logic: Logic = quotient.logic
    private val rules = logic.rules
    private val theory: Theory = quotient.theory
    private val ring: CommutativeRing = lifting.ring

    private val intPairs: Type = TyApp(Product.TypeName, List(numbers, numbers))
    private val a: FVar = Term.variable("a", integers)
    private val b: FVar = Term.variable("b", integers)
    private val n: FVar = Term.variable("n", numbers)
    private val d: FVar = Term.variable("d", numbers)
    private val u: FVar = Term.variable("u", intPairs)
    private val w: FVar = Term.variable("w", intPairs)
    private val p: FVar = Term.variable("p", Pairs)
    private val q: FVar = Term.variable("q", Pairs)
    private val r: FVar = Term.variable("r", Pairs)
    private val s: FVar = Term.variable("s", Pairs)
    private val x: FVar = Term.variable("x", Classes)
    private val y: FVar = Term.variable("y", Classes)
    private val z: FVar = Term.variable("z", Classes)

    private def read(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)

    private def assume(term: Term): Either[LogicError, Kernel.Thm] = LogicError.lift(Kernel.assume(term))

    /** The two sides of an application of a binary constant. */
    private def arguments(term: Term): Either[LogicError, (Term, Term)] =
      term match {
        case App(App(_, left), right) => Right((left, right))
        case other => Left(NotOfForm("an application of two arguments", other))
      }

    /** From `|- INT_LE A B`, `|- A = C` and `|- B = D`, the theorem `|- INT_LE C D`. */
    private def moved(order: Kernel.Thm, left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        atMost <- LogicError.lift(theory.constant(Integer.AtMost, Type.fun(integers, Type.fun(integers, Type.Bool))))
        both <- Conv.apTerm(atMost, left).flatMap(partial => LogicError.lift(Kernel.mkComb(partial, right)))
        result <- LogicError.lift(Kernel.eqMp(both, order))
      } yield result

    /** `INT_MUL left right`, built rather than parsed so that its sides are exactly the terms given. */
    private def times(left: Term, right: Term): Either[LogicError, Term] =
      for {
        multiply <- LogicError.lift(theory.constant(Integer.Multiplication, Type.fun(integers, Type.fun(integers, integers))))
        result <- LogicError.lift(Term.appAll(multiply, List(left, right)))
      } yield result

    /** `INT_OF_NUM (SUC (SND pair))`, the denominator of a fraction as an integer. */
    private def denominatorOf(pair: FVar): Either[LogicError, Term] =
      read(s"INT_OF_NUM (SUC (SND (${pair.name}:prod(int,num))))")

    /** `SUC (SND pair)`, the natural a denominator is the embedding of. */
    private def successorOf(pair: FVar): Either[LogicError, Term] =
      read(s"SUC (SND (${pair.name}:prod(int,num)))")

    private def crossedAt(left: FVar, right: FVar): Either[LogicError, Term] =
      read(crossed(s"(${left.name}:prod(int,num))", s"(${right.name}:prod(int,num))"))

    /** [[Fraction.IntAtMostScaled]], at pairs of naturals first and then over `int`. */
    def scaled: Either[LogicError, Kernel.Thm] =
      for {
        semiring <- Semiring.construct(peano)
        atMostPairs <- integer.fact(Integer.AtMostPairs)
        mulPairs <- integer.fact(Integer.MulPairs)
        monotone <- peano.fact(Peano.MulMonotone)
        ofNaturalDefinition <- integer.definition(Integer.OfNatural)
        ofNatural <- Conv.unfold(ofNaturalDefinition, List(n)).flatMap(rules.gen(n, _))
        rewriting <- Rewrite.Rule.all(logic, Vector(ofNatural, mulPairs, atMostPairs)).map(_ ++ lifting.projections)

        premise <- read("INT_LE (INT_OF_PAIR (u:prod(num,num))) (INT_OF_PAIR (w:prod(num,num)))")
        goal <- read(
          "INT_LE (INT_MUL (INT_OF_PAIR (u:prod(num,num))) (INT_OF_NUM (n:num))) " +
            "(INT_MUL (INT_OF_PAIR (w:prod(num,num))) (INT_OF_NUM n))"
        )
        held <- assume(premise)
        opened <- rules.specAll(atMostPairs, List(u, w)).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, held)))
        bounds <- arguments(opened.conclusion)
        multiplied <- rules.specAll(monotone, List(n, bounds._1, bounds._2)).flatMap(rules.mp(_, opened))
        targets <- arguments(multiplied.conclusion)

        goalRead <- Rewrite.rewrite(rewriting, goal)
        readSides <- rightOfTheorem(goalRead).flatMap(arguments)
        leftEqual <- semiring.prove(readSides._1, targets._1)
        rightEqual <- semiring.prove(readSides._2, targets._2)
        numAtMost <- LogicError.lift(theory.constant(Peano.NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool))))
        bridge <- Conv.apTerm(numAtMost, leftEqual).flatMap(partial => LogicError.lift(Kernel.mkComb(partial, rightEqual)))
        whole <- Conv.trans(goalRead, bridge)
        proved <- Conv.sym(whole).flatMap(back => LogicError.lift(Kernel.eqMp(back, multiplied)))
        atPairs <- rules.disch(premise, proved).flatMap(rules.genAll(_, List(u, w, n)))

        chooser <- LogicError.lift(
          integer.quotient.theory.constant(integer.quotient.names.representative, Type.fun(integers, intPairs))
        )
        chosenA <- LogicError.lift(Term.app(chooser, a))
        chosenB <- LogicError.lift(Term.app(chooser, b))
        back <- integer.quotient.fact(Quotient.ProjectionOfRepresentative).flatMap(Rewrite.Rule.of(logic, _))
        result <- rules
          .specAll(atPairs, List(chosenA, chosenB, n))
          .flatMap(Rewrite.inTheorem(Vector(back), _))
          .flatMap(rules.genAll(_, List(a, b, n)))
      } yield result

    /** [[Fraction.IntAtMostCancels]]: totality, and the other order makes the products equal. */
    def cancels(scaledLaw: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        total <- integer.fact(Integer.AtMostTotal)
        antisymmetric <- integer.fact(Integer.AtMostAntisymmetric)
        reflexive <- integer.fact(Integer.AtMostReflexive)
        positive <- integer.fact(Integer.CancelsPositive)

        premise <- read("INT_LE (INT_MUL (a:int) (INT_OF_NUM (SUC (d:num)))) (INT_MUL (b:int) (INT_OF_NUM (SUC d)))")
        target <- read("INT_LE (a:int) (b:int)")
        other <- read("INT_LE (b:int) (a:int)")
        successor <- read("SUC (d:num)")
        held <- assume(premise)
        products <- arguments(premise)

        cases <- rules.specAll(total, List(a, b))
        already <- assume(target)
        reversed <- assume(other)
        flipped <- rules.specAll(scaledLaw, List(b, a, successor)).flatMap(rules.mp(_, reversed))
        productsEqual <- rules
          .specAll(antisymmetric, List(products._1, products._2))
          .flatMap(rules.mp(_, held))
          .flatMap(rules.mp(_, flipped))
        equal <- rules.specAll(positive, List(a, b, d)).flatMap(rules.mp(_, productsEqual))
        atSelf <- rules.spec(a, reflexive)
        atMost <- LogicError.lift(theory.constant(Integer.AtMost, Type.fun(integers, Type.fun(integers, Type.Bool))))
        leftFixed <- LogicError.lift(Term.app(atMost, a))
        fromOther <- Conv.apTerm(leftFixed, equal).flatMap(step => LogicError.lift(Kernel.eqMp(step, atSelf)))

        settled <- rules.disjElim(cases, already, fromOther)
        result <- rules.disch(premise, settled).flatMap(rules.genAll(_, List(a, b, d)))
      } yield result

    /** [[Fraction.AtMostRespects]]. */
    def respects(scaledLaw: Kernel.Thm, cancelsLaw: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        first <- unfoldedAt(lifting.definition, lifting.projections, p, r)
        second <- unfoldedAt(lifting.definition, lifting.projections, q, s)
        firstPremise <- leftOf(first)
        secondPremise <- leftOf(second)
        firstEquation <- assume(firstPremise).flatMap(held => LogicError.lift(Kernel.eqMp(first, held)))
        secondEquation <- assume(secondPremise).flatMap(held => LogicError.lift(Kernel.eqMp(second, held)))

        premise <- crossedAt(p, q)
        held <- assume(premise)
        sides <- arguments(premise)

        denominatorP <- denominatorOf(p)
        denominatorQ <- denominatorOf(q)
        denominatorR <- denominatorOf(r)
        denominatorS <- denominatorOf(s)
        successorR <- successorOf(r)
        successorS <- successorOf(s)

        // Scale by the denominator of `r`, then by the denominator of `s`.
        once <- rules.specAll(scaledLaw, List(sides._1, sides._2, successorR)).flatMap(rules.mp(_, held))
        onceSides <- arguments(once.conclusion)
        twice <- rules.specAll(scaledLaw, List(onceSides._1, onceSides._2, successorS)).flatMap(rules.mp(_, once))
        twiceSides <- arguments(twice.conclusion)

        // Each side, rewritten by one premise into the new numerator times both old denominators.
        target <- crossedAt(r, s)
        newSides <- arguments(target)
        oldDenominators <- times(denominatorP, denominatorQ)
        leftTarget <- times(newSides._1, oldDenominators)
        rightTarget <- times(newSides._2, oldDenominators)
        leftCoefficient <- times(denominatorQ, denominatorS)
        rightCoefficient <- times(denominatorP, denominatorR)
        leftEqual <- ring.consequence(twiceSides._1, leftTarget, List(firstEquation -> leftCoefficient))
        rightEqual <- ring.consequence(twiceSides._2, rightTarget, List(secondEquation -> rightCoefficient))
        rearranged <- moved(twice, leftEqual, rightEqual)

        // The product of the old denominators read as one embedded successor, and taken off.
        indexP <- read("SND (p:prod(int,num))")
        indexQ <- read("SND (q:prod(int,num))")
        stored <- rules.specAll(lifting.denominator, List(indexP, indexQ)).flatMap(Conv.sym)
        leftRead <- underFactor(newSides._1, stored)
        rightRead <- underFactor(newSides._2, stored)
        readBack <- moved(rearranged, leftRead, rightRead)
        index <- rightOfTheorem(stored).flatMap(indexOf)
        cancelled <- rules.specAll(cancelsLaw, List(newSides._1, newSides._2, index)).flatMap(rules.mp(_, readBack))

        result <- rules
          .disch(premise, cancelled)
          .flatMap(rules.disch(secondPremise, _))
          .flatMap(rules.disch(firstPremise, _))
          .flatMap(rules.genAll(_, List(p, q, r, s)))
      } yield result

    /** From `|- D1 = D2`, the theorem `|- INT_MUL left D1 = INT_MUL left D2`. */
    private def underFactor(left: Term, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        multiply <- LogicError.lift(theory.constant(Integer.Multiplication, Type.fun(integers, Type.fun(integers, integers))))
        partial <- LogicError.lift(Term.app(multiply, left))
        result <- Conv.apTerm(partial, equation)
      } yield result

    /**
     * [[Fraction.AtMostPairs]]: the constant at two projections is the order at the pairs.
     *
     * The constant reads the representatives, each related to the pair it was chosen for by
     * `REPR_REL`, so the respectfulness carries the order across in both directions and the two
     * implications are one equation.
     */
    def atPairs(definition: Kernel.Thm, respectsLaw: Kernel.Thm, symmetric: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        projectedP <- read("RAT_OF_PAIR (p:prod(int,num))")
        projectedQ <- read("RAT_OF_PAIR (q:prod(int,num))")
        unfolded <- Conv.unfold(definition, List(projectedP, projectedQ))
        chooser <- LogicError.lift(theory.constant(quotient.names.representative, Type.fun(Classes, Pairs)))
        chosenP <- LogicError.lift(Term.app(chooser, projectedP))
        chosenQ <- LogicError.lift(Term.app(chooser, projectedQ))
        related <- quotient.fact(Quotient.RelatedToRepresentative)
        pToChosen <- rules.spec(p, related)
        qToChosen <- rules.spec(q, related)
        chosenToP <- rules.specAll(symmetric, List(p, chosenP)).flatMap(rules.mp(_, pToChosen))
        chosenToQ <- rules.specAll(symmetric, List(q, chosenQ)).flatMap(rules.mp(_, qToChosen))

        atChosen <- rightOfTheorem(unfolded)
        atGiven <- crossedAt(p, q)
        chosenHeld <- assume(atChosen)
        givenHeld <- assume(atGiven)
        forwards <- rules
          .specAll(respectsLaw, List(chosenP, chosenQ, p, q))
          .flatMap(rules.mp(_, chosenToP))
          .flatMap(rules.mp(_, chosenToQ))
          .flatMap(rules.mp(_, chosenHeld))
        backwards <- rules
          .specAll(respectsLaw, List(p, q, chosenP, chosenQ))
          .flatMap(rules.mp(_, pToChosen))
          .flatMap(rules.mp(_, qToChosen))
          .flatMap(rules.mp(_, givenHeld))
        equivalent = Kernel.deductAntisym(backwards, forwards)
        result <- Conv.trans(unfolded, equivalent).flatMap(rules.genAll(_, List(p, q)))
      } yield result

    /**
     * A law proved at pairs, with the order written out, put on classes: the order folded back into
     * `RAT_LE` of two projections, the pair variables specialised at the chosen representatives, and
     * each projection of a representative rewritten to the class it came from.
     */
    private def onClasses(
      atPairsLaw: Kernel.Thm,
      pairLaw: Kernel.Thm,
      pairs: List[FVar],
      classes: List[FVar],
      unfolding: Vector[Rewrite.Rule] = Vector.empty
    ): Either[LogicError, Kernel.Thm] =
      for {
        folding <- rules
          .specAll(atPairsLaw, List(p, q))
          .flatMap(Conv.sym)
          .flatMap(rules.genAll(_, List(p, q)))
          .flatMap(Rewrite.Rule.of(logic, _))
        chooser <- LogicError.lift(theory.constant(quotient.names.representative, Type.fun(Classes, Pairs)))
        chosen <- classes.foldRight[Either[LogicError, List[Term]]](Right(Nil)) { (variable, rest) =>
          rest.flatMap(tail => LogicError.lift(Term.app(chooser, variable)).map(_ :: tail))
        }
        back <- quotient.fact(Quotient.ProjectionOfRepresentative).flatMap(Rewrite.Rule.of(logic, _))
        // `unfolding` turns a projection of an operation's pair back into the operation on the
        // projections, and of a constant's pair back into the constant: what a law about `RAT_ADD`
        // or `RAT_ZERO` is stated with, where the order at pairs can only mention the pairs.
        foldedOrder <- rules.genAll(pairLaw, pairs).flatMap(Rewrite.inTheorem(Vector(folding), _))
        folded <- if (unfolding.isEmpty) Right(foldedOrder) else Rewrite.inTheorem(unfolding, foldedOrder)
        result <- rules
          .specAll(folded, chosen)
          .flatMap(Rewrite.inTheorem(Vector(back), _))
          .flatMap(rules.genAll(_, classes))
      } yield result

    /** The four laws of a total order, at pairs and then on classes. */
    def laws(
      atPairsLaw: Kernel.Thm,
      scaledLaw: Kernel.Thm,
      cancelsLaw: Kernel.Thm
    ): Either[LogicError, Vector[(String, Kernel.Thm)]] =
      for {
        reflexive <- integer.fact(Integer.AtMostReflexive)
        transitive <- integer.fact(Integer.AtMostTransitive)
        antisymmetric <- integer.fact(Integer.AtMostAntisymmetric)
        total <- integer.fact(Integer.AtMostTotal)
        equal <- quotient.fact(Quotient.ProjectionEqual)

        // Reflexivity: the order at `p p` compares a product with itself.
        atSelf <- crossedAt(p, p).flatMap(arguments)
        reflexiveAtPairs <- rules.spec(atSelf._1, reflexive)
        reflexiveLaw <- onClasses(atPairsLaw, reflexiveAtPairs, List(p), List(x))

        // Totality: the order at `q p` is the order at `p q` with its sides exchanged.
        atPQ <- crossedAt(p, q).flatMap(arguments)
        totalAtPairs <- rules.specAll(total, List(atPQ._1, atPQ._2))
        totalLaw <- onClasses(atPairsLaw, totalAtPairs, List(p, q), List(x, y))

        // Antisymmetry: the two orders make the cross-products equal, which is the relation.
        forwardsTerm <- crossedAt(p, q)
        backwardsTerm <- crossedAt(q, p)
        forwardsHeld <- assume(forwardsTerm)
        backwardsHeld <- assume(backwardsTerm)
        crossEqual <- rules
          .specAll(antisymmetric, List(atPQ._1, atPQ._2))
          .flatMap(rules.mp(_, forwardsHeld))
          .flatMap(rules.mp(_, backwardsHeld))
        relation <- unfoldedAt(lifting.definition, lifting.projections, p, q).flatMap(fold(_, crossEqual))
        classesEqual <- rules
          .specAll(equal, List(p, q))
          .flatMap(Conv.sym)
          .flatMap(back => LogicError.lift(Kernel.eqMp(back, relation)))
        antisymmetricAtPairs <- rules.disch(backwardsTerm, classesEqual).flatMap(rules.disch(forwardsTerm, _))
        antisymmetricLaw <- onClasses(atPairsLaw, antisymmetricAtPairs, List(p, q), List(x, y))

        // Transitivity: scale the first by the denominator of `r` and the second by that of `p`,
        // meet in the middle, and take the denominator of `q` off.
        firstTerm <- crossedAt(p, q)
        secondTerm <- crossedAt(q, r)
        firstHeld <- assume(firstTerm)
        secondHeld <- assume(secondTerm)
        firstSides <- arguments(firstTerm)
        secondSides <- arguments(secondTerm)
        successorR <- successorOf(r)
        successorP <- successorOf(p)
        firstScaled <- rules
          .specAll(scaledLaw, List(firstSides._1, firstSides._2, successorR))
          .flatMap(rules.mp(_, firstHeld))
        secondScaled <- rules
          .specAll(scaledLaw, List(secondSides._1, secondSides._2, successorP))
          .flatMap(rules.mp(_, secondHeld))
        firstScaledSides <- arguments(firstScaled.conclusion)
        secondScaledSides <- arguments(secondScaled.conclusion)
        middle <- ring.prove(firstScaledSides._2, secondScaledSides._1)
        firstMet <- moved(firstScaled, Conv.refl(firstScaledSides._1), middle)
        chained <- rules
          .specAll(transitive, List(firstScaledSides._1, secondScaledSides._1, secondScaledSides._2))
          .flatMap(rules.mp(_, firstMet))
          .flatMap(rules.mp(_, secondScaled))
        target <- crossedAt(p, r).flatMap(arguments)
        denominatorQ <- denominatorOf(q)
        leftTarget <- times(target._1, denominatorQ)
        rightTarget <- times(target._2, denominatorQ)
        leftEqual <- ring.prove(firstScaledSides._1, leftTarget)
        rightEqual <- ring.prove(secondScaledSides._2, rightTarget)
        rearranged <- moved(chained, leftEqual, rightEqual)
        indexQ <- read("SND (q:prod(int,num))")
        cancelled <- rules.specAll(cancelsLaw, List(target._1, target._2, indexQ)).flatMap(rules.mp(_, rearranged))
        transitiveAtPairs <- rules.disch(secondTerm, cancelled).flatMap(rules.disch(firstTerm, _))
        transitiveLaw <- onClasses(atPairsLaw, transitiveAtPairs, List(p, q, r), List(x, y, z))
      } yield Vector(
        AtMostReflexive -> reflexiveLaw,
        AtMostTransitive -> transitiveLaw,
        AtMostAntisymmetric -> antisymmetricLaw,
        AtMostTotal -> totalLaw
      )

    /**
     * `|- RAT_LE c1 c2 = NUM_LE m n` for two of the constants, which is how both facts about the
     * units are read: the definitions and [[Fraction.AtMostPairs]] bring the order to one between
     * two products of `int`, the ring and `SUC ZERO` read as `INT_ONE` bring those to `INT_ZERO`
     * or `INT_ONE`, and the embedding carries the comparison into `num`.
     */
    private def unitsAsNaturals(
      statement: String,
      atPairsLaw: Kernel.Thm,
      constants: Vector[Kernel.Thm],
      leftValue: String,
      rightValue: String
    ): Either[LogicError, Kernel.Thm] =
      for {
        subject <- read(statement)
        rewriting <- Rewrite.Rule
          .all(logic, constants :+ atPairsLaw :+ lifting.embeddedOne)
          .map(_ ++ lifting.projections)
        onIntegers <- Rewrite.rewrite(rewriting, subject)
        sides <- rightOfTheorem(onIntegers).flatMap(arguments)
        leftInteger <- read(leftValue)
        rightInteger <- read(rightValue)
        leftEqual <- ring.prove(sides._1, leftInteger)
        rightEqual <- ring.prove(sides._2, rightInteger)
        leftEmbedded <- embeddingOf(leftValue)
        rightEmbedded <- embeddingOf(rightValue)
        leftAll <- Conv.trans(leftEqual, leftEmbedded)
        rightAll <- Conv.trans(rightEqual, rightEmbedded)
        atMost <- LogicError.lift(theory.constant(Integer.AtMost, Type.fun(integers, Type.fun(integers, Type.Bool))))
        onEmbedded <- Conv.apTerm(atMost, leftAll).flatMap(partial => LogicError.lift(Kernel.mkComb(partial, rightAll)))
        leftNatural <- rightOfTheorem(leftEmbedded).flatMap(argumentOf)
        rightNatural <- rightOfTheorem(rightEmbedded).flatMap(argumentOf)
        naturals <- integer.fact(Integer.AtMostOfNatural).flatMap(rules.specAll(_, List(leftNatural, rightNatural)))
        result <- Conv.trans(onIntegers, onEmbedded).flatMap(Conv.trans(_, naturals))
      } yield result

    /** `|- INT_ZERO = INT_OF_NUM ZERO` or `|- INT_ONE = INT_OF_NUM (SUC ZERO)`. */
    private def embeddingOf(value: String): Either[LogicError, Kernel.Thm] =
      value match {
        case "INT_ZERO" => integer.fact(Integer.OfNaturalZero).flatMap(Conv.sym)
        case "INT_ONE" => Conv.sym(lifting.embeddedOne)
        case other => read(other).flatMap(term => Left(NotOfForm("INT_ZERO or INT_ONE", term)))
      }

    private def argumentOf(term: Term): Either[LogicError, Term] =
      term match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("an application", other))
      }

    /** [[Fraction.ZeroAtMostOne]] and [[Fraction.OneNotAtMostZero]]. */
    def units(atPairsLaw: Kernel.Thm, zero: Kernel.Thm, one: Kernel.Thm): Either[LogicError, Vector[(String, Kernel.Thm)]] =
      for {
        upwards <- unitsAsNaturals("RAT_LE RAT_ZERO RAT_ONE", atPairsLaw, Vector(zero, one), "INT_ZERO", "INT_ONE")
        downwards <- unitsAsNaturals("RAT_LE RAT_ONE RAT_ZERO", atPairsLaw, Vector(zero, one), "INT_ONE", "INT_ZERO")
        least <- peano.fact(Peano.ZeroIsLeast)
        atMostZero <- peano.fact(Peano.AtMostZero)
        never <- peano.naturals.fact(Natural.SuccessorNotZero)
        successorZero <- read("SUC ZERO")
        zeroNumber <- read("ZERO")

        below <- rules.spec(successorZero, least)
        zeroAtMostOne <- Conv.sym(upwards).flatMap(back => LogicError.lift(Kernel.eqMp(back, below)))

        premise <- leftOf(downwards)
        held <- assume(premise)
        onNaturals <- LogicError.lift(Kernel.eqMp(downwards, held))
        collapsed <- rules.spec(successorZero, atMostZero).flatMap(rules.mp(_, onNaturals))
        clash <- rules.spec(zeroNumber, never).flatMap(rules.notElim(_, collapsed))
        oneNotAtMostZero <- rules.notIntro(premise, clash)
      } yield Vector(ZeroAtMostOne -> zeroAtMostOne, OneNotAtMostZero -> oneNotAtMostZero)

    /** Every fact of the order, in the order they are built. */
    /* ------------------------------------------------------------------ the ordered field */

    /** `|- !x. ... ` turned round under its quantifiers, so that it rewrites right to left. */
    private def reversed(theorem: Kernel.Thm, variables: List[FVar]): Either[LogicError, Rewrite.Rule] =
      rules.specAll(theorem, variables).flatMap(Conv.sym).flatMap(rules.genAll(_, variables)).flatMap(Rewrite.Rule.of(logic, _))

    /** A proposition read with the free pairs and integers this class declares. */
    private def statement(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)

    /** `crossed(A, B)` for two pair terms, built by substitution rather than by printing them. */
    private def crossedOf(left: Term, right: Term): Either[LogicError, Term] =
      for {
        template <- crossedAt(p, q)
        result <- LogicError.lift(Term.substitute(Map(p -> left, q -> right), template))
      } yield result

    /** `|- crossed(A, B) = INT_LE L R`, the projections read and the stored denominators read back. */
    private def readOrder(order: Term): Either[LogicError, Kernel.Thm] =
      Rewrite.rewrite(lifting.projections ++ lifting.denominators, order)

    /** `f A B`, reduced, which is the pair an operation gives. */
    private def applied(operation: Term, arguments: Term*): Either[LogicError, Term] =
      for {
        term <- LogicError.lift(Term.appAll(operation, arguments.toList))
        equation <- Conv.betaNormalise(term)
        result <- rightOfTheorem(equation)
      } yield result

    /**
     * [[Fraction.IntSign]]: every integer is the embedding of a natural or its negation. An integer
     * is the class of a pair `(m, k)`; the naturals are totally ordered, so `k + d = m` or
     * `m + d = k` for some `d`, and the pair is related to `(d, 0)` or to `(0, d)`.
     */
    def intSign: Either[LogicError, Kernel.Thm] = {
      val dd = Term.variable("d", numbers)
      for {
        semiring <- Semiring.construct(peano)
        cases <- integer.fact(Integer.Cases)
        equal <- integer.fact(Integer.Equal)
        sameDefinition <- integer.definition(Integer.SameName)
        ofNaturalDefinition <- integer.definition(Integer.OfNatural)
        negPair <- integer.fact(Integer.NegPair)
        total <- peano.fact(Peano.Total)
        atMostDefinition <- peano.definition(Peano.NonStrictOrder)
        goal <- statement("(?n:num. (a:int) = INT_OF_NUM n) \\/ (?n:num. (a:int) = INT_NEG (INT_OF_NUM n))")
        goalParts <- logic.destDisj(goal).toRight(NotOfForm("a disjunction", goal))
        (positiveGoal, negativeGoal) = goalParts
        represented <- statement("(a:int) = INT_OF_PAIR (u:prod(num,num))")
        heldRepresented <- assume(represented)
        first <- read("FST (u:prod(num,num))")
        second <- read("SND (u:prod(num,num))")
        zero <- Parser.term(theory, notation, "0", numbers)
        add <- LogicError.lift(theory.constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers))))
        pairing <- LogicError.lift(
          theory.constant(Product.Pairing, Type.fun(numbers, Type.fun(numbers, TyApp(Product.TypeName, List(numbers, numbers)))))
        )

        // `|- INT_OF_PAIR u = INT_OF_PAIR target`, given the equation under `INT_SAME u target`
        // once the projections of `target` are read, as a function of its two sides.
        relatedTo = (target: Term, arithmetic: (Term, Term) => Either[LogicError, Kernel.Thm]) =>
          for {
            unfolded <- Conv.unfold(sameDefinition, List(u, target))
            readBody <- Rewrite.rewrite(lifting.projections, rightOf(unfolded))
            sides <- Term.destEq(rightOf(readBody)).toRight(NotOfForm("an equation", rightOf(readBody)))
            proof <- arithmetic(sides._1, sides._2)
            bodyHolds <- Conv.sym(readBody).flatMap(back => LogicError.lift(Kernel.eqMp(back, proof)))
            sameHolds <- Conv.sym(unfolded).flatMap(back => LogicError.lift(Kernel.eqMp(back, bodyHolds)))
            classes <- rules.specAll(equal, List(u, target)).flatMap(Conv.sym)
              .flatMap(back => LogicError.lift(Kernel.eqMp(back, sameHolds)))
          } yield classes

        /** The witness of `NUM_LE left right` opened: the case's hypothesis, the existential, the body. */
        opening = (left: Term, right: Term) =>
          for {
            atMost <- Conv.unfold(atMostDefinition, List(left, right))
            caseStatement <- leftOf(atMost)
            held <- assume(caseStatement)
            opened <- LogicError.lift(Kernel.eqMp(atMost, held))
            body <- logic.destExistsPredicate(opened.conclusion).toRight(NotOfForm("an existential", opened.conclusion))
              .flatMap(pred => LogicError.lift(Term.app(pred, dd))).flatMap(Conv.betaRoot).map(rightOf)
            witness <- assume(body)
          } yield (opened, witness)

        // `snd u + d = fst u`: `u` is related to `(d, 0)`, since `fst u + 0 = (snd u + d) + 0 = d + snd u`
        positive <- {
          for {
            opened <- opening(second, first)
            (existential, witness) = opened
            target <- LogicError.lift(Term.appAll(pairing, List(dd, zero)))
            classes <- relatedTo(target, (left, right) =>
              for {
                back <- Conv.sym(witness)
                substituted <- Conv.apTerm(add, back).flatMap(Conv.apThm(_, zero))
                closing <- semiring.prove(rightOf(substituted), right)
                result <- Conv.trans(substituted, closing)
              } yield result)
            ofNatural <- Conv.unfold(ofNaturalDefinition, List(dd)).flatMap(Conv.sym)
            equation <- Conv.trans(heldRepresented, classes).flatMap(Conv.trans(_, ofNatural))
            witnessed <- logic.destExistsPredicate(positiveGoal).toRight(NotOfForm("an existential", positiveGoal))
              .flatMap(pred => rules.existsIntro(pred, dd, equation))
            injected <- rules.disjIntro1(negativeGoal, witnessed)
            result <- rules.existsElim(existential, dd, injected)
          } yield result
        }

        // `fst u + d = snd u`: `u` is related to `(0, d)`, since `fst u + d = 0 + (fst u + d) = 0 + snd u`
        negative <- {
          for {
            opened <- opening(first, second)
            (existential, witness) = opened
            target <- LogicError.lift(Term.appAll(pairing, List(zero, dd)))
            classes <- relatedTo(target, (left, right) =>
              for {
                sum <- LogicError.lift(Term.appAll(add, List(first, dd)))
                shifted <- LogicError.lift(Term.appAll(add, List(zero, sum)))
                opening <- semiring.prove(left, shifted)
                substituted <- LogicError.lift(Term.app(add, zero)).flatMap(Conv.apTerm(_, witness))
                result <- Conv.trans(opening, substituted)
              } yield result)
            ofNatural <- Conv.unfold(ofNaturalDefinition, List(dd))
            negation <- LogicError.lift(theory.constant(Integer.Negation, Type.fun(integers, integers)))
            negated <- Conv.apTerm(negation, ofNatural)
            swapped <- rightOf(negated) match {
              case App(_, App(_, pair)) => rules.spec(pair, negPair)
              case other => Left(NotOfForm("a negated class", other))
            }
            readSwap <- Rewrite.rewrite(lifting.projections, rightOf(swapped))
            chain <- Conv.trans(negated, swapped).flatMap(Conv.trans(_, readSwap)).flatMap(Conv.sym)
            equation <- Conv.trans(heldRepresented, classes).flatMap(Conv.trans(_, chain))
            witnessed <- logic.destExistsPredicate(negativeGoal).toRight(NotOfForm("an existential", negativeGoal))
              .flatMap(pred => rules.existsIntro(pred, dd, equation))
            injected <- rules.disjIntro2(positiveGoal, witnessed)
            result <- rules.existsElim(existential, dd, injected)
          } yield result
        }

        split <- rules.specAll(total, List(second, first))
        byCases <- rules.disjElim(split, positive, negative)
        atA <- rules.spec(a, cases)
        eliminated <- rules.existsElim(atA, u, byCases)
        result <- rules.gen(a, eliminated)
      } yield result
    }

    /**
     * [[Fraction.IntNonNegative]]: a non-negative integer is the embedding of a natural. The negative
     * case `a = -N` gives `N <= 0` once `N` is added to both sides, so `N` is the embedding of `0`.
     */
    def intNonNegative(sign: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val nn = Term.variable("n", numbers)
      for {
        monotone <- integer.fact(Integer.AddMonotone)
        ofNatural <- integer.fact(Integer.AtMostOfNatural)
        ofNaturalZero <- integer.fact(Integer.OfNaturalZero)
        atMostZero <- peano.fact(Peano.AtMostZero)
        premise <- statement("INT_LE INT_ZERO (a:int)")
        heldPremise <- assume(premise)
        goal <- statement("?n:num. (a:int) = INT_OF_NUM n")
        atA <- rules.spec(a, sign)
        parts <- logic.destDisj(atA.conclusion).toRight(NotOfForm("a disjunction", atA.conclusion))
        positive <- assume(parts._1)
        negativeCase <- {
          for {
            negativeHeld <- assume(parts._2)
            body <- logic.destExistsPredicate(parts._2).toRight(NotOfForm("an existential", parts._2))
              .flatMap(pred => LogicError.lift(Term.app(pred, nn))).flatMap(Conv.betaRoot).flatMap(rightOfTheorem)
            equation <- assume(body)
            embedded <- read("INT_OF_NUM (n:num)")
            zeroInt <- read("INT_ZERO")
            atNegation <- moved(heldPremise, Conv.refl(zeroInt), equation)
            shifted <- rules.specAll(monotone, List(zeroInt, rightOf(equation), embedded)).flatMap(rules.mp(_, atNegation))
            sides <- arguments(shifted.conclusion)
            leftEqual <- ring.prove(sides._1, embedded)
            zeroNumeral <- Parser.term(theory, notation, "0", numbers)
            embeddedZero <- LogicError.lift(Term.app(embeddedConstant, zeroNumeral))
            rightEqual <- ring.prove(sides._2, zeroInt).flatMap(eq => Conv.sym(ofNaturalZero).flatMap(Conv.trans(eq, _)))
            belowZero <- moved(shifted, leftEqual, rightEqual)
            asNaturals <- rules.specAll(ofNatural, List(nn, zeroNumeral)).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, belowZero)))
            isZero <- rules.spec(nn, atMostZero).flatMap(rules.mp(_, asNaturals))
            // a = -(INT_OF_NUM n) = -(INT_OF_NUM 0) = -INT_ZERO = INT_ZERO = INT_OF_NUM 0
            negation <- LogicError.lift(theory.constant(Integer.Negation, Type.fun(integers, integers)))
            atZero <- Conv.apTerm(embeddedConstant, isZero).flatMap(Conv.apTerm(negation, _))
            throughZero <- Conv.apTerm(negation, ofNaturalZero)
            negatedZero <- rightOfTheorem(throughZero)
            collapsed <- ring.prove(negatedZero, zeroInt)
            back <- Conv.sym(ofNaturalZero)
            chain <- Conv.trans(equation, atZero).flatMap(Conv.trans(_, throughZero)).flatMap(Conv.trans(_, collapsed)).flatMap(Conv.trans(_, back))
            witnessed <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
              .flatMap(pred => rules.existsIntro(pred, zeroNumeral, chain))
            result <- rules.existsElim(negativeHeld, nn, witnessed)
          } yield result
        }
        byCases <- rules.disjElim(atA, positive, negativeCase)
        result <- rules.disch(premise, byCases).flatMap(rules.gen(a, _))
      } yield result
    }

    private def rightOf(theorem: Kernel.Thm): Term =
      Term.destEq(theorem.conclusion).map(_._2).getOrElse(theorem.conclusion)

    private def embeddedConstant: Term =
      theory.constant(Integer.OfNatural, Type.fun(numbers, integers)).fold(error => throw new IllegalStateException(error.message), identity)

    /**
     * [[Fraction.IntMulNonNegative]]: the product of two non-negative integers is non-negative. The
     * second is the embedding of a natural, and a natural factor preserves the order.
     */
    def intMulNonNegative(nonNegative: Kernel.Thm, scaledLaw: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val mm = Term.variable("m", numbers)
      for {
        first <- statement("INT_LE INT_ZERO (a:int)")
        second <- statement("INT_LE INT_ZERO (b:int)")
        heldFirst <- assume(first)
        heldSecond <- assume(second)
        natural <- rules.spec(b, nonNegative).flatMap(rules.mp(_, heldSecond))
        body <- logic.destExistsPredicate(natural.conclusion).toRight(NotOfForm("an existential", natural.conclusion))
          .flatMap(pred => LogicError.lift(Term.app(pred, mm))).flatMap(Conv.betaRoot).flatMap(rightOfTheorem)
        equation <- assume(body)
        zeroInt <- read("INT_ZERO")
        scaledOrder <- rules.specAll(scaledLaw, List(zeroInt, a, mm)).flatMap(rules.mp(_, heldFirst))
        sides <- arguments(scaledOrder.conclusion)
        leftEqual <- ring.prove(sides._1, zeroInt)
        product <- times(a, b)
        rightEqual <- Conv.sym(equation).flatMap(underFactor(a, _))
        result0 <- moved(scaledOrder, leftEqual, rightEqual)
        eliminated <- rules.existsElim(natural, mm, result0)
        result <- rules.disch(second, eliminated).flatMap(rules.disch(first, _)).flatMap(rules.genAll(_, List(a, b)))
      } yield result
    }

    /**
     * [[Fraction.AtMostAdd]]: adding a rational to both sides keeps the order. At pairs, with `F` the
     * denominator of the rational added and `K` the cross term they share, the premise scaled twice by
     * `F` and shifted by `K` is the conclusion read through the ring.
     */
    def addMonotone(atPairsLaw: Kernel.Thm, scaledLaw: Kernel.Thm, addOperation: Term, addPairs: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        monotone <- integer.fact(Integer.AddMonotone)
        premise <- crossedAt(p, q)
        held <- assume(premise)
        sides <- arguments(premise)
        successorR <- successorOf(r)
        once <- rules.specAll(scaledLaw, List(sides._1, sides._2, successorR)).flatMap(rules.mp(_, held))
        onceSides <- arguments(once.conclusion)
        twice <- rules.specAll(scaledLaw, List(onceSides._1, onceSides._2, successorR)).flatMap(rules.mp(_, once))
        twiceSides <- arguments(twice.conclusion)
        shared <- read(
          "INT_MUL (FST (r:prod(int,num))) (INT_MUL (INT_OF_NUM (SUC (SND (p:prod(int,num))))) " +
            "(INT_MUL (INT_OF_NUM (SUC (SND (q:prod(int,num))))) (INT_OF_NUM (SUC (SND r)))))"
        )
        shifted <- rules.specAll(monotone, List(twiceSides._1, twiceSides._2, shared)).flatMap(rules.mp(_, twice))
        shiftedSides <- arguments(shifted.conclusion)
        leftPair <- applied(addOperation, p, r)
        rightPair <- applied(addOperation, q, r)
        goal <- crossedOf(leftPair, rightPair)
        readGoal <- readOrder(goal)
        goalSides <- rightOfTheorem(readGoal).flatMap(arguments)
        leftEqual <- ring.prove(shiftedSides._1, goalSides._1)
        rightEqual <- ring.prove(shiftedSides._2, goalSides._2)
        atGoal <- moved(shifted, leftEqual, rightEqual)
        proved <- Conv.sym(readGoal).flatMap(back => LogicError.lift(Kernel.eqMp(back, atGoal)))
        pairLaw <- rules.disch(premise, proved)
        unfolding <- reversed(addPairs, List(p, q))
        result <- onClasses(atPairsLaw, pairLaw, List(p, q, r), List(x, y, z), Vector(unfolding))
      } yield result

    /**
     * [[Fraction.AtMostMul]]: the product of two non-negative rationals is non-negative. At pairs the
     * order against `(0, 0)` reads as `INT_LE INT_ZERO a`, and the integers' law does the rest.
     */
    def mulNonNegative(
      atPairsLaw: Kernel.Thm,
      zeroDefinition: Kernel.Thm,
      mulOperation: Term,
      mulPairs: Kernel.Thm,
      productLaw: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        zeroPair <- read("PAIR INT_ZERO ZERO")
        zeroInt <- read("INT_ZERO")
        // `crossed(Z, t)`, and `|- crossed(Z, t) = INT_LE L R` with `|- L = INT_ZERO` beside it
        againstZero = (pair: Term) =>
          for {
            order <- crossedOf(zeroPair, pair)
            readEquation <- readOrder(order)
            sides <- arguments(rightOf(readEquation))
            leftIsZero <- ring.prove(sides._1, zeroInt)
          } yield (order, readEquation, leftIsZero, sides._2)
        /** `|- INT_LE INT_ZERO (FST t)` from the held order against zero. */
        numeratorNonNegative = (pair: FVar) =>
          for {
            reading <- againstZero(pair)
            (order, readEquation, leftIsZero, right) = reading
            held <- assume(order)
            numerator <- read(s"FST (${pair.name}:prod(int,num))")
            readHeld <- LogicError.lift(Kernel.eqMp(readEquation, held))
            rightIsNumerator <- ring.prove(right, numerator)
            result <- moved(readHeld, leftIsZero, rightIsNumerator)
          } yield (order, numerator, result)
        first <- numeratorNonNegative(p)
        second <- numeratorNonNegative(q)
        product <- rules.specAll(productLaw, List(first._2, second._2))
          .flatMap(rules.mp(_, first._3)).flatMap(rules.mp(_, second._3))
        productPair <- applied(mulOperation, p, q)
        goal <- againstZero(productPair)
        (goalOrder, goalRead, goalLeftIsZero, goalRight) = goal
        productSides <- arguments(product.conclusion)
        leftEqual <- Conv.sym(goalLeftIsZero)
        rightEqual <- ring.prove(productSides._2, goalRight)
        atRead <- moved(product, leftEqual, rightEqual)
        proved <- Conv.sym(goalRead).flatMap(back => LogicError.lift(Kernel.eqMp(back, atRead)))
        pairLaw <- rules.disch(second._1, proved).flatMap(rules.disch(first._1, _))
        unfoldProduct <- reversed(mulPairs, List(p, q))
        unfoldZero <- Conv.sym(zeroDefinition).flatMap(Rewrite.Rule.of(logic, _))
        result <- onClasses(atPairsLaw, pairLaw, List(p, q), List(x, y), Vector(unfoldProduct, unfoldZero))
      } yield result

    /**
     * [[Fraction.InverseExists]], [[Fraction.MulInverse]] and [[Fraction.InverseAtZero]].
     *
     * A rational that is not zero has a representative `(a, d)` with `a` not zero, [[Fraction.IntSign]]
     * writes `a` as `k + 1` or its negation, and the class of `(d + 1, k)`, or of `(-(d + 1), k)`, is
     * its inverse: the product is `(a * (d + 1), ...)`, whose denominator [[Fraction.Denominator]] reads
     * as `(d + 1) * (k + 1)`. The constant chooses the inverse where one exists and is zero at zero,
     * which is a convention the definition writes rather than an assumption.
     */
    def inverse(
      inverseDefinition: Kernel.Thm,
      zeroDefinition: Kernel.Thm,
      oneDefinition: Kernel.Thm,
      mulOperation: Term,
      mulPairs: Kernel.Thm,
      sign: Kernel.Thm
    ): Either[LogicError, (Kernel.Thm, Kernel.Thm, Kernel.Thm)] = {
      val nn = Term.variable("n", numbers)
      val kk = Term.variable("k", numbers)
      for {
        chooser <- LogicError.lift(theory.constant(quotient.names.representative, Type.fun(Classes, Pairs)))
        projection <- LogicError.lift(theory.constant(Projection, Type.fun(Pairs, Classes)))
        multiply <- LogicError.lift(theory.constant(Multiplication, Type.fun(Classes, Type.fun(Classes, Classes))))
        pairing <- LogicError.lift(theory.constant(Product.Pairing, Type.fun(integers, Type.fun(numbers, Pairs))))
        negation <- LogicError.lift(theory.constant(Integer.Negation, Type.fun(integers, integers)))
        equal <- quotient.fact(Quotient.ProjectionEqual)
        representative <- quotient.fact(Quotient.ProjectionOfRepresentative)
        cases <- peano.naturals.fact(Natural.ZeroOrSuccessor)
        ofNaturalZero <- integer.fact(Integer.OfNaturalZero)
        condTrue <- quotient.classical.fact(Classical.CondTrue).map(Kernel.instType(Map(Classical.TypeVariable -> Classes), _))
        condFalse <- quotient.classical.fact(Classical.CondFalse).map(Kernel.instType(Map(Classical.TypeVariable -> Classes), _))
        choice <- quotient.classical.axiom(Classical.Choice)
        sameness <- LogicError.lift(theory.constant(SameName, Type.fun(Pairs, Type.fun(Pairs, Type.Bool))))

        chosen <- LogicError.lift(Term.app(chooser, x))
        back <- rules.spec(x, representative)
        zeroPair <- read("PAIR INT_ZERO ZERO")
        onePair <- read("PAIR INT_ONE ZERO")
        zeroInt <- read("INT_ZERO")
        oneInt <- read("INT_ONE")
        nonZero <- statement("~((x:rat) = RAT_ZERO)")
        heldNonZero <- assume(nonZero)
        goal <- statement("?y:rat. RAT_MUL (x:rat) y = RAT_ONE")
        goalPredicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))

        // the representative is not related to `(0, 0)`, since then `x` would be `RAT_ZERO`
        notRelated <- {
          for {
            relation <- LogicError.lift(Term.appAll(sameness, List(chosen, zeroPair)))
            held <- assume(relation)
            classes <- rules.specAll(equal, List(chosen, zeroPair)).flatMap(Conv.sym)
              .flatMap(backwards => LogicError.lift(Kernel.eqMp(backwards, held)))
            isZero <- Conv.sym(back).flatMap(Conv.trans(_, classes)).flatMap(step => Conv.sym(zeroDefinition).flatMap(Conv.trans(step, _)))
            absurd <- rules.notElim(heldNonZero, isZero)
            result <- rules.notIntro(relation, absurd)
          } yield result
        }
        numerator <- read("FST (t:prod(int,num))").flatMap(t =>
          LogicError.lift(Term.substitute(Map(Term.variable("t", Pairs) -> chosen), t)))
        // so its numerator is not zero
        numeratorNonZero <- {
          for {
            zeroNumerator <- LogicError.lift(Term.eq(numerator, zeroInt))
            held <- assume(zeroNumerator)
            relation <- lifting.related(chosen, zeroPair, List(held -> oneInt))
            absurd <- rules.notElim(notRelated, relation)
            result <- rules.notIntro(zeroNumerator, absurd)
          } yield result
        }
        denominator <- read("INT_OF_NUM (SUC (SND (t:prod(int,num))))").flatMap(t =>
          LogicError.lift(Term.substitute(Map(Term.variable("t", Pairs) -> chosen), t)))

        signAtA <- rules.spec(numerator, sign)
        signParts <- logic.destDisj(signAtA.conclusion).toRight(NotOfForm("a disjunction", signAtA.conclusion))

        /** One sign: `a = s (INT_OF_NUM n)` with `s` the identity or the negation. */
        bySign = (existential: Term, negative: Boolean) =>
          for {
            heldExistential <- assume(existential)
            body <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
              .flatMap(pred => LogicError.lift(Term.app(pred, nn))).flatMap(Conv.betaRoot).map(rightOf)
            heldBody <- assume(body)
            embedded <- LogicError.lift(Term.app(embeddedConstant, nn))
            signed = (inner: Term) => if (negative) LogicError.lift(Term.app(negation, inner)) else Right(inner)
            atN <- rules.spec(nn, cases)
            caseParts <- logic.destDisj(atN.conclusion).toRight(NotOfForm("a disjunction", atN.conclusion))

            // n = 0 makes the numerator zero, which it is not
            zeroCase <- for {
              held <- assume(caseParts._1)
              embeddedZero <- Conv.apTerm(embeddedConstant, held).flatMap(Conv.trans(_, ofNaturalZero))
              signedZero <- if (negative) Conv.apTerm(negation, embeddedZero) else Right(embeddedZero)
              collapsed <- ring.prove(rightOf(signedZero), zeroInt)
              isZero <- Conv.trans(heldBody, signedZero).flatMap(Conv.trans(_, collapsed))
              absurd <- rules.notElim(numeratorNonZero, isZero)
              result <- rules.falsityElim(goal, absurd)
            } yield result

            // n = SUC k: the inverse is the class of (s (d + 1), k)
            successorCase <- for {
              heldSuccessor <- assume(caseParts._2)
              successorBody <- logic.destExistsPredicate(caseParts._2).toRight(NotOfForm("an existential", caseParts._2))
                .flatMap(pred => LogicError.lift(Term.app(pred, kk))).flatMap(Conv.betaRoot).map(rightOf)
              heldK <- assume(successorBody)
              atSuccessor <- Conv.apTerm(embeddedConstant, heldK)
              signedSuccessor <- if (negative) Conv.apTerm(negation, atSuccessor) else Right(atSuccessor)
              numeratorIs <- Conv.trans(heldBody, signedSuccessor)
              inverseNumerator <- signed(denominator)
              inversePair <- LogicError.lift(Term.appAll(pairing, List(inverseNumerator, kk)))
              productPair <- applied(mulOperation, chosen, inversePair)
              coefficient <- signed(denominator)
              // the relation comes back over the pair with its projections read, so the
              // classes are equated there and the product's own pair is carried to it
              reading <- Rewrite.rewrite(lifting.projections, productPair)
              readPair = rightOf(reading)
              relation <- lifting.related(readPair, onePair, List(numeratorIs -> coefficient))
              classes <- rules.specAll(equal, List(readPair, onePair)).flatMap(Conv.sym)
                .flatMap(backwards => LogicError.lift(Kernel.eqMp(backwards, relation)))
              projectedReading <- Conv.apTerm(projection, reading)
              lifted <- rules.specAll(mulPairs, List(chosen, inversePair))
              projectedInverse <- LogicError.lift(Term.app(projection, inversePair))
              atX <- Conv.sym(back).flatMap(Conv.apTerm(multiply, _)).flatMap(Conv.apThm(_, projectedInverse))
              chain <- Conv.trans(atX, lifted).flatMap(Conv.trans(_, projectedReading)).flatMap(Conv.trans(_, classes))
                .flatMap(step => Conv.sym(oneDefinition).flatMap(Conv.trans(step, _)))
              witnessed <- rules.existsIntro(goalPredicate, projectedInverse, chain)
              result <- rules.existsElim(heldSuccessor, kk, witnessed)
            } yield result

            byCases <- rules.disjElim(atN, zeroCase, successorCase)
            result <- rules.existsElim(heldExistential, nn, byCases)
          } yield result

        positiveCase <- bySign(signParts._1, false)
        negativeCase <- bySign(signParts._2, true)
        exists <- rules.disjElim(signAtA, positiveCase, negativeCase)
        existence <- rules.disch(nonZero, exists).flatMap(rules.gen(x, _))

        // the constant at a non-zero rational is the chosen inverse
        witness <- Classical.witnessFrom(logic, choice, exists)
        reduced <- Conv.betaRoot(witness.conclusion).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, witness)))
        unfolded <- Conv.unfold(inverseDefinition, List(x))
        parts <- rightOf(unfolded) match {
          case App(App(App(_, test), yes), no) => Right((test, yes, no))
          case other => Left(NotOfForm("a conditional", other))
        }
        (test, yes, no) = parts
        chosenInverse <- rules.specAll(condFalse, List(test, yes, no)).flatMap(rules.mp(_, heldNonZero))
        inverseIs <- Conv.trans(unfolded, chosenInverse)
        product <- LogicError.lift(Term.app(multiply, x)).flatMap(Conv.apTerm(_, inverseIs))
        mulInverse <- Conv.trans(product, reduced).flatMap(rules.disch(nonZero, _)).flatMap(rules.gen(x, _))

        // and zero at zero
        zeroClass <- read("RAT_ZERO")
        unfoldedAtZero <- Conv.unfold(inverseDefinition, List(zeroClass))
        zeroParts <- rightOf(unfoldedAtZero) match {
          case App(App(App(_, zeroTest), zeroYes), zeroNo) => Right((zeroTest, zeroYes, zeroNo))
          case other => Left(NotOfForm("a conditional", other))
        }
        atZero <- rules.specAll(condTrue, List(zeroParts._1, zeroParts._2, zeroParts._3))
          .flatMap(rules.mp(_, Conv.refl(zeroClass)))
        inverseAtZero <- Conv.trans(unfoldedAtZero, atZero)
      } yield (existence, mulInverse, inverseAtZero)
    }

    def facts(
      definition: Kernel.Thm,
      zero: Kernel.Thm,
      one: Kernel.Thm,
      symmetric: Kernel.Thm
    ): Either[LogicError, Vector[(String, Kernel.Thm)]] =
      for {
        scaledLaw <- scaled
        cancelsLaw <- cancels(scaledLaw)
        respectsLaw <- respects(scaledLaw, cancelsLaw)
        atPairsLaw <- atPairs(definition, respectsLaw, symmetric)
        orderLaws <- laws(atPairsLaw, scaledLaw, cancelsLaw)
        unitLaws <- units(atPairsLaw, zero, one)
      } yield Vector(
        IntAtMostScaled -> scaledLaw,
        IntAtMostCancels -> cancelsLaw,
        AtMostRespects -> respectsLaw,
        AtMostPairs -> atPairsLaw
      ) ++ orderLaws ++ unitLaws
  }

  private def rightOfTheorem(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
