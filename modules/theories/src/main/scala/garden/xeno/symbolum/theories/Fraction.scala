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
 * Not here yet: the inverse of a non-zero rational and the order, which are what make `rat` an
 * ordered field and what the reals as cuts will ask of it. The inverse wants a case split on the
 * sign of the numerator, which the pair `(a, d)` holds as an integer rather than as a sign and a
 * size; the order wants `INT_LE` preserved by a positive factor.
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
  val facts: Map[String, Kernel.Thm]
) {

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
}

object Fraction {

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
    UnitsDistinct -> "~(RAT_ZERO = RAT_ONE)"
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

      checked <- (Vector(
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
      ) ++ laws :+ (UnitsDistinct, distinct)).foldRight[Either[LogicError, Vector[(String, Kernel.Thm)]]](Right(Vector.empty)) {
        case ((name, theorem), rest) =>
          for {
            statement <- Parser.proposition(whole, notation, statementOf(name))
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
      whole,
      notation,
      widened,
      Map(SameName -> sameDefinition, Zero -> zeroDefinition, One -> oneDefinition) ++ complete.definitions,
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
  private final case class Lifting(
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
    private def related(left: Term, right: Term, premises: List[(Kernel.Thm, Term)]): Either[LogicError, Kernel.Thm] =
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

  private def rightOfTheorem(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
