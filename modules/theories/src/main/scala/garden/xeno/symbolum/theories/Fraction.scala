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
 * The relation, its three equivalence facts, and the type. **No arithmetic**: the operations are a
 * piece of their own and what decides their cost is measured rather than guessed. `Integer` closes
 * every one of its obligations with `Semiring`, which decides identities on `num` and which the
 * pair representation of an integer puts within reach; the carrier here is pairs of **integers**,
 * and there is no such procedure over `int`. `Semiring` is written against `Peano` and `Ring`
 * against the reals' `Arithmetic`, so the respectfulness of a lifted product here is a hand
 * derivation over `INT_MUL_ASSOC` and `INT_MUL_SYM` until something decides that algebra. The card
 * that owns this work carries the measurement.
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
        "RAT_SAME p q ==> RAT_SAME q r ==> RAT_SAME p r")
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
  def construct(classical: Classical, integer: Integer, product: Product): Either[LogicError, Fraction] =
    construct(classical, integer, product, integer.theory, integer.notation)

  /**
   * The same, extending a theory that already holds something else, which is the chain's entry
   * point when this development joins it.
   */
  def construct(
    classical: Classical,
    integer: Integer,
    product: Product,
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

      checked <- Vector(
        (SwapFactors, swap),
        (SameReflexive, reflexive),
        (SameSymmetric, symmetric),
        (SameTransitive, transitive)
      ).foldRight[Either[LogicError, Vector[(String, Kernel.Thm)]]](Right(Vector.empty)) {
        case ((name, theorem), rest) =>
          for {
            statement <- Parser.proposition(quotient.theory, notation, statementOf(name))
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
      quotient.theory,
      notation,
      quotient,
      Map(SameName -> sameDefinition) ++ quotient.definitions,
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
}
