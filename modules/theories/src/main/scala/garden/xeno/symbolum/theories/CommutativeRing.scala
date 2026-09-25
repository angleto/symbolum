package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Identities of a commutative semiring or ring, decided over whatever constants and laws the
 * caller hands in.
 *
 * `Semiring` decided identities of `num` and nothing else: its rules were `Peano`'s lemmas by name
 * and its order was chosen for `NUM_ADD` and `NUM_MUL`. `Integer` could close every obligation with
 * it because its carrier is pairs of **naturals**; the rationals' carrier is pairs of **integers**,
 * and nothing decided identities there, so each lifted operation of `Fraction` would have been a
 * derivation by hand, paid again for every quotient after it. Angelo decided on 2026-09-25 that the
 * procedure is generalised rather than the obligations written out (Mycelium card `fa8737ad`), and
 * this is the generalisation: the constants and the minimal laws are parameters, and everything
 * else is derived here once.
 *
 * == What it is handed, and what it derives ==
 *
 * The laws are the axioms of the structure and nothing more: associativity, commutativity and the
 * unit of each operation, distribution on the left, and then either `x * 0 = 0` for a semiring or
 * `x + -x = 0` for a ring. From those it derives the rules a normaliser needs and a caller would
 * otherwise re-derive per carrier: both exchanges, the units and zeros on the left, distribution on
 * the right, and for a ring `x * 0 = 0` itself, the inverse on the left, uniqueness of the inverse,
 * `--x = x`, `-0 = 0`, `-(x + y) = -x + -y`, `-x * y = -(x * y)`, `x * -y = -(x * y)` and the
 * cancellation `x + (-x + y) = y`. A caller that already holds one of those under its own name
 * passes it as `supplied`, and the rule set uses the caller's theorem, which is how `Semiring` keeps
 * `Peano`'s published exchange and zeros in its rules.
 *
 * == The order, which is the one decision here that is not a table ==
 *
 * Negations are pushed down through sums and pulled up out of products, so every monomial carries at
 * most one negation, at its head, and cancellation is a rewrite between neighbours. That needs the
 * order to put `m` beside `-m`, which is `Arithmetic.ringOrder`'s idea: compare the terms under
 * their negations first and the number of negations last. And it needs a sum to outrank each of its
 * summands whatever the operations are called, or associativity stops flattening wherever the left
 * summand is a product, which is `Semiring.order`'s idea and the reason `Arithmetic`'s docstring
 * warns that its own order does not transfer. [[CommutativeRing.order]] is the two together; with no
 * negation it is exactly the order `Semiring` has always used, so its normal forms do not move.
 *
 * == What it does not do ==
 *
 * It decides identities of the structure and nothing that needs more: no numeral of the carrier is
 * evaluated unless the caller hands in rules that open numerals, no subtraction is unfolded unless
 * the caller hands in its definition, and a law that holds only in a particular ring (a
 * characteristic, a cancellation by a non-zero factor) is outside it and refused rather than
 * decided. `Arithmetic`'s own normalisation of the reals is still its own; moving it here is a piece
 * of work of its own, because it bootstraps the reals' negation facts through the normaliser it is
 * building and every derivation in the chain rests on it.
 */
final class CommutativeRing private (
  val operations: CommutativeRing.Operations,
  val logic: Logic,
  val facts: Map[String, Kernel.Thm],
  val normalisation: Rewrite.Conversion
) {

  /** `|- left = right` for an identity of the structure, or a refusal naming what stopped. */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    Rewrite.proveEquation(logic, normalisation, goal)

  /** The same, for two terms rather than an equation. */
  def prove(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    LogicError.lift(Term.eq(left, right)).flatMap(prove)

  /** The normal form of a term, as a theorem saying the two are equal. */
  def normalise(term: Term): Either[LogicError, Kernel.Thm] = normalisation(term)

  /** A derived rule, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object CommutativeRing {

  /** The carrier and its operations, as constants of the caller's theory at the carrier's type. */
  final case class Operations(
    carrier: Type,
    add: Term,
    multiply: Term,
    zero: Term,
    one: Term,
    negate: Option[Term]
  )

  /**
   * The axioms: `(x + y) + z = x + (y + z)`, `x + y = y + x`, `x + 0 = x`, the same three for the
   * product with `x * 1 = x`, `x * (y + z) = x * y + x * z`, and `x * 0 = 0` for a semiring or
   * `x + -x = 0` for a ring. Each universally quantified in that order of variables.
   */
  final case class Laws(
    addAssociative: Kernel.Thm,
    addCommutative: Kernel.Thm,
    addZero: Kernel.Thm,
    multiplyAssociative: Kernel.Thm,
    multiplyCommutative: Kernel.Thm,
    multiplyOne: Kernel.Thm,
    distributive: Kernel.Thm,
    multiplyZero: Option[Kernel.Thm],
    inverse: Option[Kernel.Thm]
  )

  /* The derived rules, by the names they are held under. */
  val AddExchange: String = "ADD_EXCHANGE"
  val MultiplyExchange: String = "MUL_EXCHANGE"
  val ZeroPlus: String = "ADD_ZERO_LEFT"
  val OneTimes: String = "MUL_ONE_LEFT"
  val RightDistributive: String = "RIGHT_DISTRIBUTE"
  val TimesZero: String = "MUL_ZERO_RIGHT"
  val ZeroTimes: String = "MUL_ZERO_LEFT"
  val InverseOnTheLeft: String = "ADD_INVERSE_LEFT"
  val UniqueInverse: String = "UNIQUE_INVERSE"
  val CancelMiddle: String = "ADD_CANCEL"
  val NegateNegate: String = "NEG_NEG"
  val NegateZero: String = "NEG_ZERO"
  val NegateAdd: String = "NEG_ADD"
  val NegateMultiplyLeft: String = "NEG_MUL_LEFT"
  val NegateMultiplyRight: String = "NEG_MUL_RIGHT"

  /**
   * The order the sorting rules use, for a structure whose negation is `negation` if it has one.
   *
   * Under the negations first, so a term sorts beside its own negation; then size, at every level of
   * the recursion, so a sum outranks either of its summands; then structure; and the number of
   * negations last. With no negation the first and last steps are inert and this is the order
   * `Semiring` used before it was generalised, to the comparison.
   */
  def order(negation: Option[String]): Ordering[Term] = new Ordering[Term] {

    def compare(left: Term, right: Term): Int = {
      val (leftBase, leftDepth) = strip(left, 0)
      val (rightBase, rightDepth) = strip(right, 0)
      val bySize = size(leftBase).compare(size(rightBase))
      if (bySize != 0) bySize
      else {
        val byStructure = structurally(leftBase, rightBase)
        if (byStructure != 0) byStructure else leftDepth.compare(rightDepth)
      }
    }

    private def structurally(left: Term, right: Term): Int = (left, right) match {
      case (App(leftFn, leftArgument), App(rightFn, rightArgument)) =>
        val byFunction = compare(leftFn, rightFn)
        if (byFunction != 0) byFunction else compare(leftArgument, rightArgument)

      case (Abs(leftType, leftBody), Abs(rightType, rightBody)) =>
        val byBinder = Type.ordering.compare(leftType, rightType)
        if (byBinder != 0) byBinder else compare(leftBody, rightBody)

      case _ => Term.ordering.compare(left, right)
    }

    private def size(term: Term): Int = term match {
      case App(fn, argument) => size(fn) + size(argument)
      case Abs(_, body) => 1 + size(body)
      case _ => 1
    }

    @annotation.tailrec
    private def strip(term: Term, depth: Int): (Term, Int) = term match {
      case App(Const(name, _), argument) if negation.contains(name) => strip(argument, depth + 1)
      case other => (other, depth)
    }
  }

  /**
   * A commutative semiring: no negation, and `x * 0 = 0` among the laws, since without an inverse
   * it does not follow from the others. `extra` are rules a caller adds unconditionally, such as
   * the ones that open its numerals; `supplied` are derived rules the caller already holds.
   */
  def semiring(
    logic: Logic,
    operations: Operations,
    laws: Laws,
    extra: Vector[Kernel.Thm] = Vector.empty,
    supplied: Map[String, Kernel.Thm] = Map.empty,
    limit: Int = Rewrite.DefaultLimit
  ): Either[LogicError, CommutativeRing] =
    for {
      multiplyZero <- laws.multiplyZero.toRight(MissingDefinition("x * 0 = 0, which a semiring is handed"))
      steps = Steps(logic, operations)
      common <- commonFacts(steps, laws, supplied)
      zeroTimes <- supplied.get(ZeroTimes).map(Right(_)).getOrElse(steps.flipped(laws.multiplyCommutative, multiplyZero))
      facts = common + (TimesZero -> multiplyZero) + (ZeroTimes -> zeroTimes)
      unconditional <- Rewrite.Rule.all(
        logic,
        extra ++ Vector(
          laws.distributive, facts(RightDistributive), laws.multiplyOne, facts(OneTimes),
          multiplyZero, zeroTimes, laws.addZero, facts(ZeroPlus)
        )
      )
      ordered <- orderedRules(logic, laws, facts)
    } yield new CommutativeRing(operations, logic, facts, Rewrite.normaliser(unconditional, ordered, order(None), limit))

  /**
   * A commutative ring: a negation, and `x + -x = 0` among the laws. `x * 0 = 0` is derived rather
   * than asked for, and so is everything about the negation the normaliser needs.
   */
  def ring(
    logic: Logic,
    operations: Operations,
    laws: Laws,
    extra: Vector[Kernel.Thm] = Vector.empty,
    supplied: Map[String, Kernel.Thm] = Map.empty,
    limit: Int = Rewrite.DefaultLimit
  ): Either[LogicError, CommutativeRing] =
    for {
      negate <- operations.negate.toRight(MissingDefinition("the negation a ring is handed"))
      negationName <- negate match {
        case Const(name, _) => Right(name)
        case other => Left(NotOfForm("a negation that is a constant", other))
      }
      inverse <- laws.inverse.toRight(MissingDefinition("x + -x = 0, which a ring is handed"))
      steps = Steps(logic, operations)
      common <- commonFacts(steps, laws, supplied)
      negations <- negationFacts(steps, laws, inverse, common, supplied)
      facts = common ++ negations
      unconditional <- Rewrite.Rule.all(
        logic,
        extra ++ Vector(
          laws.distributive, facts(RightDistributive), laws.multiplyOne, facts(OneTimes),
          facts(TimesZero), facts(ZeroTimes),
          facts(NegateNegate), facts(NegateZero), facts(NegateAdd),
          facts(NegateMultiplyLeft), facts(NegateMultiplyRight),
          inverse, facts(CancelMiddle), laws.addZero, facts(ZeroPlus)
        )
      )
      ordered <- orderedRules(logic, laws, facts)
    } yield new CommutativeRing(
      operations,
      logic,
      facts,
      Rewrite.normaliser(unconditional, ordered, order(Some(negationName)), limit)
    )

  private def orderedRules(logic: Logic, laws: Laws, facts: Map[String, Kernel.Thm]): Either[LogicError, Vector[Rewrite.Rule]] =
    Rewrite.Rule.all(
      logic,
      Vector(
        laws.addAssociative, laws.addCommutative, facts(AddExchange),
        laws.multiplyAssociative, laws.multiplyCommutative, facts(MultiplyExchange)
      )
    )

  /* ================================================================== the moves */

  /** Terms over the operations and the few moves every derivation below makes. */
  private final case class Steps(logic: Logic, operations: Operations) {
    val rules: Rules = logic.rules
    val x: FVar = Term.variable("x", operations.carrier)
    val y: FVar = Term.variable("y", operations.carrier)
    val z: FVar = Term.variable("z", operations.carrier)

    def add(left: Term, right: Term): Either[LogicError, Term] = LogicError.lift(Term.appAll(operations.add, List(left, right)))
    def multiply(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(operations.multiply, List(left, right)))
    def negate(term: Term): Either[LogicError, Term] =
      operations.negate.toRight(MissingDefinition("a negation")).flatMap(n => LogicError.lift(Term.app(n, term)))

    def at(theorem: Kernel.Thm, arguments: Term*): Either[LogicError, Kernel.Thm] = rules.specAll(theorem, arguments.toList)

    /** `|- op a b = op a' b'` from `|- a = a'` and `|- b = b'`. */
    def binary(op: Term, left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv.apTerm(op, left).flatMap(partial => LogicError.lift(Kernel.mkComb(partial, right)))

    def chain(steps: Either[LogicError, Kernel.Thm]*): Either[LogicError, Kernel.Thm] =
      steps.tail.foldLeft(steps.head)((acc, next) => for { l <- acc; r <- next; joined <- Conv.trans(l, r) } yield joined)

    /** `|- !x. c x = d`, turned round by commutativity into `|- !x. x c = d`, or the reverse. */
    def flipped(commutative: Kernel.Thm, law: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        atX <- rules.spec(x, law)
        sides <- Term.destEq(atX.conclusion).toRight(NotOfForm("an equation", atX.conclusion))
        arguments <- sides._1 match {
          case App(App(_, first), second) => Right((first, second))
          case other => Left(NotOfForm("a binary operation", other))
        }
        swapped <- at(commutative, arguments._2, arguments._1)
        result <- Conv.trans(swapped, atX).flatMap(rules.gen(x, _))
      } yield result
  }

  /** `x + (y + z) = y + (x + z)`, from associativity and commutativity, for either operation. */
  private def exchange(steps: Steps, op: Term, associative: Kernel.Thm, commutative: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    chain(
      at(associative, x, y, z).flatMap(Conv.sym),
      at(commutative, x, y).flatMap(binary(op, _, Conv.refl(z))),
      at(associative, y, x, z)
    ).flatMap(rules.genAll(_, List(x, y, z)))
  }

  /** The rules both structures share, derived unless the caller supplied them. */
  private def commonFacts(
    steps: Steps,
    laws: Laws,
    supplied: Map[String, Kernel.Thm]
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    import steps.*
    def orDerive(name: String, derive: => Either[LogicError, Kernel.Thm]): Either[LogicError, (String, Kernel.Thm)] =
      supplied.get(name).map(Right(_)).getOrElse(derive).map(name -> _)

    val ops = steps.operations
    for {
      addExchange <- orDerive(AddExchange, exchange(steps, ops.add, laws.addAssociative, laws.addCommutative))
      multiplyExchange <- orDerive(
        MultiplyExchange,
        exchange(steps, ops.multiply, laws.multiplyAssociative, laws.multiplyCommutative)
      )
      zeroPlus <- orDerive(ZeroPlus, flipped(laws.addCommutative, laws.addZero))
      oneTimes <- orDerive(OneTimes, flipped(laws.multiplyCommutative, laws.multiplyOne))
      // `(x + y) * z = z * (x + y) = z * x + z * y = x * z + y * z`
      rightDistributive <- orDerive(
        RightDistributive,
        for {
          sum <- add(x, y)
          result <- chain(
            at(laws.multiplyCommutative, sum, z),
            at(laws.distributive, z, x, y),
            for {
              left <- at(laws.multiplyCommutative, z, x)
              right <- at(laws.multiplyCommutative, z, y)
              both <- binary(ops.add, left, right)
            } yield both
          )
          general <- rules.genAll(result, List(x, y, z))
        } yield general
      )
    } yield Map(addExchange, multiplyExchange, zeroPlus, oneTimes, rightDistributive)
  }

  /** Everything about the negation, from `x + -x = 0` and the other axioms. */
  private def negationFacts(
    steps: Steps,
    laws: Laws,
    inverse: Kernel.Thm,
    common: Map[String, Kernel.Thm],
    supplied: Map[String, Kernel.Thm]
  ): Either[LogicError, Map[String, Kernel.Thm]] = {
    import steps.*
    val ops = steps.operations
    val zero = ops.zero
    def orDerive(name: String, derive: => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      supplied.get(name).map(Right(_)).getOrElse(derive)

    for {
      // `x * 0 = x * 0 + 0 = x * 0 + (x * 0 + -(x * 0)) = (x * 0 + x * 0) + -(x * 0)
      //        = x * (0 + 0) + -(x * 0) = x * 0 + -(x * 0) = 0`
      timesZero <- orDerive(
        TimesZero,
        for {
          a <- multiply(x, zero)
          negated <- negate(a)
          result <- chain(
            at(laws.addZero, a).flatMap(Conv.sym),
            at(inverse, a).flatMap(Conv.sym).flatMap(binary(ops.add, Conv.refl(a), _)),
            at(laws.addAssociative, a, a, negated).flatMap(Conv.sym),
            for {
              gathered <- at(laws.distributive, x, zero, zero).flatMap(Conv.sym)
              collapsed <- at(laws.addZero, zero).flatMap(binary(ops.multiply, Conv.refl(x), _))
              product <- Conv.trans(gathered, collapsed)
              both <- binary(ops.add, product, Conv.refl(negated))
            } yield both,
            at(inverse, a)
          )
          general <- rules.gen(x, result)
        } yield general
      )
      zeroTimes <- orDerive(ZeroTimes, flipped(laws.multiplyCommutative, timesZero))
      // `-x + x = x + -x = 0`
      inverseLeft <- orDerive(
        InverseOnTheLeft,
        for {
          negated <- negate(x)
          result <- chain(at(laws.addCommutative, negated, x), at(inverse, x))
          general <- rules.gen(x, result)
        } yield general
      )
      // `x + y = 0 ==> y = -x`:
      // `y = y + 0 = y + (x + -x) = (y + x) + -x = (x + y) + -x = 0 + -x = -x`
      unique <- orDerive(
        UniqueInverse,
        for {
          sum <- add(x, y)
          hypothesis <- LogicError.lift(Term.eq(sum, zero))
          assumed <- LogicError.lift(Kernel.assume(hypothesis))
          negated <- negate(x)
          result <- chain(
            at(laws.addZero, y).flatMap(Conv.sym),
            at(inverse, x).flatMap(Conv.sym).flatMap(binary(ops.add, Conv.refl(y), _)),
            at(laws.addAssociative, y, x, negated).flatMap(Conv.sym),
            at(laws.addCommutative, y, x).flatMap(binary(ops.add, _, Conv.refl(negated))),
            binary(ops.add, assumed, Conv.refl(negated)),
            at(common(ZeroPlus), negated)
          )
          general <- rules.disch(hypothesis, result).flatMap(rules.genAll(_, List(x, y)))
        } yield general
      )
      // `--x = x`, the inverse of `-x` being `x`
      negateNegate <- orDerive(
        NegateNegate,
        for {
          negated <- negate(x)
          atThem <- at(unique, negated, x)
          backwards <- at(inverseLeft, x).flatMap(rules.mp(atThem, _))
          result <- Conv.sym(backwards).flatMap(rules.gen(x, _))
        } yield result
      )
      // `-0 = 0`
      negateZero <- orDerive(
        NegateZero,
        for {
          atThem <- at(unique, zero, zero)
          backwards <- at(laws.addZero, zero).flatMap(rules.mp(atThem, _))
          result <- Conv.sym(backwards)
        } yield result
      )
      // `x + (-x + y) = (x + -x) + y = 0 + y = y`
      cancelMiddle <- orDerive(
        CancelMiddle,
        for {
          negated <- negate(x)
          result <- chain(
            at(laws.addAssociative, x, negated, y).flatMap(Conv.sym),
            at(inverse, x).flatMap(binary(ops.add, _, Conv.refl(y))),
            at(common(ZeroPlus), y)
          )
          general <- rules.genAll(result, List(x, y))
        } yield general
      )
      // `-(x + y) = -x + -y`, since `(x + y) + (-x + -y) = x + (y + (-x + -y)) = x + (-x + (y + -y))
      //                                                = x + (-x + 0) = x + -x = 0`
      negateAdd <- orDerive(
        NegateAdd,
        for {
          negatedX <- negate(x)
          negatedY <- negate(y)
          sum <- add(x, y)
          negatedSum <- add(negatedX, negatedY)
          inner <- chain(
            at(common(AddExchange), y, negatedX, negatedY),
            at(inverse, y).flatMap(binary(ops.add, Conv.refl(negatedX), _)),
            at(laws.addZero, negatedX)
          )
          premise <- chain(
            at(laws.addAssociative, x, y, negatedSum),
            binary(ops.add, Conv.refl(x), inner),
            at(inverse, x)
          )
          atThem <- at(unique, sum, negatedSum)
          backwards <- rules.mp(atThem, premise)
          result <- Conv.sym(backwards).flatMap(rules.genAll(_, List(x, y)))
        } yield result
      )
      // `-x * y = -(x * y)`, since `x * y + -x * y = (x + -x) * y = 0 * y = 0`
      negateMultiplyLeft <- orDerive(
        NegateMultiplyLeft,
        for {
          negatedX <- negate(x)
          product <- multiply(x, y)
          negatedProduct <- multiply(negatedX, y)
          premise <- chain(
            at(common(RightDistributive), x, negatedX, y).flatMap(Conv.sym),
            at(inverse, x).flatMap(binary(ops.multiply, _, Conv.refl(y))),
            at(zeroTimes, y)
          )
          atThem <- at(unique, product, negatedProduct)
          result <- rules.mp(atThem, premise).flatMap(rules.genAll(_, List(x, y)))
        } yield result
      )
      // `x * -y = -y * x = -(y * x) = -(x * y)`
      negateMultiplyRight <- orDerive(
        NegateMultiplyRight,
        for {
          negatedY <- negate(y)
          negation <- ops.negate.toRight(MissingDefinition("a negation"))
          result <- chain(
            at(laws.multiplyCommutative, x, negatedY),
            at(negateMultiplyLeft, y, x),
            at(laws.multiplyCommutative, y, x).flatMap(Conv.apTerm(negation, _))
          )
          general <- rules.genAll(result, List(x, y))
        } yield general
      )
    } yield Map(
      TimesZero -> timesZero,
      ZeroTimes -> zeroTimes,
      InverseOnTheLeft -> inverseLeft,
      UniqueInverse -> unique,
      NegateNegate -> negateNegate,
      NegateZero -> negateZero,
      CancelMiddle -> cancelMiddle,
      NegateAdd -> negateAdd,
      NegateMultiplyLeft -> negateMultiplyLeft,
      NegateMultiplyRight -> negateMultiplyRight
    )
  }
}
