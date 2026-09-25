package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What the reals as cuts ask of the rationals beyond an ordered field: that they are Archimedean
 * and dense, with the strict order and the naturals inside `rat` that those two are stated with.
 *
 * == Where the work is done, and why mostly on classes ==
 *
 * `Fraction` proves each of its laws at pairs, by the ring of `int`, because until those laws
 * existed nothing could decide an identity between classes. Once they exist the arrangement turns
 * around: `CommutativeRing` instantiated at the eight laws of `rat` decides every identity between
 * rationals, [[CommutativeRing.consequence]] decides one that holds under a premise such as
 * `2 * RAT_INV 2 = 1` given its coefficient, and the order facts `RAT_LE_ADD` and `RAT_LE_MUL` move
 * an inequality. So the density, the positivity of an inverse and the reciprocal form of Archimedes
 * are arguments about rationals, written as a reader would write them, and none of them opens a
 * representative.
 *
 * Three things do open one, because they are about what a class **is**: the value of `RAT_OF_NUM`
 * at zero and at a successor, and Archimedes itself. The last is where the numerator's sign is
 * spent: a representative `(a, d)` has `a = m` or `a = -m`, and `RAT_OF_NUM m` or `RAT_OF_NUM 0`
 * bounds it, the comparison being one of naturals carried into `int`.
 *
 * == The strict order is a definition, not a second relation ==
 *
 * `RAT_LT x y` is `~(RAT_LE y x)`, which on a total order is the strict one, and every fact about
 * it is proved by assuming `RAT_LE y x` and deriving falsity. That is why nothing here is
 * classical: a strict inequality is a negation, so proving one never needs the excluded middle, and
 * using one is `notElim`.
 */
private[theories] final case class Density(
  quotient: Quotient,
  notation: Notation,
  lifting: Fraction.Lifting,
  integer: Integer,
  peano: Peano,
  known: Map[String, Kernel.Thm],
  zeroDefinition: Kernel.Thm,
  oneDefinition: Kernel.Thm,
  lessDefinition: Kernel.Thm,
  numberDefinition: Kernel.Thm
) {
  private val logic: Logic = quotient.logic
  private val rules = logic.rules
  private val theory: Theory = quotient.theory
  private val integers: Type = TyApp(Integer.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  private def lift[T](result: Either[KernelError, T]): Either[LogicError, T] = LogicError.lift(result)
  private def read(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)
  private def statement(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)
  private def assume(term: Term): Either[LogicError, Kernel.Thm] = lift(Kernel.assume(term))
  private def app(fn: Term, arguments: Term*): Either[LogicError, Term] = lift(Term.appAll(fn, arguments.toList))
  private def fact(name: String): Either[LogicError, Kernel.Thm] = known.get(name).toRight(MissingDefinition(name))

  private def sides(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
    Term.destEq(theorem.conclusion).toRight(NotOfForm("an equation", theorem.conclusion))

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] = sides(theorem).map(_._2)

  /** The two arguments of a binary constant applied. */
  private def binary(term: Term): Either[LogicError, (Term, Term)] =
    term match {
      case App(App(_, left), right) => Right((left, right))
      case other => Left(NotOfForm("an application of two arguments", other))
    }

  /** The last argument of an application. */
  private def argument(term: Term): Either[LogicError, Term] =
    term match {
      case App(_, last) => Right(last)
      case other => Left(NotOfForm("an application", other))
    }

  /** The instance of an existential's predicate at `variable`, reduced. */
  private def instance(existential: Term, variable: Term): Either[LogicError, Term] =
    for {
      predicate <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
      applied <- app(predicate, variable)
      reduced <- Conv.betaRoot(applied).flatMap(rightOf)
    } yield reduced

  /** From `|- R a b`, `|- a = a'` and `|- b = b'`, the theorem `|- R a' b'`, for any relation. */
  private def comparedAt(order: Kernel.Thm, left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    order.conclusion match {
      case App(App(relation, _), _) =>
        for {
          both <- Conv.apTerm(relation, left).flatMap(partial => lift(Kernel.mkComb(partial, right)))
          result <- lift(Kernel.eqMp(both, order))
        } yield result
      case other => Left(NotOfForm("a comparison", other))
    }

  /** From `|- NUM_LE a s` and `|- s = t`, the theorem `|- NUM_LE a t`. */
  private def atMostAt(order: Kernel.Thm, lower: Term, upper: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    comparedAt(order, Conv.refl(lower), upper)

  /** `|- left = right` in `num`, by the semiring. */
  private def naturally(semiring: Semiring, left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    semiring.prove(left, right)

  /**
   * `|- SUC t = NUM_ADD t (SUC ZERO)`, from `t + SUC 0 = SUC (t + 0)` and `t + 0 = t`: the semiring
   * has no rule for the successor, which is how `Fraction.Lifting` reaches it too.
   */
  private def asSum(v: Vocabulary, t: Term): Either[LogicError, Kernel.Thm] =
    for {
      addSuccessor <- peano.fact(Peano.AddAtSuccessor)
      addZero <- peano.fact(Peano.AddAtZero)
      stepped <- rules.specAll(addSuccessor, List(t, v.natZero))
      inner <- rules.spec(t, addZero).flatMap(Conv.apTerm(v.successor, _))
      result <- Conv.trans(stepped, inner).flatMap(Conv.sym)
    } yield result

  /** The constants the arguments are built from, read once. */
  private final case class Vocabulary(
    le: Term, lt: Term, add: Term, mul: Term, neg: Term, inv: Term, zero: Term, one: Term, number: Term,
    intMul: Term, intAdd: Term, intNeg: Term, intOne: Term, embed: Term,
    successor: Term, natAdd: Term, natZero: Term, pairing: Term
  )

  private def vocabulary: Either[LogicError, Vocabulary] =
    for {
      le <- read(Fraction.AtMost)
      lt <- read(Fraction.LessThan)
      add <- read(Fraction.Addition)
      mul <- read(Fraction.Multiplication)
      neg <- read(Fraction.Negation)
      inv <- read(Fraction.Inverse)
      zero <- read(Fraction.Zero)
      one <- read(Fraction.One)
      number <- read(Fraction.OfNumber)
      intMul <- read(Integer.Multiplication)
      intAdd <- read(Integer.Addition)
      intNeg <- read(Integer.Negation)
      intOne <- read(Integer.One)
      embed <- read(Integer.OfNatural)
      successor <- read(Natural.NumberSuccessor)
      natAdd <- read("NUM_ADD")
      natZero <- read("ZERO")
      pairing <- lift(theory.constant(Product.Pairing, Type.fun(integers, Type.fun(numbers, Fraction.Pairs))))
    } yield Vocabulary(
      le, lt, add, mul, neg, inv, zero, one, number, intMul, intAdd, intNeg, intOne, embed,
      successor, natAdd, natZero, pairing
    )

  /** The `rat` instance of `CommutativeRing`, over the laws `Fraction` proved about classes. */
  private def ratRing(v: Vocabulary): Either[LogicError, CommutativeRing] =
    for {
      addAssociative <- fact(Fraction.AddAssociative)
      addCommutative <- fact(Fraction.AddCommutative)
      addZero <- fact(Fraction.AddAtZero)
      mulAssociative <- fact(Fraction.MulAssociative)
      mulCommutative <- fact(Fraction.MulCommutative)
      mulOne <- fact(Fraction.MulAtOne)
      distributive <- fact(Fraction.Distributive)
      inverse <- fact(Fraction.AddNegation)
      ring <- CommutativeRing.ring(
        logic,
        CommutativeRing.Operations(Fraction.Classes, v.add, v.mul, v.zero, v.one, Some(v.neg)),
        CommutativeRing.Laws(
          addAssociative, addCommutative, addZero, mulAssociative, mulCommutative, mulOne,
          distributive, None, Some(inverse)
        )
      )
    } yield ring

  /**
   * The moves an argument about the order is made of, each a derived rule over the published facts.
   * `moved` rewrites both sides of a comparison, and it is the same for `RAT_LE` and `INT_LE`.
   */
  private final case class Moves(
    v: Vocabulary,
    ring: CommutativeRing,
    leAdd: Kernel.Thm,
    leMul: Kernel.Thm,
    leTrans: Kernel.Thm,
    leTotal: Kernel.Thm,
    leRefl: Kernel.Thm,
    zeroLeOne: Kernel.Thm,
    oneNotLeZero: Kernel.Thm
  ) {
    def le(a: Term, b: Term): Either[LogicError, Term] = app(v.le, a, b)
    def lt(a: Term, b: Term): Either[LogicError, Term] = app(v.lt, a, b)
    def plus(a: Term, b: Term): Either[LogicError, Term] = app(v.add, a, b)
    def times(a: Term, b: Term): Either[LogicError, Term] = app(v.mul, a, b)
    def minus(a: Term): Either[LogicError, Term] = app(v.neg, a)

    /** `|- a = b` by the ring of `rat`, reflexivity where the two are already the same term. */
    def same(a: Term, b: Term): Either[LogicError, Kernel.Thm] =
      if (a == b) Right(Conv.refl(a)) else ring.prove(a, b)

    def moved(order: Kernel.Thm, left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      comparedAt(order, left, right)

    /** The two sides of a comparison, rewritten to the terms given by the ring of `rat`. */
    def rewritten(order: Kernel.Thm, left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      for {
        current <- binary(order.conclusion)
        leftEqual <- same(current._1, left)
        rightEqual <- same(current._2, right)
        result <- moved(order, leftEqual, rightEqual)
      } yield result

    /** `a <= b` gives `a + z <= b + z`. */
    def shifted(order: Kernel.Thm, z: Term): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(order.conclusion)
        result <- rules.specAll(leAdd, List(ab._1, ab._2, z)).flatMap(rules.mp(_, order))
      } yield result

    def transitive(first: Kernel.Thm, second: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(first.conclusion)
        bc <- binary(second.conclusion)
        result <- rules.specAll(leTrans, List(ab._1, ab._2, bc._2))
          .flatMap(rules.mp(_, first))
          .flatMap(rules.mp(_, second))
      } yield result

    /** `0 <= a` and `0 <= b` give `0 <= a * b`. */
    def product(first: Kernel.Thm, second: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        a <- binary(first.conclusion).map(_._2)
        b <- binary(second.conclusion).map(_._2)
        result <- rules.specAll(leMul, List(a, b)).flatMap(rules.mp(_, first)).flatMap(rules.mp(_, second))
      } yield result

    /** `a <= b` gives `0 <= b + -a`. */
    def difference(order: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(order.conclusion)
        negated <- minus(ab._1)
        moved <- shifted(order, negated)
        gap <- plus(ab._2, negated)
        result <- rewritten(moved, v.zero, gap)
      } yield result

    /** `0 <= b + -a` gives `a <= b`. */
    def fromDifference(order: Kernel.Thm, a: Term, b: Term): Either[LogicError, Kernel.Thm] =
      shifted(order, a).flatMap(rewritten(_, a, b))

    /** `0 <= c` and `a <= b` give `c * a <= c * b`. */
    def scaled(factor: Kernel.Thm, order: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        c <- binary(factor.conclusion).map(_._2)
        ab <- binary(order.conclusion)
        gap <- difference(order)
        positive <- product(factor, gap)
        ca <- times(c, ab._1)
        cb <- times(c, ab._2)
        target <- minus(ca).flatMap(plus(cb, _))
        spread <- rewritten(positive, v.zero, target)
        result <- fromDifference(spread, ca, cb)
      } yield result

    /** `|- RAT_LT a b = ~(RAT_LE b a)`. */
    def unfolded(a: Term, b: Term): Either[LogicError, Kernel.Thm] = Conv.unfold(lessDefinition, List(a, b))

    /** `a < b` gives `a <= b`, by totality: the other side contradicts the premise. */
    def weakened(less: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(less.conclusion)
        (a, b) = ab
        opened <- unfolded(a, b).flatMap(eq => lift(Kernel.eqMp(eq, less)))
        total <- rules.specAll(leTotal, List(a, b))
        forwards <- le(a, b).flatMap(assume)
        backwardsTerm <- le(b, a)
        backwards <- assume(backwardsTerm)
        absurd <- rules.notElim(opened, backwards)
        fromBackwards <- le(a, b).flatMap(rules.falsityElim(_, absurd))
        result <- rules.disjElim(total, forwards, fromBackwards)
      } yield result

    /** `a < b` from a refutation of `b <= a`, which is what the definition asks. */
    def strict(a: Term, b: Term)(refute: Kernel.Thm => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for {
        backwardsTerm <- le(b, a)
        backwards <- assume(backwardsTerm)
        absurd <- refute(backwards)
        negated <- rules.notIntro(backwardsTerm, absurd)
        result <- unfolded(a, b).flatMap(Conv.sym).flatMap(eq => lift(Kernel.eqMp(eq, negated)))
      } yield result

    /** Falsity from `a < b` and `b <= a`. */
    def contradicts(less: Kernel.Thm, order: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(less.conclusion)
        opened <- unfolded(ab._1, ab._2).flatMap(eq => lift(Kernel.eqMp(eq, less)))
        result <- rules.notElim(opened, order)
      } yield result

    /** Falsity from `1 <= 0`. */
    def absurd(order: Kernel.Thm): Either[LogicError, Kernel.Thm] = rules.notElim(oneNotLeZero, order)

    /** `0 < x` gives `~(x = 0)`: at zero the premise is `~(0 <= 0)`. */
    def nonZero(positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        x <- binary(positive.conclusion).map(_._2)
        isZeroTerm <- lift(Term.eq(x, v.zero))
        isZero <- assume(isZeroTerm)
        lessThanZero <- app(v.lt, v.zero)
        atZero <- Conv.apTerm(lessThanZero, isZero).flatMap(eq => lift(Kernel.eqMp(eq, positive)))
        reflexive <- rules.spec(v.zero, leRefl)
        falsity <- contradicts(atZero, reflexive)
        result <- rules.notIntro(isZeroTerm, falsity)
      } yield result
  }

  /** Every fact of the development, under its name. */
  def facts: Either[LogicError, Vector[(String, Kernel.Thm)]] =
    for {
      v <- vocabulary
      ring <- ratRing(v)
      moves <- for {
        leAdd <- fact(Fraction.AtMostAdd)
        leMul <- fact(Fraction.AtMostMul)
        leTrans <- fact(Fraction.AtMostTransitive)
        leTotal <- fact(Fraction.AtMostTotal)
        leRefl <- fact(Fraction.AtMostReflexive)
        zeroLeOne <- fact(Fraction.ZeroAtMostOne)
        oneNotLeZero <- fact(Fraction.OneNotAtMostZero)
      } yield Moves(v, ring, leAdd, leMul, leTrans, leTotal, leRefl, zeroLeOne, oneNotLeZero)
      semiring <- Semiring.construct(peano)

      weakens <- lessWeakens(moves)
      scaling <- mulLeftMonotone(moves)
      inversePositive <- inverseIsPositive(moves)
      numberZero <- ofNumberZero(v)
      numberSuccessor <- ofNumberSuccessor(v, semiring)
      numberNonNegative <- ofNumberNonNegative(moves, numberZero, numberSuccessor)
      archimedes <- archimedean(v, semiring)
      reciprocal <- archimedeanInverse(moves, inversePositive, archimedes, numberSuccessor, numberNonNegative)
      dense <- density(moves, inversePositive)
    } yield Vector(
      (Fraction.LessWeakens, weakens),
      (Fraction.MulLeftMonotone, scaling),
      (Fraction.InversePositive, inversePositive),
      (Fraction.OfNumberZero, numberZero),
      (Fraction.OfNumberSuccessor, numberSuccessor),
      (Fraction.OfNumberNonNegative, numberNonNegative),
      (Fraction.Archimedes, archimedes),
      (Fraction.ArchimedesInverse, reciprocal),
      (Fraction.Dense, dense)
    )

  private val x: FVar = Term.variable("x", Fraction.Classes)
  private val y: FVar = Term.variable("y", Fraction.Classes)
  private val c: FVar = Term.variable("c", Fraction.Classes)
  private val e: FVar = Term.variable("e", Fraction.Classes)
  private val n: FVar = Term.variable("n", numbers)
  private val m: FVar = Term.variable("m", numbers)

  /** [[Fraction.LessWeakens]]. */
  private def lessWeakens(moves: Moves): Either[LogicError, Kernel.Thm] =
    for {
      less <- moves.lt(x, y).flatMap(assume)
      weak <- moves.weakened(less)
      result <- rules.disch(less.conclusion, weak).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
    } yield result

  /** [[Fraction.MulLeftMonotone]]. */
  private def mulLeftMonotone(moves: Moves): Either[LogicError, Kernel.Thm] =
    for {
      factor <- moves.le(moves.v.zero, c).flatMap(assume)
      order <- moves.le(x, y).flatMap(assume)
      scaled <- moves.scaled(factor, order)
      result <- rules.disch(order.conclusion, scaled)
        .flatMap(rules.disch(factor.conclusion, _))
        .flatMap(rules.gen(y, _))
        .flatMap(rules.gen(x, _))
        .flatMap(rules.gen(c, _))
    } yield result

  /**
   * [[Fraction.InversePositive]]. If `RAT_INV x <= 0` then `0 <= -RAT_INV x`, so
   * `0 <= x * -RAT_INV x`, which is `-1` because `x * RAT_INV x = 1`; adding one gives `1 <= 0`.
   */
  private def inverseIsPositive(moves: Moves): Either[LogicError, Kernel.Thm] = {
    val v = moves.v
    for {
      mulInverse <- fact(Fraction.MulInverse)
      positive <- moves.lt(v.zero, x).flatMap(assume)
      nonZero <- moves.nonZero(positive)
      unit <- rules.spec(x, mulInverse).flatMap(rules.mp(_, nonZero))
      inverse <- app(v.inv, x)
      minusOne <- moves.minus(v.one)
      result <- moves.strict(v.zero, inverse) { below =>
        for {
          negated <- moves.minus(inverse)
          aboveZero <- moves.difference(below).flatMap(moves.rewritten(_, v.zero, negated))
          nonNegative <- moves.weakened(positive)
          product <- moves.product(nonNegative, aboveZero)
          productTerm <- binary(product.conclusion).map(_._2)
          isMinusOne <- moves.ring.consequence(productTerm, minusOne, List(unit -> minusOne))
          atMinusOne <- moves.moved(product, Conv.refl(v.zero), isMinusOne)
          raised <- moves.shifted(atMinusOne, v.one)
          oneBelowZero <- moves.rewritten(raised, v.one, v.zero)
          falsity <- moves.absurd(oneBelowZero)
        } yield falsity
      }
      discharged <- rules.disch(positive.conclusion, result).flatMap(rules.gen(x, _))
    } yield discharged
  }

  /** [[Fraction.OfNumberZero]]: the definition at `ZERO`, with `INT_OF_NUM ZERO = INT_ZERO` inside. */
  private def ofNumberZero(v: Vocabulary): Either[LogicError, Kernel.Thm] =
    for {
      embeddedZero <- integer.fact(Integer.OfNaturalZero)
      unfolded <- Conv.unfold(numberDefinition, List(v.natZero))
      rewriting <- Rewrite.Rule.all(logic, Vector(embeddedZero))
      read <- Rewrite.inTheorem(rewriting, unfolded)
      result <- Conv.sym(zeroDefinition).flatMap(Conv.trans(read, _))
    } yield result

  /**
   * [[Fraction.OfNumberSuccessor]], at pairs. The class of `(SUC n, 0)` against the sum of the classes
   * of `(n, 0)` and `(1, 0)`: the relation between the two pairs is `SUC n = n + 1` in `int`, scaled
   * by one once the stored denominators are read back as `INT_ONE`.
   */
  private def ofNumberSuccessor(v: Vocabulary, semiring: Semiring): Either[LogicError, Kernel.Thm] =
    for {
      addPairs <- fact(Fraction.AddPairs)
      equal <- quotient.fact(Quotient.ProjectionEqual)
      embeddedSum <- integer.fact(Integer.OfNaturalSum)
      successorN <- app(v.successor, n)
      successorZero <- app(v.successor, v.natZero)

      atSuccessor <- Conv.unfold(numberDefinition, List(successorN))
      atN <- Conv.unfold(numberDefinition, List(n))
      successorPair <- rightOf(atSuccessor).flatMap(argument)
      numberPair <- rightOf(atN).flatMap(argument)
      onePair <- rightOf(oneDefinition).flatMap(argument)

      // RAT_ADD (RAT_OF_NUM n) RAT_ONE = RAT_ADD (RAT_OF_PAIR (n, 0)) (RAT_OF_PAIR (1, 0))
      opened <- Conv.apTerm(v.add, atN).flatMap(partial => lift(Kernel.mkComb(partial, oneDefinition)))
      summed <- rules.specAll(addPairs, List(numberPair, onePair))
        .flatMap(Rewrite.inTheorem(lifting.projections, _))
      sumPair <- rightOf(summed).flatMap(argument)

      // INT_OF_NUM (SUC n) = INT_ADD (INT_OF_NUM n) INT_ONE
      successorSum <- asSum(v, n)
      carried <- Conv.apTerm(v.embed, successorSum)
      split <- rules.specAll(embeddedSum, List(n, successorZero))
      oneRule <- Rewrite.Rule.all(logic, Vector(lifting.embeddedOne))
      successorInt <- Conv.trans(carried, split).flatMap(Rewrite.inTheorem(oneRule, _))

      relation <- lifting.related(successorPair, sumPair, List(successorInt -> v.intOne))
      classes <- rules.specAll(equal, List(successorPair, sumPair))
        .flatMap(Conv.sym)
        .flatMap(backwards => lift(Kernel.eqMp(backwards, relation)))
      result <- Conv.trans(atSuccessor, classes)
        .flatMap(step => Conv.sym(summed).flatMap(Conv.trans(step, _)))
        .flatMap(step => Conv.sym(opened).flatMap(Conv.trans(step, _)))
        .flatMap(rules.gen(n, _))
    } yield result

  /** [[Fraction.OfNumberNonNegative]], by induction: `0 <= 1 <= RAT_OF_NUM k + 1`. */
  private def ofNumberNonNegative(
    moves: Moves,
    numberZero: Kernel.Thm,
    numberSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val v = moves.v
    for {
      induction <- peano.naturals.fact(Natural.Induction)
      goal <- statement("!n:num. RAT_LE RAT_ZERO (RAT_OF_NUM n)")
      driver = Induct.withCloser(logic, moves.ring.prove, induction)
      result <- driver.proveBy(
        goal,
        _ =>
          for {
            reflexive <- rules.spec(v.zero, moves.leRefl)
            back <- Conv.sym(numberZero)
            atZero <- moves.moved(reflexive, Conv.refl(v.zero), back)
          } yield atZero,
        step =>
          for {
            raised <- moves.shifted(step.hypothesis, v.one)
            successor <- rules.spec(step.variable, numberSuccessor).flatMap(Conv.sym)
            oneEqual <- binary(raised.conclusion).flatMap(ab => moves.same(ab._1, v.one))
            aboveOne <- moves.moved(raised, oneEqual, successor)
            result <- moves.transitive(moves.zeroLeOne, aboveOne)
          } yield result
      )
    } yield result
  }

  /**
   * [[Fraction.Archimedes]], at pairs. The representative `(a, d)` of `x` has `a = m` or `a = -m`.
   * In the first case `RAT_OF_NUM m` bounds it, since `1 <= SUC d` scaled by `m` is the
   * cross-multiplied order; in the second `RAT_OF_NUM 0` does, since `0 <= m` shifted by `-m` is.
   */
  private def archimedean(v: Vocabulary, semiring: Semiring): Either[LogicError, Kernel.Thm] =
    for {
      chooser <- lift(theory.constant(quotient.names.representative, Type.fun(Fraction.Classes, Fraction.Pairs)))
      representative <- quotient.fact(Quotient.ProjectionOfRepresentative)
      atPairs <- fact(Fraction.AtMostPairs)
      sign <- fact(Fraction.IntSign)
      scaledLaw <- fact(Fraction.IntAtMostScaled)
      embeddedZero <- integer.fact(Integer.OfNaturalZero)
      embeddedOrder <- integer.fact(Integer.AtMostOfNatural)
      addMonotone <- integer.fact(Integer.AddMonotone)
      atMostSum <- peano.fact(Peano.AtMostSum)
      intRing <- Right(lifting.ring)

      chosen <- app(chooser, x)
      back <- rules.spec(x, representative)
      numerator <- read("FST (t:prod(int,num))").flatMap(t =>
        lift(Term.substitute(Map(Term.variable("t", Fraction.Pairs) -> chosen), t)))
      index <- read("SND (t:prod(int,num))").flatMap(t =>
        lift(Term.substitute(Map(Term.variable("t", Fraction.Pairs) -> chosen), t)))
      goal <- statement("?n:num. RAT_LE (x:rat) (RAT_OF_NUM n)")
      goalPredicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
      signAtA <- rules.spec(numerator, sign)
      signParts <- logic.destDisj(signAtA.conclusion).toRight(NotOfForm("a disjunction", signAtA.conclusion))
      minusOne <- app(v.intNeg, v.intOne)

      /** `x <= RAT_OF_NUM bound`, given a proof of the cross-multiplied order read at the pairs. */
      bounded = (bound: Term, crossed: (Term, Term) => Either[LogicError, Kernel.Thm]) =>
        for {
          embeddedBound <- app(v.embed, bound)
          boundPair <- app(v.pairing, embeddedBound, v.natZero)
          order <- rules.specAll(atPairs, List(chosen, boundPair))
          reading <- rightOf(order).flatMap(Rewrite.rewrite(lifting.projections ++ lifting.denominators, _))
          target <- rightOf(reading).flatMap(binary)
          proved <- crossed(target._1, target._2)
          backwards <- Conv.trans(order, reading).flatMap(Conv.sym)
          atClasses <- lift(Kernel.eqMp(backwards, proved))
          unfolded <- Conv.unfold(numberDefinition, List(bound)).flatMap(Conv.sym)
          result <- comparedAt(atClasses, back, unfolded)
        } yield result

      /** One sign: `a = m` bounded by `m`, or `a = -m` bounded by `0`. */
      bySign = (existential: Term, negative: Boolean) =>
        for {
          held <- assume(existential)
          body <- instance(existential, m)
          heldBody <- assume(body)
          embedded <- app(v.embed, m)
          bound = if (negative) v.natZero else m
          successorZero <- app(v.successor, v.natZero)
          witnessed <- bounded(
            bound,
            (left, right) =>
              if (!negative)
                for {
                  // 1 <= SUC d in num, then in int, then scaled by m
                  successorIndex <- app(v.successor, index)
                  sum <- app(v.natAdd, successorZero, index)
                  atMost <- rules.specAll(atMostSum, List(successorZero, index))
                  swapped <- app(v.natAdd, index, successorZero).flatMap(naturally(semiring, sum, _))
                  sumIs <- asSum(v, index).flatMap(Conv.sym).flatMap(Conv.trans(swapped, _))
                  natural <- atMostAt(atMost, successorZero, sumIs)
                  inInt <- rules.specAll(embeddedOrder, List(successorZero, successorIndex))
                    .flatMap(Conv.sym)
                    .flatMap(eq => lift(Kernel.eqMp(eq, natural)))
                  lowerFactor <- app(v.embed, successorZero)
                  upperFactor <- app(v.embed, successorIndex)
                  scaled <- rules.specAll(scaledLaw, List(lowerFactor, upperFactor, m)).flatMap(rules.mp(_, inInt))
                  scaledSides <- binary(scaled.conclusion)
                  leftEqual <- intRing.consequence(
                    scaledSides._1, left, List(heldBody -> minusOne, lifting.embeddedOne -> embedded)
                  )
                  rightEqual <- intRing.prove(scaledSides._2, right)
                  result <- comparedAt(scaled, leftEqual, rightEqual)
                } yield result
              else
                for {
                  // 0 <= m in num, then in int, then shifted by -m
                  sum <- app(v.natAdd, v.natZero, m)
                  atMost <- rules.specAll(atMostSum, List(v.natZero, m))
                  sumIs <- naturally(semiring, sum, m)
                  natural <- atMostAt(atMost, v.natZero, sumIs)
                  inInt <- rules.specAll(embeddedOrder, List(v.natZero, m))
                    .flatMap(Conv.sym)
                    .flatMap(eq => lift(Kernel.eqMp(eq, natural)))
                  embeddedZeroTerm <- app(v.embed, v.natZero)
                  negated <- app(v.intNeg, embedded)
                  shifted <- rules.specAll(addMonotone, List(embeddedZeroTerm, embedded, negated))
                    .flatMap(rules.mp(_, inInt))
                  shiftedSides <- binary(shifted.conclusion)
                  denominator <- binary(right).map(_._2)
                  minusDenominator <- app(v.intNeg, denominator)
                  leftEqual <- intRing.consequence(
                    shiftedSides._1, left, List(heldBody -> minusOne, embeddedZero -> v.intOne)
                  )
                  rightEqual <- intRing.consequence(shiftedSides._2, right, List(embeddedZero -> minusDenominator))
                  result <- comparedAt(shifted, leftEqual, rightEqual)
                } yield result
          )
          introduced <- rules.existsIntro(goalPredicate, bound, witnessed)
          result <- rules.existsElim(held, m, introduced)
        } yield result

      positiveCase <- bySign(signParts._1, false)
      negativeCase <- bySign(signParts._2, true)
      both <- rules.disjElim(signAtA, positiveCase, negativeCase)
      result <- rules.gen(x, both)
    } yield result

  /**
   * [[Fraction.ArchimedesInverse]]. Archimedes at `RAT_INV e` gives `RAT_INV e <= n < n + 1 = N`, and
   * if `e <= RAT_INV N` then multiplying by `N * RAT_INV e`, which is not negative, gives
   * `N <= RAT_INV e`.
   */
  private def archimedeanInverse(
    moves: Moves,
    inversePositive: Kernel.Thm,
    archimedes: Kernel.Thm,
    numberSuccessor: Kernel.Thm,
    numberNonNegative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val v = moves.v
    for {
      mulInverse <- fact(Fraction.MulInverse)
      positive <- moves.lt(v.zero, e).flatMap(assume)
      inverse <- app(v.inv, e)
      inverseAbove <- rules.spec(e, inversePositive).flatMap(rules.mp(_, positive)).flatMap(moves.weakened)
      eUnit <- moves.nonZero(positive).flatMap(nonZero => rules.spec(e, mulInverse).flatMap(rules.mp(_, nonZero)))

      bound <- rules.spec(inverse, archimedes)
      body <- instance(bound.conclusion, n)
      heldBody <- assume(body)
      goal <- statement("?n:num. RAT_LT (RAT_INV (RAT_OF_NUM (SUC n))) (e:rat)")
      goalPredicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))

      numberN <- app(v.number, n)
      big <- app(v.successor, n).flatMap(app(v.number, _))
      bigIs <- rules.spec(n, numberSuccessor)
      oneAtMostBig <- rules.spec(n, numberNonNegative)
        .flatMap(moves.shifted(_, v.one))
        .flatMap(raised =>
          binary(raised.conclusion).flatMap(ab => moves.same(ab._1, v.one))
            .flatMap(oneEqual => Conv.sym(bigIs).flatMap(moves.moved(raised, oneEqual, _))))
      bigPositive <- moves.strict(v.zero, big) { below =>
        moves.transitive(oneAtMostBig, below).flatMap(moves.absurd)
      }
      bigAbove <- moves.weakened(bigPositive)
      bigUnit <- moves.nonZero(bigPositive).flatMap(nonZero => rules.spec(big, mulInverse).flatMap(rules.mp(_, nonZero)))

      inverseBelowBig <- moves.strict(inverse, big) { above =>
        for {
          reaching <- moves.transitive(above, heldBody)
          opened <- moves.moved(reaching, bigIs, Conv.refl(numberN))
          negated <- moves.minus(numberN)
          lowered <- moves.shifted(opened, negated)
          oneBelowZero <- moves.rewritten(lowered, v.one, v.zero)
          falsity <- moves.absurd(oneBelowZero)
        } yield falsity
      }

      bigInverse <- app(v.inv, big)
      result <- moves.strict(bigInverse, e) { above =>
        for {
          factor <- moves.product(bigAbove, inverseAbove)
          scaled <- moves.scaled(factor, above)
          sidesOfScaled <- binary(scaled.conclusion)
          leftEqual <- moves.ring.consequence(sidesOfScaled._1, big, List(eUnit -> big))
          rightEqual <- moves.ring.consequence(sidesOfScaled._2, inverse, List(bigUnit -> inverse))
          reversed <- moves.moved(scaled, leftEqual, rightEqual)
          falsity <- moves.contradicts(inverseBelowBig, reversed)
        } yield falsity
      }
      introduced <- rules.existsIntro(goalPredicate, n, result)
      eliminated <- rules.existsElim(bound, n, introduced)
      discharged <- rules.disch(positive.conclusion, eliminated).flatMap(rules.gen(e, _))
    } yield discharged
  }

  /**
   * [[Fraction.Dense]]. The midpoint `(x + y) * RAT_INV 2` is strictly between: doubling
   * `midpoint <= x` gives `x + y <= x + x`, which is `y <= x`, and the other side is the same.
   */
  private def density(moves: Moves, inversePositive: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val v = moves.v
    for {
      mulInverse <- fact(Fraction.MulInverse)
      two <- moves.plus(v.one, v.one)
      oneAtMostTwo <- moves.shifted(moves.zeroLeOne, v.one).flatMap(moves.rewritten(_, v.one, two))
      twoPositive <- moves.strict(v.zero, two) { below =>
        moves.transitive(oneAtMostTwo, below).flatMap(moves.absurd)
      }
      twoAbove <- moves.weakened(twoPositive)
      twoUnit <- moves.nonZero(twoPositive).flatMap(nonZero => rules.spec(two, mulInverse).flatMap(rules.mp(_, nonZero)))
      half <- app(v.inv, two)

      less <- moves.lt(x, y).flatMap(assume)
      sum <- moves.plus(x, y)
      middle <- moves.times(sum, half)
      doubled <- moves.times(two, middle)
      middleIsHalf <- moves.ring.consequence(doubled, sum, List(twoUnit -> sum))
      goal <- statement("?z:rat. RAT_LT (x:rat) z /\\ RAT_LT z (y:rat)")
      goalPredicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))

      above <- moves.strict(x, middle) { below =>
        for {
          scaled <- moves.scaled(twoAbove, below)
          sumBelow <- moves.times(two, x).flatMap(tx => moves.plus(x, x).flatMap(moves.same(tx, _)))
          atSums <- moves.moved(scaled, middleIsHalf, sumBelow)
          negated <- moves.minus(x)
          lowered <- moves.shifted(atSums, negated)
          backwards <- moves.rewritten(lowered, y, x)
          falsity <- moves.contradicts(less, backwards)
        } yield falsity
      }
      belowY <- moves.strict(middle, y) { above =>
        for {
          scaled <- moves.scaled(twoAbove, above)
          sumAbove <- moves.times(two, y).flatMap(ty => moves.plus(y, y).flatMap(moves.same(ty, _)))
          atSums <- moves.moved(scaled, sumAbove, middleIsHalf)
          negated <- moves.minus(y)
          lowered <- moves.shifted(atSums, negated)
          backwards <- moves.rewritten(lowered, y, x)
          falsity <- moves.contradicts(less, backwards)
        } yield falsity
      }
      between <- rules.conjIntro(above, belowY)
      introduced <- rules.existsIntro(goalPredicate, middle, between)
      result <- rules.disch(less.conclusion, introduced).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
    } yield result
  }
}
