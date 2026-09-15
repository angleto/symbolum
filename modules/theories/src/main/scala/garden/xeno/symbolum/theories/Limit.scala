package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What a sequence of reals converges to, which is the first analysis this repository has.
 *
 * `converges s l` is the epsilon-N statement and nothing more: past some index every term of `s` is
 * within every positive distance of `l`. `lim s` is the value, named by choice the way `NUM_GCD`
 * and `max` are, and pinned by [[Unique]]: where a sequence converges at all, `lim` is what it
 * converges to, and where it does not the term denotes and nothing here says what.
 *
 * == Why this is the missing piece and not one of several ==
 *
 * The reals have carried `COMPLETENESS` since the beginning and until 2026-09-13 nothing read it;
 * `Peano.NUM_ARCHIMEDES` was the first thing to spend it. What the axiom is **for** is convergence,
 * and convergence could not be said here at all: `docs/proving.md` has listed the transcendental
 * functions as the fourth thing to add since it was written, and the reason given each time is that
 * they need sequences. This is the sequences.
 *
 * [[Transcendental]] is the consumer it was written for and the two landed together, which is
 * `docs/adr/0007`'s rule about an axiom arriving in the commit whose derivation needs it, read for
 * a definition instead: a limit operator with no limit taken is a constant nobody has checked.
 *
 * == It costs no axiom, and one thing it does not do ==
 *
 * Both constants are definitions. `lim` reaches `select`, which the chain already pays for, so what
 * a development over this must believe is what it was before; `LimitSpec` asserts that as an
 * equality rather than as a ceiling, the way `CodingSpec` does.
 *
 * **Nothing here proves that a sequence converges.** Every fact below takes convergence as a
 * hypothesis and moves it, with one exception: [[Constant]], where the sequence does not move at
 * all. This is the vocabulary and the bookkeeping rather than an instrument for establishing the
 * thing. What establishes it in general is the monotone convergence theorem, which is the next
 * piece of this development and is where `COMPLETENESS` is spent a second time; until it lands, a
 * caller that wants a limit hands one over or has a sequence that is eventually constant.
 *
 * That pair, [[Constant]] with [[Eventually]], is more than it looks: it settles every sequence
 * that stops moving, which is what a power series at zero is, and it is the whole of what
 * [[Transcendental]] can reach today.
 *
 * == The epsilon principle is here rather than in `Order`, and that is an argument worth making ==
 *
 * [[BelowEveryPositive]] is a fact about the order on the reals and mentions neither constant of
 * this file, so `Order` is where a reader would look for it. It is here because it is what a limit
 * argument spends and nothing below has ever wanted it: three links down it would sit where nothing
 * cites it. If a second consumer appears below this, it moves, and the citation moves with it.
 */
final class Limit private (
  val magnitude: Magnitude,
  val peano: Peano,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = magnitude.classical.logic
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

  /** `|- !x. 0 <= x ==> (!e. 0 < e ==> x < e) ==> x = 0`, the epsilon principle. */
  def belowEveryPositive: Either[LogicError, Kernel.Thm] = fact(Limit.BelowEveryPositive)

  /** `|- !c. converges (\n. c) c` */
  def constantSequence: Either[LogicError, Kernel.Thm] = fact(Limit.Constant)

  /** `|- !s a b. converges s a ==> converges s b ==> a = b` */
  def unique: Either[LogicError, Kernel.Thm] = fact(Limit.Unique)

  /** `|- !s l. converges s l ==> lim s = l` */
  def valueOfConverges: Either[LogicError, Kernel.Thm] = fact(Limit.ValueOfConverges)

  /** `|- !s t l N. (!n. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l` */
  def eventually: Either[LogicError, Kernel.Thm] = fact(Limit.Eventually)
}

object Limit {

  /** `converges s l` says the sequence `s` converges to `l`. */
  val Converges: String = "converges"

  /** `lim s` is what `s` converges to, where it converges to anything. */
  val Value: String = "lim"

  /**
   * The epsilon-N definition, as the text a person checks it by.
   *
   * Written out in the concrete syntax rather than assembled, for the reason `docs/adr/0004` gives
   * for the sixteen axioms: what a reader has to check is that this says "past some index, within
   * every positive distance", and a reader checks a sentence rather than a sequence of builder
   * calls.
   *
   * `NUM_LE N n` rather than `NUM_LT`, and the distance is strict. Both are the usual conventions
   * and neither is load-bearing: the same sequences converge either way, since an index can be
   * stepped and a tolerance can be halved. What **is** load-bearing is that the tolerance is a real
   * and not a natural, which is what makes this convergence in the reals.
   */
  val ConvergesBody: String =
    "\\s:num -> real. \\l:real. !e:real. 0 < e ==> ?N:num. !n:num. NUM_LE N n ==> abs (s n - l) < e"

  /**
   * The value, which is choice applied to the predicate above and nothing else.
   *
   * The same construction as `NUM_GCD`, `NUM_FLOOR` and `max`: a term that denotes at every
   * argument and about which nothing is provable except where something satisfies the predicate.
   * [[Unique]] is what makes that exception the whole of the interesting case: a sequence has at
   * most one limit, so `lim s` is not merely *a* limit of `s` but *the* one.
   */
  val ValueBody: String = "\\s:num -> real. select (\\l:real. converges s l)"

  /** `|- !x. 0 <= x ==> (!e. 0 < e ==> x < e) ==> x = 0` */
  val BelowEveryPositive: String = "LE_BELOW_EVERY_POSITIVE"

  /** `|- !c. converges (\n. c) c` */
  val Constant: String = "CONVERGES_CONSTANT"

  /** `|- !s a b. converges s a ==> converges s b ==> a = b` */
  val Unique: String = "CONVERGES_UNIQUE"

  /** `|- !s l. converges s l ==> lim s = l` */
  val ValueOfConverges: String = "LIM_OF_CONVERGES"

  /** `|- !s t l N. (!n. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l` */
  val Eventually: String = "CONVERGES_EVENTUALLY"

  /** Everything this development proves, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    BelowEveryPositive -> "!x:real. 0 <= x ==> (!e:real. 0 < e ==> x < e) ==> x = 0",
    Constant -> "!c:real. converges (\\n:num. c) c",
    Unique -> "!s:num -> real. !a:real. !b:real. converges s a ==> converges s b ==> a = b",
    ValueOfConverges -> "!s:num -> real. !l:real. converges s l ==> lim s = l",
    Eventually ->
      ("!s:num -> real. !t:num -> real. !l:real. !N:num. " +
        "(!n:num. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l")
  )

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val sequences: Type = Type.fun(numbers, values)

  /** The standard development, which is the chain's own and not a second one beside it. */
  lazy val standard: Limit = Chain.standard.limit

  /**
   * The development over a magnitude and a Peano arithmetic that are in one signature.
   *
   * `base` is the theory to extend rather than `magnitude.theory`, for the reason `Rotation` gives:
   * a constant declared into a side branch is unreachable from every link above it, so what this
   * extends is whatever the chain has reached by the time it gets here.
   */
  def construct(
    magnitude: Magnitude,
    peano: Peano,
    reals: RealTheory,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Limit] = {
    val classical = magnitude.classical

    for {
      convergesBody <- Parser.term(base, notation, ConvergesBody)
      definedConverges <- LogicError.lift(Kernel.defineConstant(base, Converges, convergesBody))
      (afterConverges, convergesDefinition) = definedConverges

      valueBody <- Parser.term(afterConverges, notation, ValueBody)
      definedValue <- LogicError.lift(Kernel.defineConstant(afterConverges, Value, valueBody))
      (theory, valueDefinition) = definedValue

      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)

      irreflexive <- reals.axiom("LT_IRREFLEXIVE")
      leCases <- magnitude.order.leCases
      absCases <- magnitude.absCases
      absAbove <- magnitude.absAbove
      absAboveNegation <- magnitude.absAboveNegation
      absNonNegative <- magnitude.absNonNegative
      absZero <- magnitude.absZero
      atMostSum <- peano.fact(Peano.AtMostSum)
      transitive <- peano.fact(Peano.Transitive)
      addCommutative <- peano.fact(Peano.AddCommutative)

      bounds = Bounds(absCases, absAbove, absAboveNegation, absNonNegative, absZero)
      indices = Indices(atMostSum, transitive, addCommutative)

      epsilon <- belowEveryPositive(logic, linarith, theory, notation, irreflexive, leCases)
      constant <- constantSequence(logic, linarith, theory, notation, convergesDefinition, absCases)
      unique <- uniqueLimit(
        logic, linarith, theory, notation, convergesDefinition, bounds, indices, epsilon)
      value <- valueOfConverges(logic, classical, theory, notation, valueDefinition, unique)
      eventually <- eventuallyEqual(
        logic, theory, notation, convergesDefinition, indices)
    } yield new Limit(
      magnitude,
      peano,
      theory,
      notation,
      Map(Converges -> convergesDefinition, Value -> valueDefinition),
      Map(
        BelowEveryPositive -> epsilon,
        Constant -> constant,
        Unique -> unique,
        ValueOfConverges -> value,
        Eventually -> eventually
      )
    )
  }

  /**
   * What a derivation about `abs` needs, so that each one names what it uses.
   *
   * A record rather than a tuple for the reason `Magnitude.SignPieces` gives: a positional read of
   * five theorems of the same type is how a derivation gets assembled out of the wrong pieces.
   */
  private final case class Bounds(
    cases: Kernel.Thm,
    above: Kernel.Thm,
    aboveNegation: Kernel.Thm,
    nonNegative: Kernel.Thm,
    zero: Kernel.Thm
  )

  /** What a derivation that puts two indices together needs: a sum is above each summand. */
  private final case class Indices(
    atMostSum: Kernel.Thm,
    transitive: Kernel.Thm,
    commutative: Kernel.Thm
  )

  /**
   * `|- !x. 0 <= x ==> (!e. 0 < e ==> x < e) ==> x = 0`, and it is classical in nothing.
   *
   * The textbook proof argues by contradiction from the excluded middle. That is not needed and the
   * route here says why: `Order.LE_CASES` turns `0 <= x` into `0 < x \/ 0 = x`, and the first
   * disjunct is refuted **directly** by instantiating the hypothesis at `e := x`, which gives
   * `x < x` against the irreflexivity axiom. What comes out is a disjunction elimination rather
   * than a contradiction, so **this derivation** reaches no classical axiom, which `LimitSpec`
   * asserts rather than this sentence claiming it.
   *
   * It is the only one in the file of which that is true, and the reason is worth knowing before
   * reading the rest: everything else here touches `abs`, which is defined through `select`, so the
   * choice axiom arrives with the first `Magnitude` fact whatever route the proof takes. What the
   * route buys is not a cheaper foundation, it is that nothing here **decides** anything by the
   * excluded middle.
   *
   * The instantiation at `e := x` is the whole content, and it is the step somebody rediscovers
   * every time they meet this lemma: the hypothesis is about **every** positive tolerance, so it is
   * about the number itself.
   */
  private def belowEveryPositive(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    irreflexive: Kernel.Thm,
    leCases: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", values)

    for {
      nonNegative <- Parser.proposition(theory, notation, "0 <= x:real")
      assumedNonNegative <- LogicError.lift(Kernel.assume(nonNegative))

      everyPositive <- Parser.proposition(theory, notation, "!e:real. 0 < e ==> x:real < e")
      assumedEvery <- LogicError.lift(Kernel.assume(everyPositive))

      target <- Parser.proposition(theory, notation, "x:real = 0")
      zero <- Parser.term(theory, notation, "0:real", values)

      split <- rules.specAll(leCases, List(zero, x)).flatMap(rules.mp(_, assumedNonNegative))

      strict <- Parser.proposition(theory, notation, "0 < x:real")
      fromStrict <- for {
        assumed <- LogicError.lift(Kernel.assume(strict))
        atItself <- rules.spec(x, assumedEvery).flatMap(rules.mp(_, assumed))
        never <- rules.spec(x, irreflexive)
        clash <- rules.notElim(never, atItself)
        anything <- rules.falsityElim(target, clash)
      } yield anything

      equated <- Parser.proposition(theory, notation, "0 = x:real")
      fromEquated <- for {
        assumed <- LogicError.lift(Kernel.assume(equated))
        turn <- linarith.prove("!a:real. 0 = a ==> a = 0")
        applied <- rules.spec(x, turn).flatMap(rules.mp(_, assumed))
      } yield applied

      settled <- rules.disjElim(split, fromStrict, fromEquated)
      result <- rules
        .disch(everyPositive, settled)
        .flatMap(rules.disch(nonNegative, _))
        .flatMap(rules.gen(x, _))
    } yield result
  }

  /**
   * `|- !c. converges (\n. c) c`, the one sequence whose limit needs no analysis.
   *
   * Every index answers, so the witness is `0` and the distance is `abs (c - c)`. That the distance
   * is zero is `Magnitude.ABS_CASES` and one linear step in each branch, which is cheaper than it
   * looks: the two branches differ only in the sign of a difference that vanishes either way.
   *
   * It is not decoration. [[Eventually]] turns it into every sequence that is eventually constant,
   * and that pair is what [[Transcendental]] evaluates a power series at zero with, without any
   * convergence theorem at all.
   */
  private def constantSequence(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    absCases: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val c = Term.variable("c", values)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)

    for {
      sequence <- Parser.term(theory, notation, "\\n:num. c:real", sequences)
      unfolded <- Conv.unfold(convergesDefinition, List(sequence, c))
      opened <- normaliseRight(unfolded)
      body <- rightOf(opened)

      difference <- Parser.term(theory, notation, "c:real - c:real", values)
      distance <- Parser.term(theory, notation, "abs (c:real - c:real)", values)
      split <- rules.spec(difference, absCases)

      plain <- Parser.proposition(theory, notation, "abs (c:real - c:real) = c - c")
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        cancels <- linarith.prove("!a:real. a - a = 0")
        result <- rules.spec(c, cancels).flatMap(Conv.trans(assumed, _))
      } yield result

      negated <- Parser.proposition(theory, notation, "abs (c:real - c:real) = -(c - c)")
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negated))
        cancels <- linarith.prove("!a:real. -(a - a) = 0")
        result <- rules.spec(c, cancels).flatMap(Conv.trans(assumed, _))
      } yield result

      vanishes <- rules.disjElim(split, fromPlain, fromNegated)

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      small <- linarith.prove("!a:real. !e:real. a = 0 ==> 0 < e ==> a < e")
      close <- rules
        .specAll(small, List(distance, e))
        .flatMap(rules.mp(_, vanishes))
        .flatMap(rules.mp(_, assumedPositive))

      guard <- Parser.proposition(theory, notation, "NUM_LE 0 n:num")
      guarded <- rules.disch(guard, close).flatMap(rules.gen(n, _))

      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> abs (c:real - c:real) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      first <- Parser.term(theory, notation, "0:num", numbers)
      witnessed <- rules.existsIntro(predicate, first, guarded)

      whole <- rules.disch(positive, witnessed).flatMap(rules.gen(e, _))
      _ <- sameStatement(notation, whole, body)

      folded <- Conv.sym(opened).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))
      result <- rules.gen(c, folded)
    } yield result
  }

  /**
   * `|- !s a b. converges s a ==> converges s b ==> a = b`: a sequence has at most one limit.
   *
   * The argument is the standard one, and the two places it could have been harder are both closed
   * by something this chain already has. Halving the tolerance is `Linarith`'s, since a numeral
   * denominator is a rational coefficient to it and `0 < e ==> 0 < e / 2` is inside the fragment it
   * decides. Putting the two indices together is `Peano.NUM_LE_ADD`: their sum is above each of
   * them, so no maximum on `num` is needed, and there is none.
   *
   * What is left is one case split on the sign of `a - b`, because the distance between the two
   * limits has to be compared with the tolerance and `abs` is not linear. Each branch is a single
   * `Linarith` step over five hypotheses, which is the triangle inequality written out rather than
   * `Magnitude.ABS_TRIANGLE` applied: the two bounds it would be assembled from are already in
   * hand, and putting them together with the case hypothesis is what the procedure is for.
   *
   * The conclusion is reached through [[BelowEveryPositive]] rather than by contradiction, and what
   * that is worth is stated where that lemma is: not a cheaper foundation, since `abs` costs choice
   * either way, but no step that decides a question by the excluded middle.
   */
  private def uniqueLimit(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds,
    indices: Indices,
    epsilon: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val a = Term.variable("a", values)
    val b = Term.variable("b", values)
    val e = Term.variable("e", values)
    val m = Term.variable("m", numbers)
    val k = Term.variable("k", numbers)

    for {
      toA <- Parser.proposition(theory, notation, "converges (s:num -> real) (a:real)")
      toB <- Parser.proposition(theory, notation, "converges (s:num -> real) (b:real)")
      assumedA <- LogicError.lift(Kernel.assume(toA))
      assumedB <- LogicError.lift(Kernel.assume(toB))

      unfoldedA <- Conv.unfold(convergesDefinition, List(s, a)).flatMap(normaliseRight)
      unfoldedB <- Conv.unfold(convergesDefinition, List(s, b)).flatMap(normaliseRight)
      bodyA <- LogicError.lift(Kernel.eqMp(unfoldedA, assumedA))
      bodyB <- LogicError.lift(Kernel.eqMp(unfoldedB, assumedB))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      half <- Parser.term(theory, notation, "e:real / 2", values)
      halfPositive <- linarith
        .prove("!e:real. 0 < e ==> 0 < e / 2")
        .flatMap(rules.spec(e, _))
        .flatMap(rules.mp(_, assumedPositive))

      nearA <- rules.spec(half, bodyA).flatMap(rules.mp(_, halfPositive))
      nearB <- rules.spec(half, bodyB).flatMap(rules.mp(_, halfPositive))

      // Inside the two witnesses, at the one index that answers both.
      insideA <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (a:real)) < e:real / 2"
      )
      insideB <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE k:num n ==> abs ((s:num -> real) n - (b:real)) < e:real / 2"
      )
      assumedInsideA <- LogicError.lift(Kernel.assume(insideA))
      assumedInsideB <- LogicError.lift(Kernel.assume(insideB))

      index <- Parser.term(theory, notation, "NUM_ADD m:num k:num", numbers)
      aboveM <- rules.specAll(indices.atMostSum, List(m, k))
      aboveK <- for {
        other <- rules.specAll(indices.atMostSum, List(k, m))
        swap <- rules.specAll(indices.commutative, List(k, m))
        carried <- rewriteWith(swap, other)
      } yield carried

      closeA <- rules.spec(index, assumedInsideA).flatMap(rules.mp(_, aboveM))
      closeB <- rules.spec(index, assumedInsideB).flatMap(rules.mp(_, aboveK))

      // The term at the index that answers both, and the two distances, read rather than built:
      // what a reader checks against the case split below is a sentence.
      atIndex <- Parser.term(theory, notation, "(s:num -> real) (NUM_ADD m:num k:num)", values)
      gapA <- Parser.term(
        theory, notation, "(s:num -> real) (NUM_ADD m:num k:num) - (a:real)", values)
      gapB <- Parser.term(
        theory, notation, "(s:num -> real) (NUM_ADD m:num k:num) - (b:real)", values)
      distanceA <- Parser.term(
        theory, notation, "abs ((s:num -> real) (NUM_ADD m:num k:num) - (a:real))", values)
      distanceB <- Parser.term(
        theory, notation, "abs ((s:num -> real) (NUM_ADD m:num k:num) - (b:real))", values)
      distance <- Parser.term(theory, notation, "abs (a:real - b:real)", values)
      difference <- Parser.term(theory, notation, "a:real - b:real", values)

      // The four bounds the triangle inequality is made of, two per limit.
      aboveA <- rules.spec(gapA, bounds.above)
      aboveNegA <- rules.spec(gapA, bounds.aboveNegation)
      aboveB <- rules.spec(gapB, bounds.above)
      aboveNegB <- rules.spec(gapB, bounds.aboveNegation)

      split <- rules.spec(difference, bounds.cases)

      plain <- Parser.proposition(theory, notation, "abs (a:real - b:real) = a - b")
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !u:real. !v:real. !g:real. !e:real. " +
            "-(x - p) <= u ==> x - q <= v ==> u < e / 2 ==> v < e / 2 ==> g = p - q ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atIndex, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveNegA))
          .flatMap(rules.mp(_, aboveB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      negated <- Parser.proposition(theory, notation, "abs (a:real - b:real) = -(a - b)")
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negated))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !u:real. !v:real. !g:real. !e:real. " +
            "x - p <= u ==> -(x - q) <= v ==> u < e / 2 ==> v < e / 2 ==> g = -(p - q) ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atIndex, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveA))
          .flatMap(rules.mp(_, aboveNegB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      closeGap <- rules.disjElim(split, fromPlain, fromNegated)

      withoutB <- rules.existsElim(nearB, k, closeGap)
      withoutA <- rules.existsElim(nearA, m, withoutB)

      everyPositive <- rules.disch(positive, withoutA).flatMap(rules.gen(e, _))
      nonNegative <- rules.spec(difference, bounds.nonNegative)
      vanishes <- rules
        .spec(distance, epsilon)
        .flatMap(rules.mp(_, nonNegative))
        .flatMap(rules.mp(_, everyPositive))
      differenceZero <- rules.spec(difference, bounds.zero).flatMap(rules.mp(_, vanishes))
      equal <- linarith
        .prove("!p:real. !q:real. p - q = 0 ==> p = q")
        .flatMap(rules.specAll(_, List(a, b)))
        .flatMap(rules.mp(_, differenceZero))

      result <- rules
        .disch(toB, equal)
        .flatMap(rules.disch(toA, _))
        .flatMap(rules.gen(b, _))
        .flatMap(rules.gen(a, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s l. converges s l ==> lim s = l`, which is what makes `lim` more than a term.
   *
   * `select` says that a predicate holds of what it chooses **where something satisfies it**, and
   * the convergence in the hypothesis is that something. So `lim s` is a limit of `s`, and
   * [[Unique]] turns "a limit" into "the limit". Both halves are needed and neither is enough: the
   * choice alone would leave `lim s` an arbitrary limit if a sequence could have two.
   */
  private def valueOfConverges(
    logic: Logic,
    classical: Classical,
    theory: Theory,
    notation: Notation,
    valueDefinition: Kernel.Thm,
    unique: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val l = Term.variable("l", values)

    for {
      converges <- Parser.proposition(theory, notation, "converges (s:num -> real) (l:real)")
      assumed <- LogicError.lift(Kernel.assume(converges))

      existential <- Parser.proposition(theory, notation, "?m:real. converges (s:num -> real) m")
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, l, assumed)
      chosen <- classical.witness(witnessed)
      reduced <- Conv
        .betaNormalise(chosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))

      unfolded <- Conv.unfold(valueDefinition, List(s))
      backwards <- Conv.sym(unfolded)
      atLimit <- rewriteWith(backwards, reduced)

      value <- Parser.term(theory, notation, "lim (s:num -> real)", values)
      result <- rules
        .specAll(unique, List(s, value, l))
        .flatMap(rules.mp(_, atLimit))
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.disch(converges, _))
        .flatMap(rules.gen(l, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s t l N. (!n. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l`
   *
   * Agreement past an index is all a limit sees, and the index where the two hypotheses meet is
   * again a sum rather than a maximum. What the derivation actually spends is one congruence: at an
   * index past both, `s n = t n` turns the distance from `l` into the other sequence's distance
   * from `l`, and the tolerance never moves.
   *
   * Stated with the agreement first because that is the hypothesis a caller has: it knows its
   * sequence settles, and it is asking what that buys.
   */
  private def eventuallyEqual(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    indices: Indices
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val t = Term.variable("t", sequences)
    val l = Term.variable("l", values)
    val bound = Term.variable("N", numbers)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)

    for {
      agreement <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE N:num n ==> (s:num -> real) n = (t:num -> real) n"
      )
      assumedAgreement <- LogicError.lift(Kernel.assume(agreement))

      convergesS <- Parser.proposition(theory, notation, "converges (s:num -> real) (l:real)")
      assumedS <- LogicError.lift(Kernel.assume(convergesS))
      unfoldedS <- Conv.unfold(convergesDefinition, List(s, l)).flatMap(normaliseRight)
      bodyS <- LogicError.lift(Kernel.eqMp(unfoldedS, assumedS))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- rules.spec(e, bodyS).flatMap(rules.mp(_, assumedPositive))

      inside <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (l:real)) < e:real"
      )
      assumedInside <- LogicError.lift(Kernel.assume(inside))

      index <- Parser.term(theory, notation, "NUM_ADD m:num N:num", numbers)
      guard <- Parser.proposition(theory, notation, "NUM_LE (NUM_ADD m:num N:num) n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))

      aboveM <- rules.specAll(indices.atMostSum, List(m, bound))
      pastM <- rules
        .conjIntro(aboveM, assumedGuard)
        .flatMap(both => rules.specAll(indices.transitive, List(m, index, n)).flatMap(rules.mp(_, both)))

      aboveN <- for {
        other <- rules.specAll(indices.atMostSum, List(bound, m))
        swap <- rules.specAll(indices.commutative, List(bound, m))
        carried <- rewriteWith(swap, other)
      } yield carried
      pastN <- rules
        .conjIntro(aboveN, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(bound, index, n)).flatMap(rules.mp(_, both)))

      close <- rules.spec(n, assumedInside).flatMap(rules.mp(_, pastM))
      same <- rules.spec(n, assumedAgreement).flatMap(rules.mp(_, pastN))
      moved <- rewriteInProposition(same, close)

      guarded <- rules.disch(guard, moved).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?M:num. !n:num. NUM_LE M n ==> abs ((t:num -> real) n - (l:real)) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, index, guarded)
      eliminated <- rules.existsElim(near, m, witnessed)

      whole <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))
      unfoldedT <- Conv.unfold(convergesDefinition, List(t, l)).flatMap(normaliseRight)
      bodyT <- rightOf(unfoldedT)
      _ <- sameStatement(notation, whole, bodyT)
      folded <- Conv
        .sym(unfoldedT)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))

      result <- rules
        .disch(convergesS, folded)
        .flatMap(rules.disch(agreement, _))
        .flatMap(rules.gen(bound, _))
        .flatMap(rules.gen(l, _))
        .flatMap(rules.gen(t, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * Rewrite the last argument of an application inside a theorem, by congruence.
   *
   * `equation` is `u = v` and `theorem` proves `P ... u`; what comes back proves `P ... v`. Written
   * once because four derivations here want it, and each of them would otherwise take an
   * application apart by hand, which is where a derivation silently starts being about the wrong
   * argument.
   */
  private def rewriteWith(
    equation: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    theorem.conclusion match {
      case App(partial, _) =>
        for {
          congruence <- Conv.apTerm(partial, equation)
          moved <- LogicError.lift(Kernel.eqMp(congruence, theorem))
        } yield moved
      case other => Left(NotOfForm("an application", other))
    }

  /**
   * Rewrite one subterm of a proposition with an equation, wherever in it the subterm occurs.
   *
   * The congruence above reaches the last argument of an application and no further, and what this
   * needs is a term buried under `abs` and a subtraction. So the proposition is abstracted over the
   * subterm, the abstraction is applied to each side of the equation, and the two applications are
   * reduced: that is the general rewrite, written here rather than reached for from `Rewrite`
   * because what is wanted is one occurrence of one term and not a normalising pass.
   */
  private def rewriteInProposition(
    equation: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Term.destEq(equation.conclusion) match {
      case None => Left(NotOfForm("an equation", equation.conclusion))
      case Some((left, _)) =>
        val placeholder = Conv.freshVariable(
          "u",
          Term.typeOf(left),
          Term.freeVariables(theorem.conclusion) ++ Term.freeVariables(equation.conclusion)
        )

        for {
          replaced <- LogicError.lift(replace(theorem.conclusion, left, placeholder))

          // A replacement that found nothing would make the congruence below a no-op and hand back
          // the theorem it was given, which is what a rewrite that missed looks like from outside.
          _ <- if (replaced != theorem.conclusion) Right(())
               else Left(NotOfForm(s"a proposition mentioning ${left}", theorem.conclusion))

          template <- LogicError.lift(Term.abs(placeholder, replaced))
          congruence <- Conv.apTerm(template, equation)
          reduced <- Conv.betaSides(congruence)
          moved <- LogicError.lift(Kernel.eqMp(reduced, theorem))
        } yield moved
    }

  /** Every occurrence of `target` inside `term`, replaced by `replacement`. */
  private def replace(term: Term, target: Term, replacement: Term): Either[KernelError, Term] =
    if (term == target) Right(replacement)
    else
      term match {
        case App(fn, argument) =>
          for {
            left <- replace(fn, target, replacement)
            right <- replace(argument, target, replacement)
            joined <- Term.app(left, right)
          } yield joined
        // No descent under a binder: the kernel keeps those constructors to itself, and no
        // caller here rewrites inside one. An occurrence that is only under a binder therefore
        // leaves the term unchanged, which the check above turns into a refusal.
        case other => Right(other)
      }

  /** Refuse with both statements named where a derivation and its target have drifted apart. */
  private def sameStatement(
    notation: Notation,
    theorem: Kernel.Thm,
    target: Term
  ): Either[LogicError, Unit] =
    if (theorem.conclusion == target) Right(())
    else Left(NotOfForm(s"a proof of ${Show.show(notation, target)}", theorem.conclusion))

  /** Beta-normalise the right side of an equation, keeping it an equation. */
  private def normaliseRight(equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      right <- rightOf(equation)
      normal <- Conv.betaNormalise(right)
      joined <- Conv.trans(equation, normal)
    } yield joined

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
