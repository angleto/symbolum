package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Continuity of a real function at a point, the intermediate value theorem, and the extreme value
 * theorem.
 *
 * `continuous f x` is the epsilon-delta statement written out, the way `converges` is the
 * epsilon-N one: for every positive tolerance there is a positive radius inside which `f` stays
 * within the tolerance of `f x`. It is a definition and costs no axiom. What it buys is
 * [[Continuity.IntermediateValue]]: a function continuous on `[a, b]` takes every value between
 * `f a` and `f b` somewhere in `[a, b]`, which is what every fact about `ln` waits on, since `ln`
 * is the inverse of the exponential named by choice and a choice is silent until something says
 * the exponential reaches the value. And since 2026-09-25 it buys [[Continuity.AttainsMaximum]] and
 * [[Continuity.AttainsMinimum]], that such a function takes a greatest and a least value on
 * `[a, b]`, through [[Continuity.IntervalGluing]], the compactness of the interval stated for a
 * property that glues. Their derivation is `ExtremeValue`, whose docstring is the argument.
 *
 * == Why this is the fourth thing `COMPLETENESS` buys ==
 *
 * The rationals are an ordered field in which the theorem is false: `x * x - 2` is continuous, is
 * negative at `0` and positive at `2`, and has no rational root. So the proof has to spend the
 * sixteenth axiom, as `Peano.NUM_ARCHIMEDES`, `Limit.MONOTONE_CONVERGES` and `Root.SQRT_EXISTS` do.
 * The argument is the textbook one: the points of `[a, b]` where `f` is at most the value hold `a`
 * and sit under `b`, so they have a least upper bound `s`, and `f s` is neither below the value nor
 * above it. Below, continuity at `s` puts a point a little past `s` in the set, so `s` was not an
 * upper bound; above, it keeps `f` over the value on a stretch below `s`, so a point a little
 * before `s` is an upper bound already and `s` was not the least.
 *
 * `COMPLETENESS` is spent **inline** here, as it is in those three, rather than through a published
 * supremum. This said until 2026-09-25 that the fifth consumer to want the supremum by name would
 * move it into a development of its own. The fifth and sixth are `ExtremeValue`'s, and what they
 * do with the axiom was read rather than predicted: each of the six specialises it at a set,
 * beta-reduces, detaches the two premises and opens the existential, about five lines, and the
 * axiom **is** already the statement a supremum development would publish. What such a development
 * would add is the supremum as a term, a `sup S` to write in a statement, and none of the six
 * writes one, since each opens the existential once and works under it. So the forecast is
 * withdrawn rather than met, and the first statement that needs to name a supremum is what
 * revives it.
 *
 * == The derivation has no quotient in it that a procedure is asked about ==
 *
 * The one step that moves by "a little" moves by `min (d / 2) (b - s)` below the root and
 * `min (d / 2) (s - a)` above it, which stays inside `[a, b]` and inside the radius at once. A
 * numeral denominator is a rational coefficient to `Linarith`, so `d / 2` is inside the fragment it
 * decides, and `Magnitude`'s three facts about `min` are the only thing said about the minimum.
 *
 * == What it costs ==
 *
 * One constant, no axiom. It is a development of its own rather than a section of [[Limit]],
 * whose first sentence says it is what a sequence converges to, and continuity at a point is a
 * statement about a function and a radius with no sequence in it.
 */
final class Continuity private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Continuity {

  /* ---------------------------------------------------------------- the constant */

  /**
   * `continuous f x`: `f` is continuous at `x`, **two-sided**, looking at the points on both sides
   * of `x` whatever interval a caller has in mind. So the interval theorems' hypothesis `!x. a <= x
   * /\ x <= b ==> continuous f x` asks more at the two ends than a textbook's "continuous on
   * `[a, b]`" does, and each of them has a textbook form stated with [[ContinuousWithin]]: this
   * file's and `Derivative`'s since 2026-09-25, `Integral`'s since 2026-09-26, which the sentence
   * here said of all of them a day before it was true. `IntegralWithinSpec` holds the census, and
   * lists as pending, with the card that owes it, any that has none yet.
   */
  val Continuous: String = "continuous"

  /** The definition, as text: the epsilon-delta statement at one point. */
  val ContinuousBody: String =
    "\\f:real -> real. \\x:real. !e:real. 0 < e ==> " +
      "?d:real. 0 < d /\\ (!y:real. abs (y - x) < d ==> abs (f y - f x) < e)"

  /* ------------------------------------------------------------------- the facts */

  /**
   * `|- !c x. continuous (\y. c) x`
   *
   * A constant function is continuous everywhere. Published for what it guards rather than for
   * what it says: a definition nothing satisfies would make the intermediate value theorem true
   * and empty, and this and [[Identity]] are the two functions every other fact about continuity
   * is built from.
   */
  val Constant: String = "CONTINUOUS_CONST"

  /** `|- !x. continuous (\y. y) x`: the identity is continuous everywhere, at radius the tolerance. */
  val Identity: String = "CONTINUOUS_ID"

  /**
   * `|- !f a b y. a <= b ==> (!x. a <= x /\ x <= b ==> continuous f x) ==>
   * f a <= y ==> y <= f b ==> ?x. a <= x /\ x <= b /\ f x = y`
   *
   * The intermediate value theorem, for a value between `f a` and `f b` in that order. The other
   * order is this one at `\x. 0 - f x`, whose continuity is [[Negation]].
   */
  val IntermediateValue: String = "INTERMEDIATE_VALUE"

  /**
   * `|- !P a b. a <= b ==> (!u v w. u <= v /\ v <= w /\ P u v /\ P v w ==> P u w) ==>
   * (!x. a <= x /\ x <= b ==> ?d. 0 < d /\ (!u v. a <= u /\ u <= x /\ x <= v /\ v <= b /\ v - u < d
   * ==> P u v)) ==> P a b`
   *
   * The compactness of `[a, b]`, in the one form the facts below need: a property of intervals
   * that glues end to end, and holds on every short enough interval around each point, holds on
   * `[a, b]`. It is about no function and could live with the order; it is here because it is what
   * continuity at every point of an interval is turned into a statement about the interval with,
   * and [[Continuity.Bounded]] and [[AttainsMaximum]] are each one instance of it.
   */
  val IntervalGluing: String = "INTERVAL_GLUING"

  /**
   * `|- !f x. continuous f x ==> continuous (\y. 0 - f y) x`
   *
   * The first fact about combining continuous functions anything here needed: [[AttainsMinimum]] is
   * [[AttainsMaximum]] at the negation. [[Linear]] is the general one since 2026-09-25; this stays
   * because it is what the minimum is written with, and is shorter than that one at `-1` and `0`.
   */
  val Negation: String = "CONTINUOUS_NEG"

  /**
   * `|- !f a b. a <= b ==> (!x. a <= x /\ x <= b ==> continuous f x) ==>
   * ?M. !x. a <= x /\ x <= b ==> f x <= M`
   *
   * A function continuous on `[a, b]` is bounded above there. The bound below is this at
   * `\y. 0 - f y`, or [[AttainsMinimum]], which says more.
   */
  val Bounded: String = "CONTINUOUS_BOUNDED"

  /**
   * `|- !f a b. a <= b ==> (!x. a <= x /\ x <= b ==> continuous f x) ==>
   * ?m. a <= m /\ m <= b /\ (!x. a <= x /\ x <= b ==> f x <= f m)`
   *
   * The extreme value theorem, for the maximum: a function continuous on `[a, b]` takes a greatest
   * value there. Like [[IntermediateValue]] it is false over the rationals, where `x * (2 - x * x)`
   * on `[0, 2]` climbs towards its maximum at the square root of two-thirds and never reaches it, so
   * it spends `COMPLETENESS`.
   */
  val AttainsMaximum: String = "CONTINUOUS_ATTAINS_MAX"

  /**
   * `|- !f a b. a <= b ==> (!x. a <= x /\ x <= b ==> continuous f x) ==>
   * ?m. a <= m /\ m <= b /\ (!x. a <= x /\ x <= b ==> f m <= f x)`
   *
   * The extreme value theorem, for the minimum.
   */
  val AttainsMinimum: String = "CONTINUOUS_ATTAINS_MIN"

  /**
   * `|- !f g x p q. continuous f x ==> continuous g x ==> continuous (\y. p * f y + q * g y) x`
   *
   * A linear combination of two functions continuous at a point is continuous there. It is what the
   * mean value theorem asked for, at `(b - a) * f y - (f b - f a) * y`, and it is stated for any
   * two functions and any two coefficients rather than for that one, since the special case would
   * be the general one proved with the letters fixed. The product is [[Product]]; a quotient is not
   * here, because nothing has asked for one.
   */
  val Linear: String = "CONTINUOUS_LINEAR"

  /**
   * `|- !f g x. continuous f x ==> continuous g x ==> continuous (\y. f y * g y) x`
   *
   * The product of two functions continuous at a point is continuous there. Taylor's theorem asked
   * for it: Rolle wants the remainder continuous at both ends of the interval, and every term of a
   * Taylor polynomial is a derivative times a power. The argument splits `f y * g y - f x * g x` into
   * `f y * (g y - g x) + g x * (f y - f x)`, and the first factor of the first term is held below
   * `abs (f x) + 1` by `f`'s continuity at tolerance one, which is the third radius the two shares
   * of `e` are taken under.
   */
  val Product: String = "CONTINUOUS_MUL"

  /**
   * `|- !f g x. continuous f x ==> continuous g x ==> continuous (\y. f y + g y) x`
   *
   * The sum of two functions continuous at a point is continuous there. It is [[Linear]] at the
   * coefficients one and one, and nothing more is proved for it: the kernel's abstraction rule
   * carries `1 * f y + 1 * g y = f y + g y` under the binder, so the function is the sum as written
   * and no extensionality is spent.
   */
  val Sum: String = "CONTINUOUS_ADD"

  /**
   * `|- !f g x. continuous g x ==> continuous f (g x) ==> continuous (\y. f (g y)) x`
   *
   * A function continuous at `g x` composed with a function continuous at `x` is continuous at `x`.
   * The radius `f` answers at `g x` is handed to `g` as its tolerance, which is the whole argument
   * and why no share of `e` is taken; it compares nothing, and so reaches no axiom, which
   * `ContinuitySpec` asserts. With [[Sum]], [[Product]], [[Constant]] and [[Identity]] it
   * is what makes a polynomial, or a continuous function of one, continuous by composing lemmas
   * rather than by a derivation of its own.
   */
  val Compose: String = "CONTINUOUS_COMPOSE"

  /**
   * `f` continuous on `[a, b]` is uniformly continuous there: for every tolerance one radius serves
   * every pair of points of the interval. Heine and Cantor's theorem, and the gluing's third use,
   * over "one radius serves every point of `[u, v]` against every point at all", which is the form
   * of the property that glues. It costs what the extreme value theorem costs.
   */
  val Uniform: String = "CONTINUOUS_UNIFORM"

  /**
   * `continuous_within f a b x`: `f` is continuous at `x` relative to `[a, b]`, the epsilon-delta
   * statement with the nearby points restricted to the interval. What a textbook means by "continuous
   * on `[a, b]`" at an end, where `continuous` also looks outside. `Within` has the argument.
   */
  val ContinuousWithin: String = "continuous_within"

  val ContinuousWithinBody: String =
    "\\f:real -> real. \\a:real. \\b:real. \\x:real. !e:real. 0 < e ==> ?d:real. 0 < d /\\ " +
      "(!y:real. a <= y /\\ y <= b /\\ abs (y - x) < d ==> abs (f y - f x) < e)"

  /**
   * `tends f x l`: `f` tends to `l` at `x`, the epsilon-delta statement over the points **other
   * than** `x`, so nothing is asked of `f x` and `f` need not be defined sensibly there. What a
   * limit of a function is, as `converges` is a limit of a sequence; `Derivative`'s L'Hopital is
   * its first consumer, where the function is a quotient whose denominator vanishes at `x`.
   */
  val Tends: String = "tends"

  /** The definition, as text: [[ContinuousBody]] with `0 < abs (y - x)` among the conditions on `y`. */
  val TendsBody: String =
    "\\f:real -> real. \\x:real. \\l:real. !e:real. 0 < e ==> " +
      "?d:real. 0 < d /\\ (!y:real. 0 < abs (y - x) /\\ abs (y - x) < d ==> abs (f y - l) < e)"

  /**
   * `|- !f x. continuous f x ==> tends f x (f x)`: a continuous function tends to its value, the
   * radius of the continuity serving the limit, which asks less of the points near `x`.
   */
  val ContinuousTends: String = "CONTINUOUS_TENDS"

  /** `|- !f a b x. continuous f x ==> continuous_within f a b x`: the relative hypothesis is the weaker. */
  val WithinOfContinuous: String = "CONTINUOUS_WITHIN_OF_CONTINUOUS"

  /** `|- !f a b x. a <= x /\ x <= b ==> COND (x < a) (f a) (COND (b < x) (f b) (f x)) = f x`. */
  val ExtensionAgrees: String = "CONTINUOUS_EXTENSION_AGREES"

  /**
   * `|- !f a b. a <= b ==> (!x. a <= x /\ x <= b ==> continuous_within f a b x) ==>
   * !x. continuous (\y. COND (y < a) (f a) (COND (b < y) (f b) (f y))) x`: a function continuous
   * relative to the interval, extended by its value at the nearer end, is continuous everywhere.
   * The lemma every textbook form below is carried by.
   */
  val Extension: String = "CONTINUOUS_EXTENSION"

  /** [[IntermediateValue]] with continuity relative to `[a, b]`. */
  val IntermediateValueWithin: String = "INTERMEDIATE_VALUE_WITHIN"

  /** [[Bounded]] with continuity relative to `[a, b]`. */
  val BoundedWithin: String = "CONTINUOUS_BOUNDED_WITHIN"

  /** [[AttainsMaximum]] with continuity relative to `[a, b]`. */
  val AttainsMaximumWithin: String = "CONTINUOUS_ATTAINS_MAX_WITHIN"

  /** [[AttainsMinimum]] with continuity relative to `[a, b]`. */
  val AttainsMinimumWithin: String = "CONTINUOUS_ATTAINS_MIN_WITHIN"

  /** [[Uniform]] with continuity relative to `[a, b]`. */
  val UniformWithin: String = "CONTINUOUS_UNIFORM_WITHIN"

  private val RelativeText: String = "(!x:real. a <= x /\\ x <= b ==> continuous_within f a b x)"

  /** What every derived fact says, as text, in the order they are derived. */
  val Statements: Vector[(String, String)] = Vector(
    Constant -> "!c:real. !x:real. continuous (\\y:real. c) x",
    Identity -> "!x:real. continuous (\\y:real. y) x",
    IntermediateValue ->
      ("!f:real -> real. !a:real. !b:real. !y:real. a <= b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> continuous f x) ==> f a <= y ==> y <= f b ==> " +
        "?x:real. a <= x /\\ x <= b /\\ f x = y"),
    IntervalGluing ->
      ("!P:real -> real -> bool. !a:real. !b:real. a <= b ==> " +
        "(!u:real. !v:real. !w:real. u <= v /\\ v <= w /\\ P u v /\\ P v w ==> P u w) ==> " +
        "(!x:real. a <= x /\\ x <= b ==> ?d:real. 0 < d /\\ " +
        "(!u:real. !v:real. a <= u /\\ u <= x /\\ x <= v /\\ v <= b /\\ v - u < d ==> P u v)) ==> P a b"),
    Negation -> "!f:real -> real. !x:real. continuous f x ==> continuous (\\y:real. 0 - f y) x",
    Bounded ->
      ("!f:real -> real. !a:real. !b:real. a <= b ==> (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "?M:real. !x:real. a <= x /\\ x <= b ==> f x <= M"),
    AttainsMaximum ->
      ("!f:real -> real. !a:real. !b:real. a <= b ==> (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "?m:real. a <= m /\\ m <= b /\\ (!x:real. a <= x /\\ x <= b ==> f x <= f m)"),
    AttainsMinimum ->
      ("!f:real -> real. !a:real. !b:real. a <= b ==> (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "?m:real. a <= m /\\ m <= b /\\ (!x:real. a <= x /\\ x <= b ==> f m <= f x)"),
    Linear ->
      ("!f:real -> real. !g:real -> real. !x:real. !p:real. !q:real. continuous f x ==> continuous g x ==> " +
        "continuous (\\y:real. p * f y + q * g y) x"),
    Product ->
      "!f:real -> real. !g:real -> real. !x:real. continuous f x ==> continuous g x ==> continuous (\\y:real. f y * g y) x",
    Sum ->
      "!f:real -> real. !g:real -> real. !x:real. continuous f x ==> continuous g x ==> continuous (\\y:real. f y + g y) x",
    Compose ->
      "!f:real -> real. !g:real -> real. !x:real. continuous g x ==> continuous f (g x) ==> continuous (\\y:real. f (g y)) x",
    Uniform ->
      ("!f:real -> real. !a:real. !b:real. !e:real. a <= b ==> (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "0 < e ==> ?d:real. 0 < d /\\ (!x:real. !y:real. a <= x /\\ x <= b /\\ a <= y /\\ y <= b /\\ " +
        "abs (x - y) < d ==> abs (f x - f y) < e)"),
    WithinOfContinuous ->
      "!f:real -> real. !a:real. !b:real. !x:real. continuous f x ==> continuous_within f a b x",
    ContinuousTends -> "!f:real -> real. !x:real. continuous f x ==> tends f x (f x)",
    ExtensionAgrees ->
      ("!f:real -> real. !a:real. !b:real. !x:real. a <= x /\\ x <= b ==> " +
        "COND (x < a) (f a) (COND (b < x) (f b) (f x)) = f x"),
    Extension ->
      (s"!f:real -> real. !a:real. !b:real. a <= b ==> $RelativeText ==> " +
        "!x:real. continuous (\\y:real. COND (y < a) (f a) (COND (b < y) (f b) (f y))) x"),
    IntermediateValueWithin ->
      (s"!f:real -> real. !a:real. !b:real. !y:real. a <= b ==> $RelativeText ==> f a <= y ==> y <= f b ==> " +
        "?x:real. a <= x /\\ x <= b /\\ f x = y"),
    BoundedWithin ->
      (s"!f:real -> real. !a:real. !b:real. a <= b ==> $RelativeText ==> " +
        "?M:real. !x:real. a <= x /\\ x <= b ==> f x <= M"),
    AttainsMaximumWithin ->
      (s"!f:real -> real. !a:real. !b:real. a <= b ==> $RelativeText ==> " +
        "?m:real. a <= m /\\ m <= b /\\ (!x:real. a <= x /\\ x <= b ==> f x <= f m)"),
    AttainsMinimumWithin ->
      (s"!f:real -> real. !a:real. !b:real. a <= b ==> $RelativeText ==> " +
        "?m:real. a <= m /\\ m <= b /\\ (!x:real. a <= x /\\ x <= b ==> f m <= f x)"),
    UniformWithin ->
      (s"!f:real -> real. !a:real. !b:real. !e:real. a <= b ==> $RelativeText ==> " +
        "0 < e ==> ?d:real. 0 < d /\\ (!x:real. !y:real. a <= x /\\ x <= b /\\ a <= y /\\ y <= b /\\ " +
        "abs (x - y) < d ==> abs (f x - f y) < e)")
  )

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Functions: Type = Type.fun(Reals, Reals)

  /** The development in the chain's signature, which is the one a consumer reaches for. */
  lazy val standard: Continuity = Chain.standard.continuity

  /**
   * The development over the reals, their order and their magnitude, extending `base`.
   *
   * `base` is the chain's end when this is built rather than `reals.theory`, for the reason every
   * link gives: a constant declared into a side branch is unreachable from every link above it.
   */
  def construct(
    classical: Classical,
    reals: RealTheory,
    magnitude: Magnitude,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Continuity] =
    for {
      body <- Parser.term(base, notation, ContinuousBody)
      defined <- LogicError.lift(Kernel.defineConstant(base, Continuous, body))
      (withContinuous, definition) = defined
      withinBody <- Parser.term(withContinuous, notation, ContinuousWithinBody)
      withinDefined <- LogicError.lift(Kernel.defineConstant(withContinuous, ContinuousWithin, withinBody))
      (withWithin, withinDefinition) = withinDefined
      tendsBody <- Parser.term(withWithin, notation, TendsBody)
      tendsDefined <- LogicError.lift(Kernel.defineConstant(withWithin, Tends, tendsBody))
      (theory, tendsDefinition) = tendsDefined

      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)
      steps = Steps(logic, linarith, theory, notation, definition)

      constant <- constantFunction(steps, magnitude)
      identity <- identityFunction(steps)
      intermediate <- intermediateValue(steps, reals, magnitude)
      extremes <- ExtremeValue.prove(steps, reals, magnitude, classical)
      linear <- linearCombination(steps, reals, magnitude)
      product <- productOfTwo(steps, reals, magnitude)
      sum <- sumOfTwo(steps, linear)
      composed <- composition(steps, reals, magnitude)

      twoSided = Map(Constant -> constant, Identity -> identity, IntermediateValue -> intermediate, Linear -> linear, Product -> product,
        Sum -> sum, Compose -> composed) ++
        extremes
      relative <- Within.prove(steps, withinDefinition, reals, magnitude, classical, twoSided)
      tends <- continuousTends(steps, tendsDefinition)
      facts = twoSided ++ relative + (ContinuousTends -> tends)

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
    } yield new Continuity(
      theory, notation, logic,
      Map(Continuous -> definition, ContinuousWithin -> withinDefinition, Tends -> tendsDefinition), facts)

  /**
   * The few moves every derivation below makes, over one theory, which is `Root`'s arrangement:
   * `lemma` is the one place anything is decided, `Linarith` on a closed schematic statement over
   * real variables, and everything else specialises, detaches and unfolds.
   */
  private[theories] final case class Steps(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    definition: Kernel.Thm
  ) {
    val rules: Rules = logic.rules

    def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)
    def real(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, Reals)
    def assume(text: String): Either[LogicError, Kernel.Thm] =
      proposition(text).flatMap(statement => LogicError.lift(Kernel.assume(statement)))

    /** A schematic arithmetic fact, closed. Refused here if `Linarith` cannot settle it. */
    def lemma(text: String): Either[LogicError, Kernel.Thm] = linarith.prove(text)

    def at(theorem: Either[LogicError, Kernel.Thm], arguments: String*): Either[LogicError, Kernel.Thm] =
      theorem.flatMap(proved =>
        arguments.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, text) =>
          for { terms <- acc; term <- real(text) } yield terms :+ term
        }.flatMap(rules.specAll(proved, _)))

    def mp(implication: Kernel.Thm, premises: Either[LogicError, Kernel.Thm]*): Either[LogicError, Kernel.Thm] =
      premises.foldLeft[Either[LogicError, Kernel.Thm]](Right(implication)) { (acc, premise) =>
        for { current <- acc; proved <- premise; next <- rules.mp(current, proved) } yield next
      }

    def conj(left: Either[LogicError, Kernel.Thm], right: Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for { l <- left; r <- right; both <- rules.conjIntro(l, r) } yield both

    def existential(text: String): Either[LogicError, Term] =
      proposition(text).flatMap(statement =>
        logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement)))

    /** `|- continuous f x = <the epsilon-delta statement at f and x>`, reduced. */
    def unfolded(function: Term, point: Term): Either[LogicError, Kernel.Thm] =
      for {
        equation <- Conv.unfold(definition, List(function, point))
        right <- Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
        normal <- Conv.betaNormalise(right)
        joined <- Conv.trans(equation, normal)
      } yield joined

    /** `|- continuous f x` from a proof of its epsilon-delta statement. */
    def folded(function: Term, point: Term, statement: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        equation <- unfolded(function, point)
        backwards <- Conv.sym(equation)
        result <- LogicError.lift(Kernel.eqMp(backwards, statement))
      } yield result
  }

  /** [[Constant]]: the distance of `c` from `c` is zero, under every tolerance, at radius one. */
  private def constantFunction(steps: Steps, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val c = Term.variable("c", Reals)
    val x = Term.variable("x", Reals)
    val e = Term.variable("e", Reals)
    val y = Term.variable("y", Reals)
    for {
      function <- Parser.term(theory, notation, "\\y:real. c:real", Functions)
      positive <- proposition("0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      distance <- at(magnitude.fact(Magnitude.OfNonNegative), "c - c:real")
        .flatMap(mp(_, lemma("!c:real. 0 <= c - c").flatMap(rules.spec(c, _))))
      within <- at(lemma("!a:real c:real e:real. a = c - c ==> 0 < e ==> a < e"), "abs (c - c:real)", "c:real", "e:real")
        .flatMap(mp(_, Right(distance), Right(assumedPositive)))
      near <- proposition("abs (y - x:real) < 1")
      everyPoint <- rules.disch(near, within).flatMap(rules.gen(y, _))
      radius <- conj(lemma("(0:real) < 1"), Right(everyPoint))
      one <- real("1:real")
      witnessed <- existential("?d:real. 0 < d /\\ (!y:real. abs (y - x:real) < d ==> abs (c - c:real) < e:real)")
        .flatMap(rules.existsIntro(_, one, radius))
      statement <- rules.disch(positive, witnessed).flatMap(rules.gen(e, _))
      result <- folded(function, x, statement).flatMap(rules.gen(x, _)).flatMap(rules.gen(c, _))
    } yield result
  }

  /** [[Identity]]: at radius the tolerance, the distance of the value is the distance of the point. */
  private def identityFunction(steps: Steps): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    val e = Term.variable("e", Reals)
    val y = Term.variable("y", Reals)
    for {
      function <- Parser.term(theory, notation, "\\y:real. y", Functions)
      positive <- proposition("0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- proposition("abs (y - x:real) < e:real")
      assumedNear <- LogicError.lift(Kernel.assume(near))
      everyPoint <- rules.disch(near, assumedNear).flatMap(rules.gen(y, _))
      radius <- rules.conjIntro(assumedPositive, everyPoint)
      witnessed <- existential("?d:real. 0 < d /\\ (!y:real. abs (y - x:real) < d ==> abs (y - x) < e:real)")
        .flatMap(rules.existsIntro(_, e, radius))
      statement <- rules.disch(positive, witnessed).flatMap(rules.gen(e, _))
      result <- folded(function, x, statement).flatMap(rules.gen(x, _))
    } yield result
  }

  /** Membership of the set whose supremum is the crossing, at a point named `x`. */
  private val Member: String = "a:real <= x:real /\\ x <= b:real /\\ (f:real -> real) x <= y:real"

  /** What the theorem concludes, over the free `f`, `a`, `b` and `y`. */
  private val Goal: String = "?x:real. a:real <= x /\\ x <= b:real /\\ (f:real -> real) x = y:real"

  /** `w = min (d / 2) gap` is positive when `d` and the gap are, from `MIN_CASES`. */
  private[theories] def minimumPositive(
    steps: Steps,
    magnitude: Magnitude,
    gap: String,
    dPositive: Either[LogicError, Kernel.Thm],
    gapPositive: Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val w = s"min (d / 2) ($gap)"
    for {
      cases <- at(magnitude.fact(Magnitude.MinCases), "d / 2", gap)
      halfCase <- proposition(s"$w = d / 2")
      gapCase <- proposition(s"$w = $gap")
      fromHalf <- LogicError.lift(Kernel.assume(halfCase)).flatMap(assumed =>
        at(lemma("!w:real d:real. w = d / 2 ==> 0 < d ==> 0 < w"), w, "d:real")
          .flatMap(mp(_, Right(assumed), dPositive)))
      fromGap <- LogicError.lift(Kernel.assume(gapCase)).flatMap(assumed =>
        at(lemma("!w:real g:real. w = g ==> 0 < g ==> 0 < w"), w, gap)
          .flatMap(mp(_, Right(assumed), gapPositive)))
      result <- rules.disjElim(cases, fromHalf, fromGap)
    } yield result
  }

  /**
   * The tolerance `e * inv (2 * (abs p + 1))` a coefficient `p` is given, with `0 < T` and
   * `2 * (abs p + 1) * T = e`, under the assumption `0 < e`.
   *
   * The reciprocal is `Root`'s arrangement: `MUL_INVERSE` at a denominator already known positive,
   * and every step after it a closed statement `Linarith` decides with the reciprocal as a
   * variable. `abs p + 1` rather than `abs p` because `p` may be zero, and the two because each of
   * a pair of terms is given half of `e`. `Derivative`'s linearity spends the same share at `e *
   * abs h`.
   */
  private[theories] final case class Share(term: String, positive: Kernel.Thm, equation: Kernel.Thm)

  /**
   * The general form of [[share]]: `T = e * inv (k * (P + 1))` for a measure `P` known not to be
   * negative, with `0 < T` and `k * (P + 1) * T = e`, under the assumption `0 < e`. `k` is how many
   * terms the tolerance is shared among; the product rule shares it four ways and a linear
   * combination two. The term is written in brackets, so it reads as one factor wherever a caller
   * multiplies it.
   */
  private[theories] def portion(
    steps: Steps,
    reals: RealTheory,
    measure: String,
    nonNegative: Kernel.Thm,
    parts: Int,
    ePositive: Kernel.Thm
  ): Either[LogicError, Share] = {
    import steps.*
    val c = s"$parts * (($measure) + 1)"
    val v = s"inv ($c)"
    val t = s"(e:real * $v)"
    for {
      cPositive <- at(lemma(s"!P:real. 0 <= P ==> 0 < $parts * (P + 1)"), measure).flatMap(mp(_, Right(nonNegative)))
      nonZero <- at(lemma("!c:real. 0 < c ==> ~(c = 0)"), c).flatMap(mp(_, Right(cPositive)))
      inverse <- at(reals.law("MUL_INVERSE"), c).flatMap(mp(_, Right(nonZero)))
      positive <- at(lemma(s"!P:real v:real e:real. 0 <= P ==> $parts * (P + 1) * v = 1 ==> 0 < e ==> 0 < e * v"),
        measure, v, "e:real").flatMap(mp(_, Right(nonNegative), Right(inverse), Right(ePositive)))
      equation <- at(
        lemma(s"!P:real v:real e:real. 0 <= P ==> 0 < e ==> $parts * (P + 1) * v = 1 ==> $parts * (P + 1) * (e * v) = e"),
        measure, v, "e:real").flatMap(mp(_, Right(nonNegative), Right(ePositive), Right(inverse)))
    } yield Share(t, positive, equation)
  }

  /** The half of `e` a coefficient `p` is given in a combination of two: [[portion]] at `abs p`. */
  private[theories] def share(
    steps: Steps,
    reals: RealTheory,
    magnitude: Magnitude,
    coefficient: String,
    ePositive: Kernel.Thm
  ): Either[LogicError, Share] =
    for {
      nonNegative <- steps.at(magnitude.fact(Magnitude.AbsNonNegative), coefficient)
      result <- portion(steps, reals, s"abs ($coefficient)", nonNegative, 2, ePositive)
    } yield result

  /**
   * `0 < min l r`, from both: the radius two tolerances share, which `MIN_CASES` settles by
   * whichever of the two it is.
   */
  private[theories] def minimumOf(
    steps: Steps,
    magnitude: Magnitude,
    left: String,
    right: String,
    leftPositive: Kernel.Thm,
    rightPositive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val w = s"min ($left) ($right)"
    val equal = "!w:real d:real. w = d ==> 0 < d ==> 0 < w"
    for {
      cases <- at(magnitude.fact(Magnitude.MinCases), left, right)
      l <- assume(s"$w = $left").flatMap(eq => at(lemma(equal), w, left).flatMap(mp(_, Right(eq), Right(leftPositive))))
      r <- assume(s"$w = $right").flatMap(eq => at(lemma(equal), w, right).flatMap(mp(_, Right(eq), Right(rightPositive))))
      result <- rules.disjElim(cases, l, r)
    } yield result
  }

  /** [[minimumOf]] at the two radii named `d1` and `d2`, which is how every caller but one names them. */
  private[theories] def minimumOfTwo(steps: Steps, magnitude: Magnitude, first: Kernel.Thm, second: Kernel.Thm) =
    minimumOf(steps, magnitude, "d1:real", "d2:real", first, second)

  /**
   * [[Linear]]: each of the two is given its [[share]] of `e`, the radius is the smaller of the two
   * they answer with, and the difference regroups into `p * (f y - f x) + q * (g y - g x)`, which
   * `ABS_TRIANGLE` and `ABS_MUL` split into the two halves.
   */
  private def linearCombination(steps: Steps, reals: RealTheory, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val x = Term.variable("x", Reals)
    val p = Term.variable("p", Reals)
    val q = Term.variable("q", Reals)
    val e = Term.variable("e", Reals)
    val y = Term.variable("y", Reals)
    val d1 = Term.variable("d1", Reals)
    val d2 = Term.variable("d2", Reals)
    val df = "(f:real -> real) y - f x"
    val dg = "(g:real -> real) y - g x"
    val whole = "p:real * (f:real -> real) y + q:real * (g:real -> real) y - (p * f x + q * g x)"
    for {
      fHyp <- proposition("continuous (f:real -> real) x")
      gHyp <- proposition("continuous (g:real -> real) x")
      fAt <- LogicError.lift(Kernel.assume(fHyp)).flatMap(t => unfolded(f, x).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, t))))
      gAt <- LogicError.lift(Kernel.assume(gHyp)).flatMap(t => unfolded(g, x).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, t))))

      positive <- proposition("0 < e:real")
      ePositive <- LogicError.lift(Kernel.assume(positive))
      forP <- share(steps, reals, magnitude, "p:real", ePositive)
      forQ <- share(steps, reals, magnitude, "q:real", ePositive)

      nearF <- real(forP.term).flatMap(rules.spec(_, fAt)).flatMap(rules.mp(_, forP.positive))
      nearG <- real(forQ.term).flatMap(rules.spec(_, gAt)).flatMap(rules.mp(_, forQ.positive))
      radiusF <- assume(s"0 < d1:real /\\ (!y:real. abs (y - x:real) < d1 ==> abs ((f:real -> real) y - f x) < ${forP.term})")
      radiusG <- assume(s"0 < d2:real /\\ (!y:real. abs (y - x:real) < d2 ==> abs ((g:real -> real) y - g x) < ${forQ.term})")
      d1Positive <- rules.conjElim1(radiusF)
      d2Positive <- rules.conjElim1(radiusG)
      insideF <- rules.conjElim2(radiusF)
      insideG <- rules.conjElim2(radiusG)
      dPositive <- minimumOfTwo(steps, magnitude, d1Positive, d2Positive)

      near <- proposition("abs (y - x:real) < min (d1:real) (d2:real)")
      assumedNear <- LogicError.lift(Kernel.assume(near))
      below1 <- at(magnitude.fact(Magnitude.MinBelowLeft), "d1:real", "d2:real")
      below2 <- at(magnitude.fact(Magnitude.MinBelowRight), "d1:real", "d2:real")
      within1 <- at(lemma("!A:real w:real d:real. A < w ==> w <= d ==> A < d"), "abs (y - x:real)", "min (d1:real) (d2:real)", "d1:real")
        .flatMap(mp(_, Right(assumedNear), Right(below1)))
      within2 <- at(lemma("!A:real w:real d:real. A < w ==> w <= d ==> A < d"), "abs (y - x:real)", "min (d1:real) (d2:real)", "d2:real")
        .flatMap(mp(_, Right(assumedNear), Right(below2)))
      fClose <- rules.spec(y, insideF).flatMap(rules.mp(_, within1))
      gClose <- rules.spec(y, insideG).flatMap(rules.mp(_, within2))

      regrouped <- at(lemma("!p:real q:real F:real G:real F0:real G0:real. p * F + q * G - (p * F0 + q * G0) = p * (F - F0) + q * (G - G0)"),
        "p:real", "q:real", "(f:real -> real) y", "(g:real -> real) y", "(f:real -> real) x", "(g:real -> real) x")
      absFn <- Parser.term(theory, notation, "abs", Functions)
      sameAbs <- Conv.apTerm(absFn, regrouped)
      triangle <- at(magnitude.fact(Magnitude.Triangle), s"p:real * ($df)", s"q:real * ($dg)")
      mulP <- at(magnitude.fact(Magnitude.Multiplicative), "p:real", df)
      mulQ <- at(magnitude.fact(Magnitude.Multiplicative), "q:real", dg)
      pNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), "p:real")
      qNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), "q:real")
      scaledP <- at(lemma("!P:real A:real T:real. 0 <= P ==> A < T ==> P * A <= P * T"), "abs (p:real)", s"abs ($df)", forP.term)
        .flatMap(mp(_, Right(pNonNeg), Right(fClose)))
      scaledQ <- at(lemma("!P:real A:real T:real. 0 <= P ==> A < T ==> P * A <= P * T"), "abs (q:real)", s"abs ($dg)", forQ.term)
        .flatMap(mp(_, Right(qNonNeg), Right(gClose)))
      halfP <- at(lemma("!R:real X:real P:real T:real e:real. R = X ==> X <= P * T ==> 0 <= P ==> 0 < T ==> 2 * (P + 1) * T = e ==> R < e / 2"),
        s"abs (p:real * ($df))", s"abs (p:real) * abs ($df)", "abs (p:real)", forP.term, "e:real")
        .flatMap(mp(_, Right(mulP), Right(scaledP), Right(pNonNeg), Right(forP.positive), Right(forP.equation)))
      halfQ <- at(lemma("!R:real X:real P:real T:real e:real. R = X ==> X <= P * T ==> 0 <= P ==> 0 < T ==> 2 * (P + 1) * T = e ==> R < e / 2"),
        s"abs (q:real * ($dg))", s"abs (q:real) * abs ($dg)", "abs (q:real)", forQ.term, "e:real")
        .flatMap(mp(_, Right(mulQ), Right(scaledQ), Right(qNonNeg), Right(forQ.positive), Right(forQ.equation)))
      combined <- at(lemma("!E:real S:real X:real Y:real e:real. E = S ==> S <= X + Y ==> X < e / 2 ==> Y < e / 2 ==> E < e"),
        s"abs ($whole)", s"abs (p:real * ($df) + q:real * ($dg))", s"abs (p:real * ($df))", s"abs (q:real * ($dg))", "e:real")
        .flatMap(mp(_, Right(sameAbs), Right(triangle), Right(halfP), Right(halfQ)))

      everyY <- rules.disch(near, combined).flatMap(rules.gen(y, _))
      radius <- rules.conjIntro(dPositive, everyY)
      minimum <- real("min (d1:real) (d2:real)")
      witnessed <- existential(s"?d:real. 0 < d /\\ (!y:real. abs (y - x:real) < d ==> abs ($whole) < e:real)")
        .flatMap(rules.existsIntro(_, minimum, radius))
      withoutG <- rules.existsElim(nearG, d2, witnessed)
      withoutF <- rules.existsElim(nearF, d1, withoutG)
      statement <- rules.disch(positive, withoutF).flatMap(rules.gen(e, _))
      function <- Parser.term(theory, notation, "\\y:real. p:real * (f:real -> real) y + q:real * (g:real -> real) y", Functions)
      result <- folded(function, x, statement)
      closed <- rules.disch(gHyp, result).flatMap(rules.disch(fHyp, _)).flatMap(rules.genAll(_, List(f, g, x, p, q)))
    } yield closed
  }

  /**
   * `|- (\y. 1 * f y + 1 * g y) = (\y. f y + g y)`, by the abstraction rule over the pointwise
   * equation, at the two functions named `f` and `g`. [[Sum]] and `Derivative.Sum` both read their
   * function off [[Linear]]'s this way.
   */
  private[theories] def unitCombination(steps: Steps): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val y = Term.variable("y", Reals)
    for {
      pointwise <- at(lemma("!A:real B:real. 1 * A + 1 * B = A + B"), "(f:real -> real) y", "(g:real -> real) y")
      lambdas <- LogicError.lift(Kernel.abs(y, pointwise))
    } yield lambdas
  }

  /** [[Sum]]: [[Linear]] at one and one, its function rewritten by [[unitCombination]]. */
  private def sumOfTwo(steps: Steps, linear: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val x = Term.variable("x", Reals)
    for {
      one <- real("1:real")
      instance <- rules.specAll(linear, List(f, g, x, one, one))
      fHyp <- proposition("continuous (f:real -> real) x")
      gHyp <- proposition("continuous (g:real -> real) x")
      combined <- mp(instance, LogicError.lift(Kernel.assume(fHyp)), LogicError.lift(Kernel.assume(gHyp)))
      lambdas <- unitCombination(steps)
      continuous <- Parser.term(theory, notation, Continuous, Type.fun(Functions, Type.fun(Reals, Type.Bool)))
      atX <- Conv.apTerm(continuous, lambdas).flatMap(Conv.apThm(_, x))
      summed <- LogicError.lift(Kernel.eqMp(atX, combined))
      closed <- rules.disch(gHyp, summed).flatMap(rules.disch(fHyp, _)).flatMap(rules.genAll(_, List(f, g, x)))
    } yield closed
  }

  /**
   * [[Compose]]: `f` at `g x` answers `e` with a radius `d1`, `g` at `x` answers `d1` with a radius
   * `d2`, and within `d2` of `x` the value `g y` is within `d1` of `g x`, where `f` is within `e`.
   */
  private def composition(steps: Steps, reals: RealTheory, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val x = Term.variable("x", Reals)
    val e = Term.variable("e", Reals)
    val y = Term.variable("y", Reals)
    val d1 = Term.variable("d1", Reals)
    val d2 = Term.variable("d2", Reals)
    for {
      gHyp <- proposition("continuous (g:real -> real) x")
      fHyp <- proposition("continuous (f:real -> real) ((g:real -> real) x)")
      gx <- real("(g:real -> real) x")
      gAt <- LogicError.lift(Kernel.assume(gHyp)).flatMap(t => unfolded(g, x).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, t))))
      fAt <- LogicError.lift(Kernel.assume(fHyp)).flatMap(t => unfolded(f, gx).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, t))))

      positive <- proposition("0 < e:real")
      ePositive <- LogicError.lift(Kernel.assume(positive))
      nearF <- rules.spec(e, fAt).flatMap(rules.mp(_, ePositive))
      radiusF <- assume("0 < d1:real /\\ (!y:real. abs (y - (g:real -> real) x) < d1 ==> abs ((f:real -> real) y - f (g x)) < e:real)")
      d1Positive <- rules.conjElim1(radiusF)
      insideF <- rules.conjElim2(radiusF)
      nearG <- rules.spec(d1, gAt).flatMap(rules.mp(_, d1Positive))
      radiusG <- assume("0 < d2:real /\\ (!y:real. abs (y - x:real) < d2 ==> abs ((g:real -> real) y - g x) < d1:real)")
      d2Positive <- rules.conjElim1(radiusG)
      insideG <- rules.conjElim2(radiusG)

      near <- proposition("abs (y - x:real) < d2:real")
      assumedNear <- LogicError.lift(Kernel.assume(near))
      gClose <- rules.spec(y, insideG).flatMap(rules.mp(_, assumedNear))
      gy <- real("(g:real -> real) y")
      fClose <- rules.spec(gy, insideF).flatMap(rules.mp(_, gClose))

      everyY <- rules.disch(near, fClose).flatMap(rules.gen(y, _))
      radius <- rules.conjIntro(d2Positive, everyY)
      witnessed <- existential("?d:real. 0 < d /\\ (!y:real. abs (y - x:real) < d ==> abs ((f:real -> real) ((g:real -> real) y) - f (g x)) < e:real)")
        .flatMap(rules.existsIntro(_, d2, radius))
      withoutG <- rules.existsElim(nearG, d2, witnessed)
      withoutF <- rules.existsElim(nearF, d1, withoutG)
      statement <- rules.disch(positive, withoutF).flatMap(rules.gen(e, _))
      function <- Parser.term(theory, notation, "\\y:real. (f:real -> real) ((g:real -> real) y)", Functions)
      result <- folded(function, x, statement)
      closed <- rules.disch(fHyp, result).flatMap(rules.disch(gHyp, _)).flatMap(rules.genAll(_, List(f, g, x)))
    } yield closed
  }

  /**
   * [[Product]]: `f`'s share of `e` is weighed against `abs (g x)` as in [[Linear]], `g`'s against
   * `abs (f x) + 1`, which bounds `abs (f y)` wherever `f` is within one of `f x`, and the radius is
   * the least of the three.
   */
  private def productOfTwo(steps: Steps, reals: RealTheory, magnitude: Magnitude): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val x = Term.variable("x", Reals)
    val e = Term.variable("e", Reals)
    val y = Term.variable("y", Reals)
    val d1 = Term.variable("d1", Reals)
    val d2 = Term.variable("d2", Reals)
    val d3 = Term.variable("d3", Reals)
    val fy = "(f:real -> real) y"
    val fx = "(f:real -> real) x"
    val gy = "(g:real -> real) y"
    val gx = "(g:real -> real) x"
    val df = s"$fy - $fx"
    val dg = s"$gy - $gx"
    val whole = s"$fy * $gy - $fx * $gx"
    val bound = s"abs ($fx) + 1"
    val through = "!A:real w:real d:real. A < w ==> w <= d ==> A < d"
    val radius3 = "min (d1:real) (min (d2:real) (d3:real))"
    val halfRule = "!R:real X:real P:real T:real e:real. R = X ==> X <= P * T ==> 0 <= P ==> 0 < T ==> 2 * (P + 1) * T = e ==> R < e / 2"
    for {
      fHyp <- proposition("continuous (f:real -> real) x")
      gHyp <- proposition("continuous (g:real -> real) x")
      fAt <- LogicError.lift(Kernel.assume(fHyp)).flatMap(t => unfolded(f, x).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, t))))
      gAt <- LogicError.lift(Kernel.assume(gHyp)).flatMap(t => unfolded(g, x).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, t))))

      positive <- proposition("0 < e:real")
      ePositive <- LogicError.lift(Kernel.assume(positive))
      forF <- share(steps, reals, magnitude, gx, ePositive)
      absFNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), fx)
      boundNonNeg <- at(lemma("!A:real. 0 <= A ==> 0 <= A + 1"), s"abs ($fx)").flatMap(mp(_, Right(absFNonNeg)))
      forG <- portion(steps, reals, bound, boundNonNeg, 2, ePositive)

      one <- real("1:real")
      nearF <- real(forF.term).flatMap(rules.spec(_, fAt)).flatMap(rules.mp(_, forF.positive))
      nearG <- real(forG.term).flatMap(rules.spec(_, gAt)).flatMap(rules.mp(_, forG.positive))
      nearOne <- rules.spec(one, fAt).flatMap(mp(_, lemma("(0:real) < 1")))
      radiusF <- assume(s"0 < d1:real /\\ (!y:real. abs (y - x:real) < d1 ==> abs ($df) < ${forF.term})")
      radiusG <- assume(s"0 < d2:real /\\ (!y:real. abs (y - x:real) < d2 ==> abs ($dg) < ${forG.term})")
      radiusOne <- assume(s"0 < d3:real /\\ (!y:real. abs (y - x:real) < d3 ==> abs ($df) < 1)")
      d1Positive <- rules.conjElim1(radiusF)
      d2Positive <- rules.conjElim1(radiusG)
      d3Positive <- rules.conjElim1(radiusOne)
      insideF <- rules.conjElim2(radiusF)
      insideG <- rules.conjElim2(radiusG)
      insideOne <- rules.conjElim2(radiusOne)
      innerPositive <- minimumOf(steps, magnitude, "d2:real", "d3:real", d2Positive, d3Positive)
      dPositive <- minimumOf(steps, magnitude, "d1:real", "min (d2:real) (d3:real)", d1Positive, innerPositive)

      near <- proposition("abs (y - x:real) < min (d1:real) (min (d2:real) (d3:real))")
      assumedNear <- LogicError.lift(Kernel.assume(near))
      outerLeft <- at(magnitude.fact(Magnitude.MinBelowLeft), "d1:real", "min (d2:real) (d3:real)")
      outerRight <- at(magnitude.fact(Magnitude.MinBelowRight), "d1:real", "min (d2:real) (d3:real)")
      innerLeft <- at(magnitude.fact(Magnitude.MinBelowLeft), "d2:real", "d3:real")
      innerRight <- at(magnitude.fact(Magnitude.MinBelowRight), "d2:real", "d3:real")
      within1 <- at(lemma(through), "abs (y - x:real)", radius3, "d1:real").flatMap(mp(_, Right(assumedNear), Right(outerLeft)))
      withinInner <- at(lemma(through), "abs (y - x:real)", radius3, "min (d2:real) (d3:real)").flatMap(mp(_, Right(assumedNear), Right(outerRight)))
      within2 <- at(lemma(through), "abs (y - x:real)", "min (d2:real) (d3:real)", "d2:real").flatMap(mp(_, Right(withinInner), Right(innerLeft)))
      within3 <- at(lemma(through), "abs (y - x:real)", "min (d2:real) (d3:real)", "d3:real").flatMap(mp(_, Right(withinInner), Right(innerRight)))
      fClose <- rules.spec(y, insideF).flatMap(rules.mp(_, within1))
      gClose <- rules.spec(y, insideG).flatMap(rules.mp(_, within2))
      fOne <- rules.spec(y, insideOne).flatMap(rules.mp(_, within3))

      absFn <- Parser.term(theory, notation, "abs", Functions)
      // abs (f y) <= abs (f x) + 1, by the triangle at (f y - f x) + f x.
      rejoined <- at(lemma("!F:real F0:real. (F - F0) + F0 = F"), fy, fx)
      sameAbsF <- Conv.apTerm(absFn, rejoined)
      triangleF <- at(magnitude.fact(Magnitude.Triangle), df, fx)
      fBounded <- at(lemma("!A:real B:real C:real D:real. B = A ==> B <= C + D ==> C < 1 ==> A <= D + 1"),
        s"abs ($fy)", s"abs (($df) + $fx)", s"abs ($df)", s"abs ($fx)")
        .flatMap(mp(_, Right(sameAbsF), Right(triangleF), Right(fOne)))

      regrouped <- at(lemma("!F:real G:real F0:real G0:real. F * G - F0 * G0 = F * (G - G0) + G0 * (F - F0)"), fy, gy, fx, gx)
      sameAbs <- Conv.apTerm(absFn, regrouped)
      triangle <- at(magnitude.fact(Magnitude.Triangle), s"$fy * ($dg)", s"$gx * ($df)")
      mulG <- at(magnitude.fact(Magnitude.Multiplicative), fy, dg)
      mulF <- at(magnitude.fact(Magnitude.Multiplicative), gx, df)
      fyNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), fy)
      dgNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), dg)
      gxNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), gx)
      scaledG <- at(lemma("!A:real B:real P:real T:real. 0 <= A ==> A <= P ==> 0 <= B ==> B < T ==> A * B <= P * T"),
        s"abs ($fy)", s"abs ($dg)", bound, forG.term)
        .flatMap(mp(_, Right(fyNonNeg), Right(fBounded), Right(dgNonNeg), Right(gClose)))
      scaledF <- at(lemma("!P:real A:real T:real. 0 <= P ==> A < T ==> P * A <= P * T"), s"abs ($gx)", s"abs ($df)", forF.term)
        .flatMap(mp(_, Right(gxNonNeg), Right(fClose)))
      halfG <- at(lemma(halfRule), s"abs ($fy * ($dg))", s"abs ($fy) * abs ($dg)", bound, forG.term, "e:real")
        .flatMap(mp(_, Right(mulG), Right(scaledG), Right(boundNonNeg), Right(forG.positive), Right(forG.equation)))
      halfF <- at(lemma(halfRule), s"abs ($gx * ($df))", s"abs ($gx) * abs ($df)", s"abs ($gx)", forF.term, "e:real")
        .flatMap(mp(_, Right(mulF), Right(scaledF), Right(gxNonNeg), Right(forF.positive), Right(forF.equation)))
      combined <- at(lemma("!E:real S:real X:real Y:real e:real. E = S ==> S <= X + Y ==> X < e / 2 ==> Y < e / 2 ==> E < e"),
        s"abs ($whole)", s"abs ($fy * ($dg) + $gx * ($df))", s"abs ($fy * ($dg))", s"abs ($gx * ($df))", "e:real")
        .flatMap(mp(_, Right(sameAbs), Right(triangle), Right(halfG), Right(halfF)))

      everyY <- rules.disch(near, combined).flatMap(rules.gen(y, _))
      radius <- rules.conjIntro(dPositive, everyY)
      minimum <- real(radius3)
      witnessed <- existential(s"?d:real. 0 < d /\\ (!y:real. abs (y - x:real) < d ==> abs ($whole) < e:real)")
        .flatMap(rules.existsIntro(_, minimum, radius))
      withoutOne <- rules.existsElim(nearOne, d3, witnessed)
      withoutG <- rules.existsElim(nearG, d2, withoutOne)
      withoutF <- rules.existsElim(nearF, d1, withoutG)
      statement <- rules.disch(positive, withoutF).flatMap(rules.gen(e, _))
      function <- Parser.term(theory, notation, "\\y:real. (f:real -> real) y * (g:real -> real) y", Functions)
      result <- folded(function, x, statement)
      closed <- rules.disch(gHyp, result).flatMap(rules.disch(fHyp, _)).flatMap(rules.genAll(_, List(f, g, x)))
    } yield closed
  }

  /**
   * [[ContinuousTends]]: the radius continuity gives at `e` serves the limit at `e`, whose statement
   * asks about the same points less `x` itself.
   */
  private def continuousTends(steps: Steps, tendsDefinition: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val x = Term.variable("x", Reals)
    val e = Term.variable("e", Reals)
    val d = Term.variable("d", Reals)
    val y = Term.variable("y", Reals)
    for {
      hypothesis <- proposition("continuous (f:real -> real) x:real")
      opened <- LogicError.lift(Kernel.assume(hypothesis)).flatMap(t => unfolded(f, x).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, t))))
      positive <- proposition("0 < e:real")
      near <- LogicError.lift(Kernel.assume(positive)).flatMap(p => rules.spec(e, opened).flatMap(rules.mp(_, p)))
      radius <- assume("0 < d:real /\\ (!y:real. abs (y - x:real) < d ==> abs ((f:real -> real) y - f x) < e:real)")
      dPositive <- rules.conjElim1(radius)
      inside <- rules.conjElim2(radius)
      punctured <- proposition("0 < abs (y:real - x:real) /\\ abs (y - x) < d:real")
      close <- LogicError.lift(Kernel.assume(punctured)).flatMap(rules.conjElim2).flatMap(member => rules.spec(y, inside).flatMap(rules.mp(_, member)))
      everyY <- rules.disch(punctured, close).flatMap(rules.gen(y, _))
      pair <- rules.conjIntro(dPositive, everyY)
      witnessed <- existential("?d:real. 0 < d /\\ (!y:real. 0 < abs (y - x:real) /\\ abs (y - x) < d ==> abs ((f:real -> real) y - f x) < e:real)")
        .flatMap(rules.existsIntro(_, d, pair))
      eliminated <- rules.existsElim(near, d, witnessed)
      statement <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))
      value <- real("(f:real -> real) x:real")
      unfoldedTends <- Conv.unfold(tendsDefinition, List(f, x, value))
      right <- Term.destEq(unfoldedTends.conclusion).map(_._2).toRight(NotOfForm("an equation", unfoldedTends.conclusion))
      normal <- Conv.betaNormalise(right)
      equation <- Conv.trans(unfoldedTends, normal)
      back <- Conv.sym(equation)
      folded <- LogicError.lift(Kernel.eqMp(back, statement))
      closed <- rules.disch(hypothesis, folded).flatMap(rules.genAll(_, List(f, x)))
    } yield closed
  }

  /** [[IntermediateValue]], from `COMPLETENESS` at the points of `[a, b]` where `f` is at most `y`. */
  private def intermediateValue(
    steps: Steps,
    reals: RealTheory,
    magnitude: Magnitude
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val y = Term.variable("y", Reals)
    val x = Term.variable("x", Reals)
    val s = Term.variable("s", Reals)
    val d = Term.variable("d", Reals)

    val ordered = assume("a:real <= b:real")
    val atA = assume("(f:real -> real) a <= y:real")
    val atB = assume("y:real <= (f:real -> real) b")
    val everywhere = assume("!x:real. a:real <= x /\\ x <= b:real ==> continuous (f:real -> real) x")

    for {
      completeness <- reals.law("COMPLETENESS")
      total <- reals.law("LT_TOTAL")
      leCases <- magnitude.order.fact(Order.LeCases)
      goal <- proposition(Goal)
      memberStatement <- proposition(Member)

      /* ------------------------------------------------ inhabited by `a`, bounded by `b` */

      set <- Parser.term(theory, notation, s"\\x:real. $Member", Type.fun(Reals, Type.Bool))
      aMember <- conj(at(lemma("!a:real. a <= a"), "a:real"), conj(ordered, atA))
      inhabited <- existential(s"?x:real. $Member").flatMap(rules.existsIntro(_, a, aMember))
      assumedMember <- LogicError.lift(Kernel.assume(memberStatement))
      memberBelowB <- rules.conjElim2(assumedMember).flatMap(rules.conjElim1)
      everyBelowB <- rules.disch(memberStatement, memberBelowB).flatMap(rules.gen(x, _))
      bounded <- existential(s"?c:real. !x:real. $Member ==> x <= c").flatMap(rules.existsIntro(_, b, everyBelowB))

      atSet <- rules.spec(set, completeness)
      opened <- Conv.betaNormalise(atSet.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atSet)))
      supremumExists <- conj(Right(inhabited), Right(bounded)).flatMap(rules.mp(opened, _))

      supremum <- assume(
        s"(!x:real. $Member ==> x <= s:real) /\\ (!c:real. (!x:real. $Member ==> x <= c) ==> s <= c)")
      upper <- rules.conjElim1(supremum)
      least <- rules.conjElim2(supremum)
      sAboveA <- rules.spec(a, upper).flatMap(rules.mp(_, aMember))
      sBelowB <- rules.spec(b, least).flatMap(rules.mp(_, everyBelowB))

      continuousAtS <- everywhere
        .flatMap(rules.spec(s, _))
        .flatMap(mp(_, conj(Right(sAboveA), Right(sBelowB))))
      epsilonDelta <- unfolded(f, s).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, continuousAtS)))

      /* -------------------------------------------- below the value: `s` was not an upper bound */

      below <- {
        val under = assume("(f:real -> real) s < y:real")
        val gap = "b - s"
        val w = s"min (d / 2) ($gap)"
        val t = s"s + $w"
        for {
          tolerance <- real("y - (f:real -> real) s")
          tolerancePositive <- at(lemma("!p:real q:real. p < q ==> 0 < q - p"), "(f:real -> real) s", "y:real")
            .flatMap(mp(_, under))
          near <- rules.spec(tolerance, epsilonDelta).flatMap(rules.mp(_, tolerancePositive))
          radius <- assume(
            "0 < d:real /\\ (!z:real. abs (z - s:real) < d ==> " +
              "abs ((f:real -> real) z - f s) < y:real - f s)")
          dPositive <- rules.conjElim1(radius)
          inside <- rules.conjElim2(radius)

          // At `s = b` the value is `f b`, which is not below `y`.
          atEnd <- for {
            same <- assume("s:real = b:real")
            values <- Conv.apTerm(f, same)
            absurd <- at(lemma("!p:real q:real r:real. p < q ==> p = r ==> q <= r ==> F"),
              "(f:real -> real) s", "y:real", "(f:real -> real) b")
              .flatMap(mp(_, under, Right(values), atB))
            result <- rules.falsityElim(goal, absurd)
          } yield result

          // Before it, `s + min (d / 2) (b - s)` is in the set and past `s`.
          beforeEnd <- for {
            strictly <- assume("s:real < b:real")
            gapPositive = at(lemma("!s:real b:real. s < b ==> 0 < b - s"), "s:real", "b:real").flatMap(mp(_, Right(strictly)))
            wPositive <- minimumPositive(steps, magnitude, gap, Right(dPositive), gapPositive)
            wHalf <- at(magnitude.fact(Magnitude.MinBelowLeft), "d / 2", gap)
            wGap <- at(magnitude.fact(Magnitude.MinBelowRight), "d / 2", gap)
            magnitudeIs <- at(magnitude.fact(Magnitude.OfNonNegative), s"($t) - s")
              .flatMap(mp(_, at(lemma("!s:real w:real. 0 < w ==> 0 <= (s + w) - s"), "s:real", w).flatMap(mp(_, Right(wPositive)))))
            close <- at(
              lemma("!m:real s:real w:real d:real. m = (s + w) - s ==> w <= d / 2 ==> 0 < d ==> m < d"),
              s"abs (($t) - s)", "s:real", w, "d:real"
            ).flatMap(mp(_, Right(magnitudeIs), Right(wHalf), Right(dPositive)))
            tTerm <- real(t)
            valueNear <- rules.spec(tTerm, inside).flatMap(rules.mp(_, close))
            above <- at(magnitude.fact(Magnitude.AbsAbove), s"(f:real -> real) ($t) - f s")
            stillUnder <- at(
              lemma("!m:real p:real q:real v:real. p - q <= m ==> m < v - q ==> p <= v"),
              s"abs ((f:real -> real) ($t) - f s)", s"(f:real -> real) ($t)", "(f:real -> real) s", "y:real"
            ).flatMap(mp(_, Right(above), Right(valueNear)))
            tAboveA <- at(lemma("!a:real s:real w:real. a <= s ==> 0 < w ==> a <= s + w"), "a:real", "s:real", w)
              .flatMap(mp(_, Right(sAboveA), Right(wPositive)))
            tBelowB <- at(lemma("!s:real w:real b:real. w <= b - s ==> s + w <= b"), "s:real", w, "b:real")
              .flatMap(mp(_, Right(wGap)))
            tMember <- conj(Right(tAboveA), conj(Right(tBelowB), Right(stillUnder)))
            passes <- rules.spec(tTerm, upper).flatMap(rules.mp(_, tMember))
            absurd <- at(lemma("!s:real w:real. 0 < w ==> s + w <= s ==> F"), "s:real", w)
              .flatMap(mp(_, Right(wPositive), Right(passes)))
            result <- rules.falsityElim(goal, absurd)
          } yield result

          split <- rules.specAll(leCases, List(s, b)).flatMap(rules.mp(_, sBelowB))
          cases <- rules.disjElim(split, beforeEnd, atEnd)
          result <- rules.existsElim(near, d, cases)
        } yield result
      }

      /* ------------------------------------------------------------ at the value: `s` is it */

      equal <- for {
        hit <- assume("(f:real -> real) s = y:real")
        inside <- rules.conjIntro(sBelowB, hit)
        both <- rules.conjIntro(sAboveA, inside)
        result <- existential(Goal).flatMap(rules.existsIntro(_, s, both))
      } yield result

      /* --------------------------------------- above the value: `s` was not the least bound */

      above <- {
        val over = assume("y:real < (f:real -> real) s")
        val gap = "s - a"
        val w = s"min (d / 2) ($gap)"
        val lower = s"s - $w"
        for {
          tolerance <- real("(f:real -> real) s - y")
          tolerancePositive <- at(lemma("!p:real q:real. p < q ==> 0 < q - p"), "y:real", "(f:real -> real) s")
            .flatMap(mp(_, over))
          near <- rules.spec(tolerance, epsilonDelta).flatMap(rules.mp(_, tolerancePositive))
          radius <- assume(
            "0 < d:real /\\ (!z:real. abs (z - s:real) < d ==> " +
              "abs ((f:real -> real) z - f s) < f s - y:real)")
          dPositive <- rules.conjElim1(radius)
          inside <- rules.conjElim2(radius)

          // At `s = a` the value is `f a`, which is not above `y`.
          atStart <- for {
            same <- assume("a:real = s:real")
            values <- Conv.apTerm(f, same)
            absurd <- at(lemma("!p:real q:real r:real. p < q ==> r = q ==> r <= p ==> F"),
              "y:real", "(f:real -> real) s", "(f:real -> real) a")
              .flatMap(mp(_, over, Right(values), atA))
            result <- rules.falsityElim(goal, absurd)
          } yield result

          // After it, `s - min (d / 2) (s - a)` bounds the set already.
          afterStart <- for {
            strictly <- assume("a:real < s:real")
            gapPositive = at(lemma("!a:real s:real. a < s ==> 0 < s - a"), "a:real", "s:real").flatMap(mp(_, Right(strictly)))
            wPositive <- minimumPositive(steps, magnitude, gap, Right(dPositive), gapPositive)
            wHalf <- at(magnitude.fact(Magnitude.MinBelowLeft), "d / 2", gap)
            member <- LogicError.lift(Kernel.assume(memberStatement))
            memberUnder <- rules.conjElim2(member).flatMap(rules.conjElim2)
            atMostS <- rules.spec(x, upper).flatMap(rules.mp(_, member))
            lowerTerm <- real(lower)
            trichotomy <- rules.specAll(total, List(lowerTerm, x))

            // Past the candidate bound the point is within the radius of `s`, so `f` is over `y`
            // there, which a member of the set is not.
            past <- for {
              beyond <- assume(s"$lower < x:real")
              magnitudeIs <- at(magnitude.fact(Magnitude.OfNonPositive), "x - s:real")
                .flatMap(mp(_, at(lemma("!x:real s:real. x <= s ==> x - s <= 0"), "x:real", "s:real").flatMap(mp(_, Right(atMostS)))))
              close <- at(
                lemma("!m:real x:real s:real w:real d:real. m = -(x - s) ==> s - w < x ==> w <= d / 2 ==> 0 < d ==> m < d"),
                "abs (x - s:real)", "x:real", "s:real", w, "d:real"
              ).flatMap(mp(_, Right(magnitudeIs), Right(beyond), Right(wHalf), Right(dPositive)))
              valueNear <- rules.spec(x, inside).flatMap(rules.mp(_, close))
              underAbs <- at(magnitude.fact(Magnitude.AbsAboveNegation), "(f:real -> real) x - f s")
              valueOver <- at(
                lemma("!m:real p:real q:real v:real. -(p - q) <= m ==> m < q - v ==> v < p"),
                "abs ((f:real -> real) x - f s)", "(f:real -> real) x", "(f:real -> real) s", "y:real"
              ).flatMap(mp(_, Right(underAbs), Right(valueNear)))
              absurd <- at(lemma("!p:real q:real. p < q ==> q <= p ==> F"), "y:real", "(f:real -> real) x")
                .flatMap(mp(_, Right(valueOver), Right(memberUnder)))
              claim <- proposition(s"x:real <= $lower")
              result <- rules.falsityElim(claim, absurd)
            } yield result
            meets <- assume(s"$lower = x:real").flatMap(equation =>
              at(lemma("!p:real q:real. p = q ==> q <= p"), lower, "x:real").flatMap(mp(_, Right(equation))))
            short <- assume(s"x:real < $lower").flatMap(strict =>
              at(lemma("!p:real q:real. p < q ==> p <= q"), "x:real", lower).flatMap(mp(_, Right(strict))))
            rest <- assume(s"$lower = x:real \\/ x:real < $lower").flatMap(rules.disjElim(_, meets, short))
            underLower <- rules.disjElim(trichotomy, past, rest)
            bound <- rules.disch(memberStatement, underLower).flatMap(rules.gen(x, _))
            passes <- rules.spec(lowerTerm, least).flatMap(rules.mp(_, bound))
            absurd <- at(lemma("!s:real w:real. 0 < w ==> s <= s - w ==> F"), "s:real", w)
              .flatMap(mp(_, Right(wPositive), Right(passes)))
            result <- rules.falsityElim(goal, absurd)
          } yield result

          split <- rules.specAll(leCases, List(a, s)).flatMap(rules.mp(_, sAboveA))
          cases <- rules.disjElim(split, afterStart, atStart)
          result <- rules.existsElim(near, d, cases)
        } yield result
      }

      /* --------------------------------------------------- the three cases, and the closing */

      value <- real("(f:real -> real) s")
      trichotomy <- rules.specAll(total, List(value, y))
      rest <- assume("(f:real -> real) s = y:real \\/ y:real < (f:real -> real) s")
        .flatMap(rules.disjElim(_, equal, above))
      cases <- rules.disjElim(trichotomy, below, rest)
      eliminated <- rules.existsElim(supremumExists, s, cases)

      result <- List(
        "y:real <= (f:real -> real) b",
        "(f:real -> real) a <= y:real",
        "!x:real. a:real <= x /\\ x <= b:real ==> continuous (f:real -> real) x",
        "a:real <= b:real"
      ).foldLeft[Either[LogicError, Kernel.Thm]](Right(eliminated)) { (acc, text) =>
        for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
      }.flatMap(rules.genAll(_, List(f, a, b, y)))
    } yield result
  }
}
