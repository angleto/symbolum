package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.{Type, TyApp}
import garden.xeno.symbolum.theories.{Natural, Peano, Real, Series}

/**
 * What a theory's undefined constants denote, and how many things each declared type holds.
 *
 * A theory says nothing about what its constants mean. That is the whole reason declaring one is
 * conservative, and it is why `+` proves nothing until an axiom says something about it. A model is
 * the other half: a choice of what those names stand for, made outside the logic, where a wrong
 * choice costs nothing because nothing here produces a theorem.
 *
 * == Why this is on the untrusted side ==
 *
 * Everything in this file is a claim about arithmetic on `Double`, and `Double` is not the reals:
 * addition is not associative on it, and the sixteen axioms the theory holds are therefore not all
 * true of this model. That is not a defect to be fixed by a better model. It is what an evaluator
 * is for. It answers "is this false at a point I can compute", which is a cheap question, and it
 * never answers "is this true", which is the kernel's.
 *
 * The arrangement is the one `docs/adr/0003` already describes for the algebra system: the fast,
 * approximate half proposes and refutes, and nothing it says is believed.
 *
 * == What a model does not carry ==
 *
 * No carrier for `real`. There is not a finite one, and pretending otherwise would let a universal
 * over the reals come back "true" after a few hundred points, which is exactly the mistake
 * [[Discovery]] documents itself against. A quantifier over `real` is not evaluated; it is sampled,
 * by whoever is doing the sampling, and the sample is evidence and not a verdict.
 */
final case class Model(
  carriers: Map[String, Int],
  constants: Map[String, Model.Value],
  /**
   * The constants this model computes with no `Double` anywhere in the answer.
   *
   * Empty for [[Model.Reals]], because every one of its seven is arithmetic on `Double` and the
   * file says so in its first paragraph. Not empty for [[Model.Numbers]], where the six operations
   * on `num` are `BigInt` and a point found among them is a **refutation** rather than evidence
   * about a model. `Evaluate.exact` is what reads this and `Abduce.Gap.decisive` is what a caller
   * gets from it.
   */
  exact: Set[String] = Set.empty,
  /** The types whose values this model holds exactly, for the same reading. */
  exactTypes: Set[Type] = Set.empty
) {

  /** The elements of a declared type, or `None` when the model does not bound it. */
  def carrierOf(name: String): Option[Vector[Model.Value]] =
    carriers.get(name).filter(_ > 0).map(size => Vector.tabulate(size)(Model.Element(name, _)))

  /** The same model with one more constant interpreted. */
  def interpreting(name: String, value: Model.Value): Model =
    copy(constants = constants.updated(name, value))

  /** The same model with a declared type given a size. */
  def sizing(typeName: String, size: Int): Model =
    copy(carriers = carriers.updated(typeName, size))
}

object Model {

  /**
   * What a term can denote.
   *
   * `Mapping` holds a function rather than a table because the domain may be `real`, where there is
   * no table to hold. Two of them are compared by [[Evaluate]] at every point of their domain when
   * that domain is finite, and not at all when it is not: `==` on a `Mapping` compares two closures
   * and is never the question anybody meant to ask.
   */
  sealed trait Value

  /** A proposition's value. */
  final case class Truth(value: Boolean) extends Value

  /** A real, as far as a `Double` is one. See the note above. */
  final case class Quantity(value: Double) extends Value

  /** The `index`-th inhabitant of a declared type, and nothing else is known about it. */
  final case class Element(carrier: String, index: Int) extends Value

  /**
   * A natural number, exactly, and not an [[Element]] of a carrier called `num`.
   *
   * The distinction is the one [[Element]]'s own line makes: an element of a declared type is
   * opaque, two of them are compared by index and nothing else is known, and that is what makes a
   * carrier safe to enumerate. A natural number is the opposite: `NUM_ADD` has to be able to add
   * two of them, and reusing `Element` for that would quietly make one of the two sentences false.
   *
   * `BigInt` rather than `Int` because nothing here bounds it. What **is** bounded is what the
   * functions over it will compute: see [[Model.Terms]].
   */
  final case class Whole(value: BigInt) extends Value

  /** A function, with the type of its argument, which is what makes it comparable. */
  final case class Mapping(domain: Type, apply: Value => Option[Value]) extends Value

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val natural: Type = TyApp(Natural.TypeName, Nil)

  /**
   * How many terms of a sum, a product or a power this model will compute before declining.
   *
   * A bound and not a limit of the arithmetic. `Sum f n` at an `n` of a million is a million
   * evaluations of the summand, and a screening loop asking for one has stopped being a screen. A
   * point past this is a point where the question was not asked, which every caller here already
   * knows how to skip.
   */
  val Terms: Int = 2000

  /** A one-argument function on reals, undefined where `operation` says so. */
  def unary(operation: Double => Option[Double]): Value =
    Mapping(real, {
      case Quantity(argument) => operation(argument).map(Quantity.apply)
      case _ => None
    })

  /** A two-argument function on reals, curried as the logic curries it. */
  def binary(operation: (Double, Double) => Option[Value]): Value =
    Mapping(real, {
      case Quantity(left) =>
        Some(Mapping(real, {
          case Quantity(right) => operation(left, right)
          case _ => None
        }))
      case _ => None
    })

  /**
   * A value as a reader checks it, which is the last place a constructor name belongs.
   *
   * `Quantity(1.97)` is what the model carries and `1.97` is what somebody verifies by hand. The
   * case that makes this worth a method rather than a `toString` is [[Mapping]]: a sampled summand
   * is a closure, and a witness printed as `Mapping(num,Lambda$0x78000150e898@13cd7ea5)` is a
   * rumour rather than a counterexample. A function of the naturals is shown by its first few
   * values, which is what a reader would ask it for anyway.
   */
  def show(value: Value): String = value match {
    case Quantity(quantity) => quantity.toString
    case Whole(whole) => whole.toString
    case Truth(truth) => truth.toString
    case Element(carrier, index) => s"$carrier#$index"
    case Mapping(domain, apply) if domain == natural =>
      (0 until Shown)
        .map(index => apply(Whole(index)).map(show).getOrElse("?"))
        .mkString("<", ", ", ", ...>")
    case Mapping(domain, _) => s"a function of $domain"
  }

  /** How many values of a sampled function [[show]] prints before giving up on the reader. */
  private val Shown: Int = 4

  /** A one-argument function on the naturals, undefined where `operation` says so. */
  def onWhole(operation: BigInt => Option[Value]): Value =
    Mapping(natural, {
      case Whole(argument) => operation(argument)
      case _ => None
    })

  /** A two-argument function on the naturals, curried as the logic curries it. */
  def onWholePair(operation: (BigInt, BigInt) => Option[Value]): Value =
    Mapping(natural, {
      case Whole(left) =>
        Some(Mapping(natural, {
          case Whole(right) => operation(left, right)
          case _ => None
        }))
      case _ => None
    })

  /**
   * The intended model of the reals: the seven constants the theory declares and does not define.
   *
   * `sub`, `div`, `le` and the two numeral bits are absent on purpose. They are definitional
   * extensions, so the theory already says what they mean, and [[Evaluate]] unfolds them. Writing
   * them here as well would be a second statement of the same thing, free to disagree with the
   * first.
   *
   * `inv 0` is undefined rather than infinite, which matches the theory: `MUL_INVERSE` holds only
   * under `~(x = 0)`, so there is nothing for a model to say at zero. An undefined point is skipped
   * by every caller here, because a place where the question was not asked is not a counterexample.
   */
  val Reals: Model = Model(
    carriers = Map.empty,
    constants = Map(
      Real.Zero -> Quantity(0.0),
      Real.One -> Quantity(1.0),
      Real.Addition -> binary((left, right) => Some(Quantity(left + right))),
      Real.Multiplication -> binary((left, right) => Some(Quantity(left * right))),
      Real.Negation -> unary(argument => Some(-argument)),
      Real.Inverse -> unary(argument => if (argument == 0.0) None else Some(1.0 / argument)),
      // Strict below the tolerance the screening uses everywhere else, so that `<` and `=` cannot
      // both be true of one pair: within the tolerance the two are equal and neither is less.
      Real.Order -> binary((left, right) => Some(Truth(Evaluate.strictlyLess(left, right))))
    )
  )

  /**
   * The reals as [[Reals]] has them, and the naturals beside them.
   *
   * Until 2026-09-11 there was only the first, and the consequence was measured rather than
   * suspected: of the 116 proposals `Propose.standard.audit` produces, **nineteen name a constant of
   * the `num` side and not one of them was decided either way**. Fifteen came back `Open` and four
   * `Unreadable`, and reading the fifteen by hand, every one of them was false at a small point.
   * `Evaluate` was doing the right thing and `Refutation` was doing the right thing; half the
   * library was simply outside what either could ask about.
   *
   * == There is no carrier for `num`, and that is the decision ==
   *
   * A finite carrier would make a universal over `num` enumerable, and it would make this model
   * **lie**: with a successor that saturates at the top element, `!n. ~(SUC n = n)` comes back
   * false, and a refutation of a theorem is the one output this repository must never produce. With
   * a successor that is undefined at the top, no universal that mentions it has a value at all,
   * which is honest and useless.
   *
   * So `num` is treated the way `real` already is: not enumerated, **sampled** by whoever is doing
   * the sampling, and a point that is found is a genuine natural number and therefore a genuine
   * witness. `Refutation.grid` is where the points come from and `Refutation.whole` is the sequence.
   *
   * == What each constant is, and where it declines ==
   *
   * `ZERO`, `SUC`, `NUM_ADD`, `NUM_MUL`, `NUM_LE` and `NUM_LT` are exact on `BigInt` and total.
   * `real_of_num` crosses into the reals and is therefore as good as a `Double`, which is the same
   * bargain the rest of this file makes. `Sum`, `Power` and `Prod` are computed from their
   * recurrences and decline past [[Terms]], and `Power` also declines where the answer overflows a
   * `Double`: an infinity is not a value, and a caller that read one as a number would have a
   * witness made of nothing.
   *
   * == Why not unfold the definitions instead ==
   *
   * Every constant here is **defined** rather than declared, so in principle `Evaluate` could unfold
   * each one and never need a model. In practice it cannot: they are defined through the recursion
   * theorem, whose body is a choice over a predicate, and choice is not something a model of this
   * shape computes. Measured before this was written: `Evaluate.over(chain.reals, ...)` holds five
   * definitions, `BIT0`, `BIT1`, `div`, `le` and `sub`, so every name below falls through to the
   * model rather than being shadowed by an unfolding that cannot finish.
   */
  val Numbers: Model = Model(
    // The eight operations on `num` and nothing else: `real_of_num`, `Sum`, `Power` and `Prod` all
    // produce a `Double`, so a claim that mentions one of them is evidence rather than a decision,
    // however exact its naturals were on the way in.
    exact = Set(
      Natural.NumberZero,
      Natural.NumberSuccessor,
      Peano.Addition,
      Peano.Multiplication,
      Peano.Predecessor,
      Peano.Subtraction,
      Peano.NonStrictOrder,
      Peano.StrictOrder
    ),
    exactTypes = Set(natural, Type.Bool),
    carriers = Reals.carriers,
    constants = Reals.constants ++ Map(
      Natural.NumberZero -> Whole(0),
      Natural.NumberSuccessor -> onWhole(n => Some(Whole(n + 1))),
      Peano.Addition -> onWholePair((left, right) => Some(Whole(left + right))),
      Peano.Multiplication -> onWholePair((left, right) => Some(Whole(left * right))),
      // Truncated at zero, exactly as `Peano` defines them, and the word "exactly" is the whole of
      // this line. `PRE` is defined by recursion with `PRE ZERO = ZERO` and `NUM_SUB` by iterating
      // it, so `NUM_SUB 0 1` is `0` and `NUM_ZERO_SUB` is a theorem. A plain `BigInt` subtraction
      // here would answer `-1`, and the model would then hand back a counterexample to a theorem,
      // which is the one thing an untrusted model must never be able to do.
      //
      // They are in `exact` for the reason the six above are: both are total on `BigInt` at these
      // definitions, so a point found among them is a refutation and not evidence. Before this they
      // were absent, and `Propose` reported two demonstrably false proposals about them as
      // `Unreadable` — "I could not ask" where the honest answer was a witness.
      Peano.Predecessor -> onWhole(n => Some(Whole(if (n <= 0) BigInt(0) else n - 1))),
      Peano.Subtraction ->
        onWholePair((left, right) => Some(Whole(if (left <= right) BigInt(0) else left - right))),
      Peano.NonStrictOrder -> onWholePair((left, right) => Some(Truth(left <= right))),
      Peano.StrictOrder -> onWholePair((left, right) => Some(Truth(left < right))),
      Peano.Embedding -> onWhole(n => finite(n.toDouble)),
      Series.PowerName -> Mapping(real, {
        case Quantity(base) => Some(onWhole(exponent => raised(base, exponent)))
        case _ => None
      }),
      Series.SumName -> folded(0.0, _ + _),
      Series.ProdName -> folded(1.0, _ * _)
    )
  )

  /** A quantity, unless it is not one: an infinity and a NaN are places without a value. */
  private def finite(value: Double): Option[Value] =
    if (value.isNaN || value.isInfinite) None else Some(Quantity(value))

  /** `base ^ exponent`, declining where the exponent is unreasonable or the answer is not a number. */
  private def raised(base: Double, exponent: BigInt): Option[Value] =
    if (exponent < 0 || exponent > Terms) None else finite(math.pow(base, exponent.toDouble))

  /**
   * `Sum` and `Prod`, which are the same fold over the same recurrence with a different unit.
   *
   * Both run from `0` up to but not including `n`, which is what the definitions in `Series` say and
   * is the off-by-one a reader should check first. A summand with no value at any index loses the
   * whole answer rather than being skipped, for the reason the quantifier gives in `Evaluate`:
   * passing over the one point where something fails is how a model comes back true about a claim
   * that is false.
   */
  private def folded(unit: Double, combine: (Double, Double) => Double): Value =
    Mapping(Type.fun(natural, real), {
      case Mapping(_, summand) =>
        Some(onWhole { length =>
          if (length < 0 || length > Terms) None
          else
            (BigInt(0) until length)
              .foldLeft(Option(unit)) { (running, index) =>
                for {
                  total <- running
                  value <- summand(Whole(index))
                  quantity <- value match {
                    case Quantity(number) => Some(number)
                    case _ => None
                  }
                } yield combine(total, quantity)
              }
              .flatMap(finite)
        })
      case _ => None
    })
}
