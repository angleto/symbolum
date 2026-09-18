package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.Logic
import garden.xeno.symbolum.theories.{Real, RealTheory}

/**
 * A term, in a model, at an assignment: what it denotes, if anything.
 *
 * The half of the propose-and-check loop that has been missing. `Discovery` screens numerically and
 * then certifies, but it screens `Expr`, whose variables have values, and it certifies `Term`,
 * whose constants have none. Everything the proof side can say about a domain is therefore
 * unscreenable today: a hypothesis set can be contradictory and nothing notices, and an entailment
 * can be false and nothing produces the assignment that shows it.
 *
 * This is that missing piece, and `docs/adr/0003` says where it goes: the untrusted side, beside
 * the algebra system, never producing a theorem. It answers two questions, and they are the same
 * search run for two purposes.
 *
 *  - **Is this entailment false?** An assignment where every premise holds and the conclusion does
 *    not is a counterexample, and it is a fact about the model rather than about the theory.
 *  - **Are these premises consistent?** An assignment satisfying all of them is evidence that they
 *    are, and `h1..hn |- c` is vacuously true when they are not. The kernel will print `H |- c` and
 *    `H |- ~c` with equal cheer, and nothing else here would notice.
 *
 * == What it interprets, and what it refuses to state twice ==
 *
 * Almost nothing is built in. The theory's undefined constants come from the [[Model]]; every
 * defined constant is unfolded from the equation the kernel proved when it was introduced, so
 * `sub`, `div`, `le` and the numeral bits are evaluated by the theory's own account of them rather
 * than by a second one written here. What is built in is equality, which belongs to the kernel and
 * not to any theory, and the eight logical constants.
 *
 * The eight are the one place this file states something twice, and it is deliberate: their
 * definitions are equations between functions at higher types, so evaluating `p /\ q` through its
 * definition means comparing two functions over a sixteen-element carrier, for every conjunction in
 * every candidate. `EvaluateSpec` closes the gap that opens by checking the built-in against the
 * definition **exhaustively**, over every boolean assignment, rather than by sampling: for the
 * propositional connectives that is a complete proof of agreement, not evidence of it.
 *
 * == Where it stops, and why that is the honest answer ==
 *
 * A quantifier is evaluated by enumerating its domain, so it is decided over `bool`, over a
 * declared type the model has sized, and over functions between those. Over `real` it is not
 * decided at all and comes back as `None`. That is not a limitation to be worked around by trying a
 * few hundred points: `!x:real. p x` is not made true by any number of points, and a caller that
 * wants sampling strips the quantifier itself and samples the free variable, which is what
 * [[Refutation]] does.
 *
 * `None` means "no answer here", never "false". A term mentioning a constant no model interprets, a
 * division by zero, and a universal over the reals all come back the same way, and every caller in
 * this repository skips such a point rather than counting it.
 */
final class Evaluate private (
  private val definitions: Map[String, (Type, Term)],
  val model: Model,
  val reals: RealTheory
) {

  import Model.*

  /** The proposition's truth value in this model, or `None` where the model has nothing to say. */
  def proposition(term: Term, assignment: Map[String, Value]): Option[Boolean] =
    value(term, assignment).collect { case Truth(answer) => answer }

  /** What the term denotes. */
  def value(term: Term, assignment: Map[String, Value]): Option[Value] =
    evaluate(term, assignment, Nil)

  /**
   * Whether every value this evaluator can produce for the term is exact.
   *
   * The question behind a distinction this repository would otherwise have to give up: over the
   * reals a counterexample found by sampling can be a rounding artefact, which is why nothing here
   * promotes one to a verdict. Over the naturals it cannot, because `Model.Numbers` computes them
   * on `BigInt`. So the same search produces evidence in one case and a refutation in the other,
   * and this is what tells them apart.
   *
   * Conservative on purpose, and a syntactic walk rather than a property of the evaluation: every
   * constant has to be one the model computes exactly or one of the logical constants, and every
   * variable and every binder has to be at a type the model holds exactly. A claim that mentions
   * `real_of_num` fails it even though its naturals were exact on the way in, because the answer
   * came out as a `Double`. Erring the other way would be the one mistake that matters here.
   */
  def exact(term: Term): Boolean = term match {
    case Const(name, _) =>
      name == Term.EqualityName || Evaluate.LogicDefinitions.contains(name) ||
        model.exact.contains(name)
    case FVar(_, ty) => model.exactTypes.contains(ty)
    case BVar(_) => true
    case App(function, argument) => exact(function) && exact(argument)
    case Abs(binder, body) => model.exactTypes.contains(binder) && exact(body)
  }

  /** True when every one of them holds at the assignment; `None` if any of them has no value. */
  def all(terms: Iterable[Term], assignment: Map[String, Value]): Option[Boolean] =
    terms.foldLeft(Option(true)) { (answer, term) =>
      for {
        running <- answer
        current <- proposition(term, assignment)
      } yield running && current
    }

  /**
   * `bound` is the de Bruijn environment, innermost binder first, which is the order
   * `Term.abs` closes in.
   */
  private def evaluate(
    term: Term,
    assignment: Map[String, Value],
    bound: List[Value]
  ): Option[Value] = term match {
    case BVar(index) => bound.lift(index)

    // By name, not by name and type. Two free variables called `x` at different types are
    // distinct to the kernel and would collide here, and the value one of them found would be of
    // the wrong shape for the other. What happens then is that every operation over it declines,
    // so the answer is `None` rather than a wrong one; `EvaluateSpec` pins that. Keying an
    // assignment by the pair would fix it and is not worth the interface until such a term exists.
    case FVar(name, _) => assignment.get(name)
    case Const(name, ty) => constant(name, ty)

    case App(function, argument) =>
      for {
        applied <- evaluate(function, assignment, bound)
        supplied <- evaluate(argument, assignment, bound)
        result <- applyTo(applied, supplied)
      } yield result

    // A closure rather than a table: the domain may be `real`, where there is no table.
    case Abs(binder, body) =>
      Some(Mapping(binder, argument => evaluate(body, assignment, argument :: bound)))
  }

  /**
   * Apply a function value to an argument.
   *
   * Public because a caller holding a `Mapping`, which is what a lambda evaluates to, has no other
   * way to ask what it does: `EvaluateSpec` needs exactly this to run a connective's own definition
   * against the built-in that stands in for it.
   */
  def applyTo(function: Value, argument: Value): Option[Value] = function match {
    case Mapping(_, apply) => apply(argument)
    case _ => None
  }

  /* ------------------------------------------------------------------- constants */

  private def constant(name: String, ty: Type): Option[Value] =
    if (name == Term.EqualityName) equality(ty)
    else
      logical(name, ty)
        .orElse(unfold(name, ty))
        .orElse(model.constants.get(name))

  /**
   * The defining equation, at the type this occurrence uses.
   *
   * A definition is stated once, at whatever type it was introduced with, and `le` is at `real`
   * while a domain definition could be at a type variable. Matching the two and substituting is
   * what makes one equation serve every instance, and it is the same step `Conv.unfold` takes on
   * the proving side.
   */
  private def unfold(name: String, ty: Type): Option[Value] =
    definitions.get(name).flatMap { case (schema, body) =>
      val instantiated =
        if (schema == ty) Some(body)
        else Type.matchType(schema, ty).map(substitution => Term.substituteTypes(substitution, body))

      instantiated.flatMap(term => evaluate(term, Map.empty, Nil))
    }

  private def logical(name: String, ty: Type): Option[Value] = name match {
    case Logic.Truth => Some(Truth(true))
    case Logic.Falsity => Some(Truth(false))
    case Logic.Negation => Some(onTruths(answer => !answer))
    case Logic.Conjunction => Some(onTruthPairs(_ && _))
    case Logic.Disjunction => Some(onTruthPairs(_ || _))
    case Logic.Implication => Some(onTruthPairs(!_ || _))
    case Logic.Universal => quantifier(ty, _.forall(identity))
    case Logic.Existential => quantifier(ty, _.exists(identity))
    case _ => None
  }

  private def onTruths(operation: Boolean => Boolean): Value =
    Mapping(Type.Bool, {
      case Truth(answer) => Some(Truth(operation(answer)))
      case _ => None
    })

  private def onTruthPairs(operation: (Boolean, Boolean) => Boolean): Value =
    Mapping(Type.Bool, {
      case Truth(left) =>
        Some(Mapping(Type.Bool, {
          case Truth(right) => Some(Truth(operation(left, right)))
          case _ => None
        }))
      case _ => None
    })

  /**
   * A quantifier over the domain of the predicate it is applied to.
   *
   * The whole quantifier is `None` when any single point is, rather than ignoring that point.
   * Skipping would let `!x. inv x * x = 1` come back true by passing over the one place it fails,
   * which is the shape of wrong answer this file exists to avoid.
   */
  private def quantifier(ty: Type, decide: Vector[Boolean] => Boolean): Option[Value] =
    for {
      predicateType <- Type.destFun(ty).map(_._1)
      domain <- Type.destFun(predicateType).map(_._1)
      points <- carrier(domain)
    } yield Mapping(
      predicateType,
      predicate =>
        points
          .foldLeft(Option(Vector.empty[Boolean])) { (answers, point) =>
            for {
              running <- answers
              applied <- applyTo(predicate, point)
              answer <- applied match {
                case Truth(value) => Some(value)
                case _ => None
              }
            } yield running :+ answer
          }
          .map(answers => Truth(decide(answers)))
    )

  /* -------------------------------------------------------------------- equality */

  private def equality(ty: Type): Option[Value] =
    Type.destFun(ty).map(_._1).map { operand =>
      Mapping(operand, left => Some(Mapping(operand, right => equal(left, right).map(Truth.apply))))
    }

  /**
   * Whether two values are the same, or `None` when the question cannot be settled here.
   *
   * Two functions are the same when they agree at every point of their domain, which is a question
   * only where the domain is finite. Over `real` it is not, and `None` is the answer rather than a
   * comparison of two closures, which would say the two are different whenever they were written
   * differently.
   */
  private def equal(left: Value, right: Value): Option[Boolean] = (left, right) match {
    case (Quantity(first), Quantity(second)) => Some(Evaluate.indistinguishable(first, second))
    case (Truth(first), Truth(second)) => Some(first == second)
    case (Element(first, at), Element(second, to)) => Some(first == second && at == to)

    // Exact, which is the difference between a natural and a real here. Two `Quantity` values one
    // ulp apart are the same number as far as this file is concerned, and two naturals one apart
    // are two numbers.
    case (Whole(first), Whole(second)) => Some(first == second)

    case (Mapping(domain, _), Mapping(_, _)) =>
      carrier(domain).flatMap { points =>
        points.foldLeft(Option(true)) { (answer, point) =>
          for {
            running <- answer
            here <- applyTo(left, point)
            there <- applyTo(right, point)
            same <- equal(here, there)
          } yield running && same
        }
      }

    case _ => None
  }

  /* --------------------------------------------------------------------- carriers */

  /**
   * Everything of a type, when there is a finite everything, or `None` when there is not.
   *
   * Public because whoever builds a grid of assignments needs it: a variable of a finite type is
   * enumerated and one of type `real` is sampled, and only this can tell the two apart.
   */
  def inhabitants(ty: Type): Option[Vector[Value]] = carrier(ty)

  /**
   * Everything of a type, when there is a finite everything.
   *
   * `bool` has two, a declared type has what the model sized it at, and a function type has as many
   * as there are tables from one to the other. That last case is what lets the connectives be
   * checked against their own definitions, which are equations between functions at higher types:
   * without it the check would have nothing to compare.
   */
  private def carrier(ty: Type): Option[Vector[Value]] =
    if (ty == Type.Bool) Some(Vector(Truth(false), Truth(true)))
    else
      ty match {
        case TyApp("fun", List(domain, codomain)) =>
          for {
            from <- carrier(domain)
            to <- carrier(codomain)
            size = math.pow(to.length.toDouble, from.length.toDouble)
            if size <= Evaluate.FunctionCarrierBound.toDouble
          } yield tables(from, to).map(table =>
            Mapping(
              domain,
              argument =>
                from.indexWhere(point => equal(point, argument).contains(true)) match {
                  case -1 => None
                  case at => Some(table(at))
                }
            )
          )

        case TyApp(name, Nil) => model.carrierOf(name)
        case _ => None
      }

  /** Every way of choosing one value of `to` for each point of `from`. */
  private def tables(from: Vector[Value], to: Vector[Value]): Vector[Vector[Value]] =
    from.foldLeft(Vector(Vector.empty[Value])) { (rows, _) =>
      rows.flatMap(row => to.map(choice => row :+ choice))
    }
}

object Evaluate {

  /**
   * How many functions of a type this will enumerate before declining.
   *
   * Two hundred and fifty-six covers what the logic's own definitions need, which is the sixteen
   * functions `bool -> bool -> bool` that conjunction's definition quantifies over, with room for a
   * declared type of three or four inhabitants. Past that the count is `|codomain| ^ |domain|` and
   * grows the way that grows, so a bound is the difference between an evaluator that declines and
   * one that stops responding.
   */
  val FunctionCarrierBound: Int = 256

  /**
   * Whether two computed reals are close enough to be the same number.
   *
   * The same relative tolerance the `Expr` screening uses, and deliberately the same number: the
   * two are the same judgement about the same arithmetic, and a second constant would be a second
   * place for it to drift. `Discovery` explains why it is loose.
   */
  def indistinguishable(left: Double, right: Double): Boolean = {
    val scale = math.max(1.0, math.max(math.abs(left), math.abs(right)))
    math.abs(left - right) <= Discovery.Tolerance * scale
  }

  /**
   * Strictly less, by more than the tolerance.
   *
   * Stated through [[indistinguishable]] rather than beside it so that the order and the equality
   * cannot disagree: within the tolerance two values are equal and neither is below the other,
   * which is what keeps trichotomy true of this model.
   */
  def strictlyLess(left: Double, right: Double): Boolean =
    left < right && !indistinguishable(left, right)

  /**
   * Over a theory, with a model of the constants it leaves undefined.
   *
   * The definitions come from the theory and from the logic beneath it, as the equations the kernel
   * proved when each constant was introduced. Nothing is copied: if a definition changes, this
   * changes with it.
   */
  def over(reals: RealTheory, model: Model): Evaluate = {
    val fromTheory = reals.definitions.toVector.flatMap { case (name, theorem) =>
      equationOf(name, theorem)
    }

    val fromLogic = LogicDefinitions.flatMap { name =>
      reals.logic.definitionOf(name).toOption.flatMap(theorem => equationOf(name, theorem))
    }

    new Evaluate((fromLogic ++ fromTheory).toMap, model, reals)
  }

  /** The standard theory of the reals under its intended model. */
  lazy val standard: Evaluate = over(Real.standard, Model.Numbers)

  /**
   * The logic's own definitions, listed rather than read off the logic, which keeps them private.
   *
   * They are here so that `EvaluateSpec` can compare each built-in connective against the
   * equation the kernel holds for it. The evaluator itself never reaches them, because the built-in
   * matches first.
   */
  val LogicDefinitions: Vector[String] = Vector(
    Logic.Truth,
    Logic.Falsity,
    Logic.Conjunction,
    Logic.Disjunction,
    Logic.Implication,
    Logic.Negation,
    Logic.Universal,
    Logic.Existential
  )

  /** The right-hand side of `c = body`, with the type the constant was introduced at. */
  private def equationOf(name: String, theorem: Kernel.Thm): Option[(String, (Type, Term))] =
    Term.destEq(theorem.conclusion).flatMap {
      case (Const(defined, ty), body) if defined == name => Some(name -> (ty, body))
      case _ => None
    }
}
