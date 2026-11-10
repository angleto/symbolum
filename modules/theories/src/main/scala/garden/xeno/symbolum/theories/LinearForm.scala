package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A term as a linear form: a coefficient for each atom, and a constant.
 *
 * The untrusted half of [[Linarith]], which held this and the readers below it until 2026-09-11 and
 * was nineteen hundred lines with them. What decided the split is not the length: it is that this
 * is a **value type with an algebra of its own**, and a class nested inside an object about proving
 * could not be handed to a property test. `LinearFormSpec` hammers the laws that addition,
 * negation, scaling and the product obey over generated forms, which is the only way to find out
 * whether they hold on inputs nobody wrote by hand.
 *
 * Untrusted, and it does not have to be right. It decides which hypotheses to try adding; the
 * ring tactic decides whether the answer was correct. A form that misreads a term makes the
 * search miss a proof, never find a wrong one.
 *
 * **The coefficients are rational, and were whole until 2026-09-09.** A quotient by a numeral is
 * a coefficient of `1 / d` and nothing else in this file changes for it: [[Farkas]] has always
 * solved over `Rational`, and the interface between the two used to widen every whole coefficient
 * on the way in. What the two representations disagreeing cost was `eps / 3 + eps / 3 + eps / 3
 * <= eps`, where `eps / 3` was an atom and `eps` was another one, so no combination could reach
 * from one to the other. Nothing on the checking side moved: a multiplier is still cleared to a
 * whole number before any theorem is built, and what shows a denominator to the kernel is `Ring`,
 * which has decided a numeral one since the same day.
 */
final case class LinearForm(coefficients: Map[Term, Rational], constant: Rational) {
  def +(other: LinearForm): LinearForm =
    LinearForm(
      (coefficients.keySet ++ other.coefficients.keySet)
        .map(key =>
          key -> (coefficients.getOrElse(key, Rational.zero) + other.coefficients
            .getOrElse(key, Rational.zero))
        )
        .filter { case (_, value) => !value.isZero }
        .toMap,
      constant + other.constant
    )

  def unary_- : LinearForm = LinearForm(coefficients.map { case (k, v) => k -> -v }, -constant)

  def scaled(factor: Rational): LinearForm =
    if (factor.isZero) LinearForm.zero
    else LinearForm(coefficients.map { case (k, v) => k -> v * factor }, constant * factor)

  /**
   * The form of the product of two terms whose forms these are.
   *
   * `atom` is asked for the key that stands for a product of two atoms, because a `LinearForm`
   * never builds terms: its keys are only ever compared with one another, and the caller is the
   * one that knows how the goal's own atoms are spelt.
   *
   * Exact, and it has to be: this is what lets `0 < x /\ 0 < y ==> 0 < x * y` be found at all,
   * by putting the goal's atom `x * y` into a hypothesis where no combination of forms over `x`
   * and `y` could ever reach it.
   */
  def times(other: LinearForm, atom: (Term, Term) => Term): LinearForm = {
    val crossed = for {
      (left, leftValue) <- coefficients.toVector
      (right, rightValue) <- other.coefficients.toVector
    } yield LinearForm(Map(atom(left, right) -> leftValue * rightValue), Rational.zero)

    val scaledByConstants =
      Vector(other.scaled(constant), scaled(other.constant)) :+
        LinearForm(Map.empty, -(constant * other.constant))

    (crossed ++ scaledByConstants).foldLeft(LinearForm.zero)(_ + _)
  }

  def isZero: Boolean = coefficients.isEmpty && constant.isZero

  def atoms: Set[Term] = coefficients.keySet

  def at(atom: Term): Rational = coefficients.getOrElse(atom, Rational.zero)
}

object LinearForm {

  val zero: LinearForm = LinearForm(Map.empty, Rational.zero)
  def atom(term: Term): LinearForm = LinearForm(Map(term -> Rational.one), Rational.zero)
  def number(value: Rational): LinearForm = LinearForm(Map.empty, value)

  /**
   * A term that stands for a constant, as that constant, or nothing when it names an unknown.
   *
   * One definition, used by both the reader and the report on what the reader could not see, so
   * that "this is a coefficient" and "this is not the obstacle" can never disagree. They were two
   * definitions until 2026-09-09 and the disagreement they could hold was not hypothetical: a
   * quotient was a coefficient to neither and was named an obstacle by one of them.
   *
   * A numeral, a negated one, an inverse of a non-zero numeral, and a quotient of two of those.
   * **Zero is not a denominator here**, which is the rule `Ring` already keeps: `inv 0` is an atom
   * this search holds no fact about, so `x / 0` is an unknown and not a scaled `x`. A symbolic
   * denominator is not one either, and it never becomes one by looking harder: whether `inv y` is
   * anything at all needs `~(y = 0)`, which is `Field`'s to charge for and not this procedure's.
   */
  private[theories] def coefficient(reals: Signature, term: Term): Option[Rational] = {
    def denominator(current: Term): Option[Rational] = coefficient(reals, current).filter(!_.isZero)

    Numeral.valueOf(reals, term).map(Rational.of) match {
      case Some(value) => Some(value)
      case None =>
        term match {
          case App(Const(Real.Negation, _), argument) => coefficient(reals, argument).map(-_)
          case App(Const(Real.Inverse, _), argument) => denominator(argument).map(Rational.one / _)
          case App(App(Const(Real.Division, _), left), right) =>
            for {
              numerator <- coefficient(reals, left)
              divisor <- denominator(right)
            } yield numerator / divisor
          case _ => None
        }
    }
  }

  /**
   * What in a term the linear form cannot see, named, or nothing when it can see all of it.
   *
   * [[of]] never fails: whatever it cannot read becomes an atom, which is the right thing for
   * the search and the wrong thing for the caller. A goal about a quotient and a goal about a
   * product of two unknowns both come back as "no certificate", and the refusal a caller then
   * receives names neither. Measured on the frozen corpus of 2026-09-07: five goals refused, five
   * messages naming the wrong obstacle.
   *
   * The knowledge existed and was in the wrong place. `LinarithCorpusSpec` computed "an atom is not
   * a variable" for its own report while the procedure it was measuring could not say it, so a
   * benchmark harness knew more about the refusal than the caller did.
   *
   * It reports the first obstacle rather than all of them, because a caller repairs one thing at a
   * time and a list of four is a list nobody reads to the end.
   *
   * == What is an obstacle, which is narrower than it was ==
   *
   * **A denominator this procedure cannot invert, and nothing else.** Until 2026-09-11 anything the
   * cases below did not recognise was named as unreadable, and that was wrong in the same way
   * naming a product of two unknowns was wrong before 2026-09-10: `of` makes an atom of it and
   * the search runs. `0 < Power 3 k /\ Power 3 k < Power 4 k ==> 3 * Power 3 k < 4 * Power 4 k` is
   * **proved**, over two atoms this used to call unreadable, and so is a goal about `Sum f n` and
   * one about `real_of_num n`. A caller told to rewrite the atom rewrote it and was refused again.
   *
   * What is left is the honest refusal for the goals that really do stop here: a symbolic
   * denominator asks for `~(y = 0)`, which is `Field`'s to assume, and `inv 0` is an atom rather
   * than a denominator. Those keep their own messages, which name the denominator and whose price
   * it is.
   *
   * The refusal for a goal with an opaque atom in it is therefore the ordinary one — no certificate
   * from these hypotheses — which is what actually happened. `0 < Power 4 k` is not provable
   * because nothing says a power is positive, not because nobody could read it.
   *
   * Found by a consumer, which met it as LINARITH accusing its own reader for a goal it had built
   * correctly.
   */
  def unreadable(reals: Signature, term: Term): Option[String] = {
    def constant(current: Term): Boolean = coefficient(reals, current).isDefined

    def go(current: Term): Option[String] =
      if (constant(current)) None
      else
        current match {
          case App(App(Const(Real.Addition, _), left), right) => go(left).orElse(go(right))
          case App(App(Const(Real.Subtraction, _), left), right) => go(left).orElse(go(right))
          case App(Const(Real.Negation, _), argument) => go(argument)

          // A product of two unknowns is **not** an obstacle since 2026-09-10, and saying it was
          // became a wrong message the moment [[of]] started multiplying the two forms out:
          // `0 < x /\ 0 < y ==> 1 < x * y` is refused because it is false, not because it could
          // not be read, and a caller told to rewrite the product would rewrite it and be refused
          // again. What is looked for inside is the same as anywhere else, so `x * inv y` still
          // names the `inv y`.
          case App(App(Const(Real.Multiplication, _), left), right) =>
            go(left).orElse(go(right))

          // The denominator is what decides. A non-zero constant one is a coefficient, so the
          // numerator is the only thing left that can be an obstacle and `x / 2 <= x` is refused
          // for being false rather than for being written with a slash. Anything else divides by
          // something this procedure cannot invert, and the two ways of that are told apart
          // because one of them has an address and the other does not.
          case App(App(Const(Real.Division, _), left), right) =>
            if (coefficient(reals, right).exists(!_.isZero)) go(left)
            else divisor(reals, current, right)

          case App(Const(Real.Inverse, _), argument) => divisor(reals, current, argument)

          // Anything else is an atom, and an atom is not an obstacle. See the note above: the
          // search runs over atoms and decides a great many goals that carry them, so naming one
          // as unreadable describes the reader rather than the goal.
          case _ => None
        }

    go(term)
  }

  /** Why a denominator is not one, for a denominator [[coefficient]] has already declined. */
  private def divisor(reals: Signature, whole: Term, denominator: Term): Option[String] =
    if (coefficient(reals, denominator).exists(_.isZero))
      Some(
        s"${reals.show(whole)} divides by zero, and inv 0 is an atom rather than a denominator"
      )
    else
      Some(
        s"${reals.show(whole)} divides by ${reals.show(denominator)}, which is not a numeral, a " +
          "negated one, an inverse of a non-zero numeral or a quotient of two of those: " +
          "cancelling a symbolic denominator needs it to be non-zero, which is Field's to assume"
      )

  /**
   * The same, for a proposition rather than a quantity: the sides of its relation are what count.
   *
   * [[unreadable]] walks a term of type real. A goal is a proposition, and handing it one produced
   * the answer "`3967 / 285489 < 14 / 1000` is not a variable, a numeral or a sum of those", which
   * is true of every inequality ever written and therefore says nothing. Measured on the frozen
   * corpus the morning after the first fix, which is why it is here: the first repair moved the
   * message from wrong to vacuous, and only running the corpus again showed the difference.
   */
  def obstacleIn(reals: Signature, proposition: Term): Option[String] =
    Order
      .destOrder(reals, proposition)
      .map { case (left, right, _) => (left, right) }
      .orElse(Term.destEq(proposition).filter { case (left, _) =>
        Term.typeOf(left) == Real.realType
      })
      .flatMap { case (left, right) =>
        unreadable(reals, left).orElse(unreadable(reals, right))
      }

  /**
   * The linear form of a term: a coefficient for each atom it is built from, and a constant.
   *
   * A product with a constant on either side is read as a coefficient, which is what lets the
   * search see that `2 * x` and `x` are about the same atom, and since 2026-09-09 a quotient by a
   * non-zero numeral is one too, so `x / 3` is `x` at a third rather than an atom of its own.
   * [[coefficient]] is the whole of what counts as a constant and says why each case is in it.
   *
   * Everything else that is not a sum, a difference or a negation is an atom, `inv y` and `x * y`
   * alike: an atom is what the search knows nothing about, and reading one wrongly costs a proof
   * rather than yielding a wrong one.
   */
  def of(reals: Signature, term: Term): Either[LogicError, LinearForm] = {
    def go(current: Term): LinearForm =
      coefficient(reals, current) match {
        case Some(value) => LinearForm.number(value)

        case None =>
          current match {
            case App(App(Const(Real.Addition, _), left), right) => go(left) + go(right)
            case App(App(Const(Real.Subtraction, _), left), right) => go(left) + (-go(right))
            case App(Const(Real.Negation, _), argument) => -go(argument)

            // A product of two unknowns is read the way a *manufactured* product is read, by
            // multiplying the two forms out. Until 2026-09-10 it was one atom, and that is the
            // whole of why `0 < p /\ d < q ==> 0 < p * (q - d)` was refused while
            // `0 < p /\ d < q ==> 0 < p * q - p * d` was proved: the pair of hypotheses
            // multiplied gives a fact over the atoms `p * q` and `p * d`, and a goal whose only
            // atom is `p * (q - d)` shares no column with it. Two statements of one thing, and
            // whether the author distributed by hand decided which one this procedure met.
            //
            // Reading it this way makes the two readings the same function, so they cannot drift:
            // both go through [[LinearForm.times]] and both key an atom through [[productAtom]].
            case App(App(Const(Real.Multiplication, _), left), right) =>
              (coefficient(reals, left), coefficient(reals, right)) match {
                case (Some(factor), _) => go(right).scaled(factor)
                case (_, Some(factor)) => go(left).scaled(factor)
                case _ => go(left).times(go(right), productAtom(reals, _, _))
              }

            // A quotient whose denominator is a constant is that constant's reciprocal applied to
            // the numerator, which is where a form gains a denominator at all. One that is not is
            // an atom, and the atom is the whole quotient rather than the numerator: `x / y` says
            // nothing about `x` that this search can use.
            case App(App(Const(Real.Division, _), left), right) =>
              coefficient(reals, right).filter(!_.isZero) match {
                case Some(divisor) => go(left).scaled(Rational.one / divisor)
                case None => atom(current)
              }

            case other => atom(other)
          }
      }

    Right(go(term))
  }

  /** A conclusion as a form, and whether it has to be reached strictly. */
  def goal(reals: Signature, term: Term): Option[(LinearForm, Boolean)] =
    Order.destOrder(reals, term).flatMap { case (left, right, strict) =>
      (for {
        leftForm <- of(reals, left)
        rightForm <- of(reals, right)
      } yield (rightForm + (-leftForm), strict)).toOption
    }

  /**
   * The key a product of two unknowns is held under, with its factors in a fixed order.
   *
   * A form's atoms are keys in an untrusted search and never reach the kernel, so what they are
   * spelt like is free: nothing is proved about them and the ring step checks the answer whatever
   * they were. Sorting the factors is therefore not a normalisation, it is a decision to let
   * `x * y` and `y * x` be one key, which makes the search find combinations it would otherwise
   * miss and can cost it nothing.
   *
   * It matters because a product of hypotheses is manufactured rather than read: the fact built
   * from `0 < x` and `0 < y` has to land on the same key as the goal's own `x * y`, whichever way
   * round the goal happened to write it. Flattening first is the same argument for associativity.
   */
  def productAtom(reals: Signature, left: Term, right: Term): Term = {
    val sorted = (factorsOf(left) ++ factorsOf(right)).sorted(using Term.ordering)
    val binary = Type.fun(Real.realType, Type.fun(Real.realType, Real.realType))

    sorted.reduceRight { (first, rest) =>
      (for {
        times <- reals.theory.constant(Real.Multiplication, binary)
        applied <- Term.appAll(times, List(first, rest))
      } yield applied).getOrElse(first)
    }
  }

  /** What a product atom multiplies, flattened, which is how its degree is counted. */
  def factorsOf(term: Term): Vector[Term] = term match {
    case App(App(Const(Real.Multiplication, _), first), second) =>
      factorsOf(first) ++ factorsOf(second)
    case other => Vector(other)
  }
}

/** A hypothesis as the search sees it: what kind it is, and its linear form. */
final case class LinearFact(kind: LinearFact.Kind, form: LinearForm)

object LinearFact {

  /**
   * What kind of fact a hypothesis is, which decides how its multiplier may be used.
   *
   * A strict one may be weighed by anything non-negative and carries strictness with it; a
   * non-strict one may be weighed the same way and carries none; an equality may be weighed by
   * anything at all, either sign, because what the multiplier multiplies is zero.
   */
  enum Kind {
    case Strict, NonStrict, Equal
  }

  /**
   * A proposition as a fact, and only if it is one of the three relations over the reals.
   *
   * This is [[of]] without its fallthrough, and the two exist apart because the fallthrough is
   * right for a procedure that proves and wrong for one that answers. A caller that will report a
   * verdict has to know that it read the proposition rather than that it produced something; this
   * is the reader that says so.
   */
  def relation(reals: Signature, term: Term): Either[LogicError, LinearFact] = {
    def difference(left: Term, right: Term, kind: Kind): Either[LogicError, LinearFact] =
      for {
        leftForm <- LinearForm.of(reals, left)
        rightForm <- LinearForm.of(reals, right)
      } yield LinearFact(kind, rightForm + (-leftForm))

    Order.destOrder(reals, term) match {
      case Some((left, right, true)) => difference(left, right, Kind.Strict)
      case Some((left, right, false)) => difference(left, right, Kind.NonStrict)

      case None =>
        Term.destEq(term) match {
          case Some((left, right)) if Term.typeOf(left) == Real.realType =>
            difference(left, right, Kind.Equal)

          case _ => Left(NotOfForm("a relation between two reals", term))
        }
    }
  }

  /**
   * A hypothesis as a fact.
   *
   * Anything that is not one of the three shapes becomes a strict fact over an atom nobody else
   * mentions, which is how a hypothesis the procedure cannot read stops being usable without
   * stopping the procedure: the search can only cancel that atom against itself, and the assembly
   * refuses it if the search ever picks it.
   *
   * **That is right here and wrong for a caller that answers**, which is why [[relation]] exists
   * beside it. A procedure that ends in a theorem or nothing can afford an unreadable hypothesis as
   * a column it will never weigh; a procedure that ends in a verdict cannot, because the column
   * carries a reading of the proposition that nobody checked. A bare proposition `p` becomes the
   * fact `0 < p` here, and over an ordered field `0 < p \/ ~(0 < p)` is a tautology, so a decider
   * built on this reader would answer that `p \/ ~p` holds. This logic does not prove that formula
   * and does not have it, and the answer would be about a question nobody asked.
   */
  def of(reals: Signature, term: Term): Either[LogicError, LinearFact] =
    relation(reals, term) match {
      case Right(fact) => Right(fact)
      case Left(_) => LinearForm.of(reals, term).map(LinearFact(Kind.Strict, _))
    }
}
