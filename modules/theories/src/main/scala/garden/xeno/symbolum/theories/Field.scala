package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A tactic for identities with a symbolic denominator: it proves them under the side conditions
 * they need, and the theorem it returns carries those conditions where a reader can see them.
 *
 * `!x y. (x * y) / y = x` is not true, and no honest tactic proves it. What is true is
 * `~(y = 0) |- (x * y) / y = x`, and that is what comes back: a sequent with the hypothesis
 * attached, not a theorem with the hypothesis discharged into silence. The difference is the whole
 * point of the tactic. `MUL_INVERSE` is an axiom with an antecedent, so a normal form that cancels
 * `y * inv y` is a normal form that owes something, and the debt is paid by carrying it rather than
 * by hiding it.
 *
 * == What it does that [[Ring]] does not ==
 *
 * Since 2026-09-08 both normal forms unfold `div`, so moving a quotient about is ordinary ring
 * algebra and [[Ring]] settles it with nothing owed: `(z * x) / (2 * y) = z * (x / (2 * y))` is a
 * theorem with no hypotheses, because it is the definition of `div` read twice and then
 * associativity. This tactic adds only the step that genuinely needs the axiom, which is
 * cancellation: `y * inv y` becoming `1`.
 *
 * So the rule for choosing between them is not "quotients here, no quotients there". It is: if the
 * identity holds for every value of the denominator, [[Ring]] proves it and owes nothing; if it
 * holds only where the denominator is not zero, this one proves it and says so.
 *
 * == A denominator that is not an atom ==
 *
 * `inv (2 * y)` was one atom until 2026-09-09, and `(2 * x) / (2 * y) = x / y` was refused for it.
 * A denominator is now taken apart by recursion before anything is assumed about it: a product's
 * reciprocal is the product of the reciprocals, a negation's is a negation, `inv a`'s is `a`, a
 * numeral's is settled by [[Positivity]] and costs nothing, and only an atom assumes `~(d = 0)`.
 * [[Coefficient.inverseOfUnit]] turns the reciprocal into a statement about `inv` in one step.
 *
 * **No fact about zero divisors is needed for that, and that is why it fits here.** The obvious
 * route derives `~(a * b = 0)` from `~(a = 0)` and `~(b = 0)`, which is a theorem with a case
 * analysis behind it. A factor of one cannot be zero, so the reciprocal this tactic builds anyway
 * is the witness, and the conditions charged are the ones the factors were charging already.
 *
 * == Why the atoms are ordered differently here ==
 *
 * A rewrite fires between neighbours. `d` and `inv d` are two atoms of a monomial, and under
 * `Arithmetic.ringOrder` they are not neighbours: `inv d` is an application and sorts with the
 * other applications, so any variable atom between them keeps them apart, and the cancellation rule
 * never matches. [[Field.atomOrder]] compares an atom by what is under its inverses first, exactly
 * as `ringOrder` compares by what is under its negations, and for exactly the same reason: it puts
 * a term next to the thing that cancels it. `Polynomial` takes the order as a parameter so this
 * choice stays inside this tactic and no other normal form moves.
 *
 * == The denominator this tactic is no longer for ==
 *
 * A numeral. `x / 2 + x / 2 = x` was refused here until 2026-09-09, and the reason was structural
 * rather than about the side condition: `~(2 = 0)` is provable, so nothing was owed. In the normal
 * form a numeral was a monomial's *coefficient* and never one of its atoms, so `2 * (x * inv 2)`
 * had the `2` on one side of that split and the `inv 2` on the other, and no rule between
 * neighbours could bring them together. Measured rather than reasoned about: a version of this
 * tactic that proved `~(n = 0)` for a numeral instead of assuming it changed nothing, because the
 * rule it prepared could never fire.
 *
 * A coefficient is a rational number now, so that case is settled by [[Ring]] before this tactic is
 * reached, and settled with nothing assumed. The numerals are not the whole of it:
 * [[Coefficient.ofInverse]] inverts a negated numeral and a ratio of numerals as well, since the
 * reciprocal is computed and a factor of one cannot be zero, so `inv (-2)` and `inv (2 * inv 3)`
 * are settled there too. `inv 0` is the constant that is not, because nothing multiplies it to one,
 * and it stays the atom it was. What is left here is a denominator with a variable in it, which has
 * no reciprocal to compute and is the kind whose being zero the theory cannot rule out, and paying
 * a hypothesis for it is the whole of what this file is.
 *
 * == What comes back, and what does not ==
 *
 * The quantifiers are put back on the variables that can carry one. A variable named in a side
 * condition cannot: `~(y = 0)` mentions `y`, so `!y` would be generalising over a variable that is
 * free in a hypothesis, which is unsound and which the kernel refuses. Such a variable stays free
 * and the hypothesis stays beside it. A goal written `!x y. (x * y) / y = x` therefore comes back
 * as `~(y = 0) |- !x. (x * y) / y = x`, and [[conditions]] is how a caller reads off what was
 * assumed.
 *
 * That is a weaker statement than the one that was asked for, and it is offered rather than
 * refused because it is the strongest true one of that shape: the reader can see both the loss and
 * the reason for it in the sequent itself. Where the denominator can be shown positive,
 * `Positivity.nonZero` discharges the condition and nothing is left owing.
 */
final class Field private (
  val reals: RealTheory,
  private val cancelling: Polynomial,
  private val coefficient: Coefficient,
  private val inverseOfUnit: Kernel.Thm,
  private val unitOfProduct: Kernel.Thm,
  private val unitOfNegation: Kernel.Thm,
  private val unitReversed: Kernel.Thm,
  private val mulInverse: Kernel.Thm,
  private val mulAssoc: Kernel.Thm,
  private val oneOnTheLeft: Kernel.Thm,
  private val zero: Term,
  private val times: Term,
  private val negation: Term,
  private val inverseConstant: Term
) {

  private val logic: Logic = reals.logic

  /**
   * Prove an equation, with or without leading quantifiers, under the side conditions it needs.
   *
   * The conditions are not guessed and not asked for: they are read off the normal forms. Whatever
   * survives as `inv d` after the ordinary normalisation is a denominator this identity depends on,
   * and `~(d = 0)` is assumed for each one. A goal with no denominator assumes nothing and this is
   * then [[Ring]] with a different atom order.
   *
   * **A denominator that is a product can be taken apart, and only is when the goal was not
   * settled without it.** `inv (24 * x)` becomes `inv 24 * inv x`, `~(24 = 0)` is then a theorem,
   * and only `~(x = 0)` reaches the caller.
   *
   * The order of the two attempts is the whole of what keeps this tactic's one promise. Splitting
   * is an inference like any other, so a rule that fires puts its conditions on the theorem whether
   * or not the proof needed them, and `(z * x) / (2 * y) = z * (x / (2 * y))` is true for every
   * `y`, zero included. Splitting first proved it while assuming `~(y = 0)`, which is the tactic
   * claiming a debt it did not owe. Trying without the split first costs one normalisation on the
   * goals that need it and nothing on the goals that do not, and it is what makes "a condition is
   * assumed only if it was used" still true rather than nearly true.
   */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Logic.stripForall(goal)
      sides <- Term.destEq(stripped._2).toRight(NotOfForm("an equation", stripped._2))
      denominators <- denominatorsOf(sides._1, sides._2)
      whole <- cancellationRules(denominators)

      proved <- Rewrite.proveWith(normalisation(Vector.empty, whole), sides._1, sides._2) match {
        case Right(theorem) => Right(theorem)
        case Left(refusal) => bySplitting(denominators, sides._1, sides._2, refusal)
      }

      general <- generalise(proved, stripped._1)
    } yield general

  /**
   * The second attempt, with every product under an inverse taken apart.
   *
   * A goal with no product denominator has nothing to split, and then the first attempt's refusal
   * is the whole answer and is what comes back. Where there is something to split, this refusal is
   * reported instead, because it is the one from the stronger attempt: the forms it names are the
   * ones the tactic could not bring together after doing everything it knows.
   */
  private def bySplitting(
    denominators: Vector[Term],
    left: Term,
    right: Term,
    refusal: LogicError
  ): Either[LogicError, Kernel.Thm] =
    for {
      splits <- splittingRules(denominators)
      rules <- cancellationRules(denominators.flatMap(Field.atomsOf).distinct)
      result <-
        if (splits.isEmpty) Left(refusal)
        else Rewrite.proveWith(normalisation(splits, rules), left, right)
    } yield result

  /** Prove an equation written in the theory's notation. */
  def prove(text: String): Either[LogicError, Kernel.Thm] =
    reals.proposition(text).flatMap(prove)

  /**
   * What a proof of this shape leans on, in the order the kernel keeps them.
   *
   * A convenience over `theorem.hypotheses`, and named because the whole contract of this tactic
   * is that a caller looks at them. A theorem whose conditions nobody read is a theorem used as if
   * it had none.
   */
  def conditions(theorem: Kernel.Thm): List[Term] = theorem.hypotheses

  /* --------------------------------------------------------------- the conversion */

  /**
   * Normalise, split, normalise, cancel, normalise.
   *
   * Five passes and not a loop, and each one is there for a reason the pass before it cannot serve.
   *
   * Splitting has to happen after a normalisation, because that is what puts a denominator into the
   * shape the rule was built for, and before the cancelling, because a factor cannot cancel while
   * it is still inside a product under one inverse. It also has to be followed by a normalisation
   * of its own: `inv (24 * x)` becoming `inv 24 * inv x` turns one atom into a coefficient and an
   * atom, and until the form is rebuilt the `24` is on the wrong side of the split between a
   * monomial's coefficient and its atoms.
   *
   * Neither middle pass can create work for itself. Splitting shrinks what is under each inverse
   * and cancelling removes atoms and never adds one, so the multiset only shrinks and no pair that
   * was apart is brought together by the removal of another. The last pass tidies what cancelling
   * leaves behind, which is a `1` where two atoms were, and re-sorts a monomial whose coefficient
   * has changed.
   */
  private def normalisation(
    splits: Vector[Rewrite.Rule],
    rules: Vector[Rewrite.Rule]
  ): Rewrite.Conversion =
    if (splits.isEmpty && rules.isEmpty) cancelling.normalisation
    else {
      // Asked before it is repeated, for the reason `Rewrite.Rule.iterable` gives: a rule with no
      // variables whose right side contains its left puts the pattern back every time it fires, so
      // a driver that repeats never reaches a fixed point and the heap goes before the step limit.
      // This pass is not `Rewrite.normaliser` and is left as it is: it carries no ordered rules and
      // no beta, and the paragraph above is the argument for its shape.
      def pass(available: Vector[Rewrite.Rule]): Rewrite.Conversion =
        if (available.isEmpty) (term: Term) => Right(Conv.refl(term))
        else
          Rewrite.Rule.iterable(available) match {
            case Left(error) => (_: Term) => Left(error)
            case Right(_) =>
              Rewrite.repeatConv(
                Rewrite.depthConv(Rewrite.firstConv(available.map(Rewrite.rewriteConv)))
              )
          }

      val split = pass(splits)
      val cancel = pass(rules)

      term =>
        for {
          normalised <- cancelling.normalisation(term)
          form <- rightOf(normalised)
          divided <- split(form)
          separated <- rightOf(divided)
          rebuilt <- cancelling.normalisation(separated)
          apart <- rightOf(rebuilt)
          cancelled <- cancel(apart)
          reduced <- rightOf(cancelled)
          settled <- cancelling.normalisation(reduced)
          result <- chain(List(normalised, divided, rebuilt, cancelled, settled))
        } yield result
    }

  /** The transitive closure of a list of steps, each one starting where the last left off. */
  private def chain(steps: List[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    steps match {
      case Nil => Left(NotOfForm("at least one step", zero))
      case head :: rest =>
        rest.foldLeft(Right(head): Either[LogicError, Kernel.Thm]) { (acc, step) =>
          acc.flatMap(Conv.trans(_, step))
        }
    }

  /* ------------------------------------------------------------- the denominators */

  /** Every `d` occurring as `inv d` in either normal form, without duplicates, in a stable order. */
  private def denominatorsOf(left: Term, right: Term): Either[LogicError, Vector[Term]] =
    for {
      leftForm <- cancelling.normalisation(left).flatMap(rightOf)
      rightForm <- cancelling.normalisation(right).flatMap(rightOf)
    } yield (inversesIn(leftForm) ++ inversesIn(rightForm)).distinct.sorted(using Arithmetic.ringOrder)

  private def inversesIn(term: Term): Vector[Term] = term match {
    case App(Const(Real.Inverse, _), argument) => inversesIn(argument) :+ argument
    case App(function, argument) => inversesIn(function) ++ inversesIn(argument)
    case Abs(_, body) => inversesIn(body)
    case _ => Vector.empty
  }

  /* ---------------------------------------------------------------- the cancelling */

  /**
   * `|- inv d = r` for every denominator whose reciprocal is something better than `inv d`.
   *
   * A denominator has a reciprocal that can be written down whenever it is built out of products,
   * negations, inverses and numerals, and [[reciprocal]] builds it alongside the proof that it is
   * one. [[Coefficient.inverseOfUnit]] then turns `d * r = 1` into `inv d = r` in one step, so
   * there is one rule shape here and not one per syntactic case.
   *
   * A denominator that is an atom has `inv d` as its own reciprocal and gets no rule: rewriting
   * `inv d` to itself is not a step, and offering it to a repeating rewriter is a loop.
   */
  private def splittingRules(
    denominators: Vector[Term]
  ): Either[LogicError, Vector[Rewrite.Rule]] =
    denominators.foldLeft(Right(Vector.empty): Either[LogicError, Vector[Rewrite.Rule]]) {
      (acc, denominator) =>
        for {
          rules <- acc
          built <- reciprocal(denominator)
          (value, unit) = built
          inverse <- LogicError.lift(Term.app(inverseConstant, denominator))
          next <-
            if (value == inverse) Right(rules)
            else
              for {
                instance <- logic.rules.specAll(inverseOfUnit, List(denominator, value))
                equated <- logic.rules.mp(instance, unit)
                rule <- Rewrite.Rule.of(logic, equated)
              } yield rules :+ rule
        } yield next
    }

  /**
   * The reciprocal of a denominator, and the proof that multiplying by it gives one.
   *
   * Four cases and one shape. A numeral's reciprocal is settled by [[Positivity]] and costs
   * nothing; a product's is the product of the reciprocals; a negation's is the negation of one;
   * and `inv a`'s reciprocal is `a` itself, which is the same fact read the other way round.
   * Anything else is an atom, its reciprocal is `inv` of it, and that is the one case where
   * `~(d = 0)` is assumed and travels to the caller.
   *
   * **Recursing is what keeps the conditions minimal, and not recursing was a defect.** A first
   * version split only the outermost product and assumed `~(d = 0)` for whatever was under it, so
   * `inv (x * (x * y))` came back having assumed `~(x * y = 0)` beside the two conditions that were
   * genuinely needed. Sound, and a hypothesis a reader has to think about for nothing, which is the
   * thing this tactic exists not to produce.
   */
  private def reciprocal(denominator: Term): Either[LogicError, (Term, Kernel.Thm)] =
    Numeral.valueOf(reals, denominator).filter(_ != 0) match {
      case Some(value) =>
        for {
          inverse <- LogicError.lift(Term.app(inverseConstant, denominator))
          unit <- coefficient.inverseOf(value)
        } yield (inverse, unit)

      case None =>
        denominator match {
          case App(App(Const(Real.Multiplication, _), left), right) =>
            for {
              first <- reciprocal(left)
              second <- reciprocal(right)
              value <- LogicError.lift(Term.appAll(times, List(first._1, second._1)))
              instance <- logic.rules
                .specAll(unitOfProduct, List(left, right, first._1, second._1))
              applied <- logic.rules.mp(instance, first._2).flatMap(logic.rules.mp(_, second._2))
            } yield (value, applied)

          case App(Const(Real.Negation, _), argument) =>
            for {
              inner <- reciprocal(argument)
              value <- LogicError.lift(Term.app(negation, inner._1))
              instance <- logic.rules.specAll(unitOfNegation, List(argument, inner._1))
              applied <- logic.rules.mp(instance, inner._2)
            } yield (value, applied)

          case App(Const(Real.Inverse, _), argument) =>
            for {
              inner <- reciprocal(argument)
              instance <- logic.rules.specAll(unitReversed, List(argument, inner._1))
              applied <- logic.rules.mp(instance, inner._2)
            } yield (argument, applied)

          case atom => unitFor(atom).map(unit => (inverseOf(atom), unit))
        }
    }

  /** `inv t`, as a term, for a `t` this tactic has decided to treat as an atom. */
  private def inverseOf(term: Term): Term =
    Term.app(inverseConstant, term).getOrElse(term)

  /**
   * `~(d = 0) |- d * inv d = 1`: the axiom, with its antecedent assumed rather than proved.
   *
   * Assuming is what the tactic is for, and this is the only place it happens. `Kernel.assume` puts
   * the proposition on the left of the turnstile and it stays there through every rule that uses
   * this theorem, which is why the condition arrives at the caller without anyone threading it by
   * hand. Every other case in [[reciprocal]] reaches this one or settles without it.
   */
  private def unitFor(denominator: Term): Either[LogicError, Kernel.Thm] =
    for {
      equated <- equation(denominator, zero)
      negated <- logic.mkNot(equated)
      assumed <- LogicError.lift(Kernel.assume(negated))
      instance <- logic.rules.spec(denominator, mulInverse)
      unit <- logic.rules.mp(instance, assumed)
    } yield unit

  private def cancellationRules(
    denominators: Vector[Term]
  ): Either[LogicError, Vector[Rewrite.Rule]] =
    denominators.foldLeft(Right(Vector.empty): Either[LogicError, Vector[Rewrite.Rule]]) {
      (acc, denominator) =>
        for {
          rules <- acc
          unit <- unitFor(denominator)
          nested <- nestedFor(denominator, unit)
          bare <- Rewrite.Rule.of(logic, unit)
          deep <- Rewrite.Rule.of(logic, nested)
        } yield rules ++ Vector(deep, bare)
    }

  /**
   * `~(d = 0) |- !r. d * (inv d * r) = r`: the same fact, in the shape a sorted product wears.
   *
   * A monomial is `a1 * (a2 * (... * ad))`, so two cancelling atoms are almost never the whole of
   * it: `d * inv d` matches only when the pair is the entire product. This is the general case, and
   * it is derived rather than assumed, from associativity and `1 * r = r`.
   */
  private def nestedFor(denominator: Term, unit: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rest = Conv.freshVariable("r", Field.real, Term.freeVariables(denominator))

    for {
      inverse <- Term.destEq(unit.conclusion).toRight(NotOfForm("an equation", unit.conclusion))
      inverted <- inverseSide(inverse._1, denominator)
      atDenominator <- logic.rules.spec(denominator, mulAssoc)
      atInverse <- logic.rules.spec(inverted, atDenominator)
      associated <- logic.rules.spec(rest, atInverse)
      scaled <- Conv.apTerm(times, unit).flatMap(Conv.apThm(_, rest))
      unitLeft <- logic.rules.spec(rest, oneOnTheLeft)
      chain <- Conv.trans(scaled, unitLeft)
      reversed <- Conv.sym(associated)
      nested <- Conv.trans(reversed, chain)
      general <- logic.rules.gen(rest, nested)
    } yield general
  }

  /** The `inv d` of a proved `d * inv d = 1`, taken from the theorem rather than rebuilt. */
  private def inverseSide(product: Term, denominator: Term): Either[LogicError, Term] =
    product match {
      case App(App(_, left), right) if left == denominator => Right(right)
      case other => Left(NotOfForm(s"${reals.show(denominator)} times its inverse", other))
    }

  /* ------------------------------------------------------------------- putting back */

  /**
   * Put back the quantifiers that can go back on.
   *
   * A variable free in a hypothesis cannot carry one and is left free. Silently, because the
   * hypothesis it appears in is right there in the sequent and says more than any message could:
   * a reader who looks at what was assumed sees which variable is no longer general and why.
   */
  private def generalise(
    theorem: Kernel.Thm,
    variables: Vector[FVar]
  ): Either[LogicError, Kernel.Thm] =
    variables.reverse.foldLeft(Right(theorem): Either[LogicError, Kernel.Thm]) { (acc, variable) =>
      acc.flatMap { current =>
        if (current.hypotheses.exists(Term.occursFree(variable, _))) Right(current)
        else logic.rules.gen(variable, current)
      }
    }

  private def equation(left: Term, right: Term): Either[LogicError, Term] =
    for {
      partial <- LogicError.lift(Term.app(Term.equalityAt(Term.typeOf(left)), left))
      whole <- LogicError.lift(Term.app(partial, right))
    } yield whole

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}

object Field {

  private val real: Type = TyApp(Real.TypeName, Nil)

  /**
   * The parts of a denominator that this tactic can say nothing about, and so must assume about.
   *
   * The leaves of the same recursion `Field.reciprocal` walks: a product contributes its factors, a
   * negation and an inverse contribute what is under them, a numeral contributes nothing because it
   * is settled, and anything else is itself.
   */
  private def atomsOf(term: Term): Vector[Term] = term match {
    case App(App(Const(Real.Multiplication, _), left), right) => atomsOf(left) ++ atomsOf(right)
    case App(Const(Real.Negation, _), argument) => atomsOf(argument)
    case App(Const(Real.Inverse, _), argument) => atomsOf(argument)
    case other => Vector(other)
  }

  /**
   * Two atoms compared by what is under their inverses, then by how many inverses that was.
   *
   * The same shape as `Arithmetic.ringOrder`, which strips negations for the same purpose, and the
   * comment there applies here too: comparing `inv x` and `x` by their outsides puts every
   * application in one place and every variable in another, and the pair that cancels ends up with
   * whatever else happened to sort between them. Stripping first makes them neighbours, which is
   * the precondition for a rewrite ever firing on them.
   *
   * Total, because it is lexicographic in a total order and a number.
   */
  val atomOrder: Ordering[Term] = new Ordering[Term] {

    def compare(left: Term, right: Term): Int = {
      val (leftBase, leftDepth) = strip(left, 0)
      val (rightBase, rightDepth) = strip(right, 0)

      val byBase = Arithmetic.ringOrder.compare(leftBase, rightBase)
      if (byBase != 0) byBase else leftDepth.compare(rightDepth)
    }

    @annotation.tailrec
    private def strip(term: Term, depth: Int): (Term, Int) = term match {
      case App(Const(Real.Inverse, _), argument) => strip(argument, depth + 1)
      case _ => (term, depth)
    }
  }

  /** Built once over the standard theory of the reals. */
  lazy val standard: Field =
    construct(Arithmetic.standard).fold(
      error => throw new IllegalStateException(s"the field tactic does not build: ${error.message}"),
      identity
    )

  /** The tactic over a theory whose arithmetic has already been proved. */
  def construct(arithmetic: Arithmetic): Either[LogicError, Field] = {
    val reals = arithmetic.reals

    for {
      positivity <- Positivity.construct(arithmetic)
      coefficient <- Coefficient.construct(arithmetic, positivity)
      cancelling <- Polynomial.construct(coefficient, atomOrder)
      inverseOfUnit <- Coefficient.inverseOfUnit(arithmetic)
      unitOfProduct <- Coefficient.unitOfProduct(arithmetic)
      unitOfNegation <- Coefficient.unitOfNegation(arithmetic)
      unitReversed <- Coefficient.unitReversed(arithmetic)
      mulInverse <- reals.axiom("MUL_INVERSE")
      mulAssoc <- reals.axiom("MUL_ASSOC")
      oneOnTheLeft <- arithmetic.lemma(Arithmetic.OneOnTheLeft)
      zero <- reals.term("0")
      times <- LogicError.lift(
        reals.theory.constant(Real.Multiplication, Type.fun(real, Type.fun(real, real)))
      )
      negation <- LogicError.lift(reals.theory.constant(Real.Negation, Type.fun(real, real)))
      inverse <- LogicError.lift(reals.theory.constant(Real.Inverse, Type.fun(real, real)))
    } yield new Field(
      reals,
      cancelling,
      coefficient,
      inverseOfUnit,
      unitOfProduct,
      unitOfNegation,
      unitReversed,
      mulInverse,
      mulAssoc,
      oneOnTheLeft,
      zero,
      times,
      negation,
      inverse
    )
  }
}
