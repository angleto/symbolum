package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The set defined by rules: the least set closed under a monotone operator, and its induction
 * principle.
 *
 * One definition in three of rewriting theory is given in this shape — "the least subset of
 * `Sigma*` containing X and closed under the following clauses" — and until this landed the shape
 * could not be **written** here. What could be done instead was to compute a closure to some depth
 * and look, which answers membership for the elements it reached and answers nothing at all about
 * non-membership. That asymmetry is the reason this file exists, and it is worth stating before the
 * definition: the closure is generated forwards, so a member turns up eventually and a non-member
 * never distinguishes itself from one that is further away than the budget.
 *
 * == The definition, which is the intersection rather than a construction ==
 *
 * `INDUCTIVE f` is the set of `x` such that every `f`-closed set holds of `x`:
 *
 * {{{
 *   INDUCTIVE = \f x. !S. (!y. f S y ==> S y) ==> S x
 * }}}
 *
 * No iteration, no ordinal, no limit. `Natural.NUM_REP` is the same trick written out by hand for
 * one operator, zero-and-successor over `ind`, and the sentence its own comment uses is the one to
 * carry here: *induction is then not a further assumption, it is this definition read back*. What
 * this file does is take the trick away from that one operator, which costs a type variable and a
 * higher-order argument and nothing else. It declares two constants and no axiom.
 *
 * == The two faces, and only one of them costs monotonicity ==
 *
 *  - [[Inductive.Induction]] is `(!y. f S y ==> S y) ==> (!x. INDUCTIVE f x ==> S x)`: an
 *    `f`-closed `S` contains the closure. It is the **definition unfolded and specialised**, so it
 *    needs no hypothesis about `f` at all. It is what proves a **non**-membership, and it is the
 *    half a forward closure computation cannot do.
 *  - [[Inductive.Introduction]] is `MONOTONE f ==> (!x. f (INDUCTIVE f) x ==> INDUCTIVE f x)`: the
 *    closure is itself `f`-closed, which is what the introduction rules of a rule set are. This one
 *    **does** need monotonicity, and the asymmetry is not bookkeeping: without monotonicity the
 *    intersection of all closed sets need not be closed, and `INDUCTIVE f` would be a set with an
 *    induction principle and no members.
 *  - [[Inductive.Fixpoint]] is the two together, `INDUCTIVE f x = f (INDUCTIVE f) x`, which is what
 *    entitles the word "fixed point" in this file's name. It is derived rather than stated twice:
 *    the direction that is not [[Inductive.Introduction]] is [[Inductive.Induction]] at `S := f
 *    (INDUCTIVE f)`, and what discharges its obligation is [[Inductive.Introduction]] pushed
 *    through monotonicity.
 *
 * `MONOTONE f` is `!S T. (!x. S x ==> T x) ==> (!x. f S x ==> f T x)`, defined here rather than
 * assumed of the caller, because a caller that has to state it inline states it differently each
 * time and nothing can then be proved once about the class.
 *
 * == What it does not do ==
 *
 * **It does not prove monotonicity, and since 2026-09-16 [[Monotone]] does.** Every operator
 * written from a rule set in the usual shape — a disjunction of clauses, each a conjunction in
 * which the set argument occurs only positively — is monotone for reasons that are visible in the
 * term, and that procedure reads them. It lives beside this file rather than in it because it
 * declares nothing and because its caller's logic, not this development's, is the one that can read
 * the caller's operator. What is still true and is the part to carry: monotonicity is an obligation
 * on the caller, and a caller whose operator is not written in that shape still owes a hand proof.
 *
 * **It does not give a recursion.** Defining a *function* by recursion over the derivation of a
 * membership is a different theorem, and `Descent` is where this repository's course-of-values
 * recursion lives. What is here is a predicate and how to reason about it.
 *
 * **There is no rewriting relation in it, and that is a dependency and not an oversight.** A step
 * `u ->_R v` of a string rewriting system says the left-hand side is a **factor** of `u`, and
 * `word` has no concatenation, so the predicate cannot be stated at all yet. That is a card of its
 * own and it is somebody else's; when it lands, the step relation and the closures over it are
 * instances of what is here rather than more of it.
 */
final class Inductive private (
  val classical: Classical,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = classical.logic
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
}

object Inductive {

  /** `MONOTONE f` — `f` takes a larger set to a larger set. */
  val Monotone: String = "MONOTONE"

  /** `INDUCTIVE f` — the least `f`-closed set, as the intersection of all of them. */
  val Name: String = "INDUCTIVE"

  /**
   * `|- !f S. (!y. f S y ==> S y) ==> (!x. INDUCTIVE f x ==> S x)`.
   *
   * The induction principle, and the only way a non-membership is ever proved. It asks **nothing**
   * of `f`: it is the definition unfolded and specialised at `S`, which is why it is derived first
   * and why [[Introduction]] is allowed to use it.
   */
  val Induction: String = "INDUCTIVE_INDUCT"

  /**
   * `|- !f. MONOTONE f ==> (!x. f (INDUCTIVE f) x ==> INDUCTIVE f x)`.
   *
   * The introduction rules of the rule set, all of them at once: whatever the clauses derive from
   * members is a member. A caller with a concrete `f` gets its own clause by specialising this and
   * picking a disjunct, which is what `InductiveSpec` does twice.
   */
  val Introduction: String = "INDUCTIVE_INTRO"

  /** `|- !f. MONOTONE f ==> (!x. INDUCTIVE f x = f (INDUCTIVE f) x)` — it really is a fixed point. */
  val Fixpoint: String = "INDUCTIVE_FIXPOINT"

  /** `'a`, the type the sets are sets of. Everything here is polymorphic in it. */
  val Element: Type = TyVar(Classical.TypeVariable)

  /** `'a -> bool`, a set said as its membership predicate. */
  val Sets: Type = Type.fun(Element, Type.Bool)

  /** `('a -> bool) -> 'a -> bool`, a rule set said as the operator it induces. */
  val Operators: Type = Type.fun(Sets, Sets)

  private val MonotoneBody: String =
    "\\f:('a->bool)->'a->bool. !S:'a->bool. !T:'a->bool. " +
      "(!x:'a. S x ==> T x) ==> (!x:'a. f S x ==> f T x)"

  private val Body: String =
    "\\f:('a->bool)->'a->bool. \\x:'a. " +
      "!S:'a->bool. (!y:'a. f S y ==> S y) ==> S x"

  /**
   * Everything this development proves, as the text a person checks it by.
   *
   * Read as a **term** rather than compared as printed text, for the reason `RotationSpec` gives: a
   * type variable is written `'a` here and printed `a`, so a printed polymorphic statement does not
   * read back and the parse is the stronger comparison anyway.
   */
  val Statements: Vector[(String, String)] = Vector(
    Induction ->
      ("!f:('a->bool)->'a->bool. !S:'a->bool. (!y:'a. f S y ==> S y) ==> " +
        "(!x:'a. INDUCTIVE f x ==> S x)"),
    Introduction ->
      ("!f:('a->bool)->'a->bool. MONOTONE f ==> " +
        "(!x:'a. f (INDUCTIVE f) x ==> INDUCTIVE f x)"),
    Fixpoint ->
      ("!f:('a->bool)->'a->bool. MONOTONE f ==> " +
        "(!x:'a. INDUCTIVE f x = f (INDUCTIVE f) x)")
  )

  /**
   * The standard development, which is the chain's own and not a second one beside it.
   *
   * A lookup rather than a second construction, for the reason `Rotation.standard` gives: nothing
   * is built on top of this yet, so a second one would have no caller and would put a second
   * `INDUCTIVE` of a different origin into the world for a consumer to trip over.
   */
  lazy val standard: Inductive = Chain.standard.inductive

  /**
   * The development, over whatever the last link of the chain is.
   *
   * `base` is the theory to **extend** and is not the theory this needs, which is only the logic:
   * nothing here mentions a number, a word or a pair. The two are different questions and
   * `Rotation.construct`'s comment is the one that says so — a constant declared into a side branch
   * is unreachable from everything above it, and `Chain.widest` is built over the last extension.
   */
  def construct(
    classical: Classical,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Inductive] =
    for {
      monotoneBody <- Parser.term(base, notation, MonotoneBody)
      monotoneDefined <- LogicError.lift(Kernel.defineConstant(base, Monotone, monotoneBody))
      (withMonotone, monotoneDefinition) = monotoneDefined

      body <- Parser.term(withMonotone, notation, Body)
      defined <- LogicError.lift(Kernel.defineConstant(withMonotone, Name, body))
      (theory, definition) = defined

      logic <- classical.logic.over(theory)

      induction <- inductionPrinciple(logic, theory, definition)
      introduction <- introductionRules(logic, theory, definition, monotoneDefinition, induction)
      fixpoint <- fixedPoint(logic, theory, definition, monotoneDefinition, induction, introduction)
    } yield new Inductive(
      classical,
      theory,
      notation,
      Map(Monotone -> monotoneDefinition, Name -> definition),
      Map(Induction -> induction, Introduction -> introduction, Fixpoint -> fixpoint)
    )

  /* ------------------------------------------------------------------ the pieces */

  private val Operator: FVar = Term.variable("f", Operators)
  private val Smaller: FVar = Term.variable("S", Sets)
  private val Point: FVar = Term.variable("x", Element)

  /** `INDUCTIVE f`, the set, as a term over the theory that declares it. */
  private def closureOf(theory: Theory, operator: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(Name, Type.fun(Operators, Sets)))
      applied <- LogicError.lift(Term.app(constant, operator))
    } yield applied

  /** `MONOTONE f`, the proposition. */
  private def monotoneOf(theory: Theory, operator: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(Monotone, Type.fun(Operators, Type.Bool)))
      applied <- LogicError.lift(Term.app(constant, operator))
    } yield applied

  /**
   * [[Induction]], which is the definition read back.
   *
   * Every step is forced: unfold `INDUCTIVE f x`, which is a claim about **every** `S`; specialise
   * it at the `S` the caller brought; detach the closure hypothesis. Nothing about `f` is used,
   * and that is the fact the docstring above turns on rather than an accident of this proof.
   */
  private def inductionPrinciple(
    logic: Logic,
    theory: Theory,
    definition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      membership <- closureOf(theory, Operator).flatMap(set => LogicError.lift(Term.app(set, Point)))
      unfolded <- Conv.unfold(definition, List(Operator, Point))

      assumed <- LogicError.lift(Kernel.assume(membership))
      opened <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      instance <- rules.spec(Smaller, opened)

      parts <- logic.destImp(instance.conclusion).toRight(NotOfForm("an implication", instance.conclusion))
      (closed, _) = parts
      assumedClosed <- LogicError.lift(Kernel.assume(closed))
      inside <- rules.mp(instance, assumedClosed)

      implication <- rules.disch(membership, inside)
      everywhere <- rules.gen(Point, implication)
      discharged <- rules.disch(closed, everywhere)
      overSets <- rules.gen(Smaller, discharged)
      result <- rules.gen(Operator, overSets)
    } yield result
  }

  /**
   * [[Introduction]], which is where monotonicity is spent and the only place it is.
   *
   * To show `INDUCTIVE f x` from `f (INDUCTIVE f) x` is to show `S x` for an arbitrary `f`-closed
   * `S`. [[Induction]] gives `INDUCTIVE f` inside `S`; monotonicity carries that inclusion under
   * `f`, so `f (INDUCTIVE f) x` gives `f S x`; and `S` being closed finishes it. The order matters
   * only in that monotonicity is applied to an inclusion the induction principle produced, which is
   * why [[Induction]] is derived first and handed in rather than re-derived.
   */
  private def introductionRules(
    logic: Logic,
    theory: Theory,
    definition: Kernel.Thm,
    monotoneDefinition: Kernel.Thm,
    induction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      closure <- closureOf(theory, Operator)
      monotone <- monotoneOf(theory, Operator)

      // `f (INDUCTIVE f) x`, the premise of a clause.
      applied <- LogicError.lift(Term.app(Operator, closure))
      atPoint <- LogicError.lift(Term.app(applied, Point))

      // `MONOTONE f` unfolded and aimed at the inclusion `INDUCTIVE f` inside `S`.
      assumedMonotone <- LogicError.lift(Kernel.assume(monotone))
      monotoneAt <- Conv.unfold(monotoneDefinition, List(Operator))
      openedMonotone <- LogicError.lift(Kernel.eqMp(monotoneAt, assumedMonotone))
      monotoneInstance <- rules.specAll(openedMonotone, List(closure, Smaller))

      // The inclusion itself, from the induction principle, under the closure hypothesis.
      inductionAt <- rules.specAll(induction, List(Operator, Smaller))
      parts <- logic
        .destImp(inductionAt.conclusion)
        .toRight(NotOfForm("an implication", inductionAt.conclusion))
      (closed, _) = parts
      assumedClosed <- LogicError.lift(Kernel.assume(closed))
      inclusion <- rules.mp(inductionAt, assumedClosed)

      // Under `f`, and then at `x`.
      carried <- rules.mp(monotoneInstance, inclusion)
      assumedAtPoint <- LogicError.lift(Kernel.assume(atPoint))
      inSmallerImage <- rules.spec(Point, carried).flatMap(rules.mp(_, assumedAtPoint))
      inSmaller <- rules.spec(Point, assumedClosed).flatMap(rules.mp(_, inSmallerImage))

      // Fold the arbitrary-`S` statement back into `INDUCTIVE f x`.
      body <- rules.disch(closed, inSmaller).flatMap(rules.gen(Smaller, _))
      unfolded <- Conv.unfold(definition, List(Operator, Point))
      folded <- Conv.sym(unfolded).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, body)))

      clause <- rules.disch(atPoint, folded)
      everywhere <- rules.gen(Point, clause)
      discharged <- rules.disch(monotone, everywhere)
      result <- rules.gen(Operator, discharged)
    } yield result
  }

  /**
   * [[Fixpoint]], which is [[Introduction]] and the direction nobody has to state separately.
   *
   * `INDUCTIVE f x ==> f (INDUCTIVE f) x` is [[Induction]] at `S := f (INDUCTIVE f)`, and the
   * obligation that leaves — that `f (INDUCTIVE f)` is itself `f`-closed — is [[Introduction]]
   * carried under `f` by monotonicity. So the second direction costs one specialisation and one
   * application of the same hypothesis the first one spent, which is the reason to derive the
   * equation rather than to publish two implications.
   */
  private def fixedPoint(
    logic: Logic,
    theory: Theory,
    definition: Kernel.Thm,
    monotoneDefinition: Kernel.Thm,
    induction: Kernel.Thm,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      closure <- closureOf(theory, Operator)
      monotone <- monotoneOf(theory, Operator)
      image <- LogicError.lift(Term.app(Operator, closure))

      membership <- LogicError.lift(Term.app(closure, Point))
      atPoint <- LogicError.lift(Term.app(image, Point))

      assumedMonotone <- LogicError.lift(Kernel.assume(monotone))

      // `|- !x. f (INDUCTIVE f) x ==> INDUCTIVE f x`, under the monotonicity hypothesis.
      introductionAt <- rules.spec(Operator, introduction).flatMap(rules.mp(_, assumedMonotone))

      // The same inclusion carried under `f`, which is the obligation the induction leaves.
      monotoneAt <- Conv.unfold(monotoneDefinition, List(Operator))
      openedMonotone <- LogicError.lift(Kernel.eqMp(monotoneAt, assumedMonotone))
      monotoneInstance <- rules.specAll(openedMonotone, List(image, closure))
      imageIsClosed <- rules.mp(monotoneInstance, introductionAt)

      // Forward: the closure is inside its own image.
      inductionAt <- rules.specAll(induction, List(Operator, image))
      forwardEverywhere <- rules.mp(inductionAt, imageIsClosed)
      assumedMembership <- LogicError.lift(Kernel.assume(membership))
      forward <- rules.spec(Point, forwardEverywhere).flatMap(rules.mp(_, assumedMembership))

      // Backward: the image is inside the closure, which is the introduction rule at `x`.
      assumedAtPoint <- LogicError.lift(Kernel.assume(atPoint))
      backward <- rules.spec(Point, introductionAt).flatMap(rules.mp(_, assumedAtPoint))

      // `deductAntisym(l, r)` concludes `l.conclusion = r.conclusion`, so the membership goes on
      // the left: the published equation reads `INDUCTIVE f x = f (INDUCTIVE f) x` and not its
      // mirror. Each side's hypothesis is the other's conclusion, so both drop and `MONOTONE f`
      // is what is left.
      equation = Kernel.deductAntisym(backward, forward)
      everywhere <- rules.gen(Point, equation)
      discharged <- rules.disch(monotone, everywhere)
      result <- rules.gen(Operator, discharged)
    } yield result
  }
}
