package garden.xeno.symbolum.logic

import scala.annotation.tailrec
import garden.xeno.symbolum.kernel.*

/**
 * Rewriting: replacing a subterm with an equal one, and proving that the result is equal to what
 * went in.
 *
 * This is the piece the arithmetic was waiting for. Proving `2 + 3 = 5` needs associativity
 * applied at a chosen position inside a term, and until now the only way to place an equation
 * anywhere but the root was to build the congruence by hand with `mkComb` and `abs` at every
 * level.
 *
 * == The shape of the thing ==
 *
 * A conversion maps a term to a theorem `|- t = t'`. That is the whole interface, and it composes:
 * a conversion that works on subterms is built from one that works on a term, a conversion that
 * repeats is built from one that runs once. Everything below is one of those combinators, and the
 * theorem always comes from the kernel, so a mistake in this file produces a proof of the wrong
 * equation or no proof at all, never a false one.
 *
 * A conversion that has nothing to do returns `|- t = t` rather than failing. That makes the
 * combinators total and their composition trivial, at the cost of building a reflexivity theorem
 * that is then discarded; [[changed]] is how a caller tells the two apart.
 *
 * == Where the bound comes from ==
 *
 * [[repeatConv]] takes a step limit and beta normalisation did not, and the difference is real
 * rather than caution. Beta reduction of a well-typed term terminates by a theorem; rewriting with
 * an arbitrary rule set does not, and commutativity alone is enough to loop forever. Reaching the
 * limit returns the theorem built so far, which is true, rather than an error: a partial
 * normalisation is a correct equation.
 */
object Rewrite {

  /** A term to a proof that it equals something. */
  type Conversion = Term => Either[LogicError, Kernel.Thm]

  /** The default ceiling on rewriting steps. */
  val DefaultLimit: Int = 200

  /**
   * Nodes in a term, which is what "larger" means for the guard in [[Rule.of]].
   *
   * A count rather than a measure of anything else, because what it has to decide is whether one
   * application of a rule leaves more term behind than it consumed, and for a rule with nothing to
   * instantiate that is exactly the node count of the two sides. Type instantiation does not enter
   * it: `Matching.matchTerm` decides a rule's type variables as well as its term variables, and a
   * type substitution rewrites the types hanging off the nodes without adding or removing one.
   */
  def nodesOf(term: Term): Int = term match {
    case App(fn, argument) => 1 + nodesOf(fn) + nodesOf(argument)
    case Abs(_, body) => 1 + nodesOf(body)
    case _ => 1
  }

  /** Whether the first term occurs anywhere in the second, itself included. */
  def occursIn(part: Term, whole: Term): Boolean =
    part == whole || (whole match {
      case App(fn, argument) => occursIn(part, fn) || occursIn(part, argument)
      case Abs(_, body) => occursIn(part, body)
      case _ => false
    })

  /* --------------------------------------------------------------------- rules */

  /**
   * An equation ready to be used left to right, with the variables that may be filled in.
   *
   * The variables are the ones the theorem quantified over. A free variable of the original
   * theorem is not one of them: `|- x + 0 = x` with `x` free says something about that particular
   * `x`, and treating it as a pattern would be reading a quantifier that is not there.
   */
  final case class Rule(variables: Set[FVar], lhs: Term, rhs: Term, theorem: Kernel.Thm) {

    /**
     * Whether firing this rule puts its own left side back, so that repeating it never stops.
     *
     * Asked only of a rule with no variables, and that is what makes it decidable rather than a
     * guess: there is nothing to instantiate, so the two sides are the two terms and containment
     * settles it once, here. Where there are variables, whether an application reproduces the
     * pattern depends on what the matcher put in them, and no property of the rule answers it;
     * `!x. f x = f (f x)` is such a rule, it is accepted, it diverges, and the step limit is what
     * stops it.
     *
     * `lhs != rhs` is not an exception being carved out. `|- t = t` is reflexivity, `changed` is
     * false on it, no driver loops on it, and `Conv.refl` builds one at every node of every
     * congruence.
     *
     * Computed once, when the rule is built, and the conjunction is in this order because of it:
     * a rule with variables pays one `isEmpty` and never walks a term.
     */
    val reproduces: Boolean = variables.isEmpty && lhs != rhs && occursIn(lhs, rhs)
  }

  object Rule {

    /**
     * The rule a theorem gives, stripping the quantifiers in front of the equation.
     *
     * Two shapes of equation are **not** rules and are refused here rather than accepted and left
     * to diverge:
     *
     *  - a left side that is one of the rule's own variables. It matches every subterm there is,
     *    and if its right side mentions the same variable each match makes the term larger.
     *  - a right side carrying a variable the left side does not bind. Matching cannot determine
     *    what to put there, so what the rewriter builds is not an instance of the theorem.
     *
     * **Measured, on 2026-09-12.** `NUM_DIV_MOD` was first stated as `m = n * (m DIV n) + m MOD n`,
     * whose left side is a bare variable. `Novelty.follows` turns every equation in the library
     * into a rule, and the rewriter then grew a term by a factor on every step: a suite ran for an
     * hour and was killed rather than failing, and a thread dump was what found it. A step limit
     * does not help, because the size is exponential in the number of steps rather than in their
     * count. The lemma was restated the other way round, which is the direction that contracts, and
     * this guard is here so that the next one of the same shape is a refusal naming the shape.
     *
     * **Found a second time the same day, in another file and by another route**, which is why the
     * guard is here rather than in the caller that met it. `MAT2_SURJECTIVE` is
     * `|- !m. m = MAT2 (MAT_E11 m) (MAT_E12 m) (MAT_E21 m) (MAT_E22 m)`, the shape
     * `PAIR_SURJECTIVE` already had: `DocumentationSpec` stopped finishing, and a thread dump found
     * one thread inside `Sweep` that had spent 540 seconds of processor time in `Rewrite` on a
     * single claim. That session repaired it by filtering such rules out inside `Novelty`; the
     * filter was removed when the two landed together, because a refusal here reaches every caller
     * and a filter there reaches one.
     *
     * `PAIR_SURJECTIVE` had been in the library since 2026-09-11 and cost nothing, because it is
     * stated over type variables and the matcher did not instantiate those. The polymorphic repair
     * of 2026-09-12 removed that accident, so the monomorphic matrix statement made observable a
     * defect that was about to become reachable anyway.
     *
     * It is not a termination check and does not claim to be: `f x = f (f x)` is accepted and
     * diverges, and the step limit is what stops that. These two are the cases where the rule is
     * not a rule at all.
     */
    def of(logic: Logic, theorem: Kernel.Thm): Either[LogicError, Rule] =
      specialiseAll(logic, theorem).flatMap { case (variables, specialised) =>
        Term.destEq(specialised.conclusion) match {
          case None => Left(NotOfForm("an equation", specialised.conclusion))

          case Some((lhs, _)) if variables.exists(variable => lhs == (variable: Term)) =>
            Left(NotOfForm("an equation whose left side is more than one of its own variables", lhs))

          case Some((lhs, rhs))
              if (Term.freeVariables(rhs) -- Term.freeVariables(lhs))
                .intersect(variables.toSet)
                .nonEmpty =>
            Left(
              NotOfForm(
                "an equation whose right side mentions only what its left side binds",
                specialised.conclusion
              )
            )

          case Some((lhs, rhs)) => Right(Rule(variables.toSet, lhs, rhs, specialised))
        }
      }

    /**
     * The rules, refused as a set if one of them cannot be repeated to a fixed point.
     *
     * **This is asked where a rule set is iterated, and not in `Rule.of`, and the measurement is
     * what moved it.** A rule with no variables whose right side contains its left grows the term
     * every time it fires and puts the pattern back, so a driver that repeats never reaches a fixed
     * point: found on 2026-09-18, where `NUM_ADD ZERO ZERO = ZERO` read the other way round went to
     * `Rewrite.inTheorem` and the heap was gone in four and a half minutes. Two copies of the left
     * side in the right means each round doubles them, so the size is exponential in the number of
     * rounds and `Rewrite.DefaultLimit` is never reached: 2^200 arrives at the heap first, which is
     * the sentence `Rule.of` already carries for `NUM_DIV_MOD`.
     *
     * The card that asked for this asked `Rule.of` to refuse a closed rule whose right side is
     * strictly larger. Every rule the whole suite builds was counted on 2026-09-18 against
     * `b680520`, and the count refused the criterion: of 127 distinct closed rules whose right side
     * is the larger, **123 do not contain their left side** and are ordinary. Every definition
     * unfolded as a rule is one of them, `MAT_MUL` at 91 nodes against 1 being the largest;
     * `NUM_ONE = SUC ZERO`, which is what `Successor` opens every numeral with, is the smallest.
     *
     * **The four that do contain their left side are deliberate, and they are an idiom rather than
     * an accident.** All four are `0 = <something holding 0>`. `Arithmetic.timesZero` derives
     * `x * 0 = 0` by rewriting `x * 0` with `0 = 0 + 0`; `Order` and `Linarith` do the same with
     * `0 = 0 - x` and its relatives. Each hands the rule to a single `Rewrite.depthConv`:
     * one pass, one replacement, finished. So what decides is the driver and not the shape, and
     * `Rule.of` cannot see the driver. Refusing there would have meant rewriting four derivations
     * the arithmetic and the order rest on, to satisfy a guard with no way of knowing they were
     * safe.
     *
     * What this does not cover, and both are the price of deciding it on one rule at a time. A set
     * can put back between its rules what no one of them puts back alone, and nothing here sees
     * that. And a reproducing rule handed to a term its left side does not occur in would have
     * terminated; that call is refused too, because what is asked about is the shape, exactly as in
     * the two guards `Rule.of` carries. Neither is the general question, which is that the step
     * limit bounds steps and not size, so this rewriter can still die where it should stop.
     */
    def iterable(rules: Vector[Rule]): Either[LogicError, Vector[Rule]] =
      rules.find(_.reproduces) match {
        case None => Right(rules)
        case Some(rule) =>
          Left(
            NotOfForm(
              "a rule set no rule of which puts its own left side back",
              rule.theorem.conclusion
            )
          )
      }

    /** Every rule of a theory, in order, refusing the first theorem that is not an equation. */
    def all(logic: Logic, theorems: Vector[Kernel.Thm]): Either[LogicError, Vector[Rule]] =
      theorems.foldLeft(Right(Vector.empty): Either[LogicError, Vector[Rule]]) { (acc, theorem) =>
        for {
          rules <- acc
          rule <- of(logic, theorem)
        } yield rules :+ rule
      }
  }

  /**
   * Strip every leading universal quantifier, specialising each to a fresh variable.
   *
   * The variables come back in the order they were bound, so a caller that wants to put the
   * quantifiers back can do it in the order the statement had them.
   *
   * The variables have to be fresh with respect to the whole theorem, not only its conclusion: one
   * that collided with a variable of a hypothesis would silently narrow the rule to the case where
   * the two are equal.
   */
  def specialiseAll(
    logic: Logic,
    theorem: Kernel.Thm
  ): Either[LogicError, (Vector[FVar], Kernel.Thm)] = {
    def go(
      current: Kernel.Thm,
      variables: Vector[FVar]
    ): Either[LogicError, (Vector[FVar], Kernel.Thm)] =
      logic.destForallPredicate(current.conclusion) match {
        case None => Right((variables, current))

        case Some(predicate) =>
          Type.destFun(Term.typeOf(predicate)) match {
            case None => Right((variables, current))

            case Some((domain, _)) =>
              val used =
                current.hypotheses.foldLeft(Term.freeVariables(current.conclusion))(_ ++ Term.freeVariables(_))
              val variable = Conv.freshVariable("a", domain, used ++ variables.toSet)

              logic.rules.spec(variable, current).flatMap(next => go(next, variables :+ variable))
          }
      }

    go(theorem, Vector.empty)
  }

  /* -------------------------------------------------------------- combinators */

  /** `|- t = t`, whatever the term. */
  val allConv: Conversion = term => Right(Conv.refl(term))

  /**
   * Whether a conversion did anything.
   *
   * The reference test first, and it is not a micro-optimisation: a conversion that did nothing
   * returns the **same object** on both sides, and the structural comparison behind it walks the
   * whole term. On a term of three thousand nodes that walk is the answer to a question already
   * settled by a pointer comparison, once per node per rule.
   */
  def changed(theorem: Kernel.Thm): Boolean =
    Term.destEq(theorem.conclusion).exists { case (lhs, rhs) => !(lhs eq rhs) && lhs != rhs }

  /**
   * Whether a step is the identity, cheaply and conservatively.
   *
   * The same object on both sides and nothing on the left of the turnstile, which is what every
   * conversion here produces when it has nothing to do. A step that satisfies this can be **left
   * out** of a congruence or a chain rather than built into it, because the theorem the caller
   * would have got is the theorem it gets: `trans(|- t = t, G |- t = u)` is `G |- t = u`, and
   * `mkComb(|- f = f, |- a = a)` is `refl (f a)`.
   *
   * Two guards and both matter. Reference equality rather than structural, because the structural
   * walk is the cost being avoided and a false negative here only means the slow path is taken.
   * And an empty hypothesis list, because a step that changed nothing may still **rest** on
   * something, and dropping that would make the finished theorem claim to rest on less than it
   * does. No conversion here produces such a step today; the guard is what keeps the reasoning
   * local to this line if one ever does.
   */
  def idle(theorem: Kernel.Thm): Boolean =
    theorem.hypotheses.isEmpty && (Term.destEq(theorem.conclusion) match {
      case Some((lhs, rhs)) => lhs eq rhs
      case None => false
    })

  /**
   * Whether the conversion has nothing left to do here.
   *
   * One more application, and the answer is whether it changed anything. This is the only way a
   * caller can tell a normal form from a term the rewriter merely stopped at: [[repeatConv]]
   * returns the theorem it had built when the step limit ran out, that theorem is true, and nothing
   * in it says whether the rewriting had finished.
   *
   * It costs a full run of the conversion, which is why it is asked only where the answer changes
   * something: after a proof has already failed, where it decides whether the failure is about the
   * identity or about the budget.
   */
  def atFixedPoint(conversion: Conversion, term: Term): Either[LogicError, Boolean] =
    conversion(term).map(step => !changed(step))

  /**
   * Contract a redex at the root, if there is one.
   *
   * Unfolding a definition puts a lambda where a constant was, and the application it now heads is
   * a redex. Without this in the same pass, rewriting would stop with the definition half applied.
   */
  val betaConv: Conversion = Conv.betaRoot

  /**
   * Rewrite at the root of the term, once, with one rule.
   *
   * The match decides the rule's type variables as well as its term variables since 2026-09-12, so
   * a rule stated over `'a` rewrites a term at `num`. `Matching.Instantiation.instance` is what
   * performs both, and it performs no type instantiation at all when there was nothing to decide,
   * which is every rule in the arithmetic.
   */
  def rewriteConv(rule: Rule): Conversion = term =>
    Matching.matchTerm(rule.variables, rule.lhs, term) match {
      case None => Right(Conv.refl(term))
      case Some(found) => LogicError.lift(found.instance(rule.theorem))
    }

  /**
   * Rewrite at the root, but only when the result is smaller in the given order.
   *
   * This is how a rule that holds in both directions becomes usable. `x + y = y + x` applies to
   * every sum and to its own result, so rewriting with it never stops; allowed only when it makes
   * the term smaller, it sorts instead, and stops when the sum is in order.
   *
   * Termination, since a total order alone does not give it: every rule used this way here keeps
   * the size of the term the same, and among terms of one size the order is a well-order because
   * there are finitely many. A rule that grew the term would need a different argument, and should
   * not be used with this.
   */
  def orderedRewriteConv(rule: Rule, order: Ordering[Term]): Conversion = term =>
    Matching.matchTerm(rule.variables, rule.lhs, term) match {
      case None => Right(Conv.refl(term))
      case Some(found) =>
        LogicError.lift(found.instance(rule.theorem)).map { instance =>
          Term.destEq(instance.conclusion) match {
            case Some((_, rhs)) if order.lt(rhs, term) => instance
            case _ => Conv.refl(term)
          }
        }
    }

  /** The first of these conversions that changes the term. */
  def firstConv(conversions: Vector[Conversion]): Conversion = term => {
    @tailrec
    def go(remaining: Vector[Conversion]): Either[LogicError, Kernel.Thm] =
      remaining.headOption match {
        case None => Right(Conv.refl(term))
        case Some(conversion) =>
          conversion(term) match {
            case Left(error) => Left(error)
            case Right(theorem) if changed(theorem) => Right(theorem)
            case Right(_) => go(remaining.tail)
          }
      }

    go(conversions)
  }

  /** One conversion, then the other on what the first produced. */
  def thenConv(first: Conversion, second: Conversion): Conversion = term =>
    for {
      firstStep <- first(term)
      middle <- rightOf(firstStep)
      secondStep <- second(middle)
      result <- chain(firstStep, secondStep)
    } yield result

  /**
   * Two steps in sequence, without building a chain for a step that did nothing.
   *
   * `trans` is a primitive inference and it compares the two middles; doing it against an identity
   * costs that comparison and one node of the proof to reach a theorem one of the two arguments
   * already is. On the corpus measured on 2026-09-11, transitivity was 19.1% of every inference and
   * nearly all of it was this.
   */
  private def chain(first: Kernel.Thm, second: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    if (idle(first)) Right(second)
    else if (idle(second)) Right(first)
    else Conv.trans(first, second)

  /**
   * Apply a conversion to the immediate subterms and rebuild the theorem by congruence.
   *
   * Going under a binder opens it with a fresh variable and closes it again, so what comes back
   * is an equation about the original term rather than about a copy of it.
   */
  def subConv(conversion: Conversion): Conversion = {
    case application @ App(fn, argument) =>
      for {
        fnStep <- conversion(fn)
        argumentStep <- conversion(argument)
        result <-
          // Both halves unchanged means the whole is unchanged, and saying so directly is the
          // theorem the congruence would have built: `mkComb(|- f = f, |- a = a)` concludes
          // `f a = f a`. Below a node where nothing fires, which is most of a large term, this is
          // the difference between a proof of the size of the term and a proof of the size of the
          // work.
          if (idle(fnStep) && idle(argumentStep)) Right(Conv.refl(application))
          else LogicError.lift(Kernel.mkComb(fnStep, argumentStep))
      } yield result

    case abstraction @ Abs(binderType, _) =>
      // Twice, when the first attempt has to be abandoned. The variable that opens the binder is
      // fresh for the term, which is all that is known before the conversion runs; the conversion
      // may then return a theorem whose hypotheses mention it, and abstracting over a variable
      // free in a hypothesis is what the kernel refuses. The second attempt knows those
      // hypotheses and avoids them, and there is no third case: the retry picks a name free in
      // nothing the theorem mentions.
      underBinder(conversion, abstraction, binderType, Term.freeVariables(abstraction)).flatMap {
        case Right(theorem) => Right(theorem)
        case Left(avoid) => underBinder(conversion, abstraction, binderType, avoid).flatMap {
          case Right(theorem) => Right(theorem)
          case Left(_) => Left(NotOfForm("a binder that can be reopened", abstraction))
        }
      }

    case other => Right(Conv.refl(other))
  }

  /**
   * One attempt at converting under a binder.
   *
   * Returns the theorem, or the set of variables a second attempt has to avoid, which is what the
   * caller could not know before running the conversion.
   */
  private def underBinder(
    conversion: Conversion,
    abstraction: Term,
    binderType: Type,
    avoid: Set[FVar]
  ): Either[LogicError, Either[Set[FVar], Kernel.Thm]] = {
    val variable = Conv.freshVariable("v", binderType, avoid)

    for {
      redex <- LogicError.lift(Term.app(abstraction, variable))
      opened <- Term.betaReduce(redex).toRight(NotOfForm("a redex", redex))
      inner <- conversion(opened)
      outcome <-
        // Re-abstracting a body nothing touched gives back the abstraction it was opened from, so
        // the identity on it is the theorem, and the kernel is not asked to rebuild what it was
        // handed.
        if (idle(inner)) Right(Right(Conv.refl(abstraction)))
        else
          Kernel.abs(variable, inner) match {
            case Right(theorem) => Right(Right(theorem))
            case Left(_) => Right(Left(avoid ++ Rules.freeIn(inner)))
          }
    } yield outcome
  }

  /** Apply a conversion everywhere it fits, subterms before the term that contains them. */
  def depthConv(conversion: Conversion): Conversion = term =>
    for {
      below <- subConv(depthConv(conversion))(term)
      rewritten <- rightOf(below)
      here <- conversion(rewritten)
      result <- chain(below, here)
    } yield result

  /** Repeat a conversion until it stops changing the term, or until the limit is reached. */
  def repeatConv(conversion: Conversion, limit: Int = DefaultLimit): Conversion = term => {
    def go(accumulated: Kernel.Thm, remaining: Int): Either[LogicError, Kernel.Thm] =
      if (remaining <= 0) Right(accumulated)
      else
        rightOf(accumulated).flatMap { current =>
          conversion(current).flatMap { step =>
            if (!changed(step)) Right(accumulated)
            else chain(accumulated, step).flatMap(go(_, remaining - 1))
          }
        }

    go(Conv.refl(term), limit)
  }

  /* ------------------------------------------------------------------- driving */

  /** Rewrite everywhere, repeatedly, with a set of rules. */
  /**
   * The normalisation strategy an arithmetic uses, assembled once.
   *
   * Two kinds of rule and they are applied differently. The unconditional ones fire wherever their
   * left side occurs; the ordered ones fire only where they make the term smaller in `order`,
   * because commutativity applies to its own output and would otherwise never stop. Repeated to a
   * fixed point, depth first, with beta at the end.
   *
   * **One function rather than one per arithmetic.** `Arithmetic.normalisationFrom` built these six
   * lines for the reals and `Semiring` needs the same six for `num`, and the two would agree on the
   * day they were written: that is the state in which a duplicate is hardest to notice, which is
   * what `Induct.afterRewriting`'s own docstring records about the last time it happened here. What
   * differs between the two arithmetics is the rules and the order, which are the parameters.
   *
   * It takes rules rather than a theory, so it knows nothing about which arithmetic it is
   * normalising, which is why it can live in this module at all.
   */
  def normaliser(
    unconditional: Vector[Rule],
    ordered: Vector[Rule],
    order: Ordering[Term],
    limit: Int = DefaultLimit
  ): Conversion = {
    // Only the unconditional half is asked, and that is a statement about `orderedRewriteConv`
    // rather than an omission: it fires only where the result is smaller in `order`, and a rule
    // that puts its own left side back is strictly larger every time, so it can never fire there.
    Rule.iterable(unconditional) match {
      case Left(error) => (_: Term) => Left(error)
      case Right(_) => repeatConv(passOver(unconditional, ordered, order), limit)
    }
  }

  /**
   * One pass of an arithmetic's rules over the whole term, without repeating.
   *
   * Published because it was being written out again. [[normaliser]] built these lines inside
   * itself and `Peano.normalisation` needs the same pass **and** the repetition of it, so it had
   * re-derived them: that is the third copy of the six lines whose docstring above says why there
   * is one function rather than one per arithmetic, and it was invisible because nothing compared
   * them.
   *
   * It is not [[stepConv]], and the difference is not cosmetic: that one drives every rule with
   * [[rewriteConv]], so a sorting rule given to it fires wherever it matches instead of only where
   * it makes the term smaller.
   */
  def passOver(
    unconditional: Vector[Rule],
    ordered: Vector[Rule],
    order: Ordering[Term]
  ): Conversion =
    depthConv(
      firstConv(
        unconditional.map(rewriteConv) ++
          ordered.map(rule => orderedRewriteConv(rule, order)) :+ betaConv
      )
    )

  def rewrite(
    rules: Vector[Rule],
    term: Term,
    limit: Int = DefaultLimit
  ): Either[LogicError, Kernel.Thm] =
    Rule.iterable(rules).flatMap(iterable => repeatConv(stepConv(iterable), limit)(term))

  /**
   * One pass of the rules over the whole term, without repeating.
   *
   * Named because [[atFixedPoint]] has to be asked with **this** and not with the repeated form,
   * and the difference is a defect rather than a nicety. A conversion that repeats to a limit
   * applied to a term where two rules undo each other comes back where it started whenever the
   * limit is even, so `changed` is false and the term is declared finished when the rewriting had
   * not finished at all. `DefaultLimit` is 200, which is even; the test that pinned this behaviour
   * chose 7 and passed for that reason alone, until 2026-09-10.
   */
  def stepConv(rules: Vector[Rule]): Conversion =
    depthConv(firstConv(rules.map(rewriteConv) :+ betaConv))

  /**
   * Whether these rules have nothing left to do to this term.
   *
   * The question a caller has to ask before reading a later failure as a statement about the
   * mathematics. [[rewrite]] hands back the theorem it had built when the step limit ran out, and
   * that theorem is true: nothing in it says whether the rewriting had finished, so a rule set that
   * does not settle looks exactly like an identity that is false.
   *
   * Named here because it has been written out twice by hand at two call sites, and a defect closed
   * in one place comes back in the next place that does the same thing: this shape reappeared in
   * `Induct.settle` on the day it was closed in `Rewrite.prove`, and again in `Family` on the day
   * the call sites were reviewed. Ask it after the failure, never before: it costs a pass of the
   * conversion, and on the path where the proof succeeded the answer changes nothing.
   *
   * **Every caller of [[rewrite]] is listed in `RewriteSpec`, with what it does about this**, and a
   * call site that is not on that list fails the suite. A review somebody did once is a review that
   * covers the code as it was that day; three occurrences of one defect in two days is the evidence
   * that this one needs a scan rather than a memory.
   */
  def finished(rules: Vector[Rule], term: Term): Either[LogicError, Boolean] =
    atFixedPoint(stepConv(rules), term)

  /**
   * Rewrite inside a theorem rather than inside a term.
   *
   * A conversion proves `t = t'`; this carries a theorem across that equation, so a theorem about
   * `x + -x < y + -x` becomes one about `0 < y - x` without anyone restating it.
   */
  def inTheorem(rules: Vector[Rule], theorem: Kernel.Thm, limit: Int = DefaultLimit): Either[LogicError, Kernel.Thm] =
    for {
      equation <- rewrite(rules, theorem.conclusion, limit)
      result <- LogicError.lift(Kernel.eqMp(equation, theorem))
    } yield result

  /**
   * Prove `left = right` by rewriting both sides to the same term.
   *
   * The two normal forms have to be equal on the nose. That is what makes this a proof rather than
   * a search: if the rules do not bring the two sides together, this says so instead of trying
   * something else.
   */
  def prove(
    rules: Vector[Rule],
    left: Term,
    right: Term,
    limit: Int = DefaultLimit
  ): Either[LogicError, Kernel.Thm] =
    proveWith(term => rewrite(rules, term, limit), left, right, Some(stepConv(rules)))

  /**
   * Prove `left = right` by putting both through the same conversion.
   *
   * `step` is one pass of the same rules, when the caller has it, and is what the finished-or-not
   * question is asked with; see [[stepConv]] for why asking the repeated conversion gives a wrong
   * answer. A caller that has only the repeated form passes nothing and gets the weaker reading,
   * which is the honest thing rather than a wrong one: it can then report a difference it is not
   * sure about, and it does.
   */
  def proveWith(
    normalise: Conversion,
    left: Term,
    right: Term,
    step: Option[Conversion] = None
  ): Either[LogicError, Kernel.Thm] =
    for {
      leftNormal <- normalise(left)
      rightNormal <- normalise(right)
      leftForm <- rightOf(leftNormal)
      rightForm <- rightOf(rightNormal)
      _ <-
        if (leftForm == rightForm) Right(())
        else unmet(step.getOrElse(normalise), leftForm, rightForm)
      reversed <- Conv.sym(rightNormal)
      result <- Conv.trans(leftNormal, reversed)
    } yield result

  /**
   * Why the two sides did not meet, which is two different findings wearing one shape.
   *
   * If either side still changes under the conversion, the rewriting had not finished and the
   * comparison was between one normal form and one waypoint: that says nothing about the identity,
   * and [[NotNormalised]] says so. Only when both sides are finished is a difference between them
   * a statement about the identity, and then the answer is the one this always gave.
   */
  private def unmet(
    normalise: Conversion,
    leftForm: Term,
    rightForm: Term
  ): Either[LogicError, Unit] =
    for {
      leftDone <- atFixedPoint(normalise, leftForm)
      rightDone <- atFixedPoint(normalise, rightForm)
      outcome <-
        if (!leftDone) Left(NotNormalised(leftForm))
        else if (!rightDone) Left(NotNormalised(rightForm))
        else Left(NotEqualTo(rightForm, leftForm))
    } yield outcome

  /**
   * `|- !x. l = r`, by normalising both sides of the body and comparing them.
   *
   * The quantifiers come off, the body is proved about fresh variables, and they go back on in the
   * order they were written. Working on the body is what lets the normalisation see the structure:
   * a quantified statement is an application of a constant to a lambda, and there is nothing in it
   * to distribute.
   *
   * Here rather than in each tactic because it is the same four steps whichever normal form is
   * passed in, and there were two copies of them: one that put back the quantifiers it had
   * stripped, and one that closed over every free variable instead. The second is a different
   * theorem from the same goal, so it stays where it is needed and is written there as the extra
   * step it is, rather than as a second version of this.
   */
  def proveEquation(
    logic: Logic,
    normalise: Conversion,
    goal: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Logic.stripForall(goal)
      sides <- Term.destEq(stripped._2).toRight(NotOfForm("an equation", stripped._2))
      proved <- proveWith(normalise, sides._1, sides._2)
      general <- logic.rules.genAll(proved, stripped._1.toList)
    } yield general

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
