package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * One-way matching of a pattern against a term.
 *
 * A rewrite rule is a theorem `|- !x y. lhs = rhs`, and using it means finding what `x` and `y`
 * have to be for `lhs` to become the subterm in hand. That is matching, not unification: the
 * subterm is fixed and only the pattern has variables to fill. Unifying instead would let a rule
 * rewrite a term into one that mentions the rule's own variables, which is not what anybody means
 * by applying a rule.
 *
 * == First order, and then the one step past it that is decidable ==
 *
 * A pattern variable used on its own stands for a term, and that is the whole of what this did
 * until 2026-09-11. `f x` matched `g y` by binding `f` to `g` and `x` to `y`, and did not match
 * `sin y` by taking `f` to be a function the pattern does not mention.
 *
 * The cost of stopping there was not in the arithmetic, where the old note said correctly that
 * nothing needed more. It was in the sixteen axioms: **completeness is the only one that quantifies
 * over a predicate, and it is the only one that separates the reals from the rationals.** To use it
 * an automation has to decide what its `P` is, `P` occurs in it applied to a bound variable, and no
 * mechanism here could answer that. The corpus report said "completeness never reached" over 46
 * goals and read as a fact about the corpus; it was a fact about the matcher.
 *
 * So there is one more case, and it is the decidable fragment rather than higher-order matching in
 * general: a **Miller pattern**, a pattern variable applied to distinct bound variables and nothing
 * else. `P x` against `x * x < 2`, under a binder for `x`, has the single answer
 * `P := \x. x * x < 2`. Isabelle and Lean run most of their work on this fragment for the same
 * reason: unique most general answers, and a decision rather than a search. Full higher-order
 * unification is undecidable and is not here.
 *
 * **The first-order answer wins wherever there is one.** `\x. F x` against `\x. sin x` still gives
 * `F := sin` and not `F := \x. sin x`, which are eta-equal and are not the same term. Every caller
 * written before this was written against the first, and the fragment is an addition rather than a
 * replacement: the higher-order construction is tried only where the first-order walk fails.
 *
 * == Types are solved for too, and it is the same one-way question ==
 *
 * Until 2026-09-12 a pattern's types had to be the target's **already**. Everything in the library
 * was over `real` or `num`, so nothing noticed; `Product` and `Word` then landed fourteen lemmas
 * over `'a` and three mechanisms broke at once. `Const("FST", prod('a,'b) -> 'a)` and
 * `Const("FST", prod(num,num) -> num)` are different terms, so a match failed on the constant
 * before it reached the arguments, and `!x:num. !y:num. FST (PAIR x y) = x` was refused by a system
 * holding the lemma that IS it.
 *
 * So a match now answers with a type substitution beside the term one, the way HOL Light's
 * `term_match` does. Three things keep it the same question rather than a larger one:
 *
 *  - **Only the pattern's type variables may be solved.** `Type.matchType` is one-way in exactly
 *    this sense and is reused rather than reimplemented; an answer naming a type variable the
 *    pattern does not have would be an answer about the target, and is refused.
 *  - **It accumulates.** A pattern using `'a` twice cannot solve it two ways: each comparison runs
 *    against the pattern's type with what is known already substituted into it, and what comes back
 *    is composed into what is known.
 *  - **An empty answer changes nothing.** A pattern whose types are ground takes the path it took
 *    before, and [[Instantiation.instance]] then performs no type instantiation at all, so no
 *    derivation grows a step it did not have.
 *
 * == Binders are opened, and that is what makes the fragment expressible here ==
 *
 * Matching used to descend into two binders together and compare indices by position. It now opens
 * both with one fresh variable and compares named terms. The reason is the kernel's boundary rather
 * than taste: building the answer `\x. x * x < 2` means **abstracting** a bound variable out of a
 * term, `Abs` is `private[kernel]`, and the only public way to build one is `Term.abs`, which
 * closes over a free variable. A term with a loose index in it cannot be handed to it at all. With
 * the binders opened there are no loose indices anywhere and the answer is built by the one public
 * constructor that exists for it.
 *
 * One fresh variable became one fresh **name** when types arrived: a binder over `'a` in the
 * pattern faces a binder over `num` in the target, and what opens each has to be at that side's own
 * type. The two are the same name at two types and are compared the way every other fixed subterm
 * is, by name and a type match.
 *
 * The escape check moved with them. A pattern variable found under a binder may not bind to a term
 * mentioning that binder's variable, which used to be a check for a loose index and is now a check
 * on a name. Same condition, and it is the reason `\x. F` does not match `\x. x`. It is asked of
 * the **target's** binder variable, because what is being checked is a piece of the target.
 */
object Matching {

  /**
   * Which condition of the decidable fragment a pair met and failed, as a value rather than a
   * sentence, so that a caller counting them does not parse prose.
   *
   * Four, and they are not the same kind of limit. [[Matching.Refusal.NoBinderInScope]] is not a
   * higher-order question at all: with nothing bound, a pattern variable applied to anything is a
   * first-order problem the walk already answers where it can, and a refusal there says only that
   * these two terms do not match. The other three are the fragment's own boundary, which is what
   * [[isTheFragmentsBoundary]] answers, and `docs/adr/0030` carries how often each is reached.
   *
   * Each carries the pattern variable it met, because that is what a caller is told to supply: a
   * refusal saying the fragment was left and not saying where would leave the caller to find the
   * variable by reading the lemma.
   */
  enum Refusal {

    /** The pattern variable at the head of the application where the condition failed. */
    def variable: FVar

    /** A pattern variable applied to something, with no binder open: first order, not this limit. */
    case NoBinderInScope(variable: FVar)

    /** A pattern variable applied to a term that is not one of the binders in scope. */
    case ArgumentIsNotABinder(variable: FVar)

    /** A pattern variable applied to the same binder twice, which has more than one answer. */
    case BinderAppliedTwice(variable: FVar)

    /** The target uses a binder the pattern variable was not applied to, so no answer of this shape. */
    case TargetSeesAnotherBinder(variable: FVar)

    /**
     * Whether this is the fragment turning a question down, rather than a first-order miss.
     *
     * A match rather than a comparison with the one case that answers `false`, so that a fifth
     * condition does not compile until somebody says which it is.
     */
    def isTheFragmentsBoundary: Boolean = this match {
      case NoBinderInScope(_)         => false
      case ArgumentIsNotABinder(_)    => true
      case BinderAppliedTwice(_)      => true
      case TargetSeesAnotherBinder(_) => true
    }

    /** What the variable was applied to, as the clause a refusal message ends with. */
    def condition: String = this match {
      case NoBinderInScope(_)         => "applied with no binder in scope"
      case ArgumentIsNotABinder(_)    => "applied to a term that is not a bound variable"
      case BinderAppliedTwice(_)      => "applied to the same bound variable twice"
      case TargetSeesAnotherBinder(_) => "not applied to a bound variable the target uses"
    }
  }


  /**
   * What a match decided: the terms the pattern's variables stand for, and the types its type
   * variables stand for.
   *
   * One record rather than a pair returned from each caller, because the two halves are used
   * together everywhere they are used at all: a theorem whose pattern matched is instantiated at
   * both, and [[instance]] is that step written once, where the argument for it can be read.
   */
  final case class Instantiation(terms: Map[FVar, Term], types: Map[String, Type]) {

    /**
     * The theorem the pattern came from, at the instance this match found.
     *
     * **Why instantiating the types here is sound.** `Kernel.instType` is a primitive rule and
     * holds for any substitution, so the question worth asking is where the types being substituted
     * in came from. They come from [[types]], whose range is read off the target and nothing else:
     * every one of them occurs in the term that was matched against. A target reaches this having
     * been built by the kernel's checking constructors, and one that entered as text was checked by
     * `Theory.checkType` as it was read. So no type operator nobody declared can enter a theorem by
     * this route. Whether `instType` should itself refuse an undeclared operator is a separate
     * question about the kernel, open as its own card, and nothing here depends on the answer.
     *
     * The term substitution's keys are the pattern's variables and carry the pattern's types, so
     * they move to the instance with the theorem. Instantiating without moving them gave a
     * substitution that matched nothing and a theorem unchanged, which is a wrong answer rather
     * than a refusal.
     */
    def instance(theorem: Kernel.Thm): Either[KernelError, Kernel.Thm] =
      if (types.isEmpty) Kernel.inst(terms, theorem)
      else
        Kernel.inst(
          terms.map { case (variable, value) => at(variable) -> value },
          Kernel.instType(types, theorem)
        )

    /** A variable of the pattern, at the types this match decided. */
    def at(variable: FVar): FVar =
      if (types.isEmpty) variable
      else Term.variable(variable.name, Type.substitute(types, variable.ty))

    /**
     * Whether the answer still says one thing per variable once the types have moved.
     *
     * A free variable is a name **and** a type, so a pattern can hold `x:'a` and `x:'b` as two
     * different variables, and a match can decide both are `num`. They are then one variable, which
     * `Kernel.instType` says of itself and is sound: the theorem held for every value of each. What
     * is not sound is the **answer**: two bindings would arrive at one key and one of them would be
     * dropped by whichever order the map iterates, so [[instance]] would return a theorem that is a
     * true instance of the lemma and not the one the match claimed to find.
     *
     * So a collision is a refusal unless the two bindings agree, which is a match that has decided
     * one thing twice and is expressible. Found by reading the map-building in [[instance]] rather
     * than by a failure; nothing in the library presents the shape today, and the guard costs a
     * grouping over a map that is empty at almost every call.
     */
    def expressible: Boolean =
      types.isEmpty ||
        terms
          .groupBy { case (variable, _) => at(variable) }
          .forall { case (_, colliding) => colliding.values.toSet.size == 1 }
  }

  object Instantiation {

    /** What a match that has decided nothing knows. */
    val empty: Instantiation = Instantiation(Map.empty, Map.empty)
  }

  /**
   * The substitution that turns `pattern` into `target`, if there is one.
   *
   * A pattern variable binds only to a term that makes sense outside the binders it was found
   * under. Matching `\x. F` against `\x. x` would otherwise bind `F` to a variable bound by a
   * lambda the substitution is about to leave, and the result would be a term with an index
   * pointing at nothing.
   *
   * **One walk, and the binders are opened even where nothing needs them opened.** A version that
   * kept the old index walk for patterns that cannot present a Miller problem was written and
   * removed: the theories module runs in 4.23 seconds with it and 4.31 without, which is noise, and
   * a second traversal kept for a saving that does not exist is a second thing to keep correct.
   */
  def matchTerm(
    variables: Set[FVar],
    pattern: Term,
    target: Term
  ): Option[Instantiation] = {

    // Chosen once, against every name that occurs in either side, so that the variable standing for
    // a binder cannot be one the terms already mention. A fixed prefix would be enough for anything
    // the parser can read, since `%` starts no name it accepts, and a term does not have to have
    // come from the parser.
    //
    // Lazy, so that a call reaching here and finding no binder to open pays nothing for it.
    lazy val prefix = {
      val taken = names(pattern) ++ names(target) ++ variables.map(_.name)
      Iterator.iterate("%")(_ + "%").find(candidate => !taken.exists(_.startsWith(candidate))).get
    }

    // What may be solved for, read off the pattern once. A solution naming anything else would be a
    // statement about the target's types, which is the direction this does not go.
    val solvable = Term.typeVariables(pattern)

    /**
     * What is known about the types, extended so that the pattern's type becomes the target's.
     *
     * Composed rather than merged: a pattern mentioning `'a` and `'b` can learn `'a := 'b` at one
     * subterm and `'b := num` at the next, and a caller that substitutes once has to get `num` for
     * both. The composition is what makes one pass enough.
     *
     * **A variable solved to itself is dropped.** Matching a polymorphic pattern against an equally
     * polymorphic target answers `'a := 'a`, which changes nothing and is not nothing: a non-empty
     * substitution sends [[Instantiation.instance]] through `Kernel.instType`, and every derivation
     * that rewrote with such a rule would grow a step that does no work. What is dropped here is
     * exactly what `Type.substitute` would have left alone.
     */
    def solving(
      known: Map[String, Type],
      patternType: Type,
      targetType: Type
    ): Option[Map[String, Type]] =
      Type.matchType(Type.substitute(known, patternType), targetType).flatMap { solved =>
        if (!solved.keySet.subsetOf(solvable)) None
        else
          Some(
            (known.map { case (name, ty) => name -> Type.substitute(solved, ty) } ++ solved)
              .filterNot { case (name, ty) => ty == TyVar(name) }
          )
      }

    def go(
      pattern: Term,
      target: Term,
      binders: List[(FVar, FVar)],
      acc: Instantiation
    ): Option[Instantiation] = {

      def bind(variable: FVar, value: Term): Option[Instantiation] =
        if (binders.exists { case (_, inTarget) => Term.occursFree(inTarget, value) }) None
        else
          solving(acc.types, variable.ty, Term.typeOf(value)).flatMap { types =>
            acc.terms.get(variable) match {
              case Some(bound) => if (bound == value) Some(acc.copy(types = types)) else None
              case None => Some(Instantiation(acc.terms.updated(variable, value), types))
            }
          }

      /** A subterm the pattern fixes: the same name, at a type the pattern's matches. */
      def fixed(
        name: String,
        ty: Type,
        targetName: String,
        targetType: Type
      ): Option[Instantiation] =
        if (name != targetName) None
        else solving(acc.types, ty, targetType).map(types => acc.copy(types = types))

      pattern match {
        case variable: FVar if variables.contains(variable) => bind(variable, target)

        case App(fn, argument) =>
          val firstOrder = target match {
            case App(targetFn, targetArgument) =>
              go(fn, targetFn, binders, acc).flatMap(go(argument, targetArgument, binders, _))
            case _ => None
          }

          firstOrder.orElse(miller(pattern, target, binders, acc, bind))

        case Abs(binderType, _) =>
          target match {
            case Abs(targetBinderType, _) =>
              solving(acc.types, binderType, targetBinderType).flatMap { types =>
                val name = s"$prefix${binders.length}"
                val inPattern = Term.variable(name, binderType)
                val inTarget = Term.variable(name, targetBinderType)

                for {
                  patternBody <- open(pattern, inPattern)
                  targetBody <- open(target, inTarget)
                  result <- go(
                    patternBody,
                    targetBody,
                    (inPattern, inTarget) :: binders,
                    acc.copy(types = types)
                  )
                } yield result
              }

            case _ => None
          }

        case Const(name, ty) =>
          target match {
            case Const(targetName, targetType) => fixed(name, ty, targetName, targetType)
            case _ => None
          }

        // A variable that is not a pattern variable, or one of the two that opened a binder.
        // Compared by name and a type match for the same reason a constant is: the two sides of an
        // opened binder are one name at two types until the types have been decided.
        case variable: FVar =>
          target match {
            case FVar(targetName, targetType) =>
              fixed(variable.name, variable.ty, targetName, targetType)
            case _ => None
          }

        case other => if (other == target) Some(acc) else None
      }
    }

    /**
     * The Miller case: a pattern variable applied to distinct binders, and nothing else.
     *
     * Every condition below is what makes the answer unique rather than one of many. Applied to
     * something that is not a binder variable, or to the same one twice, the problem has several
     * answers and this returns none of them, which is a refusal and not a wrong answer: the matcher
     * is outside the trusted base and what a miss costs is a tactic that does not fire.
     *
     * The arguments are read off the **pattern** and the abstraction is built over the **target**,
     * so each applied binder variable is carried across to its counterpart: the two are one name at
     * two types wherever the binder's own type is still being solved for.
     */
    def miller(
      pattern: Term,
      target: Term,
      binders: List[(FVar, FVar)],
      acc: Instantiation,
      bind: (FVar, Term) => Option[Instantiation]
    ): Option[Instantiation] = {
      val (head, arguments) = spine(pattern)

      head match {
        case variable: FVar if variables.contains(variable) =>
          val applied = arguments.flatMap {
            case argument: FVar => binders.find(_._1 == argument).map(_._2).toList
            case _ => Nil
          }

          if (applied.length != arguments.length || applied.distinct.length != applied.length) None
          else {
            // What the answer may not mention: a binder the variable was not applied to. `P x`
            // cannot become a `P` that is also allowed to see `y`, so a target using `y` has no
            // answer of this shape rather than a wrong one.
            val visible = applied.toSet
            val escaping = binders.map(_._2).filterNot(visible.contains)

            if (escaping.exists(Term.occursFree(_, target))) None
            else Term.absAll(applied, target).toOption.flatMap(bind(variable, _))
          }

        case _ => None
      }
    }

    go(pattern, target, Nil, Instantiation.empty).filter(_.expressible)
  }

  /**
   * Which condition of the fragment a refused match met, for a caller that has to explain one.
   *
   * [[matchTerm]] answers `None`, and `None` says nothing: a caller looking at a tactic that did
   * not fire cannot tell an ordinary miss — this lemma is simply not about this goal — from a
   * question the fragment was asked and had to turn down. That distinction is what anybody
   * measuring this matcher needs, and until 2026-09-18 the only way to get it was to instrument
   * the file and run the suite, which is how the figures in `docs/adr/0030` were taken.
   *
   * **It re-walks rather than being threaded through [[matchTerm]].** Threading a reason through
   * the walk means every one of its answers carries one, and the walk answers `None` tens of
   * millions of times in a suite: measured on 2026-09-18, one run of `tactics/test` reaches the
   * higher-order fall-through **70 314 333** times, almost all of them the ordinary first-order
   * miss. A reason built at each of those is a cost paid by everything to explain the few that
   * anybody asks about. So this is a second pass, taken only when a caller asks, and it answers
   * about the **first** place the fragment's conditions were met and failed.
   *
   * `None` here means the match was not refused by the fragment: either it succeeded, or it failed
   * for the ordinary first-order reason, which is not a limit of this matcher but an answer about
   * the two terms.
   */
  def why(variables: Set[FVar], pattern: Term, target: Term): Option[Refusal] =
    if (matchTerm(variables, pattern, target).isDefined) None
    else firstRefusal(variables, pattern, target, Nil)

  /**
   * The first condition of the Miller case this pair meets and fails, walking the same shape.
   *
   * The walk mirrors [[matchTerm]]'s: an application is decomposed first, because the first-order
   * route is tried first there too and reaching the higher-order case at all means that route had
   * no answer. What it does not mirror is the instantiation: nothing is bound here, so a pair that
   * this reports on may also have failed for a reason further along.
   */
  private def firstRefusal(
    variables: Set[FVar],
    pattern: Term,
    target: Term,
    binders: List[FVar]
  ): Option[Refusal] = pattern match {
    case Abs(_, _) =>
      target match {
        case Abs(targetBinderType, _) =>
          val binder = Term.variable(s"%${binders.length}", targetBinderType)
          for {
            patternBody <- open(pattern, binder)
            targetBody <- open(target, binder)
            found <- firstRefusal(variables, patternBody, targetBody, binder :: binders)
          } yield found

        case _ => None
      }

    case App(_, _) =>
      val (head, arguments) = spine(pattern)

      val here = head match {
        case variable: FVar if variables.contains(variable) =>
          val applied = arguments.collect { case argument: FVar if binders.contains(argument) => argument }

          if (applied.length != arguments.length)
            Some(
              if (binders.isEmpty) Refusal.NoBinderInScope(variable)
              else Refusal.ArgumentIsNotABinder(variable)
            )
          else if (applied.distinct.length != applied.length) Some(Refusal.BinderAppliedTwice(variable))
          else {
            val escaping = binders.filterNot(applied.toSet.contains)
            if (escaping.exists(Term.occursFree(_, target))) Some(Refusal.TargetSeesAnotherBinder(variable))
            else None
          }

        case _ => None
      }

      here.orElse((pattern, target) match {
        case (App(fn, argument), App(targetFn, targetArgument)) =>
          firstRefusal(variables, fn, targetFn, binders)
            .orElse(firstRefusal(variables, argument, targetArgument, binders))
        case _ => None
      })

    case _ => None
  }

  /** The head of an application and its arguments, outermost first. */
  private def spine(term: Term): (Term, List[Term]) = term match {
    case App(fn, argument) =>
      val (head, arguments) = spine(fn)
      (head, arguments :+ argument)
    case other => (other, Nil)
  }

  /**
   * The body of an abstraction, with its binder replaced by a variable.
   *
   * Applying and reducing, because `Term.open` is `private[kernel]` and this is the public route to
   * the same term: `Term.app` type-checks the application and `betaReduce` performs exactly the
   * substitution `open` would have. A `None` here would mean the binder type and the variable type
   * disagreed, which the caller has already checked.
   */
  private def open(abstraction: Term, variable: FVar): Option[Term] =
    Term.app(abstraction, variable).toOption.flatMap(Term.betaReduce)

  private def names(term: Term): Set[String] = term match {
    case variable: FVar => Set(variable.name)
    case App(fn, argument) => names(fn) ++ names(argument)
    case Abs(_, body) => names(body)
    case _ => Set.empty
  }
}
