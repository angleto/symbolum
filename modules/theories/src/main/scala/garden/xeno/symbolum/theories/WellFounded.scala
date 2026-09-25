package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Recursion along a measure into `num`: a function may call itself at any argument whose measure
 * is smaller than its own, and the recursion theorem says such a function exists.
 *
 * {{{
 *   |- !m st. (!f g x. (!y. m y < m x ==> f y = g y) ==> st f x = st g x) ==> ?f. !x. f x = st f x
 * }}}
 *
 * `Recursion` recurses on the successor and `Descent` on a number reading every smaller one;
 * neither reaches a function whose argument is not a number, and neither lets a call land at an
 * argument that is smaller only **by a measure**. Euclid's algorithm is the case that says why it
 * matters: `NUM_GCD` has been **chosen** here rather than computed, because the definition by which
 * one computes it calls itself at `(n, m MOD n)`, which is smaller than `(m, n)` in its second
 * component and in no sense `Recursion` knows. `EuclidAlgorithm` is that definition, spent.
 *
 * == The proof, which is the graph again ==
 *
 * The step `st` is the caller's and the hypothesis on it is **admissibility**: `st f x` reads `f`
 * only below `x`'s measure, said as giving the same answer to two functions that agree there. The
 * graph is the least set of pairs `(x, st f x)` over every `f` whose pairs below `x` are already
 * in the set, which is `INDUCTIVE` over one clause, and strong induction on the measure shows it the
 * graph of a function: at `x` every smaller argument has exactly one value, the function choosing
 * that value gives `st` an answer at `x`, and admissibility makes every other function the clause
 * could have used give the same one. The function is the choice of the value at each argument. It
 * is `Datatype`'s recursion theorem with the constructors replaced by a measure, and it uses that
 * builder's moves rather than a second copy of them. `docs/adr/0043` is the decision.
 *
 * == What it does not do ==
 *
 * It asks for admissibility and does not derive it: that is a fact about the caller's step, and
 * `EuclidAlgorithm` shows the shape of the obligation for one step. And the order is a measure into `num`,
 * not an arbitrary well-founded relation: every recursion this repository has needed so far is on a
 * measure, and a relation that is not one wants an induction principle of its own first.
 */
object WellFounded {

  /** The recursion theorem, over the argument type `'a` and the result type `'b`. */
  val Statement: String =
    "!m:'a -> num. !st:('a -> 'b) -> 'a -> 'b. " +
      "(!f:'a -> 'b. !g:'a -> 'b. !x:'a. (!y:'a. m y < m x ==> f y = g y) ==> st f x = st g x) ==> " +
      "?f:'a -> 'b. !x:'a. f x = st f x"

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Arguments: Type = TyVar(Classical.TypeVariable)
  private val Results: Type = TyVar(Classical.CodomainVariable)
  private val Pairs: Type = TyApp(Product.TypeName, List(Arguments, Results))

  /**
   * The theorem, over `base`, which must hold `INDUCTIVE`, the pairs and the order on `num`: the
   * chain's widest signature does.
   */
  def theorem(ground: Datatype.Ground, base: Theory, notation: Notation): Either[LogicError, Kernel.Thm] =
    for {
      logic <- ground.classical.logic.over(base)
      result <- prove(Datatype.Tools(ground, logic, base, notation))
    } yield result

  private def prove(tools: Datatype.Tools): Either[LogicError, Kernel.Thm] = {
    import tools.*
    import Datatype.{leftOf, rightOf}

    val placeholder = Term.variable("graph_", Type.fun(Pairs, Type.Bool))
    val m = Term.variable("m", Type.fun(Arguments, Num))
    val st = Term.variable("st", Type.fun(Type.fun(Arguments, Results), Type.fun(Arguments, Results)))
    val x = Term.variable("x", Arguments)
    val y = Term.variable("y", Arguments)
    val w = Term.variable("w", Results)
    val n = Term.variable("n", Num)
    val f2 = Term.variable("f'", Type.fun(Arguments, Results))
    val x2 = Term.variable("x'", Arguments)

    def read(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text)
    def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)

    /** A text over the placeholder `graph_`, with the graph put in its place. */
    def withGraph(graph: Term, text: String): Either[LogicError, Term] =
      proposition(text).flatMap(parsed => LogicError.lift(Term.substitute(Map(placeholder -> graph), parsed)))

    val exactlyOneText =
      "?v:'b. graph_ (PAIR (z:'a) v) /\\ (!w:'b. graph_ (PAIR z w) ==> w = v)"

    for {
      operator <- read(
        "\\S:prod('a,'b) -> bool. \\p:prod('a,'b). ?x:'a. ?f:'a -> 'b. " +
          "p = PAIR x ((st:('a -> 'b) -> 'a -> 'b) f x) /\\ (!y:'a. (m:'a -> num) y < m x ==> S (PAIR y (f y)))"
      )
      inductiveConstant <- constant(
        Inductive.Name,
        Type.fun(Type.fun(Type.fun(Pairs, Type.Bool), Type.fun(Pairs, Type.Bool)), Type.fun(Pairs, Type.Bool))
      )
      graph <- app(inductiveConstant, operator)
      monotone <- Monotone.prove(logic, ground.inductive, operator)
      introductionFact <- ground.inductive.fact(Inductive.Introduction)
      introduction <- rules.spec(operator, at(introductionFact, Classical.TypeVariable -> Pairs)).flatMap(rules.mp(_, monotone))
      fixpointFact <- ground.inductive.fact(Inductive.Fixpoint)
      fixpoint <- rules.spec(operator, at(fixpointFact, Classical.TypeVariable -> Pairs)).flatMap(rules.mp(_, monotone))

      admissible <- proposition(
        "!f:'a -> 'b. !g:'a -> 'b. !x:'a. (!y:'a. (m:'a -> num) y < m x ==> f y = g y) ==> " +
          "(st:('a -> 'b) -> 'a -> 'b) f x = st g x"
      )
      assumedAdmissible <- assume(admissible)

      /* `E z`: exactly one value at `z`, and `h`, the function choosing it. */
      z = Term.variable("z", Arguments)
      exactlyOneAtZ <- withGraph(graph, exactlyOneText)
      predicateAtZ <- logic.destExistsPredicate(exactlyOneAtZ).toRight(NotOfForm("an existential", exactlyOneAtZ))
      choice <- select(Results)
      chosenAtZ <- app(choice, predicateAtZ)
      h <- LogicError.lift(Term.abs(z, chosenAtZ))
      exactlyOne = (point: Term) => LogicError.lift(Term.substitute(Map(z -> point), exactlyOneAtZ))

      /*
       * From `|- E y`, the value at `y` said through `h`: `G (PAIR y (h y))` and
       * `!w. G (PAIR y w) ==> w = h y`.
       */
      valueAt = (point: Term, held: Kernel.Thm) =>
        for {
          chosen <- tools.witness(held)
          reduced <- Conv.betaRoot(chosen.conclusion)
          both <- LogicError.lift(Kernel.eqMp(reduced, chosen))
          member <- rules.conjElim1(both)
          unique <- rules.conjElim2(both)
          hAt <- app(h, point)
          contracted <- Conv.betaRoot(hAt)
          back <- Conv.sym(contracted)
          hole = Term.variable("hole_", Results)
          pairAtHole <- constant(Product.Pairing, Type.fun(Arguments, Type.fun(Results, Pairs))).flatMap(app(_, point, hole))
          memberTemplate <- app(graph, pairAtHole)
          memberMoved <- congruence(List(hole), memberTemplate, List(back))
          memberAtH <- LogicError.lift(Kernel.eqMp(memberMoved, member))
          wv = Term.variable("w", Results)
          pairAtW <- constant(Product.Pairing, Type.fun(Arguments, Type.fun(Results, Pairs))).flatMap(app(_, point, wv))
          atW <- app(graph, pairAtW)
          wEqualsHole <- equal(wv, hole)
          uniqueTemplate <- imp(atW, wEqualsHole).flatMap(logic.mkForall(wv, _))
          uniqueMoved <- congruence(List(hole), uniqueTemplate, List(back))
          uniqueAtH <- LogicError.lift(Kernel.eqMp(uniqueMoved, unique))
        } yield (memberAtH, uniqueAtH)

      /* `|- G (PAIR x (st f x))` from `|- !y. m y < m x ==> G (PAIR y (f y))`. */
      introduce = (point: Term, function: Term, below: Kernel.Thm) =>
        for {
          value <- app(st, function, point)
          pair <- constant(Product.Pairing, Type.fun(Arguments, Type.fun(Results, Pairs))).flatMap(app(_, point, value))
          unfolded <- tools.applied(operator, List(graph, pair))
          body <- rightOf(unfolded)
          proofOfBody <- rules.conjIntro(Conv.refl(pair), below)
          proved <- witnessed(body, List(point, function), proofOfBody)
          back <- Conv.sym(unfolded)
          image <- LogicError.lift(Kernel.eqMp(back, proved))
          result <- rules.spec(pair, introduction).flatMap(rules.mp(_, image))
        } yield result

      /*
       * The uniqueness at `x`, from the uniqueness below it: `G (PAIR x w) ==> w = st h x`, given
       * `|- !y. m y < m x ==> !w. G (PAIR y w) ==> w = h y`.
       */
      uniqueAbove = (point: Term, uniqueBelow: Kernel.Thm) =>
        for {
          pairTerm <- constant(Product.Pairing, Type.fun(Arguments, Type.fun(Results, Pairs))).flatMap(app(_, point, w))
          atW <- app(graph, pairTerm)
          assumedAtW <- assume(atW)
          unfolded <- rules.spec(pairTerm, fixpoint)
          image <- LogicError.lift(Kernel.eqMp(unfolded, assumedAtW))
          opened <- tools.applied(operator, List(graph, pairTerm))
          clause <- rightOf(opened)
          openedImage <- LogicError.lift(Kernel.eqMp(opened, image))
          target <- app(st, h, point).flatMap(equal(w, _))
          inside <- {
            for {
              atX2 <- logic.destExistsPredicate(clause).toRight(NotOfForm("an existential", clause))
                .flatMap(app(_, x2)).flatMap(Conv.betaRoot).flatMap(rightOf)
              body <- logic.destExistsPredicate(atX2).toRight(NotOfForm("an existential", atX2))
                .flatMap(app(_, f2)).flatMap(Conv.betaRoot).flatMap(rightOf)
              assumedBody <- assume(body)
              pairEquation <- rules.conjElim1(assumedBody)
              belowX2 <- rules.conjElim2(assumedBody)
              parts <- pairParts(pairEquation)
              (samePoint, sameValue) = parts
              // for y below x: f' y = h y
              my <- app(m, y)
              mx <- app(m, point)
              lessX <- constant("NUM_LT", Type.fun(Num, Type.fun(Num, Type.Bool))).flatMap(app(_, my, mx))
              assumedLess <- assume(lessX)
              holeA = Term.variable("hole_", Arguments)
              mHole <- app(m, holeA)
              lessTemplate <- constant("NUM_LT", Type.fun(Num, Type.fun(Num, Type.Bool))).flatMap(app(_, my, mHole))
              moved <- congruence(List(holeA), lessTemplate, List(samePoint))
              lessX2 <- LogicError.lift(Kernel.eqMp(moved, assumedLess))
              memberAtF2 <- rules.spec(y, belowX2).flatMap(rules.mp(_, lessX2))
              f2y <- app(f2, y)
              uniqueAtY <- rules.spec(y, uniqueBelow).flatMap(rules.mp(_, assumedLess)).flatMap(rules.spec(f2y, _))
              agreeAtY <- rules.mp(uniqueAtY, memberAtF2)
              agreement <- rules.disch(lessX, agreeAtY).flatMap(rules.gen(y, _))
              // st f' x = st h x
              admissibleAt <- rules.specAll(assumedAdmissible, List(f2, h, point))
              stepsAgree <- rules.mp(admissibleAt, agreement)
              // w = st f' x' = st f' x = st h x
              stAtHole <- app(st, f2, holeA)
              backPoint <- Conv.sym(samePoint)
              toX <- congruence(List(holeA), stAtHole, List(backPoint))
              result <- Conv.trans(sameValue, toX).flatMap(Conv.trans(_, stepsAgree))
            } yield result
          }
          innerOpened <- {
            val atX2Statement = logic.destExistsPredicate(clause).toRight(NotOfForm("an existential", clause))
              .flatMap(app(_, x2)).flatMap(Conv.betaRoot).flatMap(rightOf)
            for {
              statement <- atX2Statement
              assumedStatement <- assume(statement)
              result <- rules.existsElim(assumedStatement, f2, inside)
            } yield (statement, result)
          }
          (_, underX2) = innerOpened
          eliminated <- rules.existsElim(openedImage, x2, underX2)
          result <- rules.disch(atW, eliminated).flatMap(rules.gen(w, _))
        } yield result

      /* ------------------------------------------------ strong induction on the measure */

      q <- {
        for {
          mz <- app(m, z)
          equation <- equal(mz, n)
          body <- imp(equation, exactlyOneAtZ).flatMap(logic.mkForall(z, _))
          result <- LogicError.lift(Term.abs(n, body))
        } yield result
      }
      strongFact <- ground.successor.peano.fact(Peano.StrongInduction)
      strong <- rules.spec(q, strongFact)

      step <- {
        val k = Term.variable("k", Num)
        for {
          qk <- app(q, k)
          kBelowN <- constant("NUM_LT", Type.fun(Num, Type.fun(Num, Type.Bool))).flatMap(app(_, k, n))
          hypothesisStatement <- imp(kBelowN, qk).flatMap(logic.mkForall(k, _))
          hypothesis <- assume(hypothesisStatement)
          mx <- app(m, x)
          atN <- equal(mx, n)
          assumedAtN <- assume(atN)
          my <- app(m, y)
          lessX <- constant("NUM_LT", Type.fun(Num, Type.fun(Num, Type.Bool))).flatMap(app(_, my, mx))
          assumedLess <- assume(lessX)
          // m y < n, from m y < m x and m x = n
          lessN <- {
            val hole = Term.variable("hole_", Num)
            for {
              template <- constant("NUM_LT", Type.fun(Num, Type.fun(Num, Type.Bool))).flatMap(app(_, my, hole))
              moved <- congruence(List(hole), template, List(assumedAtN))
              result <- LogicError.lift(Kernel.eqMp(moved, assumedLess))
            } yield result
          }
          qAtMy <- rules.spec(my, hypothesis).flatMap(rules.mp(_, lessN))
          qOpened <- Conv.betaRoot(qAtMy.conclusion).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, qAtMy)))
          eAtY <- rules.spec(y, qOpened).flatMap(rules.mp(_, Conv.refl(my)))
          valued <- valueAt(y, eAtY)
          (memberY, uniqueY) = valued
          membersBelow <- rules.disch(lessX, memberY).flatMap(rules.gen(y, _))
          uniquesBelow <- rules.disch(lessX, uniqueY).flatMap(rules.gen(y, _))
          existence <- introduce(x, h, membersBelow)
          uniqueness <- uniqueAbove(x, uniquesBelow)
          both <- rules.conjIntro(existence, uniqueness)
          eAtX <- exactlyOne(x)
          value <- app(st, h, x)
          witnessedX <- witnessed(eAtX, List(value), both)
          discharged <- rules.disch(atN, witnessedX).flatMap(rules.gen(x, _))
          qn <- app(q, n)
          folded <- Conv.betaRoot(qn).flatMap(Conv.sym).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, discharged)))
          result <- rules.disch(hypothesisStatement, folded).flatMap(rules.gen(n, _))
        } yield result
      }
      everyMeasure <- rules.mp(strong, step)

      /* ------------------------------------------------ the function, and its equation */

      everywhere <- {
        for {
          mx <- app(m, x)
          atMx <- rules.spec(mx, everyMeasure)
          opened <- Conv.betaRoot(atMx.conclusion).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, atMx)))
          result <- rules.spec(x, opened).flatMap(rules.mp(_, Conv.refl(mx)))
        } yield result
      }
      // at every y, then below x
      eAtY <- LogicError.lift(Kernel.inst(Map(x -> y), everywhere))
      valuedY <- valueAt(y, eAtY)
      (memberY, _) = valuedY
      my <- app(m, y)
      mx <- app(m, x)
      lessX <- constant("NUM_LT", Type.fun(Num, Type.fun(Num, Type.Bool))).flatMap(app(_, my, mx))
      membersBelow <- rules.disch(lessX, memberY).flatMap(rules.gen(y, _))
      existence <- introduce(x, h, membersBelow)
      valuedX <- valueAt(x, everywhere)
      (_, uniqueX) = valuedX
      value <- app(st, h, x)
      stepIsChoice <- rules.spec(value, uniqueX).flatMap(rules.mp(_, existence))
      equation <- Conv.sym(stepIsChoice)
      closed <- rules.gen(x, equation)

      fVariable = Term.variable("f", Type.fun(Arguments, Results))
      statementBody <- {
        for {
          fx <- app(fVariable, x)
          stfx <- app(st, fVariable, x)
          eq <- equal(fx, stfx)
          result <- logic.mkForall(x, eq)
        } yield result
      }
      predicate <- LogicError.lift(Term.abs(fVariable, statementBody))
      exists <- rules.existsIntro(predicate, h, closed)
      discharged <- rules.disch(admissible, exists)
      result <- rules.genAll(discharged, List(m, st))
    } yield result
  }
}
