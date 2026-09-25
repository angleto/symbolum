package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Euclid's algorithm, defined by recursion along a measure rather than chosen.
 *
 * `NUM_GCD` is `select` applied to the characterisation of a greatest common divisor, which is why
 * `Modular` says it denotes and cannot be evaluated by unfolding: nothing inside it computes. The
 * algorithm that does compute it calls itself at `(n, m MOD n)`, which is smaller than `(m, n)` in
 * its second component and in no sense `Recursion` knows, so until [[WellFounded]] it could not be
 * written as a definition here at all. This is that definition, and it is the first thing to spend
 * that theorem:
 *
 * {{{
 *   NUM_EUCLID_GCD a b = COND (b = 0) a (NUM_EUCLID_GCD b (NUM_MOD a b))
 * }}}
 *
 * The admissibility obligation is the one line of mathematics in it: at a pair whose second
 * component is not zero the step reads the function only at `(b, a MOD b)`, and `NUM_MOD_LT` is
 * what says that is below.
 *
 * == It sits beside the chain, and that is a debt ==
 *
 * Euclid's algorithm is arithmetic anyone would want, so this is `Fraction`'s standing and not
 * `Collatz`'s: `Ask`, `Find` and the library do not reach `NUM_EUCLID_GCD` because wiring a link moves
 * `Chain.widest`, the reading register and the guide's map, which is a piece of its own. And what
 * it does not yet say is the thing it is for: that `NUM_EUCLID_GCD a b = NUM_GCD a b` whenever `a` and
 * `b` are not both zero, which wants the common divisors of `(a, b)` to be those of `(b, a MOD b)`.
 * Until that lands this is a computation with an equation, not a computation of the gcd.
 */
final class EuclidAlgorithm private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** The equation defining `name`. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object EuclidAlgorithm {

  /** `NUM_EUCLID_GCD a b`, the value of Euclid's algorithm at `a` and `b`. */
  val Name: String = "NUM_EUCLID_GCD"

  /** The recursion the definition is for, as one equation. */
  val Recursion: String = "NUM_EUCLID_GCD_RECURSION"

  /** `|- !a. NUM_EUCLID_GCD a 0 = a`. */
  val AtZero: String = "NUM_EUCLID_GCD_ZERO"

  /** `|- !a b. ~(b = 0) ==> NUM_EUCLID_GCD a b = NUM_EUCLID_GCD b (NUM_MOD a b)`. */
  val Step: String = "NUM_EUCLID_GCD_STEP"

  /** Everything published here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    Recursion -> "!a:num. !b:num. NUM_EUCLID_GCD a b = COND (b = 0) a (NUM_EUCLID_GCD b (NUM_MOD a b))",
    AtZero -> "!a:num. NUM_EUCLID_GCD a 0 = a",
    Step -> "!a:num. !b:num. ~(b = 0) ==> NUM_EUCLID_GCD a b = NUM_EUCLID_GCD b (NUM_MOD a b)"
  )

  /** The step, over a pair `(a, b)`: `a` at zero, otherwise the function at `(b, a MOD b)`. */
  val StepText: String =
    "\\f:prod(num,num) -> num. \\p:prod(num,num). COND (SND p = 0) (FST p) (f (PAIR (SND p) (NUM_MOD (FST p) (SND p))))"

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Pairs: Type = TyApp(Product.TypeName, List(Num, Num))

  /** The development over the chain it is handed. */
  def construct(chain: Chain): Either[LogicError, EuclidAlgorithm] = {
    val ground = Datatype.Ground.of(chain)
    val base = chain.widest
    val theory = base.theory
    val notation = base.notation
    for {
      logic <- chain.classical.logic.over(theory)
      tools = Datatype.Tools(ground, logic, theory, notation)
      general <- WellFounded.theorem(ground, theory, notation)
      typed = Kernel.instType(Map(Classical.TypeVariable -> Pairs, Classical.CodomainVariable -> Num), general)
      measure <- LogicError.lift(theory.constant(Product.Second, Type.fun(Pairs, Num)))
      step <- Parser.term(theory, notation, StepText)
      instance <- logic.rules.specAll(typed, List(measure, step))
      admissible <- admissibility(chain, tools, instance)
      exists <- logic.rules.mp(instance, admissible)
      defined <- define(chain, tools, exists, step)
      (extended, definition, recursion) = defined
      wide <- chain.classical.logic.over(extended)
      rest <- consequences(chain, Datatype.Tools(ground, wide, extended, notation), recursion)
      (atZero, stepped) = rest
      facts = Map(Recursion -> recursion, AtZero -> atZero, Step -> stepped)
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { case (acc, (name, text)) =>
        for {
          _ <- acc
          expected <- Parser.proposition(extended, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new EuclidAlgorithm(extended, notation, wide, Map(Name -> definition), facts)
  }

  /** The development over the standard chain. */
  lazy val standard: EuclidAlgorithm =
    construct(Chain.standard).fold(error => throw new IllegalStateException(error.message), identity)

  /**
   * The obligation `WellFounded` asks of the step: two functions agreeing on every pair whose second
   * component is below `SND x` give the same answer at `x`. At a zero second component neither is
   * read; otherwise both are read at `(SND x, FST x MOD SND x)`, and `NUM_MOD_LT` puts that below.
   */
  private def admissibility(chain: Chain, tools: Datatype.Tools, instance: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import tools.*
    import Datatype.{leftOf, rightOf}
    val f = Term.variable("f", Type.fun(Pairs, Num))
    val g = Term.variable("g", Type.fun(Pairs, Num))
    val x = Term.variable("x", Pairs)
    for {
      obligation <- logic.destImp(instance.conclusion).map(_._1).toRight(NotOfForm("an implication", instance.conclusion))
      atFGX <- assume(obligation).flatMap(rules.specAll(_, List(f, g, x)))
      parts <- logic.destImp(atFGX.conclusion).toRight(NotOfForm("an implication", atFGX.conclusion))
      (agreeing, same) = parts
      sides <- Term.destEq(same).toRight(NotOfForm("an equation", same))
      (left, right) = sides
      assumedAgreeing <- assume(agreeing)
      leftOpened <- betaAll(left)
      rightOpened <- betaAll(right)
      leftBody <- rightOf(leftOpened)
      rightBody <- rightOf(rightOpened)
      condTrue <- chain.classical.fact(Classical.CondTrue).map(at(_, Classical.TypeVariable -> Num))
      condFalse <- chain.classical.fact(Classical.CondFalse).map(at(_, Classical.TypeVariable -> Num))
      pieces = (body: Term) => body match {
        case App(App(App(_, test), yes), no) => Right((test, yes, no))
        case other => Left(NotOfForm("a conditional", other))
      }
      leftPieces <- pieces(leftBody)
      rightPieces <- pieces(rightBody)
      (test, leftYes, leftNo) = leftPieces
      (_, rightYes, rightNo) = rightPieces

      whenZero <- for {
        zero <- assume(test)
        l <- rules.specAll(condTrue, List(test, leftYes, leftNo)).flatMap(rules.mp(_, zero))
        r <- rules.specAll(condTrue, List(test, rightYes, rightNo)).flatMap(rules.mp(_, zero))
        result <- Conv.sym(r).flatMap(Conv.trans(l, _))
      } yield result

      whenNot <- for {
        notZero <- not(test).flatMap(assume)
        second <- test match {
          case App(App(_, s), _) => Right(s)
          case other => Left(NotOfForm("an equation", other))
        }
        first <- read(tools, x, Product.First)
        positive <- positiveOf(chain, tools, second, notZero)
        modBelow <- chain.modular.fact("NUM_MOD_LT").flatMap(rules.specAll(_, List(first, second))).flatMap(rules.mp(_, positive))
        remainder <- modBelow.conclusion match {
          case App(App(_, r), _) => Right(r)
          case other => Left(NotOfForm("an order", other))
        }
        sndPair <- chain.product.fact(Product.SecondOfPair)
          .map(at(_, Classical.TypeVariable -> Num, Classical.CodomainVariable -> Num))
          .flatMap(rules.specAll(_, List(second, remainder)))
        next <- leftNo match {
          case App(_, argument) => Right(argument)
          case other => Left(NotOfForm("an application", other))
        }
        hole = Term.variable("hole_", Num)
        lessThan <- constant("NUM_LT", Type.fun(Num, Type.fun(Num, Type.Bool)))
        template <- app(lessThan, hole, second)
        moved <- congruence(List(hole), template, List(sndPair))
        below <- Conv.sym(moved).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, modBelow)))
        agree <- rules.spec(next, assumedAgreeing).flatMap(rules.mp(_, below))
        l <- rules.specAll(condFalse, List(test, leftYes, leftNo)).flatMap(rules.mp(_, notZero))
        r <- rules.specAll(condFalse, List(test, rightYes, rightNo)).flatMap(rules.mp(_, notZero))
        result <- Conv.trans(l, agree).flatMap(step => Conv.sym(r).flatMap(Conv.trans(step, _)))
      } yield result

      bodies <- chain.classical.cases(test, whenZero, whenNot)
      joined <- Conv.trans(leftOpened, bodies).flatMap(step => Conv.sym(rightOpened).flatMap(Conv.trans(step, _)))
      discharged <- rules.disch(agreeing, joined)
      result <- rules.genAll(discharged, List(f, g, x))
    } yield result
  }

  /** `|- st f x = <body>` by the two root contractions, which is all a step here needs. */
  private def betaAll(term: Term): Either[LogicError, Kernel.Thm] = term match {
    case App(App(lambda, function), point) => Conv.unfold(Conv.refl(lambda), List(function, point))
    case other => Left(NotOfForm("a step applied to a function and a point", other))
  }

  /** `FST x` or `SND x`, at the pair type. */
  private def read(tools: Datatype.Tools, x: Term, projection: String): Either[LogicError, Term] =
    tools.constant(projection, Type.fun(Pairs, Num)).flatMap(tools.app(_, x))

  /** `0 < s` from `~(s = 0)`, through the trichotomy: `0 = s` is refused by it and `s < 0` by `num`. */
  private def positiveOf(chain: Chain, tools: Datatype.Tools, s: Term, notZero: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import tools.*
    for {
      zero <- Parser.term(theory, notation, "0", Num)
      trichotomy <- chain.peano.fact(Peano.Trichotomy).flatMap(rules.specAll(_, List(zero, s)))
      notBelow <- chain.peano.fact(Peano.NotBelowZero).flatMap(rules.spec(s, _))
      zeroIsS <- equal(zero, s)
      notZeroIsS <- for {
        assumed <- assume(zeroIsS)
        flipped <- Conv.sym(assumed)
        absurd <- rules.notElim(notZero, flipped)
        result <- rules.notIntro(zeroIsS, absurd)
      } yield result
      parts <- logic.destDisj(trichotomy.conclusion).toRight(NotOfForm("a disjunction", trichotomy.conclusion))
      (positive, rest) = parts
      restParts <- logic.destDisj(rest).toRight(NotOfForm("a disjunction", rest))
      (_, negative) = restParts
      glued <- glue(
        not(zeroIsS).flatMap(nz =>
          not(negative).flatMap(nn =>
            imp(trichotomy.conclusion, positive).flatMap(imp(nn, _)).flatMap(imp(nz, _))))
      )
      result <- rules.mp(glued, notZeroIsS).flatMap(rules.mp(_, notBelow)).flatMap(rules.mp(_, trichotomy))
    } yield result
  }

  /**
   * `NUM_EUCLID_GCD = \a b. S (PAIR a b)`, `S` the function the recursion theorem chose, and its one
   * equation: the step at `(a, b)` with the projections read off the pair and `S` put back as the name.
   * Every reduction is at the root, because `S` holds the step inside its own predicate and a full
   * normalisation would rewrite `S` as well and then fail to recognise it.
   */
  private def define(
    chain: Chain,
    tools: Datatype.Tools,
    exists: Kernel.Thm,
    step: Term
  ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm)] = {
    import Datatype.{leftOf, rightOf}
    val a = Term.variable("a", Num)
    val b = Term.variable("b", Num)
    for {
      predicate <- tools.logic.destExistsPredicate(exists.conclusion).toRight(NotOfForm("an existential", exists.conclusion))
      choice <- tools.select(Type.fun(Pairs, Num))
      chosen <- tools.app(choice, predicate)
      pairing <- tools.constant(Product.Pairing, Type.fun(Num, Type.fun(Num, Pairs)))
      pairAB <- tools.app(pairing, a, b)
      atAB <- tools.app(chosen, pairAB)
      body <- LogicError.lift(Term.absAll(List(a, b), atAB))
      defined <- LogicError.lift(Kernel.defineConstant(tools.theory, Name, body))
      (extended, definition) = defined
      wide <- chain.classical.logic.over(extended)
      here = Datatype.Tools(tools.ground, wide, extended, tools.notation)
      name <- here.constant(Name, Type.fun(Num, Type.fun(Num, Num)))

      // |- S x = st S x, at every x, from the choice
      witnessed <- here.witness(exists)
      opened <- Conv.betaRoot(witnessed.conclusion).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, witnessed)))
      atPair <- here.rules.spec(pairAB, opened)
      stepped <- Conv.unfold(Conv.refl(step), List(chosen, pairAB))
      reduced <- rightOf(stepped)

      // the projections read off the pair
      fstPair <- chain.product.fact(Product.FirstOfPair)
        .map(here.at(_, Classical.TypeVariable -> Num, Classical.CodomainVariable -> Num))
        .flatMap(here.rules.specAll(_, List(a, b)))
      sndPair <- chain.product.fact(Product.SecondOfPair)
        .map(here.at(_, Classical.TypeVariable -> Num, Classical.CodomainVariable -> Num))
        .flatMap(here.rules.specAll(_, List(a, b)))
      hf = Term.variable("hole_f", Num)
      hs = Term.variable("hole_s", Num)
      template <- for {
        zero <- Parser.term(extended, tools.notation, "0", Num)
        test <- here.equal(hs, zero)
        remainder <- here.constant("NUM_MOD", Type.fun(Num, Type.fun(Num, Num))).flatMap(here.app(_, hf, hs))
        nextPair <- here.app(pairing, hs, remainder)
        next <- here.app(chosen, nextPair)
        conditional <- here.conditional(Num)
        result <- here.app(conditional, test, hf, next)
      } yield result
      projected <- here.congruence(List(hf, hs), template, List(fstPair, sndPair))
      _ <- leftOf(projected).flatMap(l => if (l == reduced) Right(()) else Left(NotOfForm("the step read at a pair", l)))

      // S (PAIR b (NUM_MOD a b)) back to NUM_EUCLID_GCD b (NUM_MOD a b)
      remainderAB <- here.constant("NUM_MOD", Type.fun(Num, Type.fun(Num, Num))).flatMap(here.app(_, a, b))
      unfoldedNext <- Conv.unfold(definition, List(b, remainderAB))
      namedNext <- Conv.sym(unfoldedNext)
      hole = Term.variable("hole_", Num)
      zero <- Parser.term(extended, tools.notation, "0", Num)
      test <- here.equal(b, zero)
      conditional <- here.conditional(Num)
      nameTemplate <- here.app(conditional, test, a, hole)
      renamed <- here.congruence(List(hole), nameTemplate, List(namedNext))

      unfolded <- Conv.unfold(definition, List(a, b))
      chain1 <- Conv.trans(unfolded, atPair)
      chain2 <- Conv.trans(chain1, stepped)
      chain3 <- Conv.trans(chain2, projected)
      equation <- Conv.trans(chain3, renamed)
      result <- here.rules.genAll(equation, List(a, b))
    } yield (extended, definition, result)
  }

  /** The two equations a caller computes with: at zero, and one step down. */
  private def consequences(chain: Chain, tools: Datatype.Tools, recursion: Kernel.Thm): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    import tools.*
    import Datatype.rightOf
    val a = Term.variable("a", Num)
    val b = Term.variable("b", Num)
    for {
      zero <- Parser.term(theory, notation, "0", Num)
      condTrue <- chain.classical.fact(Classical.CondTrue).map(at(_, Classical.TypeVariable -> Num))
      condFalse <- chain.classical.fact(Classical.CondFalse).map(at(_, Classical.TypeVariable -> Num))
      pieces = (theorem: Kernel.Thm) =>
        rightOf(theorem).flatMap {
          case App(App(App(_, test), yes), no) => Right((test, yes, no))
          case other => Left(NotOfForm("a conditional", other))
        }

      atZero <- for {
        instance <- rules.specAll(recursion, List(a, zero))
        parts <- pieces(instance)
        (test, yes, no) = parts
        chosen <- rules.specAll(condTrue, List(test, yes, no)).flatMap(rules.mp(_, Conv.refl(zero)))
        equation <- Conv.trans(instance, chosen)
        result <- rules.gen(a, equation)
      } yield result

      stepped <- for {
        instance <- rules.specAll(recursion, List(a, b))
        parts <- pieces(instance)
        (test, yes, no) = parts
        notZero <- not(test)
        assumed <- assume(notZero)
        chosen <- rules.specAll(condFalse, List(test, yes, no)).flatMap(rules.mp(_, assumed))
        equation <- Conv.trans(instance, chosen)
        result <- rules.disch(notZero, equation).flatMap(rules.genAll(_, List(a, b)))
      } yield result
    } yield (atZero, stepped)
  }
}
