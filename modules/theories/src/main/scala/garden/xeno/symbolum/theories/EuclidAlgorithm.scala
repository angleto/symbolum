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
 * == It computes the gcd, and the quotient beside it ==
 *
 * `NUM_EUCLID_GCD a b = NUM_GCD a b` whenever `a` and `b` are not both zero, which is [[IsGcd]]
 * and landed on 2026-09-25: strong induction on `b`, with the common divisors of `(a, b)` shown to be
 * those of `(b, a MOD b)`. Until then this was a computation with an equation and not a computation
 * of the gcd. `NUM_EUCLID_DIV` is the same arrangement for `NUM_DIV`, repeated subtraction by the
 * same recursion along a measure, and [[DivIsDiv]] is its theorem. `EuclidAlgorithmSpec` runs both
 * sets of equations at a point and carries the answer to the chosen constant, so `NUM_GCD 4 6 = 2`
 * is a theorem reached by computing.
 *
 * == It sits beside the chain, and that is a debt ==
 *
 * Euclid's algorithm is arithmetic anyone would want, so this is `Fraction`'s standing and not
 * `Collatz`'s: `Ask`, `Find` and the library do not reach `NUM_EUCLID_GCD` because wiring a link moves
 * `Chain.widest`, the reading register and the guide's map, which is a piece of its own. The two
 * theorems above did not change that and were not the reason to: they are about constants this
 * development declares, and a link would carry them along unchanged.
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

  /**
   * `|- !a b. ~(a = 0 /\ b = 0) ==> NUM_EUCLID_GCD a b = NUM_GCD a b`: what the algorithm is for.
   *
   * Strong induction on `b`. At zero both sides are `a`, which is [[GcdAtZero]]; above zero one step
   * of the algorithm and [[GcdRemainder]] meet at `(b, a MOD b)`, which is below. The exception is
   * the one `NUM_GCD` makes itself: at `(0, 0)` every number divides both, so the choice it is
   * defined by falls where nothing can say, and the algorithm answers `0`.
   */
  val IsGcd: String = "NUM_EUCLID_GCD_IS_GCD"

  /** `|- !a. ~(a = 0) ==> NUM_GCD a 0 = a` */
  val GcdAtZero: String = "NUM_GCD_AT_ZERO"

  /**
   * `|- !a b. ~(b = 0) ==> NUM_GCD b (NUM_MOD a b) = NUM_GCD a b`
   *
   * The step Euclid's algorithm takes preserves the greatest common divisor: the common divisors of
   * `(a, b)` are those of `(b, a MOD b)`, because `a = b (a DIV b) + a MOD b`.
   */
  val GcdRemainder: String = "NUM_GCD_REMAINDER"

  /**
   * `NUM_EUCLID_DIV a b`, the quotient by repeated subtraction, which is what computes `NUM_DIV`.
   *
   * `NUM_DIV` is chosen, like `NUM_GCD`, and this is its computing counterpart, defined by the same
   * recursion along a measure, here the first component: `a - b` is below `a` once `0 < b <= a`.
   */
  val DivName: String = "NUM_EUCLID_DIV"

  /** The division's recursion, as one equation. */
  val DivRecursion: String = "NUM_EUCLID_DIV_RECURSION"

  /**
   * `|- !a b. ~(b = 0) ==> NUM_EUCLID_DIV a b = NUM_DIV a b`
   *
   * Strong induction on `a`: below `b` both are `0`, and otherwise `NUM_DIV_MOD_UNIQUE` reads
   * `a = b * SUC (NUM_DIV (a - b) b) + NUM_MOD (a - b) b` as saying the quotient went up by one. At
   * `b = 0` the division answers `0` and `NUM_DIV` is silent.
   */
  val DivIsDiv: String = "NUM_EUCLID_DIV_IS_DIV"

  /** Everything published here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    Recursion -> "!a:num. !b:num. NUM_EUCLID_GCD a b = COND (b = 0) a (NUM_EUCLID_GCD b (NUM_MOD a b))",
    AtZero -> "!a:num. NUM_EUCLID_GCD a 0 = a",
    Step -> "!a:num. !b:num. ~(b = 0) ==> NUM_EUCLID_GCD a b = NUM_EUCLID_GCD b (NUM_MOD a b)",
    GcdAtZero -> "!a:num. ~(a = 0) ==> NUM_GCD a 0 = a",
    GcdRemainder -> "!a:num. !b:num. ~(b = 0) ==> NUM_GCD b (NUM_MOD a b) = NUM_GCD a b",
    IsGcd -> "!a:num. !b:num. ~(a = 0 /\\ b = 0) ==> NUM_EUCLID_GCD a b = NUM_GCD a b",
    DivRecursion ->
      ("!a:num. !b:num. NUM_EUCLID_DIV a b = " +
        "COND (b = 0) 0 (COND (NUM_LT a b) 0 (SUC (NUM_EUCLID_DIV (NUM_SUB a b) b)))"),
    DivIsDiv -> "!a:num. !b:num. ~(b = 0) ==> NUM_EUCLID_DIV a b = NUM_DIV a b"
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
      own = Map(Recursion -> recursion, AtZero -> atZero, Step -> stepped)
      semiring <- Semiring.construct(chain.peano)
      lookup = (name: String) =>
        own.get(name).toRight(MissingDefinition(name))
          .orElse(chain.modular.fact(name))
          .orElse(chain.peano.fact(name))
          .orElse(chain.peano.naturals.fact(name))
          .orElse(chain.classical.fact(name))
          .orElse(chain.product.fact(name))
      kit = Freshman.Kit(wide, extended, notation, semiring, chain.induct, lookup)
      atZeroGcd <- Computing.gcdAtZero(kit)
      remainderGcd <- Computing.gcdRemainder(kit)
      isGcd <- Computing.euclidIsGcd(kit, atZero, stepped, atZeroGcd, remainderGcd)
      divDefined <- Computing.defineDiv(chain, extended, notation, kit)
      (withDiv, divDefinition, divRecursion) = divDefined
      wideDiv <- chain.classical.logic.over(withDiv)
      divIsDiv <- Computing.divIsDiv(Freshman.Kit(wideDiv, withDiv, notation, semiring, chain.induct, lookup), divRecursion)
      facts = own ++ Map(
        GcdAtZero -> atZeroGcd,
        GcdRemainder -> remainderGcd,
        IsGcd -> isGcd,
        DivRecursion -> divRecursion,
        DivIsDiv -> divIsDiv
      )
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { case (acc, (name, text)) =>
        for {
          _ <- acc
          expected <- Parser.proposition(withDiv, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new EuclidAlgorithm(withDiv, notation, wideDiv, Map(Name -> definition, DivName -> divDefinition), facts)
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

  /**
   * What the algorithm computes, and the division beside it: the derivations `construct` runs after
   * the definition, over the `Steps` every hand derivation here shares.
   */
  private object Computing {
    import Steps.*

    private val Num: Type = TyApp(Natural.TypeName, Nil)
    private val Pairs: Type = TyApp(Product.TypeName, List(Num, Num))




    /** `|- !a. ~(a = 0) ==> NUM_GCD a 0 = a` */
    def gcdAtZero(kit: Kit): R[Kernel.Thm] = {
      val a = Term.variable("a", Num)
      val rules = kit.rules
      for {
        haT <- kit.proposition("~((a:num) = 0)")
        ha <- assume(haT)
        z <- zero(kit)
        zz <- eqTerm(z, z).flatMap(kit.logic.mkNot)
        cond <- rules.disjIntro1(zz, ha)
        g <- kit.at("\\a:num. NUM_GCD a 0", a)
        refl <- kit.use("NUM_DIVIDES_REFL", List(a))
        atZero <- kit.use("NUM_DIVIDES_ZERO", List(a))
        both <- rules.conjIntro(refl, atZero)
        d1 <- kit.use("NUM_GCD_DIVIDES", List(a, z, a), cond, both)
        d2 <- kit.use("NUM_GCD_DIVIDES_LEFT", List(a, z), cond)
        both2 <- rules.conjIntro(d2, d1)
        r <- kit.use("NUM_DIVIDES_ANTISYM", List(g, a), both2)
        out <- rules.disch(haT, r).flatMap(rules.gen(a, _))
      } yield out
    }

    /** `|- !a b. ~(b = 0) ==> NUM_GCD b (NUM_MOD a b) = NUM_GCD a b` */
    def gcdRemainder(kit: Kit): R[Kernel.Thm] = {
      val a = Term.variable("a", Num)
      val b = Term.variable("b", Num)
      val rules = kit.rules
      for {
        hbT <- kit.proposition("~((b:num) = 0)")
        hb <- assume(hbT)
        r <- kit.at("\\a:num. \\b:num. NUM_MOD a b", a, b)
        q <- kit.at("\\a:num. \\b:num. NUM_DIV a b", a, b)
        d <- kit.at("\\a:num. \\b:num. NUM_GCD b (NUM_MOD a b)", a, b)
        e <- kit.at("\\a:num. \\b:num. NUM_GCD a b", a, b)
        bq <- mul(kit, b, q)
        rZero <- zero(kit).flatMap(eqTerm(r, _)).flatMap(kit.logic.mkNot)
        aZero <- zero(kit).flatMap(eqTerm(a, _)).flatMap(kit.logic.mkNot)
        condBR <- rules.disjIntro1(rZero, hb)
        condAB <- rules.disjIntro2(aZero, hb)
        db <- kit.use("NUM_GCD_DIVIDES_LEFT", List(b, r), condBR)
        dr <- kit.use("NUM_GCD_DIVIDES_RIGHT", List(b, r), condBR)
        dbq <- kit.use("NUM_DIVIDES_MUL", List(d, b, q), db)
        dsum <- rules.conjIntro(dbq, dr).flatMap(c => kit.use("NUM_DIVIDES_ADD", List(d, bq, r), c))
        dm <- kit.use("NUM_DIV_MOD", List(a, b))
        da <- Limit.rewriteInProposition(dm, dsum)
        de <- rules.conjIntro(da, db).flatMap(c => kit.use("NUM_GCD_DIVIDES", List(a, b, d), condAB, c))
        ea <- kit.use("NUM_GCD_DIVIDES_LEFT", List(a, b), condAB)
        eb <- kit.use("NUM_GCD_DIVIDES_RIGHT", List(a, b), condAB)
        ebq <- kit.use("NUM_DIVIDES_MUL", List(e, b, q), eb)
        dividesBy <- kit.at("\\e:num. \\x:num. NUM_DIVIDES e x", e)
        back <- Conv.sym(dm)
        eSum <- transport(dividesBy, back, ea)
        er <- kit.use("NUM_DIVIDES_SUMMAND", List(e, bq, r), ebq, eSum)
        ed <- rules.conjIntro(eb, er).flatMap(c => kit.use("NUM_GCD_DIVIDES", List(b, r, e), condBR, c))
        eq <- rules.conjIntro(de, ed).flatMap(c => kit.use("NUM_DIVIDES_ANTISYM", List(d, e), c))
        out <- rules.disch(hbT, eq).flatMap(rules.genAll(_, List(a, b)))
      } yield out
    }

    /** `|- !a b. ~(a = 0 /\ b = 0) ==> NUM_EUCLID_GCD a b = NUM_GCD a b` */
    def euclidIsGcd(kit: Kit, atZeroE: Kernel.Thm, stepE: Kernel.Thm, gz: Kernel.Thm, gr: Kernel.Thm): R[Kernel.Thm] = {
      val nm = Num
      val rules = kit.rules
      for {
        predicate <- Parser.term(kit.theory, kit.notation,
          "\\b:num. !a:num. ~(a = 0 /\\ b = 0) ==> NUM_EUCLID_GCD a b = NUM_GCD a b")
        induction <- kit.use("NUM_STRONG_INDUCTION", List(predicate))
        p0 <- imp(kit, induction.conclusion)
        (premise, _) = p0
        n = fresh("n", nm, induction)
        body <- open(kit, premise, n)
        p1 <- imp(kit, body)
        (ihT, goal) = p1
        ih <- assume(ihT)
        a = fresh("a", nm, induction, ih)
        goalA <- open(kit, goal, a)
        p2 <- imp(kit, goalA)
        (hT, eqT) = p2
        h <- assume(hT)
        z <- zero(kit)
        nIsZero <- eqTerm(n, z)
        proved <- split(kit, nIsZero)(
          hz =>
            for {
              aZeroT <- eqTerm(a, z)
              aNot <- for {
                ha <- assume(aZeroT)
                both <- rules.conjIntro(ha, hz)
                f_ <- rules.notElim(h, both)
                r <- rules.notIntro(aZeroT, f_)
              } yield r
              e1 <- rules.spec(a, atZeroE)
              g1 <- kit.applyTo(gz, List(a), aNot)
              eq0 <- Conv.sym(g1).flatMap(Conv.trans(e1, _))
              back <- Conv.sym(hz)
              r <- Limit.rewriteInProposition(back, eq0)
            } yield r,
          hn =>
            for {
              stepped <- kit.applyTo(stepE, List(a, n), hn)
              pos <- positive(kit, n, hn)
              rLt <- kit.use("NUM_MOD_LT", List(a, n), pos)
              r <- kit.at("\\a:num. \\n:num. NUM_MOD a n", a, n)
              atR <- kit.applyTo(ih, List(r), rLt)
              pNR <- Parser.term(kit.theory, kit.notation, "\\n:num. \\r:num. n = 0 /\\ r = 0")
              conjT <- app(pNR, n, r).flatMap(Conv.betaNormalise).flatMap(Limit.rightOf)
              notBoth <- for {
                hc <- assume(conjT)
                n0 <- rules.conjElim1(hc)
                f_ <- rules.notElim(hn, n0)
                r2 <- rules.notIntro(conjT, f_)
              } yield r2
              ih2 <- kit.applyTo(atR, List(n), notBoth)
              g2 <- kit.applyTo(gr, List(a, n), hn)
              r3 <- transAll(stepped, ih2, g2)
            } yield r3
        )
        _ <- if (proved.conclusion == eqT) Right(()) else Left(NotOfForm("the claim at n", proved.conclusion))
        stepThm <- rules.disch(hT, proved).flatMap(rules.gen(a, _)).flatMap(rules.disch(ihT, _)).flatMap(rules.gen(n, _))
        all <- rules.mp(induction, stepThm)
        aa = Term.variable("a", nm)
        bb = Term.variable("b", nm)
        at <- rules.spec(bb, all).flatMap(rules.spec(aa, _))
        out <- rules.genAll(at, List(aa, bb))
      } yield out
    }


    val DivStepText: String =
      "\\f:prod(num,num) -> num. \\p:prod(num,num). COND (SND p = 0) 0 " +
        "(COND (NUM_LT (FST p) (SND p)) 0 (SUC (f (PAIR (NUM_SUB (FST p) (SND p)) (SND p)))))"


    /** `a - b < a` from `0 < b` and `b <= a`. */
    private def subBelow(kit: Kit, a: Term, b: Term, pos: Kernel.Thm, le: Kernel.Thm): R[Kernel.Thm] =
      for {
        z <- zero(kit)
        diff <- kit.at("\\a:num. \\b:num. NUM_SUB a b", a, b)
        m <- kit.use(Peano.AddStrictlyMonotone, List(diff, z, b), pos)
        addZero <- kit.use(Peano.AddAtZero, List(diff))
        back <- kit.use("NUM_SUB_ADD", List(a, b), le)
        m1 <- Limit.rewriteInProposition(addZero, m)
        r <- Limit.rewriteInProposition(back, m1)
      } yield r

    private def unfoldStep(term: Term): R[Kernel.Thm] = term match {
      case App(App(lambda, function), point) => Conv.unfold(Conv.refl(lambda), List(function, point))
      case other => Left(NotOfForm("a step applied to a function and a point", other))
    }

    private def divAdmissibility(chain: Chain, kit: Kit, instance: Kernel.Thm): R[Kernel.Thm] = {
      val rules = kit.rules
      val fn = Type.fun(Pairs, Num)
      val f = Term.variable("f", fn)
      val g = Term.variable("g", fn)
      val x = Term.variable("x", Pairs)
      for {
        obligation <- kit.logic.destImp(instance.conclusion).map(_._1).toRight(NotOfForm("an implication", instance.conclusion))
        atFGX <- assume(obligation).flatMap(rules.specAll(_, List(f, g, x)))
        p1 <- imp(kit, atFGX.conclusion)
        (agreeing, same) = p1
        p2 <- sides(same)
        (left, right) = p2
        hAgree <- assume(agreeing)
        lOpen <- unfoldStep(left)
        rOpen <- unfoldStep(right)
        lBody <- Limit.rightOf(lOpen)
        rBody <- Limit.rightOf(rOpen)
        lc <- conditional(lBody)
        (t1, lz, lInner) = lc
        rc <- conditional(rBody)
        (_, rz, rInner) = rc
        bodies <- split(kit, t1)(
          yes =>
            for {
              l <- condTrue(kit, t1, lz, lInner, yes)
              r <- condTrue(kit, t1, rz, rInner, yes)
              e <- Conv.sym(r).flatMap(Conv.trans(l, _))
            } yield e,
          no =>
            for {
              l <- condFalse(kit, t1, lz, lInner, no)
              r <- condFalse(kit, t1, rz, rInner, no)
              li <- conditional(lInner)
              (t2, lz2, lSuc) = li
              ri <- conditional(rInner)
              (_, rz2, rSuc) = ri
              inner <- split(kit, t2)(
                below =>
                  for {
                    l2 <- condTrue(kit, t2, lz2, lSuc, below)
                    r2 <- condTrue(kit, t2, rz2, rSuc, below)
                    e <- Conv.sym(r2).flatMap(Conv.trans(l2, _))
                  } yield e,
                notBelow =>
                  for {
                    l2 <- condFalse(kit, t2, lz2, lSuc, notBelow)
                    r2 <- condFalse(kit, t2, rz2, rSuc, notBelow)
                    second <- t1 match {
                      case App(App(_, s), _) => Right(s)
                      case other => Left(NotOfForm("an equation", other))
                    }
                    first <- t2 match {
                      case App(App(_, fx), _) => Right(fx)
                      case other => Left(NotOfForm("an order", other))
                    }
                    pos <- positive(kit, second, no)
                    le <- kit.use("NUM_LE_OF_NOT_LT", List(first, second), notBelow)
                    lt <- subBelow(kit, first, second, pos, le)
                    next <- lSuc match {
                      case App(_, App(_, argument)) => Right(argument)
                      case other => Left(NotOfForm("a successor of an application", other))
                    }
                    diff <- kit.at("\\a:num. \\b:num. NUM_SUB a b", first, second)
                    fstNext <- kit.fact(Product.FirstOfPair)
                      .map(Kernel.instType(Map(Classical.TypeVariable -> Num, Classical.CodomainVariable -> Num), _))
                      .flatMap(rules.specAll(_, List(diff, second)))
                    belowLam <- kit.at("\\y:num. \\t:num. NUM_LT t y", first)
                    back <- Conv.sym(fstNext)
                    measured <- transport(belowLam, back, lt)
                    agree <- rules.spec(next, hAgree).flatMap(rules.mp(_, measured))
                    suc <- kit.term("SUC", Type.fun(Num, Num))
                    moved <- cong(suc, agree)
                    e <- transAll(l2, moved).flatMap(t => Conv.sym(r2).flatMap(Conv.trans(t, _)))
                  } yield e
              )
              e <- transAll(l, inner).flatMap(t => Conv.sym(r).flatMap(Conv.trans(t, _)))
            } yield e
        )
        joined <- transAll(lOpen, bodies).flatMap(t => Conv.sym(rOpen).flatMap(Conv.trans(t, _)))
        out <- rules.disch(agreeing, joined).flatMap(rules.genAll(_, List(f, g, x)))
      } yield out
    }

    /** The definition and its recursion equation, as `EuclidAlgorithm.define` builds the gcd's. */
    def defineDiv(chain: Chain, theory: Theory, notation: Notation, kit: Kit): R[(Theory, Kernel.Thm, Kernel.Thm)] = {
      val ground = Datatype.Ground.of(chain)
      val a = Term.variable("a", Num)
      val b = Term.variable("b", Num)
      for {
        logic <- chain.classical.logic.over(theory)
        tools = Datatype.Tools(ground, logic, theory, notation)
        general <- WellFounded.theorem(ground, theory, notation)
        typed = Kernel.instType(Map(Classical.TypeVariable -> Pairs, Classical.CodomainVariable -> Num), general)
        measure <- LogicError.lift(theory.constant(Product.First, Type.fun(Pairs, Num)))
        step <- Parser.term(theory, notation, DivStepText)
        instance <- logic.rules.specAll(typed, List(measure, step))
        admissible <- divAdmissibility(chain, kit, instance)
        exists <- logic.rules.mp(instance, admissible)

        predicate <- logic.destExistsPredicate(exists.conclusion).toRight(NotOfForm("an existential", exists.conclusion))
        choice <- tools.select(Type.fun(Pairs, Num))
        chosen <- tools.app(choice, predicate)
        pairing <- tools.constant(Product.Pairing, Type.fun(Num, Type.fun(Num, Pairs)))
        pairAB <- tools.app(pairing, a, b)
        atAB <- tools.app(chosen, pairAB)
        body <- LogicError.lift(Term.absAll(List(a, b), atAB))
        defined <- LogicError.lift(Kernel.defineConstant(theory, DivName, body))
        (extended, definition) = defined
        wide <- chain.classical.logic.over(extended)
        here = Datatype.Tools(ground, wide, extended, notation)
        witnessed <- here.witness(exists)
        opened <- Conv.betaRoot(witnessed.conclusion).flatMap(eqn => LogicError.lift(Kernel.eqMp(eqn, witnessed)))
        atPair <- here.rules.spec(pairAB, opened)
        stepped <- Conv.unfold(Conv.refl(step), List(chosen, pairAB))
        reduced <- Limit.rightOf(stepped)
        fstPair <- chain.product.fact(Product.FirstOfPair)
          .map(here.at(_, Classical.TypeVariable -> Num, Classical.CodomainVariable -> Num))
          .flatMap(here.rules.specAll(_, List(a, b)))
        sndPair <- chain.product.fact(Product.SecondOfPair)
          .map(here.at(_, Classical.TypeVariable -> Num, Classical.CodomainVariable -> Num))
          .flatMap(here.rules.specAll(_, List(a, b)))
        hf = Term.variable("hole_f", Num)
        hs = Term.variable("hole_s", Num)
        zero <- Parser.term(extended, notation, "0", Num)
        cond <- here.conditional(Num)
        lessThan <- here.constant("NUM_LT", Type.fun(Num, Type.fun(Num, Type.Bool)))
        minus <- here.constant("NUM_SUB", Type.fun(Num, Type.fun(Num, Num)))
        suc <- here.constant("SUC", Type.fun(Num, Num))
        template <- for {
          test <- here.equal(hs, zero)
          test2 <- here.app(lessThan, hf, hs)
          diff <- here.app(minus, hf, hs)
          nextPair <- here.app(pairing, diff, hs)
          next <- here.app(chosen, nextPair)
          succ <- here.app(suc, next)
          inner <- here.app(cond, test2, zero, succ)
          result <- here.app(cond, test, zero, inner)
        } yield result
        projected <- here.congruence(List(hf, hs), template, List(fstPair, sndPair))
        lhs <- Datatype.leftOf(projected)
        _ <- if (lhs == reduced) Right(()) else Left(NotOfForm("the step read at a pair", lhs))
        diffAB <- here.app(minus, a, b)
        unfoldedNext <- Conv.unfold(definition, List(diffAB, b))
        namedNext <- Conv.sym(unfoldedNext)
        hole = Term.variable("hole_", Num)
        nameTemplate <- for {
          test <- here.equal(b, zero)
          test2 <- here.app(lessThan, a, b)
          succ <- here.app(suc, hole)
          inner <- here.app(cond, test2, zero, succ)
          result <- here.app(cond, test, zero, inner)
        } yield result
        renamed <- here.congruence(List(hole), nameTemplate, List(namedNext))
        unfolded <- Conv.unfold(definition, List(a, b))
        equation <- transAll(unfolded, atPair, stepped, projected, renamed)
        result <- here.rules.genAll(equation, List(a, b))
      } yield (extended, definition, result)
    }

    /** `|- !a b. ~(b = 0) ==> NUM_EUCLID_DIV a b = NUM_DIV a b` */
    def divIsDiv(kit: Kit, recursion: Kernel.Thm): R[Kernel.Thm] = {
      val rules = kit.rules
      val b = Term.variable("b", Num)
      for {
        predicate <- Parser.term(kit.theory, kit.notation, "\\a:num. ~((b:num) = 0) ==> NUM_EUCLID_DIV a b = NUM_DIV a b")
        induction <- kit.use("NUM_STRONG_INDUCTION", List(predicate))
        p0 <- imp(kit, induction.conclusion)
        (premise, _) = p0
        n = fresh("n", Num, induction)
        body <- open(kit, premise, n)
        p1 <- imp(kit, body)
        (ihT, goal) = p1
        ih <- assume(ihT)
        p2 <- imp(kit, goal)
        (hbT, eqT) = p2
        hb <- assume(hbT)
        rec <- rules.specAll(recursion, List(n, b))
        recBody <- Limit.rightOf(rec)
        c0 <- conditional(recBody)
        (t1, z, inner) = c0
        c1 <- condFalse(kit, t1, z, inner, hb)
        ci <- conditional(inner)
        (t2, z2, sucTerm) = ci
        proved <- split(kit, t2)(
          below =>
            for {
              c2 <- condTrue(kit, t2, z2, sucTerm, below)
              both <- kit.use("NUM_DIV_MOD_BELOW", List(n, b), below)
              div0 <- rules.conjElim1(both)
              back <- Conv.sym(div0)
              r <- transAll(rec, c1, c2, back)
            } yield r,
          notBelow =>
            for {
              c2 <- condFalse(kit, t2, z2, sucTerm, notBelow)
              pos <- positive(kit, b, hb)
              le <- kit.use("NUM_LE_OF_NOT_LT", List(n, b), notBelow)
              lt <- subBelow(kit, n, b, pos, le)
              diff <- kit.at("\\a:num. \\b:num. NUM_SUB a b", n, b)
              dq <- kit.applyTo(ih, List(diff), lt).flatMap(rules.mp(_, hb))
              q <- kit.at("\\a:num. \\b:num. NUM_DIV a b", diff, b)
              r <- kit.at("\\a:num. \\b:num. NUM_MOD a b", diff, b)
              dm <- kit.use("NUM_DIV_MOD", List(diff, b))
              e1 <- kit.use("NUM_SUB_ADD", List(n, b), le).flatMap(Conv.sym)
              plusB <- kit.at("\\b:num. \\x:num. x + b", b)
              e2 <- Conv.sym(dm).flatMap(cong(plusB, _))
              p_e2 <- sides(e2.conclusion)
              (_, mid) = p_e2
              target <- kit.at("\\b:num. \\q:num. \\r:num. b * SUC q + r", b, q, r)
              mulSuc <- kit.use(Peano.MulAtSuccessor, List(b, q))
              e3 <- equate(kit, mid, target, Vector.empty, Vector(mulSuc))
              decomposed <- transAll(e1, e2, e3)
              rLt <- kit.use("NUM_MOD_LT", List(diff, b), pos)
              sq <- kit.at("\\q:num. SUC q", q)
              uniq <- rules.conjIntro(decomposed, rLt).flatMap(c => kit.use("NUM_DIV_MOD_UNIQUE", List(n, b, sq, r), c))
              u1 <- rules.conjElim1(uniq)
              suc <- kit.term("SUC", Type.fun(Num, Num))
              movedQ <- cong(suc, dq)
              out <- transAll(rec, c1, c2, movedQ, u1)
            } yield out
        )
        _ <- if (proved.conclusion == eqT) Right(()) else Left(NotOfForm("the claim at n", proved.conclusion))
        stepThm <- rules.disch(hbT, proved).flatMap(rules.disch(ihT, _)).flatMap(rules.gen(n, _))
        all <- rules.mp(induction, stepThm)
        aa = Term.variable("a", Num)
        at <- rules.spec(aa, all)
        out <- rules.genAll(at, List(aa, b))
      } yield out
    }
  }
}
