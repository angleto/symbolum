package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The square root of a non-negative real, defined rather than assumed, and the fact that it exists.
 *
 * `sqrt x` is `select (\y. 0 <= y /\ y * y = x)`: the non-negative number whose square is `x`,
 * named by choice the way `lim` and `ln` are. A name by choice is silent until something says the
 * predicate is satisfiable, and [[Root.Exists]] is what says it: every non-negative real has a
 * non-negative square root. From it [[Root.Squares]] reads the constant back, and [[Root.Unique]]
 * turns "a root" into "the root", the pair `Limit` makes of `LIM_OF_CONVERGES` and
 * `CONVERGES_UNIQUE` for the same reason: the choice alone would leave `sqrt x` an arbitrary root
 * if a number could have two non-negative ones.
 *
 * == Why this is the third thing `COMPLETENESS` buys, and why it is here ==
 *
 * An ordered field need not have square roots, and the rationals are the one everybody knows: no
 * rational squares to two, which is `Primes.NUM_SQUARE_NOT_DOUBLE` read over the naturals. So the
 * existence cannot come from the fifteen field and order axioms and has to spend the sixteenth, the
 * way `Peano.NUM_ARCHIMEDES` and `Limit.MONOTONE_CONVERGES` do. The argument is the textbook one and
 * every step of it is here: the set of non-negative `y` with `y * y <= x` holds zero and sits under
 * `x + 1`, so it has a least upper bound `s`; and `s * s` is neither below `x` nor above it.
 *
 * It is a development of its own and not a section of [[Limit]] or [[Transcendental]], because
 * each of those says in its first sentence what it is: the first is what a sequence converges to
 * and the second is the transcendental functions, and the square root is neither. What it needs is
 * the reals and their order, and nothing between them and the end of the chain; it is at the end
 * because that is where a link's constant is reachable from everything, which `Chain.widest` says.
 *
 * == The derivation has no quotient in it, and no classical step ==
 *
 * Both halves of the trichotomy pick a small positive `e` and push `s` by it. The obvious `e` is a
 * quotient, and a quotient with a symbolic denominator is outside every procedure here, so it
 * enters as `d * inv c` with `c` a sum already known positive, and the only property of the
 * reciprocal the derivation uses is `MUL_INVERSE` at `c`, turned into `e * c = d`. Every arithmetic
 * step after that is a schematic implication over real **variables**, settled by `Linarith` and
 * specialised afterwards; `Transcendental.EXP_ONE_ABOVE_TWO` is the same shape and says why.
 *
 * The denominators are chosen so that no case split on a minimum is needed. Below the root,
 * `e = d / (2s + 1 + d)` is under one by construction and `e * (2s + 1)` is under `d` because the
 * `d * e` it leaves out is positive; above it, `e = d / (2s + d)` does the same against `2s`. And
 * the two absurd branches reach falsity and leave by ex falso, so the existence rests on the reals
 * and on nothing the chain adds: `RootSpec` asserts that it reaches neither choice nor infinity,
 * which is what separates it from the constant built on it.
 *
 * == What it costs ==
 *
 * One constant, no axiom. [[Root.Exists]] rests on the axioms of the reals, `COMPLETENESS` among
 * them, and on nothing else; everything about `sqrt` rests on those and on `SELECT`, which the
 * choice in its definition spends.
 */
final class Root private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Root {

  /* ---------------------------------------------------------------- the constant */

  /** `sqrt x`, the non-negative square root of `x`, and silent below zero. */
  val SquareRoot: String = "sqrt"

  /** The definition, as text: the non-negative number whose square is the argument. */
  val SquareRootBody: String = "\\x:real. select (\\y:real. 0 <= y /\\ y * y = x)"

  /* ------------------------------------------------------------------- the facts */

  /**
   * `|- !x. 0 <= x ==> ?y. 0 <= y /\ y * y = x`
   *
   * The theorem the constant waits on, and the one that spends `COMPLETENESS`. It names no
   * constant of this development and reaches no axiom but the reals', which `RootSpec` asserts.
   */
  val Exists: String = "SQRT_EXISTS"

  /** `|- !x. 0 <= x ==> 0 <= sqrt x /\ sqrt x * sqrt x = x`, the choice read back. */
  val Squares: String = "SQRT"

  /** `|- !x y. 0 <= y /\ y * y = x ==> sqrt x = y`: there is one non-negative root and this is it. */
  val Unique: String = "SQRT_UNIQUE"

  /** `|- !y. 0 <= y ==> sqrt (y * y) = y`. */
  val OfSquare: String = "SQRT_SQUARE"

  /** `|- sqrt 0 = 0`. */
  val AtZero: String = "SQRT_ZERO"

  /** `|- sqrt 1 = 1`. */
  val AtOne: String = "SQRT_ONE"

  /** What every derived fact says, as text, in the order they are derived. */
  val Statements: Vector[(String, String)] = Vector(
    Exists -> "!x:real. 0 <= x ==> (?y:real. 0 <= y /\\ y * y = x)",
    Squares -> "!x:real. 0 <= x ==> 0 <= sqrt x /\\ sqrt x * sqrt x = x",
    Unique -> "!x:real y:real. 0 <= y /\\ y * y = x ==> sqrt x = y",
    OfSquare -> "!y:real. 0 <= y ==> sqrt (y * y) = y",
    AtZero -> "sqrt 0 = 0",
    AtOne -> "sqrt 1 = 1"
  )

  private val Reals: Type = TyApp(Real.TypeName, Nil)

  /** The development in the chain's signature, which is the one a consumer reaches for. */
  lazy val standard: Root = Chain.standard.root

  /**
   * The development over the reals and their order, extending `base`.
   *
   * `base` is the chain's end when this is built rather than `reals.theory`, for the reason every
   * link gives: a constant declared into a side branch is unreachable from every link above it.
   */
  def construct(
    classical: Classical,
    reals: RealTheory,
    order: Order,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Root] =
    for {
      body <- Parser.term(base, notation, SquareRootBody)
      defined <- LogicError.lift(Kernel.defineConstant(base, SquareRoot, body))
      (theory, definition) = defined

      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(order)
      completeness <- reals.axiom("COMPLETENESS")
      inverse <- reals.axiom("MUL_INVERSE")
      total <- reals.axiom("LT_TOTAL")

      steps = Steps(logic, linarith, theory, notation)
      exists <- existence(steps, completeness, inverse, total)
      squares <- readBack(steps, classical, definition, exists)
      unique <- uniqueness(steps, squares)
      ofSquare <- rootOfASquare(steps, unique)
      atZero <- steps.at(unique, "0:real", "0:real")
        .flatMap(steps.mp(_, steps.conj(steps.lemma("(0:real) <= 0"), steps.lemma("(0:real) * 0 = 0"))))
      atOne <- steps.at(unique, "1:real", "1:real")
        .flatMap(steps.mp(_, steps.conj(steps.lemma("(0:real) <= 1"), steps.lemma("(1:real) * 1 = 1"))))

      facts = Map(
        Exists -> exists,
        Squares -> squares,
        Unique -> unique,
        OfSquare -> ofSquare,
        AtZero -> atZero,
        AtOne -> atOne
      )

      // Each statement checked against the text a person reads it by, here rather than in the spec:
      // a development that built something other than what it says it built must not be handed out.
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { (acc, entry) =>
        val (name, text) = entry
        for {
          _ <- acc
          expected <- Parser.proposition(theory, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Root(theory, notation, logic, Map(SquareRoot -> definition), facts)

  /**
   * The few moves every derivation below makes, over one theory, so each step reads as the
   * arithmetic it is rather than as the plumbing that carries it.
   *
   * `lemma` is the one place anything is decided, and it is `Linarith` on a closed schematic
   * statement over real variables; everything else specialises, detaches, and moves an equation.
   */
  private final case class Steps(logic: Logic, linarith: Linarith, theory: Theory, notation: Notation) {
    val rules: Rules = logic.rules

    def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)
    def real(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, Reals)
    def assume(text: String): Either[LogicError, Kernel.Thm] =
      proposition(text).flatMap(statement => LogicError.lift(Kernel.assume(statement)))

    /** A schematic arithmetic fact, closed. Refused here if `Linarith` cannot settle it. */
    def lemma(text: String): Either[LogicError, Kernel.Thm] = linarith.prove(text)

    def at(theorem: Kernel.Thm, arguments: String*): Either[LogicError, Kernel.Thm] =
      arguments.foldLeft[Either[LogicError, List[Term]]](Right(Nil)) { (acc, text) =>
        for { terms <- acc; term <- real(text) } yield terms :+ term
      }.flatMap(rules.specAll(theorem, _))

    def at(theorem: Either[LogicError, Kernel.Thm], arguments: String*): Either[LogicError, Kernel.Thm] =
      theorem.flatMap(at(_, arguments*))

    def mp(implication: Kernel.Thm, premises: Either[LogicError, Kernel.Thm]*): Either[LogicError, Kernel.Thm] =
      premises.foldLeft[Either[LogicError, Kernel.Thm]](Right(implication)) { (acc, premise) =>
        for { current <- acc; proved <- premise; next <- rules.mp(current, proved) } yield next
      }

    def conj(left: Either[LogicError, Kernel.Thm], right: Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for { l <- left; r <- right; both <- rules.conjIntro(l, r) } yield both

    def existential(text: String): Either[LogicError, Term] =
      proposition(text).flatMap(statement =>
        logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement)))

    /** `|- a = b` and `|- P a` give `|- P b`, where `a` is the outermost argument of the conclusion. */
    def rewriteArgument(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      theorem.conclusion match {
        case App(partial, _) =>
          for {
            congruence <- Conv.apTerm(partial, equation)
            moved <- LogicError.lift(Kernel.eqMp(congruence, theorem))
          } yield moved
        case other => Left(NotOfForm("an application", other))
      }
  }

  /** The set whose supremum is the root: the non-negative numbers whose square is at most `x`. */
  private val Member: String = "0 <= y:real /\\ y * y <= x:real"

  /** What the existence concludes, at a free `x`. */
  private val Goal: String = "?y:real. 0 <= y /\\ y * y = x:real"

  /**
   * [[Exists]], from `COMPLETENESS` at the set `\y. 0 <= y /\ y * y <= x`.
   *
   * The set is inhabited by zero and bounded by `x + 1`, which is the first place a product is
   * reasoned about: a `y` past `x + 1` has a square past `y`, which is past `x`. The supremum `s` is
   * then put to `LT_TOTAL` against `x`, and the two strict cases are each refuted by an `e` that
   * moves `s`: below the root `s + e` is still in the set, so `s` was not an upper bound; above it
   * `s - e` bounds the set already, so `s` was not the least.
   */
  private def existence(
    steps: Steps,
    completeness: Kernel.Thm,
    inverse: Kernel.Thm,
    total: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    val s = Term.variable("s", Reals)
    val y = Term.variable("y", Reals)
    val nonNegative = assume("0 <= x:real")
    val zero = lemma("(0:real) <= 0")
    val zeroInside = at(lemma("!x:real. 0 <= x ==> 0 * 0 <= x"), "x:real").flatMap(mp(_, nonNegative))

    /** `c * inv c = 1`, for the text of a `c` whose positivity is given. */
    def reciprocal(c: String, positive: Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for {
        cTerm <- real(c)
        atC <- rules.spec(cTerm, inverse)
        nonZero <- at(lemma("!c:real. 0 < c ==> ~(c = 0)"), c).flatMap(mp(_, positive))
        result <- rules.mp(atC, nonZero)
      } yield result

    /** `(d * inv c) * c = d`, which is the only thing about the reciprocal anything below uses. */
    def times(d: String, c: String, dPositive: Either[LogicError, Kernel.Thm], cPositive: Either[LogicError, Kernel.Thm]) =
      at(lemma("!d:real c:real w:real. 0 < d ==> c * w = 1 ==> (d * w) * c = d"), d, c, s"inv ($c)")
        .flatMap(mp(_, dPositive, reciprocal(c, cPositive)))

    for {
      set <- Parser.term(theory, notation, s"\\y:real. $Member", Type.fun(Reals, Type.Bool))
      zeroTerm <- real("0:real")
      zeroMember <- conj(zero, zeroInside)
      inhabited <- existential(s"?y:real. $Member").flatMap(rules.existsIntro(_, zeroTerm, zeroMember))

      assumedMember <- assume(Member)
      belowBound <- at(lemma("!x:real y:real. 0 <= x ==> 0 <= y ==> y * y <= x ==> y <= x + 1"), "x:real", "y:real")
        .flatMap(mp(_, nonNegative, rules.conjElim1(assumedMember), rules.conjElim2(assumedMember)))
      memberStatement <- proposition(Member)
      everyMember <- rules.disch(memberStatement, belowBound).flatMap(rules.gen(y, _))
      ceiling <- real("x + 1")
      bounded <- existential(s"?b:real. !y:real. $Member ==> y <= b").flatMap(rules.existsIntro(_, ceiling, everyMember))

      atSet <- rules.spec(set, completeness)
      opened <- Conv.betaNormalise(atSet.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atSet)))
      supremumExists <- conj(Right(inhabited), Right(bounded)).flatMap(rules.mp(opened, _))

      supremum <- assume(s"(!y:real. $Member ==> y <= s:real) /\\ (!b:real. (!y:real. $Member ==> y <= b) ==> s <= b)")
      upper <- rules.conjElim1(supremum)
      least <- rules.conjElim2(supremum)
      sNonNegative <- rules.spec(zeroTerm, upper).flatMap(rules.mp(_, zeroMember))
      goal <- proposition(Goal)

      // Below the root: `s + e` is in the set, so `s` was not an upper bound.
      below <- {
        val d = "x - s * s"
        val c = s"2 * s + 1 + ($d)"
        val e = s"($d) * inv ($c)"
        val grows = "!s:real d:real e:real. 0 <= s ==> 0 < d ==> e * (2 * s + 1 + d) = d ==> "
        val under = assume("s * s < x:real")
        val dPositive = at(lemma("!x:real s:real. s * s < x ==> 0 < x - s * s"), "x:real", "s:real").flatMap(mp(_, under))
        val cPositive = at(lemma("!x:real s:real. 0 <= s ==> s * s < x ==> 0 < 2 * s + 1 + (x - s * s)"), "x:real", "s:real")
          .flatMap(mp(_, Right(sNonNegative), under))
        val equation = times(d, c, dPositive, cPositive)
        val ePositive = at(lemma(grows + "0 < e"), "s:real", d, e).flatMap(mp(_, Right(sNonNegative), dPositive, equation))
        val eSmall = at(lemma(grows + "e < 1"), "s:real", d, e).flatMap(mp(_, Right(sNonNegative), dPositive, equation))
        val step = at(lemma(grows + "0 < e ==> e < 1 ==> (s + e) * (s + e) <= s * s + d"), "s:real", d, e)
          .flatMap(mp(_, Right(sNonNegative), dPositive, equation, ePositive, eSmall))
        val square = at(lemma("!x:real s:real a:real. a <= s * s + (x - s * s) ==> a <= x"), "x:real", "s:real", s"(s + $e) * (s + $e)")
          .flatMap(mp(_, step))
        val stillNonNegative = at(lemma("!s:real e:real. 0 <= s ==> 0 < e ==> 0 <= s + e"), "s:real", e)
          .flatMap(mp(_, Right(sNonNegative), ePositive))
        for {
          pushed <- real(s"s + $e")
          passes <- rules.spec(pushed, upper).flatMap(mp(_, conj(stillNonNegative, square)))
          absurd <- at(lemma("!s:real e:real. 0 < e ==> s + e <= s ==> F"), "s:real", e).flatMap(mp(_, ePositive, Right(passes)))
          result <- rules.falsityElim(goal, absurd)
        } yield result
      }

      // At the root: `s` is the witness.
      equal <- for {
        root <- assume("s * s = x:real")
        both <- rules.conjIntro(sNonNegative, root)
        result <- existential(Goal).flatMap(rules.existsIntro(_, s, both))
      } yield result

      // Above the root: `s - e` is an upper bound already, so `s` was not the least.
      above <- {
        val d = "s * s - x"
        val c = s"2 * s + ($d)"
        val e = s"($d) * inv ($c)"
        val lower = s"s - $e"
        val over = assume("x:real < s * s")
        val sPositive = at(lemma("!x:real s:real. 0 <= x ==> 0 <= s ==> x < s * s ==> 0 < s"), "x:real", "s:real")
          .flatMap(mp(_, nonNegative, Right(sNonNegative), over))
        val dPositive = at(lemma("!x:real s:real. x < s * s ==> 0 < s * s - x"), "x:real", "s:real").flatMap(mp(_, over))
        val cPositive = at(lemma("!x:real s:real. 0 < s ==> x < s * s ==> 0 < 2 * s + (s * s - x)"), "x:real", "s:real")
          .flatMap(mp(_, sPositive, over))
        val equation = times(d, c, dPositive, cPositive)
        val ePositive = at(lemma("!s:real d:real e:real. 0 < s ==> 0 < d ==> e * (2 * s + d) = d ==> 0 < e"), "s:real", d, e)
          .flatMap(mp(_, sPositive, dPositive, equation))
        val eBelow = at(
          lemma("!x:real s:real e:real. 0 <= x ==> 0 < s ==> x < s * s ==> " +
            "e * (2 * s + (s * s - x)) = s * s - x ==> 0 < e ==> e < s"),
          "x:real", "s:real", e
        ).flatMap(mp(_, nonNegative, sPositive, over, equation, ePositive))
        val shrinks = at(
          lemma("!x:real s:real e:real. 0 < s ==> x < s * s ==> " +
            "e * (2 * s + (s * s - x)) = s * s - x ==> 0 < e ==> x <= (s - e) * (s - e)"),
          "x:real", "s:real", e
        ).flatMap(mp(_, sPositive, over, equation, ePositive))
        val lowerNonNegative = at(lemma("!s:real e:real. e < s ==> 0 <= s - e"), "s:real", e).flatMap(mp(_, eBelow))
        for {
          member <- assume(Member)
          yBelow <- at(
            lemma("!x:real y:real t:real. 0 <= y ==> 0 <= t ==> y * y <= x ==> x <= t * t ==> y <= t"),
            "x:real", "y:real", lower
          ).flatMap(mp(_, rules.conjElim1(member), lowerNonNegative, rules.conjElim2(member), shrinks))
          bound <- rules.disch(memberStatement, yBelow).flatMap(rules.gen(y, _))
          lowerTerm <- real(lower)
          passes <- rules.spec(lowerTerm, least).flatMap(rules.mp(_, bound))
          absurd <- at(lemma("!s:real e:real. 0 < e ==> s <= s - e ==> F"), "s:real", e).flatMap(mp(_, ePositive, Right(passes)))
          result <- rules.falsityElim(goal, absurd)
        } yield result
      }

      trichotomy <- at(total, "s * s", "x:real")
      rest <- assume("s * s = x:real \\/ x < s * s").flatMap(rules.disjElim(_, equal, above))
      cases <- rules.disjElim(trichotomy, below, rest)
      eliminated <- rules.existsElim(supremumExists, s, cases)
      assumption <- proposition("0 <= x:real")
      result <- rules.disch(assumption, eliminated).flatMap(rules.gen(x, _))
    } yield result
  }

  /**
   * [[Squares]]: the choice in the definition, at a predicate [[Exists]] says is satisfiable, read
   * back through the definition so that what it speaks of is `sqrt x` rather than the `select`.
   */
  private def readBack(
    steps: Steps,
    classical: Classical,
    definition: Kernel.Thm,
    exists: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    for {
      assumption <- proposition("0 <= x:real")
      nonNegative <- LogicError.lift(Kernel.assume(assumption))
      existential <- rules.spec(x, exists).flatMap(rules.mp(_, nonNegative))
      chosen <- classical.witness(existential)
      unfolded <- Conv.unfold(definition, List(x))
      backwards <- Conv.sym(unfolded)
      moved <- rewriteArgument(backwards, chosen)
      reduced <- Conv.betaNormalise(moved.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, moved)))
      result <- rules.disch(assumption, reduced).flatMap(rules.gen(x, _))
    } yield result
  }

  /** [[Unique]]: two non-negative numbers with one square are one number. */
  private def uniqueness(steps: Steps, squares: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val x = Term.variable("x", Reals)
    val y = Term.variable("y", Reals)
    val hypothesis = "0 <= y:real /\\ y * y = x:real"
    for {
      assumed <- assume(hypothesis)
      yNonNegative <- rules.conjElim1(assumed)
      ySquare <- rules.conjElim2(assumed)
      xNonNegative <- at(lemma("!x:real y:real. 0 <= y ==> y * y = x ==> 0 <= x"), "x:real", "y:real")
        .flatMap(mp(_, Right(yNonNegative), Right(ySquare)))
      root <- rules.spec(x, squares).flatMap(rules.mp(_, xNonNegative))
      // Two inequalities and not one equation, and that is `Linarith`'s shape rather than a
      // choice: measured on 2026-09-24, it settles `a <= b` from these hypotheses and refuses
      // `a = b` from the same ones. An equation goes through `byAntisymmetry`, which proves both
      // halves over a pool of facts built once for the equation; the reading, not verified, is that
      // the product each half needs is of its own negation with a hypothesis, which that pool never
      // holds. The same schematic fact serves both directions with its arguments swapped.
      below = lemma("!a:real b:real x:real. 0 <= a ==> 0 <= b ==> a * a = x ==> b * b = x ==> a <= b")
      rootBelow <- at(below, "sqrt x", "y:real", "x:real")
        .flatMap(mp(_, rules.conjElim1(root), Right(yNonNegative), rules.conjElim2(root), Right(ySquare)))
      rootAbove <- at(below, "y:real", "sqrt x", "x:real")
        .flatMap(mp(_, Right(yNonNegative), rules.conjElim1(root), Right(ySquare), rules.conjElim2(root)))
      same <- at(lemma("!a:real b:real. a <= b ==> b <= a ==> a = b"), "sqrt x", "y:real")
        .flatMap(mp(_, Right(rootBelow), Right(rootAbove)))
      statement <- proposition(hypothesis)
      result <- rules.disch(statement, same).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
    } yield result
  }

  /** [[OfSquare]]: [[Unique]] at a square, which is the form a caller reaches for. */
  private def rootOfASquare(steps: Steps, unique: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val y = Term.variable("y", Reals)
    for {
      assumption <- proposition("0 <= y:real")
      nonNegative <- LogicError.lift(Kernel.assume(assumption))
      square <- real("y:real * y")
      premise <- rules.conjIntro(nonNegative, Kernel.refl(square))
      atSquare <- at(unique, "y:real * y", "y:real").flatMap(rules.mp(_, premise))
      result <- rules.disch(assumption, atSquare).flatMap(rules.gen(y, _))
    } yield result
  }
}
