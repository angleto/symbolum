package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The gauge integral over `[a, b]`, Cousin's lemma, and the fundamental theorem of calculus.
 *
 * `docs/adr/0049` is the decision, and what it rejects is Darboux's integral, which would have
 * wanted a supremum per piece of a partition and the common refinement of two partitions, and
 * neither is about integration.
 *
 * == The sums ==
 *
 * `fine_sum f g u v s` says that `s` is the Riemann sum of `f` over a division of `[u, v]` fine for
 * the gauge `g`. It is not a statement about a sequence of points: it is the least relation closed
 * under two rules, taken with `Inductive.INDUCTIVE` over the triple `PAIR u (PAIR v s)`.
 * [[Integral.Piece]] is one interval with its tag, `u <= x <= v` and `v - u < g x`, whose sum is
 * `f x * (v - u)`; [[Integral.Join]] puts two adjacent divisions end to end and adds their sums.
 * Every finite division is reached by splitting, so these are the sums the textbook quantifies over.
 * [[Integral.Induction]] is the principle a consumer reasons about a division with.
 *
 * [[Integral.Exists]] is Cousin's lemma, that every gauge positive on `[a, b]` has a fine division
 * of it, and it is `Continuity.INTERVAL_GLUING` at the property "some fine sum exists": a join glues
 * two intervals and a piece covers every short interval around its tag. Without it the definition
 * below would hold of every number, because a statement about every fine sum is true of none.
 *
 * == The integral ==
 *
 * `has_integral f a b i` is the epsilon-gauge statement written out, the way `derivative` and
 * `continuous` are, and `integral f a b` is `select` applied to it, pinned by
 * [[Integral.Unique]] wherever an integral exists. Uniqueness takes one division fine for two gauges
 * at once, at their pointwise minimum, so no two divisions are ever merged.
 *
 * [[Integral.Fundamental]] is the theorem that joins the two halves of a first course: if `F` has
 * derivative `f x` at every point of `[a, b]`, then `f` has integral `F b - F a`, and nothing is
 * assumed of `f` beyond being that derivative. The gauge at `x` is a radius the derivative gives at
 * a share of the tolerance, chosen by `select`; on one piece the error is bounded from both ends to
 * the tag, which is the straddle inequality; and over a whole division the bound is an induction
 * over the relation.
 *
 * Three constants and no axiom. The integral is a link above `Derivative` because the fundamental
 * theorem names `derivative`.
 */
final class Integral private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Integral {

  /* --------------------------------------------------------------- the constants */

  /** `fine_sum f g u v s`: `s` is the sum of `f` over a division of `[u, v]` fine for `g`. */
  val FineSumName: String = "fine_sum"

  /** `has_integral f a b i`: `f` has integral `i` over `[a, b]`. */
  val HasIntegralName: String = "has_integral"

  /** `integral f a b`: the integral, where there is one. */
  val IntegralName: String = "integral"

  /**
   * The two rules, as the clause of an operator on sets of triples `PAIR u (PAIR v s)`. Each case is
   * an existential over the parts with an equation on the triple, so an introduction rule supplies
   * the parts and never has to take a pair apart.
   */
  private val Clause: String =
    "(?a:real. ?b:real. ?x:real. q = PAIR a (PAIR b (f x * (b - a))) /\\ a <= x /\\ x <= b /\\ b - a < g x) \\/ " +
      "(?a:real. ?b:real. ?c:real. ?r:real. ?t:real. q = PAIR a (PAIR c (r + t)) /\\ " +
      "S (PAIR a (PAIR b r)) /\\ S (PAIR b (PAIR c t)))"

  val FineSumBody: String =
    "\\f:real -> real. \\g:real -> real. \\u:real. \\v:real. \\s:real. " +
      "INDUCTIVE (\\S:prod(real,prod(real,real)) -> bool. \\q:prod(real,prod(real,real)). " + Clause + ") " +
      "(PAIR u (PAIR v s))"

  val HasIntegralBody: String =
    "\\f:real -> real. \\a:real. \\b:real. \\i:real. !e:real. 0 < e ==> ?g:real -> real. " +
      "(!x:real. 0 < g x) /\\ (!s:real. fine_sum f g a b s ==> abs (s - i) < e)"

  val IntegralBody: String = "\\f:real -> real. \\a:real. \\b:real. select (\\i:real. has_integral f a b i)"

  /* ------------------------------------------------------------------- the facts */

  /** One interval and its tag. */
  val Piece: String = "FINE_SUM_PIECE"

  /** Two adjacent divisions end to end. */
  val Join: String = "FINE_SUM_JOIN"

  /** Induction over a division: a property of every piece that survives a join holds of every sum. */
  val Induction: String = "FINE_SUM_INDUCT"

  /** Cousin's lemma: a gauge positive on `[a, b]` has a fine division of it. */
  val Exists: String = "FINE_SUM_EXISTS"

  /** A division fine for a gauge is fine for every larger one. */
  val Gauge: String = "FINE_SUM_GAUGE"

  /**
   * Every function continuous on `[a, b]` has an integral there. A Cauchy criterion that glues, and
   * one supremum; `Integrability` is the derivation.
   */
  val ContinuousHas: String = "CONTINUOUS_HAS_INTEGRAL"

  /** The same through `integral`: a continuous function has the integral `integral` names. */
  val ContinuousIntegral: String = "CONTINUOUS_INTEGRAL"

  /** Over a non-empty interval an integral is unique. */
  val HasUnique: String = "HAS_INTEGRAL_UNIQUE"

  /** `integral f a b` is the integral wherever there is one. */
  val Unique: String = "INTEGRAL_UNIQUE"

  /** The fundamental theorem, as a statement about `has_integral`. */
  val HasFundamental: String = "HAS_INTEGRAL_DERIVATIVE"

  /** The fundamental theorem: the integral of a derivative is the change in what it is the derivative of. */
  val Fundamental: String = "INTEGRAL_DERIVATIVE"

  /**
   * [[HasFundamental]] as a textbook states it: the derivative relative to `[a, b]`, one-sided at the
   * two ends, with nothing asked of `F` outside the interval. [[HasFundamental]] is derived from it.
   */
  val HasFundamentalWithin: String = "HAS_INTEGRAL_DERIVATIVE_WITHIN"

  /** [[Fundamental]] with the derivative relative to `[a, b]`. */
  val FundamentalWithin: String = "INTEGRAL_DERIVATIVE_WITHIN"

  /**
   * A fine sum of `\x. p * f x + q * g x` is `p * s1 + q * s2` for fine sums `s1` of `f` and `s2` of
   * `g` over the same division: induction over the relation, a piece and a join passing through both.
   */
  val SumLinear: String = "FINE_SUM_LINEAR"

  /** `has_integral f a b i ==> has_integral g a b j ==> has_integral (\x. p * f x + q * g x) a b (p * i + q * j)` */
  val HasLinear: String = "HAS_INTEGRAL_LINEAR"

  /** The same for `integral`, where both integrals exist and `a <= b`. */
  val Linear: String = "INTEGRAL_LINEAR"

  /**
   * Integration by parts: with `f` and `g` having slopes `df` and `dg` on `[a, b]`, an integral `i`
   * of `f * dg` makes `f b * g b - f a * g a - i` an integral of `df * g`. The product rule and
   * [[HasFundamental]] integrate the sum, and [[HasLinear]] at one and minus one takes `f * dg` away.
   */
  val HasParts: String = "HAS_INTEGRAL_PARTS"

  /** [[HasParts]] for `integral`. */
  val Parts: String = "INTEGRAL_PARTS"

  /**
   * The change of variables: with `g` having slope `dg` on `[a, b]` and `F` having slope `f`
   * everywhere, `\x. f (g x) * dg x` has integral `F (g b) - F (g a)`. The chain rule and
   * [[HasFundamental]] at `\y. F (g y)`.
   */
  val HasSubstitution: String = "HAS_INTEGRAL_SUBST"

  /** [[HasSubstitution]] for `integral`. */
  val Substitution: String = "INTEGRAL_SUBST"


  /** What every derived fact says, as text, in the order they are derived. */
  val Statements: Vector[(String, String)] = Vector(
    Piece ->
      ("!f:real -> real. !g:real -> real. !u:real. !v:real. !x:real. " +
        "u <= x /\\ x <= v /\\ v - u < g x ==> fine_sum f g u v (f x * (v - u))"),
    Join ->
      ("!f:real -> real. !g:real -> real. !u:real. !v:real. !w:real. !s:real. !t:real. " +
        "fine_sum f g u v s ==> fine_sum f g v w t ==> fine_sum f g u w (s + t)"),
    Induction ->
      ("!f:real -> real. !g:real -> real. !P:real -> real -> real -> bool. " +
        "(!u:real. !v:real. !x:real. u <= x /\\ x <= v /\\ v - u < g x ==> P u v (f x * (v - u))) ==> " +
        "(!u:real. !v:real. !w:real. !s:real. !t:real. P u v s ==> P v w t ==> P u w (s + t)) ==> " +
        "!u:real. !v:real. !s:real. fine_sum f g u v s ==> P u v s"),
    Exists ->
      ("!f:real -> real. !g:real -> real. !a:real. !b:real. a <= b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> 0 < g x) ==> ?s:real. fine_sum f g a b s"),
    Gauge ->
      ("!f:real -> real. !g:real -> real. !h:real -> real. !u:real. !v:real. !s:real. " +
        "(!x:real. g x <= h x) ==> fine_sum f g u v s ==> fine_sum f h u v s"),
    ContinuousHas ->
      ("!f:real -> real. !a:real. !b:real. a <= b ==> (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "?i:real. has_integral f a b i"),
    ContinuousIntegral ->
      ("!f:real -> real. !a:real. !b:real. a <= b ==> (!x:real. a <= x /\\ x <= b ==> continuous f x) ==> " +
        "has_integral f a b (integral f a b)"),
    HasUnique ->
      ("!f:real -> real. !a:real. !b:real. !i:real. !j:real. a <= b ==> " +
        "has_integral f a b i ==> has_integral f a b j ==> i = j"),
    Unique ->
      "!f:real -> real. !a:real. !b:real. !i:real. a <= b ==> has_integral f a b i ==> integral f a b = i",
    HasFundamental ->
      ("!F:real -> real. !f:real -> real. !a:real. !b:real. a <= b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> derivative F x (f x)) ==> has_integral f a b (F b - F a)"),
    Fundamental ->
      ("!F:real -> real. !f:real -> real. !a:real. !b:real. a <= b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> derivative F x (f x)) ==> integral f a b = F b - F a"),
    HasFundamentalWithin ->
      ("!F:real -> real. !f:real -> real. !a:real. !b:real. a <= b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> derivative_within F a b x (f x)) ==> has_integral f a b (F b - F a)"),
    FundamentalWithin ->
      ("!F:real -> real. !f:real -> real. !a:real. !b:real. a <= b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> derivative_within F a b x (f x)) ==> integral f a b = F b - F a"),
    SumLinear ->
      ("!f:real -> real. !g:real -> real. !p:real. !q:real. !d:real -> real. !u:real. !v:real. !s:real. " +
        "fine_sum (\\x:real. p * f x + q * g x) d u v s ==> " +
        "?s1:real. ?s2:real. fine_sum f d u v s1 /\\ fine_sum g d u v s2 /\\ s = p * s1 + q * s2"),
    HasLinear ->
      ("!f:real -> real. !g:real -> real. !a:real. !b:real. !i:real. !j:real. !p:real. !q:real. " +
        "has_integral f a b i ==> has_integral g a b j ==> has_integral (\\x:real. p * f x + q * g x) a b (p * i + q * j)"),
    Linear ->
      ("!f:real -> real. !g:real -> real. !a:real. !b:real. !i:real. !j:real. !p:real. !q:real. a <= b ==> " +
        "has_integral f a b i ==> has_integral g a b j ==> integral (\\x:real. p * f x + q * g x) a b = p * i + q * j"),
    HasParts ->
      ("!f:real -> real. !g:real -> real. !df:real -> real. !dg:real -> real. !a:real. !b:real. !i:real. a <= b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> derivative f x (df x)) ==> (!x:real. a <= x /\\ x <= b ==> derivative g x (dg x)) ==> " +
        "has_integral (\\x:real. f x * dg x) a b i ==> has_integral (\\x:real. df x * g x) a b (f b * g b - f a * g a - i)"),
    Parts ->
      ("!f:real -> real. !g:real -> real. !df:real -> real. !dg:real -> real. !a:real. !b:real. !i:real. a <= b ==> " +
        "(!x:real. a <= x /\\ x <= b ==> derivative f x (df x)) ==> (!x:real. a <= x /\\ x <= b ==> derivative g x (dg x)) ==> " +
        "has_integral (\\x:real. f x * dg x) a b i ==> integral (\\x:real. df x * g x) a b = f b * g b - f a * g a - i"),
    HasSubstitution ->
      ("!F:real -> real. !f:real -> real. !g:real -> real. !dg:real -> real. !a:real. !b:real. a <= b ==> " +
        "(!y:real. derivative F y (f y)) ==> (!x:real. a <= x /\\ x <= b ==> derivative g x (dg x)) ==> " +
        "has_integral (\\x:real. f (g x) * dg x) a b (F (g b) - F (g a))"),
    Substitution ->
      ("!F:real -> real. !f:real -> real. !g:real -> real. !dg:real -> real. !a:real. !b:real. a <= b ==> " +
        "(!y:real. derivative F y (f y)) ==> (!x:real. a <= x /\\ x <= b ==> derivative g x (dg x)) ==> " +
        "integral (\\x:real. f (g x) * dg x) a b = F (g b) - F (g a)")
  )

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Functions: Type = Type.fun(Reals, Reals)
  private val Triples: Type = TyApp(Product.TypeName, List(Reals, TyApp(Product.TypeName, List(Reals, Reals))))
  private val Properties: Type = Type.fun(Reals, Type.fun(Reals, Type.fun(Reals, Type.Bool)))

  /** The development in the chain's signature, which is the one a consumer reaches for. */
  lazy val standard: Integral = Chain.standard.integral

  /**
   * Everything this development proves, over `base`, which is the chain's end when it is built: a
   * constant declared into a side branch is unreachable from every link above it.
   */
  def construct(
    classical: Classical,
    reals: RealTheory,
    magnitude: Magnitude,
    product: Product,
    inductive: Inductive,
    continuity: Continuity,
    limit: Limit,
    derivative: Derivative,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Integral] =
    for {
      fineBody <- Parser.term(base, notation, FineSumBody)
      fineDefined <- LogicError.lift(Kernel.defineConstant(base, FineSumName, fineBody))
      (withSums, fineDefinition) = fineDefined
      hasBody <- Parser.term(withSums, notation, HasIntegralBody)
      hasDefined <- LogicError.lift(Kernel.defineConstant(withSums, HasIntegralName, hasBody))
      (withIntegrals, hasDefinition) = hasDefined
      integralBody <- Parser.term(withIntegrals, notation, IntegralBody)
      integralDefined <- LogicError.lift(Kernel.defineConstant(withIntegrals, IntegralName, integralBody))
      (theory, integralDefinition) = integralDefined

      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)
      steps = Continuity.Steps(logic, linarith, theory, notation, fineDefinition)
      sums = Sums(steps, product, inductive, fineDefinition)

      piece <- sums.piece
      join <- sums.join
      induction <- sums.induction
      gluing <- continuity.fact(Continuity.IntervalGluing)
      exists <- cousin(steps, gluing, piece, join)
      gauge <- largerGauge(steps, induction, piece, join)
      hasUnique <- uniqueness(steps, magnitude, limit, hasDefinition, exists, gauge)
      unique <- integralIsTheIntegral(steps, classical, integralDefinition, hasUnique)
      withinDefinition <- derivative.definition(Derivative.WithinName)
      hasFundamentalWithin <- fundamental(steps, reals, magnitude, classical, hasDefinition, withinDefinition, induction)
      fundamentalWithin <- integralOfDerivative(steps, unique, hasFundamentalWithin, SlopesWithin)
      ofDerivative <- derivative.fact(Derivative.WithinOfDerivative)
      hasFundamental <- twoSided(steps, hasFundamentalWithin, ofDerivative)
      fundamentalTheorem <- integralOfDerivative(steps, unique, hasFundamental, TwoSidedSlopes)
      continuous <- Integrability.prove(steps, reals, magnitude, classical, continuity, gluing, piece, join, induction,
        exists, gauge, hasDefinition, unique)
      (continuousHas, continuousIntegral) = continuous
      sumLinear <- sumsOfCombination(steps, induction, piece, join)
      hasLinear <- linearity(steps, reals, magnitude, hasDefinition, gauge, sumLinear)
      linear <- integralOfCombination(steps, unique, hasLinear)
      productRule <- derivative.fact(Derivative.ProductRule)
      chainRule <- derivative.fact(Derivative.ChainRule)
      hasParts <- byParts(steps, productRule, hasFundamental, hasLinear)
      hasSubstitution <- bySubstitution(steps, chainRule, hasFundamental)
      parts <- namedByUniqueness(steps, unique, hasParts, PartsHypotheses,
        List("f", "g", "df", "dg").map(Term.variable(_, Functions)) ++ List("a", "b", "i").map(Term.variable(_, Reals)),
        "\\x:real. (df:real -> real) x * (g:real -> real) x", "(f:real -> real) b * (g:real -> real) b - f a * g a - i:real")
      substitution <- namedByUniqueness(steps, unique, hasSubstitution, SubstitutionHypotheses,
        List("Fn", "f", "g", "dg").map(Term.variable(_, Functions)) ++ List("a", "b").map(Term.variable(_, Reals)),
        "\\x:real. (f:real -> real) ((g:real -> real) x) * (dg:real -> real) x", "(Fn:real -> real) ((g:real -> real) b) - Fn (g a)")

      facts = Map[String, Kernel.Thm](
        Piece -> piece,
        Join -> join,
        Induction -> induction,
        Exists -> exists,
        Gauge -> gauge,
        HasUnique -> hasUnique,
        Unique -> unique,
        HasFundamental -> hasFundamental,
        Fundamental -> fundamentalTheorem,
        HasFundamentalWithin -> hasFundamentalWithin,
        FundamentalWithin -> fundamentalWithin,
        ContinuousHas -> continuousHas,
        ContinuousIntegral -> continuousIntegral,
        SumLinear -> sumLinear,
        HasLinear -> hasLinear,
        Linear -> linear,
        HasParts -> hasParts,
        Parts -> parts,
        HasSubstitution -> hasSubstitution,
        Substitution -> substitution
      )

      // Each statement checked against the text a person reads it by: a development that built
      // something other than what it says it built must not be handed out.
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
    } yield new Integral(
      theory,
      notation,
      logic,
      Map(FineSumName -> fineDefinition, HasIntegralName -> hasDefinition, IntegralName -> integralDefinition),
      facts
    )

  /* ------------------------------------------------------------------ shared pieces */

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  /** `|- t` becomes `|- t'`, `t'` the beta normal form. */
  private def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Conv.betaNormalise(theorem.conclusion).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, theorem)))

  /**
   * `theorem` if it proves `target`, and otherwise a refusal carrying both terms: a refusal that
   * wrote the term into its own prose would freeze it in the kernel's notation before any reader
   * could be shown it in theirs.
   */
  private def proving(target: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    if (theorem.conclusion == target) Right(theorem) else Left(NotEqualTo(target, theorem.conclusion))

  /** A proof of the beta normal form of `target` becomes a proof of `target`. */
  private def shaped(target: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      normalising <- Conv.betaNormalise(target)
      normal <- rightOf(normalising)
      _ <- proving(normal, theorem)
      back <- Conv.sym(normalising)
      result <- LogicError.lift(Kernel.eqMp(back, theorem))
    } yield result

  /** The body of an existential at a witness, with the root application contracted. */
  private def instanceOf(logic: Logic, existential: Term, witness: Term): Either[LogicError, (Term, Term)] =
    for {
      predicate <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
      applied <- LogicError.lift(Term.app(predicate, witness))
      contraction <- Conv.betaRoot(applied)
      body <- rightOf(contraction)
    } yield (predicate, body)

  /**
   * `|- ?x1 ... xn. body` from a proof of the body at the witnesses, each introduced from the inside
   * out over the existential as it is written, so the result is that term and not a reparse of it.
   */
  private def introduce(
    logic: Logic,
    existential: Term,
    witnesses: List[Term],
    proveBody: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = witnesses match {
    case Nil => proveBody(existential)
    case witness :: rest =>
      for {
        parts <- instanceOf(logic, existential, witness)
        (predicate, body) = parts
        inner <- introduce(logic, body, rest, proveBody)
        result <- logic.rules.existsIntro(predicate, witness, inner)
      } yield result
  }

  /**
   * From `?x1 ... xn. body` assumed, whatever `useBody` proves from the body assumed at the
   * variables: the existentials are eliminated from the inside out, so the result rests on the
   * outer existential in place of the body.
   */
  private def eliminate(
    logic: Logic,
    existential: Term,
    variables: List[FVar],
    useBody: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = variables match {
    case Nil => useBody(existential)
    case variable :: rest =>
      for {
        parts <- instanceOf(logic, existential, variable)
        (_, body) = parts
        inner <- eliminate(logic, body, rest, useBody)
        assumed <- LogicError.lift(Kernel.assume(existential))
        result <- logic.rules.existsElim(assumed, variable, inner)
      } yield result
  }

  /** [[eliminate]] from a proved existential rather than an assumed one. */
  private def eliminateFrom(
    logic: Logic,
    existential: Kernel.Thm,
    variables: List[FVar],
    useBody: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      opened <- eliminate(logic, existential.conclusion, variables, useBody)
      closed <- logic.rules.disch(existential.conclusion, opened)
      result <- logic.rules.mp(closed, existential)
    } yield result

  private def conjuncts(logic: Logic, theorem: Kernel.Thm, count: Int): Either[LogicError, List[Kernel.Thm]] =
    if (count <= 1) Right(List(theorem))
    else
      for {
        first <- logic.rules.conjElim1(theorem)
        rest <- logic.rules.conjElim2(theorem).flatMap(conjuncts(logic, _, count - 1))
      } yield first :: rest

  /* ------------------------------------------------------------------ the sums */

  /**
   * The introduction rules and the induction principle of `fine_sum`, from `Inductive`'s at the
   * operator the definition applies `INDUCTIVE` to. The operator is read off the definition unfolded
   * rather than parsed a second time, because a second parse is a second term to keep in step.
   */
  private final case class Sums(steps: Continuity.Steps, product: Product, inductive: Inductive, definition: Kernel.Thm) {
    import steps.*

    private val f = Term.variable("f", Functions)
    private val g = Term.variable("g", Functions)

    /** `|- fine_sum f g u v s = INDUCTIVE op (PAIR u (PAIR v s))` at the given terms. */
    def unfoldAt(u: Term, v: Term, s: Term): Either[LogicError, Kernel.Thm] =
      Conv.unfold(definition, List(f, g, u, v, s))

    val operator: Either[LogicError, Term] =
      for {
        u <- real("u:real")
        unfolded <- unfoldAt(u, u, u)
        right <- rightOf(unfolded)
        op <- right match {
          case App(App(_, op), _) => Right(op)
          case other              => Left(NotOfForm("INDUCTIVE applied to an operator and a triple", other))
        }
      } yield op

    private def triple(u: String, v: String, s: String): Either[LogicError, Term] =
      Parser.term(theory, notation, s"PAIR ($u) (PAIR ($v) ($s))", Triples)

    /** `|- !x. op (INDUCTIVE op) x ==> INDUCTIVE op x`. */
    private val closed: Either[LogicError, Kernel.Thm] =
      for {
        op <- operator
        monotone <- Monotone.prove(logic, inductive, op)
        intro <- inductive.fact(Inductive.Introduction)
        atTriples = Kernel.instType(Map(Classical.TypeVariable -> Triples), intro)
        result <- rules.spec(op, atTriples).flatMap(rules.mp(_, monotone))
      } yield result

    /** `fine_sum f g u v s` from a proof of the clause at the triple, one disjunct of it. */
    private def fromClause(
      u: Term,
      v: Term,
      s: Term,
      tripleTerm: Term,
      prove: (Term, Term) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        rule <- closed
        instance <- rules.spec(tripleTerm, rule)
        antecedent <- logic.destImp(instance.conclusion).map(_._1).toRight(NotOfForm("an implication", instance.conclusion))
        normalising <- Conv.betaNormalise(antecedent)
        normal <- rightOf(normalising)
        sides <- logic.destDisj(normal).toRight(NotOfForm("a disjunction", normal))
        (left, right) = sides
        proved <- prove(left, right)
        clause <- Conv.sym(normalising).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, proved)))
        member <- rules.mp(instance, clause)
        unfolded <- unfoldAt(u, v, s)
        result <- Conv.sym(unfolded).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, member)))
      } yield result

    /** [[Piece]]: the first disjunct, with the parts as the witnesses and the triple equal to itself. */
    val piece: Either[LogicError, Kernel.Thm] = {
      val u = Term.variable("u", Reals)
      val v = Term.variable("v", Reals)
      val x = Term.variable("x", Reals)
      val conditions = "u:real <= x:real /\\ x <= v:real /\\ v - u < (g:real -> real) x"
      for {
        conditionTerm <- proposition(conditions)
        assumed <- LogicError.lift(Kernel.assume(conditionTerm))
        sum <- real("(f:real -> real) x * (v:real - u:real)")
        tripleTerm <- triple("u:real", "v:real", "(f:real -> real) x * (v:real - u:real)")
        member <- fromClause(u, v, sum, tripleTerm, (left, right) =>
          introduce(logic, left, List(u, v, x), body =>
            rules.conjIntro(Conv.refl(tripleTerm), assumed).flatMap(proof =>
              proving(body, proof)))
            .flatMap(rules.disjIntro1(right, _)))
        result <- rules.disch(conditionTerm, member).flatMap(rules.genAll(_, List(f, g, u, v, x)))
      } yield result
    }

    /** [[Join]]: the second disjunct, the two sums read through the definition as members of the closure. */
    val join: Either[LogicError, Kernel.Thm] = {
      val u = Term.variable("u", Reals)
      val v = Term.variable("v", Reals)
      val w = Term.variable("w", Reals)
      val s = Term.variable("s", Reals)
      val t = Term.variable("t", Reals)
      for {
        firstTerm <- proposition("fine_sum (f:real -> real) (g:real -> real) u v s")
        secondTerm <- proposition("fine_sum (f:real -> real) (g:real -> real) v w t")
        first <- LogicError.lift(Kernel.assume(firstTerm))
        second <- LogicError.lift(Kernel.assume(secondTerm))
        firstMember <- unfoldAt(u, v, s).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, first)))
        secondMember <- unfoldAt(v, w, t).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, second)))
        sum <- real("s:real + t:real")
        tripleTerm <- triple("u:real", "w:real", "s:real + t:real")
        member <- fromClause(u, w, sum, tripleTerm, (left, right) =>
          introduce(logic, right, List(u, v, w, s, t), body =>
            rules.conjIntro(firstMember, secondMember).flatMap(rules.conjIntro(Conv.refl(tripleTerm), _))
              .flatMap(proof =>
                proving(body, proof)))
            .flatMap(rules.disjIntro2(left, _)))
        result <- rules.disch(secondTerm, member).flatMap(rules.disch(firstTerm, _))
          .flatMap(rules.genAll(_, List(f, g, u, v, w, s, t)))
      } yield result
    }

    /**
     * [[Induction]]: `Inductive.INDUCTIVE_INDUCT` at the carrier `\q. P (FST q) (FST (SND q)) (SND (SND q))`.
     * The closure premise is proved in the shape `FST_PAIR` and `SND_PAIR` leave it in, each case
     * carrying the triple's equation into the carrier by congruence.
     */
    val induction: Either[LogicError, Kernel.Thm] = {
      val p = Term.variable("P", Properties)
      val y = Term.variable("y", Triples)
      val names = List("a", "b", "c", "r", "t", "x").map(Term.variable(_, Reals))
      val List(a, b, c, r, t, x) = names: @unchecked
      val base = "!u:real. !v:real. !x:real. u <= x /\\ x <= v /\\ v - u < (g:real -> real) x ==> " +
        "(P:real -> real -> real -> bool) u v ((f:real -> real) x * (v - u))"
      val step = "!u:real. !v:real. !w:real. !s:real. !t:real. (P:real -> real -> real -> bool) u v s ==> P v w t ==> P u w (s + t)"
      for {
        op <- operator
        carrier <- Parser.term(theory, notation,
          "\\q:prod(real,prod(real,real)). (P:real -> real -> real -> bool) (FST q) (FST (SND q)) (SND (SND q))",
          Type.fun(Triples, Type.Bool))
        inductionFact <- inductive.fact(Inductive.Induction)
        atTriples = Kernel.instType(Map(Classical.TypeVariable -> Triples), inductionFact)
        instance <- rules.specAll(atTriples, List(op, carrier))
        premise <- logic.destImp(instance.conclusion).map(_._1).toRight(NotOfForm("an implication", instance.conclusion))

        firstOfPair <- product.fact(Product.FirstOfPair)
        secondOfPair <- product.fact(Product.SecondOfPair)
        pairRules <- Vector(firstOfPair, secondOfPair).foldLeft[Either[LogicError, Vector[Rewrite.Rule]]](Right(Vector.empty)) {
          (acc, theorem) => for { rs <- acc; rule <- Rewrite.Rule.of(logic, theorem) } yield rs :+ rule
        }
        /* `|- carrier at a triple = P` read at its parts. */
        readAt = (tripleTerm: Term) =>
          for {
            applied <- LogicError.lift(Term.app(carrier, tripleTerm))
            contraction <- Conv.betaNormalise(applied)
            contracted <- rightOf(contraction)
            parts <- Rewrite.rewrite(pairRules, contracted)
            joined <- Conv.trans(contraction, parts)
          } yield joined

        baseHypothesis <- assume(base)
        stepHypothesis <- assume(step)

        normalising <- Conv.betaNormalise(premise)
        normal <- rightOf(normalising)
        tidying <- Rewrite.rewrite(pairRules, normal)
        tidy <- rightOf(tidying)
        stripped <- Logic.stripForall(tidy)
        point <- stripped._1.headOption.toRight(NotOfForm("a claim about every triple", tidy))
        clause <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
        (antecedent, _) = clause
        sides <- logic.destDisj(antecedent).toRight(NotOfForm("a disjunction", antecedent))
        (pieceCase, joinCase) = sides

        /* carrying `P` at the parts across the triple's equation to `P` at `FST y` and the rest */
        carried = (equation: Kernel.Thm, atParts: Kernel.Thm) =>
          for {
            along <- Conv.apTerm(carrier, equation)
            atPoint <- readAt(point)
            atTriple <- rightOf(equation).flatMap(readAt)
            chain <- Conv.sym(atPoint).flatMap(Conv.trans(_, along)).flatMap(Conv.trans(_, atTriple))
            result <- Conv.sym(chain).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, atParts)))
          } yield result

        fromPiece <- eliminate(logic, pieceCase, List(a, b, x), body =>
          for {
            assumed <- LogicError.lift(Kernel.assume(body))
            parts <- conjuncts(logic, assumed, 2)
            List(equation, conditions) = parts: @unchecked
            atParts <- rules.specAll(baseHypothesis, List(a, b, x)).flatMap(rules.mp(_, conditions))
            result <- carried(equation, atParts)
          } yield result)
        fromJoin <- eliminate(logic, joinCase, List(a, b, c, r, t), body =>
          for {
            assumed <- LogicError.lift(Kernel.assume(body))
            parts <- conjuncts(logic, assumed, 3)
            List(equation, left, right) = parts: @unchecked
            atParts <- rules.specAll(stepHypothesis, List(a, b, c, r, t)).flatMap(mp(_, Right(left), Right(right)))
            result <- carried(equation, atParts)
          } yield result)
        split <- LogicError.lift(Kernel.assume(antecedent)).flatMap(rules.disjElim(_, fromPiece, fromJoin))
        tidyProof <- rules.disch(antecedent, split).flatMap(rules.gen(point, _))
        premiseProof <- Conv.trans(normalising, tidying).flatMap(Conv.sym)
          .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, tidyProof)))
        everywhere <- rules.mp(instance, premiseProof)

        u = Term.variable("u", Reals)
        v = Term.variable("v", Reals)
        s = Term.variable("s", Reals)
        sumTerm <- proposition("fine_sum (f:real -> real) (g:real -> real) u v s")
        sum <- LogicError.lift(Kernel.assume(sumTerm))
        member <- unfoldAt(u, v, s).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, sum)))
        tripleTerm <- triple("u:real", "v:real", "s:real")
        atTriple <- rules.spec(tripleTerm, everywhere).flatMap(rules.mp(_, member))
        read <- readAt(tripleTerm)
        conclusion <- LogicError.lift(Kernel.eqMp(read, atTriple))
        result <- rules.disch(sumTerm, conclusion).flatMap(rules.genAll(_, List(u, v, s)))
          .flatMap(rules.disch(stepHypothesis.conclusion, _))
          .flatMap(rules.disch(baseHypothesis.conclusion, _))
          .flatMap(rules.genAll(_, List(f, g, p)))
      } yield result
    }
  }

  /* ------------------------------------------------------------------ Cousin */

  /**
   * [[Exists]]: `INTERVAL_GLUING` at `\u v. ?s. fine_sum f g u v s`. A join glues two intervals, and
   * around each `x` every interval containing it and shorter than `g x` is one piece tagged at `x`.
   * The two premises are proved in the shape the gluing states them, read off its instance.
   */
  private def cousin(steps: Continuity.Steps, gluing: Kernel.Thm, piece: Kernel.Thm, join: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val u = Term.variable("u", Reals)
    val v = Term.variable("v", Reals)
    val w = Term.variable("w", Reals)
    val x = Term.variable("x", Reals)
    val s = Term.variable("s", Reals)
    val t = Term.variable("t", Reals)
    val Positive = "!x:real. a:real <= x /\\ x <= b:real ==> 0 < (g:real -> real) x"
    for {
      relation <- Parser.term(theory, notation, "\\u:real. \\v:real. ?s:real. fine_sum (f:real -> real) (g:real -> real) u v s",
        Type.fun(Reals, Type.fun(Reals, Type.Bool)))
      instance <- rules.specAll(gluing, List(relation, a, b)).flatMap(reduced)
      firstParts <- logic.destImp(instance.conclusion).toRight(NotOfForm("an implication", instance.conclusion))
      secondParts <- logic.destImp(firstParts._2).toRight(NotOfForm("an implication", firstParts._2))
      thirdParts <- logic.destImp(secondParts._2).toRight(NotOfForm("an implication", secondParts._2))
      glueTerm = secondParts._1
      localTerm = thirdParts._1

      glued <- for {
        stripped <- Logic.stripForall(glueTerm)
        implication <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
        (premise, conclusion) = implication
        assumed <- LogicError.lift(Kernel.assume(premise))
        parts <- conjuncts(logic, assumed, 4)
        List(_, _, left, right) = parts: @unchecked
        List(gu, gv, gw) = stripped._1.toList: @unchecked
        joined <- eliminate(logic, left.conclusion, List(s), leftBody =>
          eliminate(logic, right.conclusion, List(t), rightBody =>
            for {
              first <- LogicError.lift(Kernel.assume(leftBody))
              second <- LogicError.lift(Kernel.assume(rightBody))
              both <- rules.specAll(join, List(f, g, gu, gv, gw, s, t)).flatMap(mp(_, Right(first), Right(second)))
              sum <- real("s:real + t:real")
              result <- introduce(logic, conclusion, List(sum), body =>
                proving(body, both))
            } yield result))
        byLeft <- rules.disch(left.conclusion, joined).flatMap(rules.mp(_, left))
        byRight <- rules.disch(right.conclusion, byLeft).flatMap(rules.mp(_, right))
        result <- rules.disch(premise, byRight).flatMap(rules.genAll(_, stripped._1.toList))
      } yield result

      local <- for {
        stripped <- Logic.stripForall(localTerm)
        implication <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
        (inside, radius) = implication
        assumedInside <- LogicError.lift(Kernel.assume(inside))
        point = stripped._1.head
        positive <- assume(Positive).flatMap(rules.spec(point, _)).flatMap(rules.mp(_, assumedInside))
        gx <- LogicError.lift(Term.app(g, point))
        result <- introduce(logic, radius, List(gx), body =>
          for {
            halves <- logic.destConj(body).toRight(NotOfForm("a conjunction", body))
            everyInterval = halves._2
            inner <- Logic.stripForall(everyInterval)
            condition <- logic.destImp(inner._2).toRight(NotOfForm("an implication", inner._2))
            (short, some) = condition
            assumedShort <- LogicError.lift(Kernel.assume(short))
            parts <- conjuncts(logic, assumedShort, 5)
            List(_, ux, xv, _, length) = parts: @unchecked
            List(iu, iv) = inner._1.toList: @unchecked
            conditions <- conj(Right(ux), conj(Right(xv), Right(length)))
            one <- rules.specAll(piece, List(f, g, iu, iv, point)).flatMap(rules.mp(_, conditions))
            sum <- real(s"(f:real -> real) ${point.name}:real * (${iv.name}:real - ${iu.name}:real)")
            witnessed <- introduce(logic, some, List(sum), target =>
              proving(target, one))
            every <- rules.disch(short, witnessed).flatMap(rules.genAll(_, inner._1.toList))
            both <- rules.conjIntro(positive, every)
            _ <- proving(body, both)
          } yield both)
          .flatMap(rules.disch(inside, _)).flatMap(rules.genAll(_, stripped._1.toList))
      } yield result

      _ <- if (glued.conclusion == glueTerm) Right(()) else Left(NotOfForm("the gluing premise", glued.conclusion))
      _ <- if (local.conclusion == localTerm) Right(()) else Left(NotOfForm("the local premise", local.conclusion))
      ordered <- assume("a:real <= b:real")
      concluded <- mp(instance, Right(ordered), Right(glued), Right(local))
      result <- List(Positive, "a:real <= b:real")
        .foldLeft[Either[LogicError, Kernel.Thm]](Right(concluded)) { (acc, text) =>
          for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
        }.flatMap(rules.genAll(_, List(f, g, a, b)))
    } yield result
  }

  /* ------------------------------------------------------------------ a larger gauge */

  /** [[Gauge]]: the induction at `\u v s. fine_sum f h u v s`, a piece fine for `g` being fine for `h`. */
  private def largerGauge(steps: Continuity.Steps, induction: Kernel.Thm, piece: Kernel.Thm, join: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val h = Term.variable("h", Functions)
    val u = Term.variable("u", Reals)
    val v = Term.variable("v", Reals)
    val w = Term.variable("w", Reals)
    val x = Term.variable("x", Reals)
    val s = Term.variable("s", Reals)
    val t = Term.variable("t", Reals)
    val Below = "!x:real. (g:real -> real) x <= (h:real -> real) x"
    for {
      property <- Parser.term(theory, notation, "\\u:real. \\v:real. \\s:real. fine_sum (f:real -> real) (h:real -> real) u v s", Properties)
      instance <- rules.specAll(induction, List(f, g, property)).flatMap(reduced)
      below <- assume(Below)

      base <- for {
        conditionTerm <- proposition("u:real <= x:real /\\ x <= v:real /\\ v - u < (g:real -> real) x")
        assumed <- LogicError.lift(Kernel.assume(conditionTerm))
        parts <- conjuncts(logic, assumed, 3)
        List(ux, xv, short) = parts: @unchecked
        larger <- rules.spec(x, below)
        shortForH <- at(lemma("!A:real G:real H:real. A < G ==> G <= H ==> A < H"),
          "v:real - u:real", "(g:real -> real) x:real", "(h:real -> real) x:real").flatMap(mp(_, Right(short), Right(larger)))
        conditions <- conj(Right(ux), conj(Right(xv), Right(shortForH)))
        one <- rules.specAll(piece, List(f, h, u, v, x)).flatMap(rules.mp(_, conditions))
        result <- rules.disch(conditionTerm, one).flatMap(rules.genAll(_, List(u, v, x)))
      } yield result

      stepped <- rules.specAll(join, List(f, h, u, v, w, s, t)).flatMap(rules.genAll(_, List(u, v, w, s, t)))
      everySum <- mp(instance, Right(base), Right(stepped))
      result <- rules.specAll(everySum, List(u, v, s))
        .flatMap(rules.disch(below.conclusion, _))
        .flatMap(rules.genAll(_, List(f, g, h, u, v, s)))
    } yield result
  }

  /* ------------------------------------------------------------------ uniqueness */

  /**
   * [[HasUnique]]: at half of any tolerance each integral has a gauge, their pointwise minimum is a
   * gauge fine for both, Cousin gives a sum fine for it, and the sum is within half the tolerance of
   * each. So the two differ by less than every positive number.
   */
  private def uniqueness(
    steps: Continuity.Steps,
    magnitude: Magnitude,
    limit: Limit,
    hasDefinition: Kernel.Thm,
    exists: Kernel.Thm,
    gauge: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val i = Term.variable("i", Reals)
    val j = Term.variable("j", Reals)
    val e = Term.variable("e", Reals)
    val x = Term.variable("x", Reals)
    val s = Term.variable("s", Reals)
    val g1 = Term.variable("g1", Functions)
    val g2 = Term.variable("g2", Functions)
    def opened(value: FVar): Either[LogicError, Kernel.Thm] =
      for {
        statement <- proposition(s"has_integral (f:real -> real) a b ${value.name}:real")
        assumed <- LogicError.lift(Kernel.assume(statement))
        equation <- Conv.unfold(hasDefinition, List(f, a, b, value))
        result <- LogicError.lift(Kernel.eqMp(equation, assumed))
      } yield result
    for {
      ordered <- assume("a:real <= b:real")
      first <- opened(i)
      second <- opened(j)
      positive <- assume("0 < e:real")
      half <- at(lemma("!e:real. 0 < e ==> 0 < e / 2"), "e:real").flatMap(mp(_, Right(positive)))
      halfTerm <- real("e:real / 2")
      firstGauge <- rules.spec(halfTerm, first).flatMap(rules.mp(_, half))
      secondGauge <- rules.spec(halfTerm, second).flatMap(rules.mp(_, half))

      within <- eliminateFrom(logic, firstGauge, List(g1), firstBody =>
        eliminateFrom(logic, secondGauge, List(g2), secondBody =>
          for {
            one <- LogicError.lift(Kernel.assume(firstBody))
            two <- LogicError.lift(Kernel.assume(secondBody))
            onePositive <- rules.conjElim1(one)
            oneClose <- rules.conjElim2(one)
            twoPositive <- rules.conjElim1(two)
            twoClose <- rules.conjElim2(two)
            smaller <- Parser.term(theory, notation, "\\x:real. min ((g1:real -> real) x) ((g2:real -> real) x)", Functions)

            bothPositive <- for {
              p1 <- rules.spec(x, onePositive)
              p2 <- rules.spec(x, twoPositive)
              least <- Continuity.minimumOf(steps, magnitude, "(g1:real -> real) x:real", "(g2:real -> real) x:real", p1, p2)
              point <- proposition("a:real <= x:real /\\ x <= b:real")
              result <- rules.disch(point, least).flatMap(rules.gen(x, _))
            } yield result
            cousinAt <- rules.specAll(exists, List(f, smaller, a, b)).flatMap(reduced)
              .flatMap(mp(_, Right(ordered), Right(bothPositive)))

            close <- eliminateFrom(logic, cousinAt, List(s), sumBody =>
              for {
                sum <- LogicError.lift(Kernel.assume(sumBody))
                minLeft <- at(magnitude.fact(Magnitude.MinBelowLeft), "(g1:real -> real) x:real", "(g2:real -> real) x:real")
                  .flatMap(rules.gen(x, _))
                minRight <- at(magnitude.fact(Magnitude.MinBelowRight), "(g1:real -> real) x:real", "(g2:real -> real) x:real")
                  .flatMap(rules.gen(x, _))
                forOne <- rules.specAll(gauge, List(f, smaller, g1, a, b, s)).flatMap(reduced)
                  .flatMap(mp(_, Right(minLeft), Right(sum)))
                forTwo <- rules.specAll(gauge, List(f, smaller, g2, a, b, s)).flatMap(reduced)
                  .flatMap(mp(_, Right(minRight), Right(sum)))
                nearI <- rules.spec(s, oneClose).flatMap(rules.mp(_, forOne))
                nearJ <- rules.spec(s, twoClose).flatMap(rules.mp(_, forTwo))
                cases <- at(magnitude.fact(Magnitude.AbsCases), "i:real - j:real")
                sI <- at(magnitude.fact(Magnitude.AbsAbove), "s:real - i:real")
                sINeg <- at(magnitude.fact(Magnitude.AbsAboveNegation), "s:real - i:real")
                sJ <- at(magnitude.fact(Magnitude.AbsAbove), "s:real - j:real")
                sJNeg <- at(magnitude.fact(Magnitude.AbsAboveNegation), "s:real - j:real")
                itself <- assume("abs (i:real - j:real) = i - j").flatMap(eq =>
                  at(lemma("!A:real i:real j:real s:real P:real Q:real e:real. A = i - j ==> -(s - i) <= P ==> P < e / 2 ==> " +
                    "s - j <= Q ==> Q < e / 2 ==> A < e"),
                    "abs (i:real - j:real)", "i:real", "j:real", "s:real", "abs (s:real - i:real)", "abs (s:real - j:real)", "e:real")
                    .flatMap(mp(_, Right(eq), Right(sINeg), Right(nearI), Right(sJ), Right(nearJ))))
                negated <- assume("abs (i:real - j:real) = -(i - j)").flatMap(eq =>
                  at(lemma("!A:real i:real j:real s:real P:real Q:real e:real. A = -(i - j) ==> s - i <= P ==> P < e / 2 ==> " +
                    "-(s - j) <= Q ==> Q < e / 2 ==> A < e"),
                    "abs (i:real - j:real)", "i:real", "j:real", "s:real", "abs (s:real - i:real)", "abs (s:real - j:real)", "e:real")
                    .flatMap(mp(_, Right(eq), Right(sI), Right(nearI), Right(sJNeg), Right(nearJ))))
                result <- rules.disjElim(cases, itself, negated)
              } yield result)
          } yield close))

      everyTolerance <- rules.disch(positive.conclusion, within).flatMap(rules.gen(e, _))
      nonNegative <- at(magnitude.fact(Magnitude.AbsNonNegative), "i:real - j:real")
      zero <- at(limit.fact(Limit.BelowEveryPositive), "abs (i:real - j:real)").flatMap(mp(_, Right(nonNegative), Right(everyTolerance)))
      difference <- at(magnitude.fact(Magnitude.AbsZero), "i:real - j:real").flatMap(mp(_, Right(zero)))
      equal <- at(lemma("!i:real j:real. i - j = 0 ==> i = j"), "i:real", "j:real").flatMap(mp(_, Right(difference)))
      result <- List("has_integral (f:real -> real) a b j", "has_integral (f:real -> real) a b i", "a:real <= b:real")
        .foldLeft[Either[LogicError, Kernel.Thm]](Right(equal)) { (acc, text) =>
          for { theorem <- acc; hypothesis <- proposition(text); next <- rules.disch(hypothesis, theorem) } yield next
        }.flatMap(rules.genAll(_, List(f, a, b, i, j)))
    } yield result
  }

  /** [[Unique]]: `SELECT` at `\i. has_integral f a b i` gives the chosen value an integral, and uniqueness names it. */
  private def integralIsTheIntegral(
    steps: Continuity.Steps,
    classical: Classical,
    integralDefinition: Kernel.Thm,
    hasUnique: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val i = Term.variable("i", Reals)
    for {
      ordered <- assume("a:real <= b:real")
      has <- assume("has_integral (f:real -> real) a b i")
      unfolding <- Conv.unfold(integralDefinition, List(f, a, b))
      chosen <- rightOf(unfolding)
      predicate <- chosen match {
        case App(_, predicate) => Right(predicate)
        case other             => Left(NotOfForm("select applied to a predicate", other))
      }
      choice <- classical.axiom(Classical.Choice)
      atReals = Kernel.instType(Map(Classical.TypeVariable -> Reals), choice)
      selected <- rules.specAll(atReals, List(predicate, i)).flatMap(reduced).flatMap(rules.mp(_, has))
      same <- rules.specAll(hasUnique, List(f, a, b, chosen, i)).flatMap(mp(_, Right(ordered), Right(selected), Right(has)))
      equal <- Conv.trans(unfolding, same)
      result <- rules.disch(has.conclusion, equal).flatMap(rules.disch(ordered.conclusion, _))
        .flatMap(rules.genAll(_, List(f, a, b, i)))
    } yield result
  }

  /* ------------------------------------------------------------------ the fundamental theorem */

  /**
   * [[HasFundamentalWithin]]. At a tolerance `e`, `T = e * inv (1 * ((b - a) + 1))` is each point's
   * share, and the gauge at `x` is chosen by `select` among the radii with `0 < d` that, where `x` is
   * in `[a, b]`, keep `abs (F y - F x - f x * (y - x)) <= T * abs (y - x)` for every `y` of `[a, b]`
   * nearer than `d`. Such a radius exists inside the interval by the relative derivative, including
   * at `y = x` where the error is zero, and outside it `1` will do; the classical case split is where
   * `SELECT` enters.
   *
   * **Only points of `[a, b]` are ever read**, and that is why the relative derivative is enough and
   * the textbook form is the one proved: the two ends of a piece are the only `y` the straddle asks
   * about, and the invariant below carries `a <= u` and `v <= b`, so both are in the interval.
   *
   * Over a division fine for that gauge the invariant is `u <= v` and, inside `[a, b]`,
   * `abs (s - (F v - F u)) <= T * (v - u)`: on a piece it is the error from each end to the tag, the
   * straddle inequality, and a join adds the two bounds. At `[a, b]` it is `T * (b - a) < e`.
   */
  private def fundamental(
    steps: Continuity.Steps,
    reals: RealTheory,
    magnitude: Magnitude,
    classical: Classical,
    hasDefinition: Kernel.Thm,
    withinDefinition: Kernel.Thm,
    induction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val bigF = Term.variable("Fn", Functions)
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val e = Term.variable("e", Reals)
    val x = Term.variable("x", Reals)
    val y = Term.variable("y", Reals)
    val u = Term.variable("u", Reals)
    val v = Term.variable("v", Reals)
    val w = Term.variable("w", Reals)
    val s = Term.variable("s", Reals)
    val t = Term.variable("t", Reals)
    val d = Term.variable("d", Reals)
    val F = "(Fn:real -> real)"
    val fx = "(f:real -> real) x:real"
    val Slopes = s"!x:real. a:real <= x /\\ x <= b:real ==> derivative_within $F a b x ((f:real -> real) x)"
    val Inside = "a:real <= x:real /\\ x <= b:real"
    val Range = "a:real <= y:real /\\ y <= b:real"

    for {
      ordered <- assume("a:real <= b:real")
      slopes <- assume(Slopes)
      positive <- assume("0 < e:real")
      measure <- at(lemma("!a:real b:real. a <= b ==> 0 <= b - a"), "a:real", "b:real").flatMap(mp(_, Right(ordered)))
      share <- Continuity.portion(steps, reals, "b:real - a:real", measure, 1, positive)
      tol = share.term
      tNonNegative <- at(lemma("!T:real. 0 < T ==> 0 <= T"), tol).flatMap(mp(_, Right(share.positive)))

      goodText = (radius: String) =>
        s"0 < $radius /\\ ($Inside ==> !y:real. $Range ==> abs (y - x) < $radius ==> abs ($F y - $F x - $fx * (y - x)) <= $tol * abs (y - x))"
      radiusPredicate <- Parser.term(theory, notation, s"\\d:real. ${goodText("d")}", Type.fun(Reals, Type.Bool))
      someRadius <- proposition(s"?d:real. ${goodText("d")}")

      /* ------------------------------------------- inside the interval, from the derivative */
      insideRadius <- for {
        inside <- proposition(Inside)
        assumedInside <- LogicError.lift(Kernel.assume(inside))
        slope <- rules.spec(x, slopes).flatMap(rules.mp(_, assumedInside))
        fxTerm <- real(fx)
        opened <- Conv.unfold(withinDefinition, List(bigF, a, b, x, fxTerm))
          .flatMap(eq => rightOf(eq).flatMap(Conv.betaNormalise).flatMap(Conv.trans(eq, _)))
          .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, slope)))
        tTerm <- real(tol)
        near <- rules.spec(tTerm, opened).flatMap(rules.mp(_, share.positive))
        result <- eliminateFrom(logic, near, List(d), body =>
          for {
            assumed <- LogicError.lift(Kernel.assume(body))
            dPositive <- rules.conjElim1(assumed)
            within <- rules.conjElim2(assumed)
            rangeTerm <- proposition(Range)
            range <- LogicError.lift(Kernel.assume(rangeTerm))
            closeTerm <- proposition("abs (y:real - x:real) < d:real")
            close <- LogicError.lift(Kernel.assume(closeTerm))
            yNonNeg <- at(magnitude.fact(Magnitude.AbsNonNegative), "y:real - x:real")
            split <- magnitude.order.fact(Order.LeCases).flatMap(c => at(Right(c), "0:real", "abs (y:real - x:real)"))
              .flatMap(rules.mp(_, yNonNeg))
            errorAt = s"$F y - $F x - $fx * (y - x)"

            apart <- for {
              away <- assume("0 < abs (y:real - x:real)")
              lowShift <- rules.conjElim1(range).flatMap(low =>
                at(lemma("!a:real x:real y:real. a <= y ==> a <= x + (y - x)"), "a:real", "x:real", "y:real").flatMap(mp(_, Right(low))))
              highShift <- rules.conjElim2(range).flatMap(high =>
                at(lemma("!y:real b:real x:real. y <= b ==> x + (y - x) <= b"), "y:real", "b:real", "x:real").flatMap(mp(_, Right(high))))
              admissible <- rules.conjIntro(lowShift, highShift).flatMap(rules.conjIntro(close, _)).flatMap(rules.conjIntro(away, _))
              h <- real("y:real - x:real")
              bound <- rules.spec(h, within).flatMap(rules.mp(_, admissible))
              argument <- at(lemma("!x:real y:real. x + (y - x) = y"), "x:real", "y:real")
              values <- Conv.apTerm(bigF, argument)
              regrouped <- at(lemma("!A:real B:real C:real M:real. A = B ==> A - C - M = B - C - M"),
                s"$F (x:real + (y:real - x))", s"$F y:real", s"$F x:real", s"$fx * (y:real - x)")
                .flatMap(mp(_, Right(values)))
              absFn <- Parser.term(theory, notation, "abs", Functions)
              sameMagnitude <- Conv.apTerm(absFn, regrouped)
              result <- at(lemma("!P:real Q:real R:real. P = Q ==> P < R ==> Q <= R"),
                s"abs ($F (x:real + (y:real - x)) - $F x - $fx * (y - x))", s"abs ($errorAt)", s"$tol * abs (y:real - x:real)")
                .flatMap(mp(_, Right(sameMagnitude), Right(bound)))
            } yield result

            still <- for {
              none <- assume("0 = abs (y:real - x:real)").flatMap(Conv.sym)
              zero <- at(magnitude.fact(Magnitude.AbsZero), "y:real - x:real").flatMap(mp(_, Right(none)))
              same <- at(lemma("!y:real x:real. y - x = 0 ==> y = x"), "y:real", "x:real").flatMap(mp(_, Right(zero)))
              values <- Conv.apTerm(bigF, same)
              times <- Parser.term(theory, notation, s"real_mul ($fx)", Functions).flatMap(Conv.apTerm(_, zero))
              errorZero <- at(lemma("!P:real Q:real m:real k:real. P = Q ==> m * k = m * 0 ==> P - Q - m * k = 0"),
                s"$F y:real", s"$F x:real", fx, "y:real - x:real").flatMap(mp(_, Right(values), Right(times)))
              itself <- at(magnitude.fact(Magnitude.OfNonNegative), errorAt)
                .flatMap(mp(_, at(lemma("!E:real. E = 0 ==> 0 <= E"), errorAt).flatMap(mp(_, Right(errorZero)))))
              result <- at(lemma("!A:real E:real T:real K:real. A = E ==> E = 0 ==> 0 <= T ==> 0 <= K ==> A <= T * K"),
                s"abs ($errorAt)", errorAt, tol, "abs (y:real - x:real)")
                .flatMap(mp(_, Right(itself), Right(errorZero), Right(tNonNegative), Right(yNonNeg)))
            } yield result

            bounded <- rules.disjElim(split, apart, still)
            everyY <- rules.disch(closeTerm, bounded).flatMap(rules.disch(rangeTerm, _)).flatMap(rules.gen(y, _))
            guarded <- rules.disch(inside, everyY)
            both <- rules.conjIntro(dPositive, guarded)
            result <- introduce(logic, someRadius, List(d), target =>
              proving(target, both))
          } yield result)
      } yield result

      /* ------------------------------------------- outside it, any positive radius */
      outsideRadius <- for {
        inside <- proposition(Inside)
        outside <- logic.mkNot(inside)
        assumedOutside <- LogicError.lift(Kernel.assume(outside))
        one <- real("1:real")
        result <- introduce(logic, someRadius, List(one), target =>
          for {
            halves <- logic.destConj(target).toRight(NotOfForm("a conjunction", target))
            onePositive <- lemma("(0:real) < 1")
            implication <- logic.destImp(halves._2).toRight(NotOfForm("an implication", halves._2))
            assumedInside <- LogicError.lift(Kernel.assume(inside))
            absurd <- rules.notElim(assumedOutside, assumedInside)
            anything <- rules.falsityElim(implication._2, absurd)
            guarded <- rules.disch(inside, anything)
            both <- rules.conjIntro(onePositive, guarded)
          } yield both)
      } yield result

      inside <- proposition(Inside)
      everyPoint <- classical.cases(inside, insideRadius, outsideRadius)

      /* ------------------------------------------- the gauge, and what it keeps at each point */
      choice <- classical.axiom(Classical.Choice)
      atReals = Kernel.instType(Map(Classical.TypeVariable -> Reals), choice)
      pointPredicate = radiusPredicate
      gaugeTerm <- Parser.term(theory, notation, s"\\x:real. select (\\d:real. ${goodText("d")})", Functions)
      keeps <- eliminateFrom(logic, everyPoint, List(d), body =>
        for {
          assumed <- LogicError.lift(Kernel.assume(body))
          selected <- rules.specAll(atReals, List(pointPredicate, d)).flatMap(reduced)
          result <- rules.mp(selected, assumed)
        } yield result)
      chosenRadius = s"select (\\d:real. ${goodText("d")})"
      gaugeFacts <- rules.gen(x, keeps)

      /* ------------------------------------------- the invariant over a division */
      invariant <- Parser.term(theory, notation,
        s"\\u:real. \\v:real. \\s:real. u <= v /\\ (a:real <= u ==> v <= b:real ==> abs (s - ($F v - $F u)) <= $tol * (v - u))",
        Properties)
      instance <- rules.specAll(induction, List(f, gaugeTerm, invariant)).flatMap(reduced)

      base <- for {
        conditionText <- Right(s"u:real <= x:real /\\ x <= v:real /\\ v - u < $chosenRadius")
        conditionTerm <- proposition(conditionText)
        assumed <- LogicError.lift(Kernel.assume(conditionTerm))
        parts <- conjuncts(logic, assumed, 3)
        List(ux, xv, short) = parts: @unchecked
        ordered <- at(lemma("!u:real x:real v:real. u <= x ==> x <= v ==> u <= v"), "u:real", "x:real", "v:real")
          .flatMap(mp(_, Right(ux), Right(xv)))
        lowTerm <- proposition("a:real <= u:real")
        highTerm <- proposition("v:real <= b:real")
        low <- LogicError.lift(Kernel.assume(lowTerm))
        high <- LogicError.lift(Kernel.assume(highTerm))
        ax <- at(lemma("!a:real u:real x:real. a <= u ==> u <= x ==> a <= x"), "a:real", "u:real", "x:real")
          .flatMap(mp(_, Right(low), Right(ux)))
        xb <- at(lemma("!x:real v:real b:real. x <= v ==> v <= b ==> x <= b"), "x:real", "v:real", "b:real")
          .flatMap(mp(_, Right(xv), Right(high)))
        here <- conj(Right(ax), Right(xb))
        atX <- rules.spec(x, gaugeFacts)
        straddle <- rules.conjElim2(atX).flatMap(rules.mp(_, here))

        rightDistance <- at(magnitude.fact(Magnitude.OfNonNegative), "v:real - x:real")
          .flatMap(mp(_, at(lemma("!x:real v:real. x <= v ==> 0 <= v - x"), "x:real", "v:real").flatMap(mp(_, Right(xv)))))
        leftDistance <- at(magnitude.fact(Magnitude.OfNonPositive), "u:real - x:real")
          .flatMap(mp(_, at(lemma("!u:real x:real. u <= x ==> u - x <= 0"), "u:real", "x:real").flatMap(mp(_, Right(ux)))))
        rightClose <- at(lemma("!A:real v:real x:real u:real G:real. A = v - x ==> u <= x ==> v - u < G ==> A < G"),
          "abs (v:real - x:real)", "v:real", "x:real", "u:real", chosenRadius).flatMap(mp(_, Right(rightDistance), Right(ux), Right(short)))
        leftClose <- at(lemma("!A:real u:real x:real v:real G:real. A = -(u - x) ==> x <= v ==> v - u < G ==> A < G"),
          "abs (u:real - x:real)", "u:real", "x:real", "v:real", chosenRadius).flatMap(mp(_, Right(leftDistance), Right(xv), Right(short)))
        av <- at(lemma("!a:real u:real x:real v:real. a <= u ==> u <= x ==> x <= v ==> a <= v"), "a:real", "u:real", "x:real", "v:real")
          .flatMap(mp(_, Right(low), Right(ux), Right(xv)))
        ub <- at(lemma("!u:real x:real v:real b:real. u <= x ==> x <= v ==> v <= b ==> u <= b"), "u:real", "x:real", "v:real", "b:real")
          .flatMap(mp(_, Right(ux), Right(xv), Right(high)))
        vIn <- conj(Right(av), Right(high))
        uIn <- conj(Right(low), Right(ub))
        atV <- rules.spec(v, straddle).flatMap(rules.mp(_, vIn)).flatMap(rules.mp(_, rightClose))
        atU <- rules.spec(u, straddle).flatMap(rules.mp(_, uIn)).flatMap(rules.mp(_, leftClose))
        tMul <- Parser.term(theory, notation, s"real_mul ($tol)", Functions)
        rightScale <- Conv.apTerm(tMul, rightDistance)
        leftScale <- Conv.apTerm(tMul, leftDistance)
        ev = s"$F v:real - $F x:real - $fx * (v - x)"
        eu = s"$F u:real - $F x:real - $fx * (u - x)"
        vBound <- at(lemma("!A:real K:real L:real. A <= K ==> K = L ==> A <= L"),
          s"abs ($ev)", s"$tol * abs (v:real - x:real)", s"$tol * (v:real - x:real)").flatMap(mp(_, Right(atV), Right(rightScale)))
        uBound <- at(lemma("!A:real K:real L:real. A <= K ==> K = L ==> A <= L"),
          s"abs ($eu)", s"$tol * abs (u:real - x:real)", s"$tol * (-(u:real - x:real))").flatMap(mp(_, Right(atU), Right(leftScale)))
        vPlus <- at(magnitude.fact(Magnitude.AbsAbove), ev)
        vMinus <- at(magnitude.fact(Magnitude.AbsAboveNegation), ev)
        uPlus <- at(magnitude.fact(Magnitude.AbsAbove), eu)
        uMinus <- at(magnitude.fact(Magnitude.AbsAboveNegation), eu)
        through = "!E:real A:real L:real. E <= A ==> A <= L ==> E <= L"
        vUp <- at(lemma(through), ev, s"abs ($ev)", s"$tol * (v:real - x:real)").flatMap(mp(_, Right(vPlus), Right(vBound)))
        vDown <- at(lemma(through), s"-($ev)", s"abs ($ev)", s"$tol * (v:real - x:real)").flatMap(mp(_, Right(vMinus), Right(vBound)))
        uUp <- at(lemma(through), eu, s"abs ($eu)", s"$tol * (-(u:real - x:real))").flatMap(mp(_, Right(uPlus), Right(uBound)))
        uDown <- at(lemma(through), s"-($eu)", s"abs ($eu)", s"$tol * (-(u:real - x:real))").flatMap(mp(_, Right(uMinus), Right(uBound)))
        target = s"$fx * (v:real - u:real) - ($F v - $F u)"
        cases <- at(magnitude.fact(Magnitude.AbsCases), target)
        itself <- assume(s"abs ($target) = $target").flatMap(eq =>
          at(lemma("!A:real m:real Fv:real Fu:real Fx:real u:real v:real x:real T:real. A = m * (v - u) - (Fv - Fu) ==> " +
            "-(Fv - Fx - m * (v - x)) <= T * (v - x) ==> Fu - Fx - m * (u - x) <= T * (-(u - x)) ==> A <= T * (v - u)"),
            s"abs ($target)", fx, s"$F v:real", s"$F u:real", s"$F x:real", "u:real", "v:real", "x:real", tol)
            .flatMap(mp(_, Right(eq), Right(vDown), Right(uUp))))
        negated <- assume(s"abs ($target) = -($target)").flatMap(eq =>
          at(lemma("!A:real m:real Fv:real Fu:real Fx:real u:real v:real x:real T:real. A = -(m * (v - u) - (Fv - Fu)) ==> " +
            "Fv - Fx - m * (v - x) <= T * (v - x) ==> -(Fu - Fx - m * (u - x)) <= T * (-(u - x)) ==> A <= T * (v - u)"),
            s"abs ($target)", fx, s"$F v:real", s"$F u:real", s"$F x:real", "u:real", "v:real", "x:real", tol)
            .flatMap(mp(_, Right(eq), Right(vUp), Right(uDown))))
        bound <- rules.disjElim(cases, itself, negated)
        guarded <- rules.disch(highTerm, bound).flatMap(rules.disch(lowTerm, _))
        both <- rules.conjIntro(ordered, guarded)
        result <- rules.disch(conditionTerm, both).flatMap(rules.genAll(_, List(u, v, x)))
      } yield result

      step <- for {
        firstTerm <- proposition(s"u:real <= v:real /\\ (a:real <= u ==> v <= b:real ==> abs (s:real - ($F v - $F u)) <= $tol * (v - u))")
        secondTerm <- proposition(s"v:real <= w:real /\\ (a:real <= v ==> w <= b:real ==> abs (t:real - ($F w - $F v)) <= $tol * (w - v))")
        first <- LogicError.lift(Kernel.assume(firstTerm))
        second <- LogicError.lift(Kernel.assume(secondTerm))
        uv <- rules.conjElim1(first)
        vw <- rules.conjElim1(second)
        ordered <- at(lemma("!u:real v:real w:real. u <= v ==> v <= w ==> u <= w"), "u:real", "v:real", "w:real")
          .flatMap(mp(_, Right(uv), Right(vw)))
        lowTerm <- proposition("a:real <= u:real")
        highTerm <- proposition("w:real <= b:real")
        low <- LogicError.lift(Kernel.assume(lowTerm))
        high <- LogicError.lift(Kernel.assume(highTerm))
        av <- at(lemma("!a:real u:real v:real. a <= u ==> u <= v ==> a <= v"), "a:real", "u:real", "v:real").flatMap(mp(_, Right(low), Right(uv)))
        vb <- at(lemma("!v:real w:real b:real. v <= w ==> w <= b ==> v <= b"), "v:real", "w:real", "b:real").flatMap(mp(_, Right(vw), Right(high)))
        leftBound <- rules.conjElim2(first).flatMap(mp(_, Right(low), Right(vb)))
        rightBound <- rules.conjElim2(second).flatMap(mp(_, Right(av), Right(high)))
        es = s"s:real - ($F v:real - $F u:real)"
        et = s"t:real - ($F w:real - $F v:real)"
        sPlus <- at(magnitude.fact(Magnitude.AbsAbove), es)
        sMinus <- at(magnitude.fact(Magnitude.AbsAboveNegation), es)
        tPlus <- at(magnitude.fact(Magnitude.AbsAbove), et)
        tMinus <- at(magnitude.fact(Magnitude.AbsAboveNegation), et)
        target = s"s:real + t:real - ($F w:real - $F u:real)"
        cases <- at(magnitude.fact(Magnitude.AbsCases), target)
        names = List(s"abs ($target)", "s:real", "t:real", s"$F u:real", s"$F v:real", s"$F w:real",
          s"abs ($es)", s"abs ($et)", "u:real", "v:real", "w:real", tol)
        itself <- assume(s"abs ($target) = $target").flatMap(eq =>
          at(lemma("!A:real s:real t:real Fu:real Fv:real Fw:real P:real Q:real u:real v:real w:real T:real. " +
            "A = s + t - (Fw - Fu) ==> s - (Fv - Fu) <= P ==> t - (Fw - Fv) <= Q ==> " +
            "P <= T * (v - u) ==> Q <= T * (w - v) ==> A <= T * (w - u)"), names*)
            .flatMap(mp(_, Right(eq), Right(sPlus), Right(tPlus), Right(leftBound), Right(rightBound))))
        negated <- assume(s"abs ($target) = -($target)").flatMap(eq =>
          at(lemma("!A:real s:real t:real Fu:real Fv:real Fw:real P:real Q:real u:real v:real w:real T:real. " +
            "A = -(s + t - (Fw - Fu)) ==> -(s - (Fv - Fu)) <= P ==> -(t - (Fw - Fv)) <= Q ==> " +
            "P <= T * (v - u) ==> Q <= T * (w - v) ==> A <= T * (w - u)"), names*)
            .flatMap(mp(_, Right(eq), Right(sMinus), Right(tMinus), Right(leftBound), Right(rightBound))))
        bound <- rules.disjElim(cases, itself, negated)
        guarded <- rules.disch(highTerm, bound).flatMap(rules.disch(lowTerm, _))
        both <- rules.conjIntro(ordered, guarded)
        result <- rules.disch(secondTerm, both).flatMap(rules.disch(firstTerm, _)).flatMap(rules.genAll(_, List(u, v, w, s, t)))
      } yield result

      everyDivision <- mp(instance, Right(base), Right(step))

      /* ------------------------------------------- over [a, b], under the tolerance */
      close <- for {
        sumTerm <- Parser.proposition(theory, notation, s"fine_sum (f:real -> real) (\\x:real. $chosenRadius) a b s")
        sum <- LogicError.lift(Kernel.assume(sumTerm))
        invariantAt <- rules.specAll(everyDivision, List(a, b, s)).flatMap(rules.mp(_, sum))
        reflexive <- lemma("!a:real. a <= a")
        aa <- rules.spec(a, reflexive)
        bb <- rules.spec(b, reflexive)
        bound <- rules.conjElim2(invariantAt).flatMap(mp(_, Right(aa), Right(bb)))
        result <- at(lemma("!A:real T:real a:real b:real e:real. A <= T * (b - a) ==> 1 * ((b - a) + 1) * T = e ==> 0 < T ==> A < e"),
          s"abs (s:real - ($F b - $F a))", tol, "a:real", "b:real", "e:real")
          .flatMap(mp(_, Right(bound), Right(share.equation), Right(share.positive)))
        closed <- rules.disch(sumTerm, result).flatMap(rules.gen(s, _))
      } yield closed

      positiveGauge <- rules.spec(x, gaugeFacts).flatMap(rules.conjElim1).flatMap(rules.gen(x, _))
      bodyNormal <- rules.conjIntro(positiveGauge, close)
      value <- real(s"$F b - $F a")
      unfolded <- Conv.unfold(hasDefinition, List(f, a, b, value))
      statement <- rightOf(unfolded)
      // At this proof's own `e`: stripping the quantifier would invent a name for the binder.
      atE <- statement match {
        case App(_, predicate) => LogicError.lift(Term.app(predicate, e)).flatMap(Conv.betaRoot).flatMap(rightOf)
        case other             => Left(NotOfForm("a universal quantification", other))
      }
      implication <- logic.destImp(atE).toRight(NotOfForm("an implication", atE))
      existsGauge = implication._2
      witnessed <- introduce(logic, existsGauge, List(gaugeTerm), target => shaped(target, bodyNormal))
      everyTolerance <- rules.disch(positive.conclusion, witnessed).flatMap(rules.gen(e, _))
      folded <- Conv.sym(unfolded).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, everyTolerance)))
      result <- rules.disch(slopes.conclusion, folded).flatMap(rules.disch(ordered.conclusion, _))
        .flatMap(rules.genAll(_, List(bigF, f, a, b)))
    } yield result
  }

  private val SlopesWithin: String =
    "!x:real. a:real <= x /\\ x <= b:real ==> derivative_within (Fn:real -> real) a b x ((f:real -> real) x)"

  private val TwoSidedSlopes: String = "!x:real. a:real <= x /\\ x <= b:real ==> derivative (Fn:real -> real) x ((f:real -> real) x)"

  /**
   * [[HasFundamental]] from [[HasFundamentalWithin]]: a derivative at a point is a derivative there
   * relative to every interval, which is `Derivative.WithinOfDerivative`.
   */
  private def twoSided(steps: Continuity.Steps, within: Kernel.Thm, ofDerivative: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val bigF = Term.variable("Fn", Functions)
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val x = Term.variable("x", Reals)
    for {
      ordered <- assume("a:real <= b:real")
      slopes <- assume(TwoSidedSlopes)
      insideTerm <- proposition("a:real <= x:real /\\ x <= b:real")
      inside <- LogicError.lift(Kernel.assume(insideTerm))
      slope <- rules.spec(x, slopes).flatMap(rules.mp(_, inside))
      fx <- real("(f:real -> real) x:real")
      relative <- rules.specAll(ofDerivative, List(bigF, a, b, x, fx)).flatMap(rules.mp(_, slope))
      everyPoint <- rules.disch(insideTerm, relative).flatMap(rules.gen(x, _))
      has <- rules.specAll(within, List(bigF, f, a, b)).flatMap(mp(_, Right(ordered), Right(everyPoint)))
      result <- rules.disch(slopes.conclusion, has).flatMap(rules.disch(ordered.conclusion, _))
        .flatMap(rules.genAll(_, List(bigF, f, a, b)))
    } yield result
  }

  /** [[Fundamental]] or [[FundamentalWithin]]: the statement about `has_integral` read through [[Unique]]. */
  private def integralOfDerivative(
    steps: Continuity.Steps,
    unique: Kernel.Thm,
    hasFundamental: Kernel.Thm,
    Slopes: String
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val bigF = Term.variable("Fn", Functions)
    val f = Term.variable("f", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    for {
      ordered <- assume("a:real <= b:real")
      slopes <- assume(Slopes)
      has <- rules.specAll(hasFundamental, List(bigF, f, a, b)).flatMap(mp(_, Right(ordered), Right(slopes)))
      value <- real("(Fn:real -> real) b - Fn a")
      named <- rules.specAll(unique, List(f, a, b, value)).flatMap(mp(_, Right(ordered), Right(has)))
      result <- rules.disch(slopes.conclusion, named).flatMap(rules.disch(ordered.conclusion, _))
        .flatMap(rules.genAll(_, List(bigF, f, a, b)))
    } yield result
  }

  /* ------------------------------------------------------------------ linearity */

  /** The body of a universal quantification at a variable of this proof's choosing. */
  private def forallAt(term: Term, variable: Term): Either[LogicError, Term] = term match {
    case App(_, predicate) => LogicError.lift(Term.app(predicate, variable)).flatMap(Conv.betaRoot).flatMap(rightOf)
    case other             => Left(NotOfForm("a universal quantification", other))
  }

  private def forallAtAll(term: Term, variables: List[Term]): Either[LogicError, Term] =
    variables.foldLeft[Either[LogicError, Term]](Right(term))((acc, variable) => acc.flatMap(forallAt(_, variable)))

  /**
   * [[SumLinear]]: the induction at the property "splits into a sum for `f` and one for `g` over the
   * same division". A piece of the combination is `(p * f x + q * g x) * (v - u)`, which is `p` times
   * the piece of `f` plus `q` times the piece of `g` at the same tag; a join adds both splits.
   */
  private def sumsOfCombination(steps: Continuity.Steps, induction: Kernel.Thm, piece: Kernel.Thm, join: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val p = Term.variable("p", Reals)
    val q = Term.variable("q", Reals)
    val d = Term.variable("d", Functions)
    val List(u, v, w, x, s, t, s1, s2, t1, t2) = List("u", "v", "w", "x", "s", "t", "s1", "s2", "t1", "t2").map(Term.variable(_, Reals)): @unchecked
    def splits(uu: String, vv: String, ss: String) =
      s"?s1:real. ?s2:real. fine_sum (f:real -> real) (d:real -> real) $uu $vv s1 /\\ fine_sum (g:real -> real) d $uu $vv s2 /\\ $ss = (p:real) * s1 + (q:real) * s2"
    for {
      combination <- Parser.term(theory, notation, "\\x:real. (p:real) * (f:real -> real) x + (q:real) * (g:real -> real) x", Functions)
      property <- Parser.term(theory, notation, s"\\u:real. \\v:real. \\s:real. ${splits("u", "v", "s")}", Properties)
      instance <- rules.specAll(induction, List(combination, d, property)).flatMap(reduced)
      first <- logic.destImp(instance.conclusion).toRight(NotOfForm("an implication", instance.conclusion))
      second <- logic.destImp(first._2).toRight(NotOfForm("an implication", first._2))
      baseTerm = first._1
      stepTerm = second._1

      base <- for {
        body <- forallAtAll(baseTerm, List(u, v, x))
        implication <- logic.destImp(body).toRight(NotOfForm("an implication", body))
        (condition, split) = implication
        assumed <- LogicError.lift(Kernel.assume(condition))
        forF <- rules.specAll(piece, List(f, d, u, v, x)).flatMap(rules.mp(_, assumed))
        forG <- rules.specAll(piece, List(g, d, u, v, x)).flatMap(rules.mp(_, assumed))
        equation <- at(lemma("!p:real q:real F:real G:real v:real u:real. (p * F + q * G) * (v - u) = p * (F * (v - u)) + q * (G * (v - u))"),
          "p:real", "q:real", "(f:real -> real) x", "(g:real -> real) x", "v:real", "u:real")
        pieceF <- real("(f:real -> real) x * (v:real - u)")
        pieceG <- real("(g:real -> real) x * (v:real - u)")
        witnessed <- introduce(logic, split, List(pieceF, pieceG), target =>
          conj(Right(forF), conj(Right(forG), Right(equation))).flatMap(proving(target, _)))
        result <- rules.disch(condition, witnessed).flatMap(rules.genAll(_, List(u, v, x)))
        _ <- proving(baseTerm, result)
      } yield result

      step <- for {
        body <- forallAtAll(stepTerm, List(u, v, w, s, t))
        firstImp <- logic.destImp(body).toRight(NotOfForm("an implication", body))
        secondImp <- logic.destImp(firstImp._2).toRight(NotOfForm("an implication", firstImp._2))
        (left, right, joined) = (firstImp._1, secondImp._1, secondImp._2)
        opened <- eliminate(logic, left, List(s1, s2), leftBody =>
          eliminate(logic, right, List(t1, t2), rightBody =>
            for {
              l <- LogicError.lift(Kernel.assume(leftBody)).flatMap(conjuncts(logic, _, 3))
              r <- LogicError.lift(Kernel.assume(rightBody)).flatMap(conjuncts(logic, _, 3))
              List(fs1, gs2, sIs) = l: @unchecked
              List(ft1, gt2, tIs) = r: @unchecked
              forF <- rules.specAll(join, List(f, d, u, v, w, s1, t1)).flatMap(mp(_, Right(fs1), Right(ft1)))
              forG <- rules.specAll(join, List(g, d, u, v, w, s2, t2)).flatMap(mp(_, Right(gs2), Right(gt2)))
              sums <- at(lemma("!s:real t:real p:real q:real a:real b:real c:real e:real. s = p * a + q * b ==> t = p * c + q * e ==> s + t = p * (a + c) + q * (b + e)"),
                "s:real", "t:real", "p:real", "q:real", "s1:real", "s2:real", "t1:real", "t2:real")
                .flatMap(mp(_, Right(sIs), Right(tIs)))
              sumF <- real("s1:real + t1")
              sumG <- real("s2:real + t2")
              witnessed <- introduce(logic, joined, List(sumF, sumG), target =>
                conj(Right(forF), conj(Right(forG), Right(sums))).flatMap(proving(target, _)))
            } yield witnessed))
        result <- rules.disch(right, opened).flatMap(rules.disch(left, _)).flatMap(rules.genAll(_, List(u, v, w, s, t)))
        _ <- proving(stepTerm, result)
      } yield result

      everySum <- mp(instance, Right(base), Right(step))
      result <- rules.specAll(everySum, List(u, v, s)).flatMap(rules.genAll(_, List(f, g, p, q, d, u, v, s)))
    } yield result
  }

  /**
   * [[HasLinear]]. At a tolerance `e`, `f` and `g` each have a gauge at their share of it, `Continuity`'s
   * `share` for the coefficients `p` and `q`; their pointwise minimum is fine for both, and a fine sum of
   * the combination splits by [[SumLinear]] into one of each over the same division. So its distance
   * from `p * i + q * j` is at most `abs p` times the one and `abs q` times the other, each under half.
   * It needs no `a <= b`: it is a statement about the sums there are.
   */
  private def linearity(
    steps: Continuity.Steps,
    reals: RealTheory,
    magnitude: Magnitude,
    hasDefinition: Kernel.Thm,
    gauge: Kernel.Thm,
    decomposed: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val a = Term.variable("a", Reals)
    val b = Term.variable("b", Reals)
    val i = Term.variable("i", Reals)
    val j = Term.variable("j", Reals)
    val p = Term.variable("p", Reals)
    val q = Term.variable("q", Reals)
    val e = Term.variable("e", Reals)
    val x = Term.variable("x", Reals)
    val s = Term.variable("s", Reals)
    val s1 = Term.variable("s1", Reals)
    val s2 = Term.variable("s2", Reals)
    val g1 = Term.variable("g1", Functions)
    val g2 = Term.variable("g2", Functions)
    val Combination = "\\x:real. (p:real) * (f:real -> real) x + (q:real) * (g:real -> real) x"
    def opened(function: Term, value: Term, text: String): Either[LogicError, (Kernel.Thm, Kernel.Thm)] =
      for {
        statement <- proposition(text)
        assumed <- LogicError.lift(Kernel.assume(statement))
        equation <- Conv.unfold(hasDefinition, List(function, a, b, value))
        result <- LogicError.lift(Kernel.eqMp(equation, assumed))
      } yield (assumed, result)
    for {
      forF <- opened(f, i, "has_integral (f:real -> real) a b i")
      forG <- opened(g, j, "has_integral (g:real -> real) a b j")
      positive <- assume("0 < e:real")
      shareP <- Continuity.share(steps, reals, magnitude, "p:real", positive)
      shareQ <- Continuity.share(steps, reals, magnitude, "q:real", positive)
      tP <- real(shareP.term)
      tQ <- real(shareQ.term)
      gaugeF <- rules.spec(tP, forF._2).flatMap(rules.mp(_, shareP.positive))
      gaugeG <- rules.spec(tQ, forG._2).flatMap(rules.mp(_, shareQ.positive))
      combination <- Parser.term(theory, notation, Combination, Functions)
      value <- real("(p:real) * i + (q:real) * j")
      unfolded <- Conv.unfold(hasDefinition, List(combination, a, b, value))
      statement <- rightOf(unfolded)
      atE <- forallAt(statement, e)
      target <- logic.destImp(atE).map(_._2).toRight(NotOfForm("an implication", atE))

      witnessed <- eliminateFrom(logic, gaugeF, List(g1), bodyF =>
        eliminateFrom(logic, gaugeG, List(g2), bodyG =>
          for {
            one <- LogicError.lift(Kernel.assume(bodyF))
            two <- LogicError.lift(Kernel.assume(bodyG))
            onePositive <- rules.conjElim1(one)
            oneClose <- rules.conjElim2(one)
            twoPositive <- rules.conjElim1(two)
            twoClose <- rules.conjElim2(two)
            smaller <- Parser.term(theory, notation, "\\x:real. min ((g1:real -> real) x) ((g2:real -> real) x)", Functions)
            bothPositive <- for {
              p1 <- rules.spec(x, onePositive)
              p2 <- rules.spec(x, twoPositive)
              least <- Continuity.minimumOf(steps, magnitude, "(g1:real -> real) x:real", "(g2:real -> real) x:real", p1, p2)
              result <- rules.gen(x, least)
            } yield result
            minLeft <- at(magnitude.fact(Magnitude.MinBelowLeft), "(g1:real -> real) x:real", "(g2:real -> real) x:real").flatMap(rules.gen(x, _))
            minRight <- at(magnitude.fact(Magnitude.MinBelowRight), "(g1:real -> real) x:real", "(g2:real -> real) x:real").flatMap(rules.gen(x, _))
            sumTerm <- proposition(s"fine_sum ($Combination) (\\x:real. min ((g1:real -> real) x) ((g2:real -> real) x)) a b s")
            sum <- LogicError.lift(Kernel.assume(sumTerm))
            split <- rules.specAll(decomposed, List(f, g, p, q, smaller, a, b, s)).flatMap(rules.mp(_, sum))
            close <- eliminateFrom(logic, split, List(s1, s2), body =>
              for {
                parts <- LogicError.lift(Kernel.assume(body)).flatMap(conjuncts(logic, _, 3))
                List(fs1, gs2, sIs) = parts: @unchecked
                forOne <- rules.specAll(gauge, List(f, smaller, g1, a, b, s1)).flatMap(reduced).flatMap(mp(_, Right(minLeft), Right(fs1)))
                forTwo <- rules.specAll(gauge, List(g, smaller, g2, a, b, s2)).flatMap(reduced).flatMap(mp(_, Right(minRight), Right(gs2)))
                nearI <- rules.spec(s1, oneClose).flatMap(rules.mp(_, forOne))
                nearJ <- rules.spec(s2, twoClose).flatMap(rules.mp(_, forTwo))
                regrouped <- at(lemma("!s:real p:real q:real a:real b:real i:real j:real. s = p * a + q * b ==> s - (p * i + q * j) = p * (a - i) + q * (b - j)"),
                  "s:real", "p:real", "q:real", "s1:real", "s2:real", "i:real", "j:real").flatMap(mp(_, Right(sIs)))
                absFn <- Parser.term(theory, notation, "abs", Functions)
                sameAbs <- Conv.apTerm(absFn, regrouped)
                triangle <- at(magnitude.fact(Magnitude.Triangle), "(p:real) * (s1 - i)", "(q:real) * (s2 - j)")
                splitP <- at(magnitude.fact(Magnitude.Multiplicative), "p:real", "s1:real - i")
                splitQ <- at(magnitude.fact(Magnitude.Multiplicative), "q:real", "s2:real - j")
                scaled = "!Y:real P:real A:real T:real. Y = P * A ==> 0 <= P ==> A < T ==> Y <= P * T"
                upP <- at(lemma(scaled), "abs ((p:real) * (s1 - i))", "abs (p:real)", "abs (s1:real - i)", shareP.term)
                  .flatMap(mp(_, Right(splitP), at(magnitude.fact(Magnitude.AbsNonNegative), "p:real"), Right(nearI)))
                upQ <- at(lemma(scaled), "abs ((q:real) * (s2 - j))", "abs (q:real)", "abs (s2:real - j)", shareQ.term)
                  .flatMap(mp(_, Right(splitQ), at(magnitude.fact(Magnitude.AbsNonNegative), "q:real"), Right(nearJ)))
                half = "!P:real T:real e:real. 2 * (P + 1) * T = e ==> 0 < T ==> P * T < e / 2"
                halfP <- at(lemma(half), "abs (p:real)", shareP.term, "e:real").flatMap(mp(_, Right(shareP.equation), Right(shareP.positive)))
                halfQ <- at(lemma(half), "abs (q:real)", shareQ.term, "e:real").flatMap(mp(_, Right(shareQ.equation), Right(shareQ.positive)))
                result <- at(lemma("!E:real X:real Y:real Z:real Y1:real Z1:real e:real. E = X ==> X <= Y + Z ==> Y <= Y1 ==> Z <= Z1 ==> Y1 < e / 2 ==> Z1 < e / 2 ==> E < e"),
                    "abs (s:real - ((p:real) * i + (q:real) * j))", "abs ((p:real) * (s1 - i) + (q:real) * (s2 - j))",
                    "abs ((p:real) * (s1 - i))", "abs ((q:real) * (s2 - j))",
                    s"abs (p:real) * ${shareP.term}", s"abs (q:real) * ${shareQ.term}", "e:real")
                  .flatMap(mp(_, Right(sameAbs), Right(triangle), Right(upP), Right(upQ), Right(halfP), Right(halfQ)))
              } yield result)
            everySum <- rules.disch(sumTerm, close).flatMap(rules.gen(s, _))
            body <- rules.conjIntro(bothPositive, everySum)
            result <- introduce(logic, target, List(smaller), shapedTarget => shaped(shapedTarget, body))
          } yield result))
      everyTolerance <- rules.disch(positive.conclusion, witnessed).flatMap(rules.gen(e, _))
      folded <- Conv.sym(unfolded).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, everyTolerance)))
      result <- rules.disch(forG._1.conclusion, folded).flatMap(rules.disch(forF._1.conclusion, _))
        .flatMap(rules.genAll(_, List(f, g, a, b, i, j, p, q)))
    } yield result
  }

  /** [[Linear]]: [[HasLinear]] read through [[Unique]]. */
  private def integralOfCombination(steps: Continuity.Steps, unique: Kernel.Thm, hasLinear: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val List(a, b, i, j, p, q) = List("a", "b", "i", "j", "p", "q").map(Term.variable(_, Reals)): @unchecked
    for {
      ordered <- assume("a:real <= b:real")
      hasF <- assume("has_integral (f:real -> real) a b i")
      hasG <- assume("has_integral (g:real -> real) a b j")
      combined <- rules.specAll(hasLinear, List(f, g, a, b, i, j, p, q)).flatMap(mp(_, Right(hasF), Right(hasG)))
      combination <- Parser.term(theory, notation, "\\x:real. (p:real) * (f:real -> real) x + (q:real) * (g:real -> real) x", Functions)
      value <- real("(p:real) * i + (q:real) * j")
      named <- rules.specAll(unique, List(combination, a, b, value)).flatMap(mp(_, Right(ordered), Right(combined)))
      result <- rules.disch(hasG.conclusion, named).flatMap(rules.disch(hasF.conclusion, _)).flatMap(rules.disch(ordered.conclusion, _))
        .flatMap(rules.genAll(_, List(f, g, a, b, i, j, p, q)))
    } yield result
  }

  /* ------------------------------------------------------------------ by parts, by substitution */

  private val PartsSlopes: List[String] = List(
    "!x:real. a:real <= x /\\ x <= b:real ==> derivative (f:real -> real) x ((df:real -> real) x)",
    "!x:real. a:real <= x /\\ x <= b:real ==> derivative (g:real -> real) x ((dg:real -> real) x)")
  private val PartsHypotheses: List[String] =
    "a:real <= b:real" :: PartsSlopes ::: List("has_integral (\\x:real. (f:real -> real) x * (dg:real -> real) x) a b i")
  private val SubstitutionHypotheses: List[String] = List(
    "a:real <= b:real",
    "!y:real. derivative (Fn:real -> real) y ((f:real -> real) y)",
    "!x:real. a:real <= x /\\ x <= b:real ==> derivative (g:real -> real) x ((dg:real -> real) x)")

  /** `theorem` with `hypotheses` discharged in reverse, so the first is the outermost antecedent. */
  private def dischargedAll(steps: Continuity.Steps, theorem: Kernel.Thm, hypotheses: List[String]): Either[LogicError, Kernel.Thm] =
    hypotheses.reverse.foldLeft[Either[LogicError, Kernel.Thm]](Right(theorem)) { (acc, text) =>
      for { current <- acc; hypothesis <- steps.proposition(text); next <- steps.rules.disch(hypothesis, current) } yield next
    }

  /**
   * [[HasParts]]. The product rule at each point gives `\y. f y * g y` the slope `df x * g x + f x * dg x`,
   * [[HasFundamental]] integrates that sum to `f b * g b - f a * g a`, and [[HasLinear]] at one and
   * minus one subtracts `f * dg`. What is left is written under the lambda by `Kernel.abs` from the
   * identity of the ring at each `x`, which costs no axiom.
   */
  private def byParts(steps: Continuity.Steps, productRule: Kernel.Thm, hasFundamental: Kernel.Thm, hasLinear: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val df = Term.variable("df", Functions)
    val dg = Term.variable("dg", Functions)
    val List(a, b, i, x) = List("a", "b", "i", "x").map(Term.variable(_, Reals)): @unchecked
    for {
      hypotheses <- PartsHypotheses.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, text) =>
        for { done <- acc; one <- assume(text) } yield done :+ one
      }
      List(ordered, slopeF, slopeG, integralOfProduct) = hypotheses: @unchecked
      productFn <- Parser.term(theory, notation, "\\y:real. (f:real -> real) y * (g:real -> real) y", Functions)
      sumFn <- Parser.term(theory, notation, "\\x:real. (df:real -> real) x * (g:real -> real) x + (f:real -> real) x * (dg:real -> real) x", Functions)
      otherFn <- Parser.term(theory, notation, "\\x:real. (f:real -> real) x * (dg:real -> real) x", Functions)
      slopes <- for {
        member <- proposition("a:real <= x:real /\\ x <= b:real")
        assumed <- LogicError.lift(Kernel.assume(member))
        atF <- rules.spec(x, slopeF).flatMap(rules.mp(_, assumed))
        atG <- rules.spec(x, slopeG).flatMap(rules.mp(_, assumed))
        m <- real("(df:real -> real) x:real")
        n <- real("(dg:real -> real) x:real")
        joined <- rules.specAll(productRule, List(f, g, x, m, n)).flatMap(mp(_, Right(atF), Right(atG)))
        result <- rules.disch(member, joined).flatMap(rules.gen(x, _))
      } yield result
      whole <- rules.specAll(hasFundamental, List(productFn, sumFn, a, b)).flatMap(reduced)
        .flatMap(mp(_, Right(ordered), Right(slopes)))
      value <- real("(f:real -> real) b * (g:real -> real) b - f a * g a")
      one <- real("1:real")
      minusOne <- real("0 - 1:real")
      combined <- rules.specAll(hasLinear, List(sumFn, otherFn, a, b, value, i, one, minusOne)).flatMap(reduced)
        .flatMap(mp(_, Right(whole), Right(integralOfProduct)))

      pointwise <- at(lemma("!P:real Q:real. 1 * (P + Q) + (0 - 1) * Q = P"), "(df:real -> real) x:real * (g:real -> real) x", "(f:real -> real) x:real * (dg:real -> real) x")
      functions <- LogicError.lift(Kernel.abs(x, pointwise))
      values <- at(lemma("!V:real i:real. 1 * V + (0 - 1) * i = V - i"), "(f:real -> real) b * (g:real -> real) b - f a * g a", "i:real")
      hasConstant <- Parser.term(theory, notation, "has_integral", Type.fun(Functions, Type.fun(Reals, Type.fun(Reals, Type.fun(Reals, Type.Bool)))))
      restated <- Conv.apTerm(hasConstant, functions).flatMap(Conv.apThm(_, a)).flatMap(Conv.apThm(_, b))
        .flatMap(eq => LogicError.lift(Kernel.mkComb(eq, values)))
      result <- LogicError.lift(Kernel.eqMp(restated, combined))
      closed <- dischargedAll(steps, result, PartsHypotheses).flatMap(rules.genAll(_, List(f, g, df, dg, a, b, i)))
    } yield closed
  }

  /**
   * [[HasSubstitution]]. The chain rule gives `\y. F (g y)` the slope `f (g x) * dg x` wherever `g` has
   * one, since `F` has one at `g x` whatever `g x` is, and [[HasFundamental]] integrates it.
   */
  private def bySubstitution(steps: Continuity.Steps, chainRule: Kernel.Thm, hasFundamental: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    import steps.*
    val bigF = Term.variable("Fn", Functions)
    val f = Term.variable("f", Functions)
    val g = Term.variable("g", Functions)
    val dg = Term.variable("dg", Functions)
    val List(a, b, x) = List("a", "b", "x").map(Term.variable(_, Reals)): @unchecked
    for {
      hypotheses <- SubstitutionHypotheses.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, text) =>
        for { done <- acc; one <- assume(text) } yield done :+ one
      }
      List(ordered, slopeF, slopeG) = hypotheses: @unchecked
      composed <- Parser.term(theory, notation, "\\y:real. (Fn:real -> real) ((g:real -> real) y)", Functions)
      integrand <- Parser.term(theory, notation, "\\x:real. (f:real -> real) ((g:real -> real) x) * (dg:real -> real) x", Functions)
      slopes <- for {
        member <- proposition("a:real <= x:real /\\ x <= b:real")
        assumed <- LogicError.lift(Kernel.assume(member))
        inner <- rules.spec(x, slopeG).flatMap(rules.mp(_, assumed))
        gx <- real("(g:real -> real) x:real")
        outer <- rules.spec(gx, slopeF)
        m <- real("(f:real -> real) ((g:real -> real) x:real)")
        n <- real("(dg:real -> real) x:real")
        joined <- rules.specAll(chainRule, List(bigF, g, x, m, n)).flatMap(mp(_, Right(inner), Right(outer)))
        result <- rules.disch(member, joined).flatMap(rules.gen(x, _))
      } yield result
      whole <- rules.specAll(hasFundamental, List(composed, integrand, a, b)).flatMap(reduced)
        .flatMap(mp(_, Right(ordered), Right(slopes)))
      closed <- dischargedAll(steps, whole, SubstitutionHypotheses).flatMap(rules.genAll(_, List(bigF, f, g, dg, a, b)))
    } yield closed
  }

  /**
   * The `integral` form of a `has_integral` fact whose hypotheses are `hypotheses`, the first being
   * `a <= b`: [[Unique]] at the function and the value the fact concludes with.
   */
  private def namedByUniqueness(
    steps: Continuity.Steps,
    unique: Kernel.Thm,
    fact: Kernel.Thm,
    hypotheses: List[String],
    variables: List[FVar],
    function: String,
    value: String
  ): Either[LogicError, Kernel.Thm] = {
    import steps.*
    for {
      assumed <- hypotheses.foldLeft[Either[LogicError, List[Kernel.Thm]]](Right(Nil)) { (acc, text) =>
        for { done <- acc; one <- assume(text) } yield done :+ one
      }
      instance <- rules.specAll(fact, variables).flatMap(theorem =>
        assumed.foldLeft[Either[LogicError, Kernel.Thm]](Right(theorem))((acc, h) => acc.flatMap(rules.mp(_, h))))
      functionTerm <- Parser.term(theory, notation, function, Functions)
      valueTerm <- real(value)
      a = Term.variable("a", Reals)
      b = Term.variable("b", Reals)
      named <- rules.specAll(unique, List(functionTerm, a, b, valueTerm)).flatMap(mp(_, Right(assumed.head), Right(instance)))
      closed <- dischargedAll(steps, named, hypotheses).flatMap(rules.genAll(_, variables))
    } yield closed
  }
}
