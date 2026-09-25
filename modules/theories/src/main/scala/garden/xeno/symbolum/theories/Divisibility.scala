package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Divisibility as a relation the reals can already state, and the facts an argument about an
 * invariant is made of.
 *
 * `Divides a b` abbreviates `?k. b = a * k`. It is a constant of type `real -> real -> bool`
 * introduced by defining it, so it is a definitional extension: the theory holds exactly the axioms
 * it held before, and `DivisibilitySpec` asserts that by comparing the two counts rather than by
 * writing either of them down.
 *
 * == What this is not, and a reader who skips this paragraph will build something wrong on it ==
 *
 * **This is not the divisibility of the integers.** Over a field every non-zero `a` divides every
 * `b`, with `inv a * b` as the witness. That is not an awkward edge of the encoding, it is the
 * whole of what the relation says here, and it is derived below rather than left for a consumer to
 * discover: [[Divisibility.NonZeroDivides]] is `!a b. ~(a = 0) ==> Divides a b`, with nothing
 * assumed. So the relation is trivially true everywhere except at `a = 0`, where
 * [[Divisibility.ZeroDivides]] settles it outright.
 *
 * What that costs, item by item:
 *
 *  - **Coprimality is not derivable and is not derived.** There is no notion of a common factor to
 *    be shared or not shared when every non-zero quantity divides everything. A consumer that needs
 *    `a` and `b` coprime carries it as an explicit hypothesis of its own theorem, in whatever form
 *    its argument actually uses, and that hypothesis is discharged by the consumer or not at all.
 *  - No primality, no factorisation, no greatest common divisor and no descent on the size of a
 *    factor: each of those needs a type in which the divisors of a quantity are finitely many,
 *    which is the integers and not this.
 *  - `Divides a b` on its own tells a reader nothing about `b`. Only the *shape* of a derivation
 *    survives the move to a field.
 *
 * == What it does buy, which is why it comes first ==
 *
 * The shape of a derivation is what a no-go argument needs. Such an argument runs: a quantity is a
 * fixed multiple of something at every step of an orbit, the target is not such a multiple,
 * therefore the target is unreachable. Written out, its steps are the ones below, and
 * [[Divisibility.LinearCombination]] is the one that does the work: an invariant preserved by a
 * step that mixes two quantities is preserved because `a` divides `x * b + y * c` whenever it
 * divides `b` and `c`. A consumer states its own arithmetic premises as hypotheses and gets a
 * theorem whose divisibility reasoning is checked, which is more than an argument carrying the
 * whole chain in prose.
 *
 * It also does not wait for the integers. `docs/adr/0007` puts the integers and the rationals ahead
 * of the reals-as-a-construction, so a consumer needing divisibility today needs it over the reals
 * or not at all. When there is a type of integers, the same statements are what a reader will
 * expect to find over it, and [[Divisibility.NonZeroDivides]] is the one that stops being true
 * there: it is the only derivation in this file that mentions `inv`, and the rest carry over
 * unchanged.
 *
 * == Both directions of the definition are theorems, and that is not decoration ==
 *
 * [[Divisibility.Intro]] goes from a witness to the relation and [[Divisibility.Elim]] the other
 * way. Every derivation here is written through that pair rather than through the defining
 * equation, because the elimination is where the side conditions live: taking a witness out of an
 * existential asks that it not escape into the conclusion or into the predicate, and both are
 * refusals from [[garden.xeno.symbolum.logic.Rules.existsElim]] rather than mistakes that yield a
 * weaker theorem. Doing it in one helper is what keeps [[Divisibility.Transitive]] and
 * [[Divisibility.LinearCombination]] readable: they open their premises, do arithmetic on plain
 * equations, and close.
 */
final class Divisibility private (
  val ring: Ring,
  val theory: Theory,
  val notation: Notation,
  /**
   * The connectives, read against **this** theory rather than the one the ring was built over.
   *
   * A `Signature` since 2026-09-12, when the five developments beside `Chain` were threaded into
   * it: `Chain.widest` has to be one, and every development the chain carries is a candidate for
   * being last. The field is what the trait wants and what a rule building a quantifier over a
   * goal that mentions `Divides` asks for; the ring's own logic was built before the constant
   * existed and cannot name it.
   */
  val logic: Logic,
  val definition: Kernel.Thm,
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  val reals: RealTheory = ring.reals

  /** The fact named, as this development proved it. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** `|- !a b k. b = a * k ==> Divides a b` */
  def intro: Either[LogicError, Kernel.Thm] = fact(Divisibility.Intro)

  /** `|- !a b. Divides a b ==> (?k. b = a * k)` */
  def elim: Either[LogicError, Kernel.Thm] = fact(Divisibility.Elim)

  /** `|- !a. Divides a a` */
  def reflexive: Either[LogicError, Kernel.Thm] = fact(Divisibility.Reflexive)

  /** `|- !a b c. Divides a b ==> Divides b c ==> Divides a c` */
  def transitive: Either[LogicError, Kernel.Thm] = fact(Divisibility.Transitive)

  /** `|- !a b c. Divides a b ==> Divides a (c * b)` */
  def multiplyLeft: Either[LogicError, Kernel.Thm] = fact(Divisibility.MultiplyLeft)

  /** `|- !a b c. Divides a b ==> Divides a (b * c)` */
  def multiplyRight: Either[LogicError, Kernel.Thm] = fact(Divisibility.MultiplyRight)

  /** `|- !a b c x y. Divides a b ==> Divides a c ==> Divides a (x * b + y * c)` */
  def linearCombination: Either[LogicError, Kernel.Thm] = fact(Divisibility.LinearCombination)

  /** `|- !a. Divides a 0` */
  def dividesZero: Either[LogicError, Kernel.Thm] = fact(Divisibility.DividesZero)

  /** `|- !b. Divides 0 b = (b = 0)` */
  def zeroDivides: Either[LogicError, Kernel.Thm] = fact(Divisibility.ZeroDivides)

  /** `|- !a b. ~(a = 0) ==> Divides a b`, which is the limit of the whole file. */
  def nonZeroDivides: Either[LogicError, Kernel.Thm] = fact(Divisibility.NonZeroDivides)

  /**
   * `Divides a b`, as a term, for a caller holding the two quantities rather than their spelling.
   *
   * A consumer whose divisor was computed rather than written out cannot go through the parser, and
   * building the application itself would mean naming the constant against some theory of its own
   * choosing: a name and a type that agree while the origins do not is a constant from another
   * chain, which `docs/adr/0008` is about. This hands out the one this development defined.
   */
  def divides(divisor: Term, dividend: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(Divisibility.DividesName, Divisibility.relation))
      applied <- LogicError.lift(Term.appAll(constant, List(divisor, dividend)))
    } yield applied

}

object Divisibility {

  /**
   * The relation's name.
   *
   * No notation of its own: `Divides a b` is read and printed as an application, like `Sum f n`.
   * An infix spelling would be a second thing to keep in agreement with the printer for no gain,
   * and `Real.notation` is shared with every development built over these reals.
   */
  val DividesName: String = "Divides"

  /** `|- !a b k. b = a * k ==> Divides a b` */
  val Intro: String = "DIVIDES_INTRO"

  /** `|- !a b. Divides a b ==> (?k. b = a * k)` */
  val Elim: String = "DIVIDES_ELIM"

  /** `|- !a. Divides a a` */
  val Reflexive: String = "DIVIDES_REFL"

  /** `|- !a b c. Divides a b ==> Divides b c ==> Divides a c` */
  val Transitive: String = "DIVIDES_TRANS"

  /**
   * `|- !a b c. Divides a b ==> Divides a (c * b)`
   *
   * The factor on the left, which is a separate theorem from [[MultiplyRight]] rather than a
   * duplicate of it. Commutativity makes the two equivalent as statements and does nothing for a
   * consumer: a detachment matches a term as it is written, so a development whose product happens
   * to be spelled the other way round would have to commute it first. Both are cheap, both are
   * here, and the alternative was for every caller to keep a commuted copy.
   */
  val MultiplyLeft: String = "DIVIDES_MUL_LEFT"

  /** `|- !a b c. Divides a b ==> Divides a (b * c)` */
  val MultiplyRight: String = "DIVIDES_MUL_RIGHT"

  /**
   * `|- !a b c x y. Divides a b ==> Divides a c ==> Divides a (x * b + y * c)`
   *
   * The one a consumer actually reaches for. An invariant that survives a step is an invariant
   * whose new value is a combination of old ones, so this is the step of such an argument that is
   * about divisibility at all; the rest is arithmetic the ring tactic closes.
   */
  val LinearCombination: String = "DIVIDES_LINEAR"

  /** `|- !a. Divides a 0` */
  val DividesZero: String = "DIVIDES_ZERO"

  /**
   * `|- !b. Divides 0 b = (b = 0)`
   *
   * An equality of propositions rather than a pair of implications, built by antisymmetry from the
   * two directions. That form is what a caller wants: it enters the rewriter as it stands, where
   * two implications would each need a detachment.
   */
  val ZeroDivides: String = "ZERO_DIVIDES"

  /**
   * `|- !a b. ~(a = 0) ==> Divides a b`
   *
   * The limit of the file, proved rather than described. `inv a * b` is the witness, so the only
   * thing standing between an arbitrary pair and this relation is `a` being zero. Anything a
   * consumer wants to conclude from `Divides a b` beyond that has to come from its own hypotheses.
   */
  val NonZeroDivides: String = "DIVIDES_NONZERO"

  private val real: Type = TyApp(Real.TypeName, Nil)
  private val relation: Type = Type.fun(real, Type.fun(real, Type.Bool))
  private val binary: Type = Type.fun(real, Type.fun(real, real))

  /**
   * The standard development, built beside the chain rather than taken from it.
   *
   * `Chain.standard.divisibility` is the one a caller almost always wants since 2026-09-12: it is
   * in the signature everything else is in, and it is the one `Library.of` collects and
   * `docs/lemmas.md` lists. This builds a **second** one, over the narrower theory, and it is kept because the
   * specs of this file are about what this development does on its own and because a caller with a
   * development of its own reaches for it.
   *
   * The two are not interchangeable and the kernel says so rather than letting them mix: a constant
   * defined here and a constant of the same name defined in the chain have different origins, which
   * `docs/adr/0008` is about, so a rule built from one is refused against the other. Loud, and not
   * silent.
   */
  lazy val standard: Divisibility =
    construct(Ring.standard).fold(
      error => throw new IllegalStateException(s"divisibility does not build: ${error.message}"),
      identity
    )

  /**
   * Define the relation over a development that already has its ring, and derive the facts.
   *
   * The ring is the argument rather than a bare theory because every derivation below ends in an
   * identity between products and sums, and [[Ring]] is what settles those. It also carries the
   * theory the definition extends, so a caller that built its reals over a domain of its own gets
   * divisibility over that domain instead of over a second copy of the reals.
   *
   * The ring was built before the constant existed and is used unchanged afterwards, which is worth
   * saying once: a theorem of a theory is a theorem of every extension of it, and no identity
   * handed to the ring mentions `Divides` in the first place.
   */
  def construct(ring: Ring): Either[LogicError, Divisibility] =
    construct(ring, ring.reals.theory)

  /**
   * The same, extending a theory that already holds something else.
   *
   * The chain entry point, the shape `Peano.construct` and `Product.construct` already had. Two
   * developments built beside each other cannot read each other's theorems, so a claim that
   * mentions `Divides` and `Sum` at once needs one theory holding both, and that means this over
   * that rather than both over the reals. `Chain` passes its widest theory so far.
   *
   * The ring is still the first argument and is still the ring the base was built from: every
   * derivation below ends in an identity between products and sums and `Ring` is what settles
   * those. A theorem of a theory is a theorem of every extension of it, so a ring built lower down
   * is used unchanged here.
   */
  def construct(ring: Ring, base: Theory): Either[LogicError, Divisibility] = {
    val reals = ring.reals

    for {
      body <- Parser.term(base, reals.notation, "\\a:real b:real. ?k:real. b = a * k")
      defined <- LogicError.lift(Kernel.defineConstant(base, DividesName, body))
      (theory, definition) = defined
      logic <- reals.logic.over(theory)
      vocabulary <- Vocabulary.over(ring, theory, definition)

      introduction <- introduce(vocabulary)
      elimination <- eliminate(vocabulary)

      reflexivity <- reflexive(vocabulary, introduction)
      transitivity <- transitive(vocabulary, introduction)
      leftFactor <- multiplyLeft(vocabulary, introduction)
      rightFactor <- multiplyRight(vocabulary, introduction)
      combination <- linearCombination(vocabulary, introduction)
      atZero <- dividesZero(vocabulary, introduction)
      byZero <- zeroDivides(vocabulary, introduction)
      byEverythingElse <- nonZeroDivides(vocabulary, introduction)
    } yield new Divisibility(
      ring,
      theory,
      reals.notation,
      logic,
      definition,
      Map(
        Intro -> introduction,
        Elim -> elimination,
        Reflexive -> reflexivity,
        Transitive -> transitivity,
        MultiplyLeft -> leftFactor,
        MultiplyRight -> rightFactor,
        LinearCombination -> combination,
        DividesZero -> atZero,
        ZeroDivides -> byZero,
        NonZeroDivides -> byEverythingElse
      )
    )
  }

  /* ------------------------------------------------------------------ plumbing */

  /**
   * A premise `Divides x y` taken apart: the existential it unfolds to, and the equation a witness
   * satisfies, assumed.
   *
   * Both halves are needed together and neither is useful alone, which is why they travel as one
   * value. The equation is read off the definition's own predicate rather than built a second time,
   * so a change to the defining body cannot leave the two spelling one statement differently.
   */
  private final case class Opened(
    premise: Term,
    existential: Kernel.Thm,
    witness: FVar,
    equation: Kernel.Thm
  )

  /**
   * The constants, and the moves every derivation below repeats.
   *
   * Held together rather than fetched in each lemma because the alternative was ten copies of the
   * same lookups, and a lemma taking the multiplication from a different theory than the one the
   * definition was made in would build a term the kernel refuses for its origin, which is
   * `docs/adr/0008`. The lemmas still take what they *rest on* as arguments, which is what keeps
   * each signature honest: nothing below reaches for a fact it was not handed.
   */
  private final class Vocabulary private (
    val ring: Ring,
    val theory: Theory,
    val definition: Kernel.Thm,
    /**
     * The connectives over the theory that has `Divides`, not over the bare logic.
     *
     * [[garden.xeno.symbolum.logic.Logic.over]] says why, and this file is the case its note names:
     * [[garden.xeno.symbolum.logic.Rules.existsIntro]] has to *build* a universal quantifier over the type
     * the witness ranges over, and a theory refuses a constant at a type operator it has never
     * heard of. `Logic.standard` has never heard of `real`, so the introduction lemma below fails
     * with "no type operator named real" against the plain logic. [[garden.xeno.symbolum.logic.Rules.gen]]
     * does not, because the quantifier it needs is already in the goal, which is why every lemma in
     * [[Order]] works without this.
     */
    val logic: Logic,
    val multiplication: Term,
    val addition: Term
  ) {

    val reals: RealTheory = ring.reals
    val rules: Rules = logic.rules

    def product(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(multiplication, List(left, right)))

    def sum(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(addition, List(left, right)))

    def zero: Either[LogicError, Term] = reals.term("0")

    def one: Either[LogicError, Term] = reals.term("1")

    def inverse(argument: Term): Either[LogicError, Term] =
      for {
        constant <- LogicError.lift(theory.constant(Real.Inverse, Type.fun(real, real)))
        applied <- LogicError.lift(Term.app(constant, argument))
      } yield applied

    /** `|- Divides x y = (?k. y = x * k)`, the defining equation at a pair. */
    def unfoldedAt(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      Conv.unfold(definition, List(left, right))

    /** An identity between two terms, by the ring tactic, which is where every derivation ends. */
    def identity(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      LogicError.lift(Term.eq(left, right)).flatMap(ring.prove)

    /** The left-hand side of an equation a step produced. */
    def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
      Term
        .destEq(theorem.conclusion)
        .map(_._1)
        .toRight(NotOfForm("an equation", theorem.conclusion))

    /** The right-hand side of an equation a step produced. */
    def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
      Term
        .destEq(theorem.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", theorem.conclusion))

    /** The `\k. y = x * k` an existential is applied to. */
    def predicateOf(term: Term): Either[LogicError, Term] =
      logic
        .destExistsPredicate(term)
        .toRight(NotOfForm("an existential quantification", term))

    /**
     * `Divides x y` assumed, with a named witness and the equation it satisfies.
     *
     * The equation comes from contracting the definition's predicate at the witness, so it is the
     * very term [[garden.xeno.symbolum.logic.Rules.existsElim]] will look for among the hypotheses. Building
     * it by hand instead is how this fails with "needs a theorem assuming ...".
     */
    def open(left: Term, right: Term, witness: FVar): Either[LogicError, Opened] =
      for {
        unfolded <- unfoldedAt(left, right)
        premise <- leftOf(unfolded)
        assumed <- LogicError.lift(Kernel.assume(premise))
        existential <- LogicError.lift(Kernel.eqMp(unfolded, assumed))

        predicate <- rightOf(unfolded).flatMap(predicateOf)
        applied <- LogicError.lift(Term.app(predicate, witness))
        contraction <- Conv.betaRoot(applied)
        instance <- rightOf(contraction)
        equation <- LogicError.lift(Kernel.assume(instance))
      } yield Opened(premise, existential, witness, equation)

    /**
     * Discharge the witness of an opened premise from a case that used it.
     *
     * What comes back carries the premise itself as a hypothesis in place of the equation, and this
     * is the call that refuses a witness escaping into the conclusion rather than quietly proving
     * something about that one witness.
     */
    def close(opened: Opened, caseTheorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      rules.existsElim(opened.existential, opened.witness, caseTheorem)

    /**
     * `Divides x y` concluded from `y = x * w`, through the introduction lemma.
     *
     * The antecedent is compared against the equation before the detachment, which is not
     * belt-and-braces. [[garden.xeno.symbolum.logic.Rules.mp]] discharges an antecedent that matches and
     * leaves one that does not standing as a hypothesis, so an equation about the wrong term comes
     * back as a *true* sequent with an extra premise rather than as an error. That is what happened
     * here first, from specialising the three quantifiers in the wrong order, and what it looked
     * like was a theorem. The refusal is the fix; the sweep in `DivisibilitySpec` over every
     * hypothesis list is the second one.
     */
    def conclude(
      introduction: Kernel.Thm,
      divisor: Term,
      dividend: Term,
      witness: Term,
      equation: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        instance <- rules.specAll(introduction, List(divisor, dividend, witness))
        parts <- logic
          .destImp(instance.conclusion)
          .toRight(NotOfForm("an implication", instance.conclusion))
        _ <- if (parts._1 == equation.conclusion) Right(())
             else Left(NotOfForm(s"a proof of ${parts._1}", equation.conclusion))
        related <- rules.mp(instance, equation)
      } yield related

    /**
     * `|- s * t = u * t`, from `|- s = u` and a `t`.
     *
     * Two kernel steps and no rewriter. The term being moved is a whole side of an equation, so
     * congruence says it once; a rewrite rule whose left-hand side is a bare variable would match
     * every subterm of the goal instead, which is not a smaller version of this but a wrong one.
     */
    def scaleOnTheRight(equation: Kernel.Thm, factor: Term): Either[LogicError, Kernel.Thm] =
      Conv.apTerm(multiplication, equation).flatMap(Conv.apThm(_, factor))

    /** `|- t * s = t * u`, from a `t` and `|- s = u`. */
    def scaleOnTheLeft(factor: Term, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        partial <- LogicError.lift(Term.app(multiplication, factor))
        congruence <- Conv.apTerm(partial, equation)
      } yield congruence

    /** `|- s + u = t + v`, from `|- s = t` and `|- u = v`. */
    def addSides(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        partial <- Conv.apTerm(addition, left)
        combined <- LogicError.lift(Kernel.mkComb(partial, right))
      } yield combined

    /**
     * Regroup the right-hand side of an equation into `x * w`, by the ring, and chain it on.
     *
     * The last two steps of every lemma that produces a witness, and the reason they are one call
     * is that the term handed to the ring has to be the term the introduction lemma will be
     * specialised at, to the node. Building it twice is how the two drift apart.
     */
    def asMultipleOf(
      equation: Kernel.Thm,
      divisor: Term,
      witness: Term
    ): Either[LogicError, Kernel.Thm] =
      for {
        grouped <- product(divisor, witness)
        regrouped <- rightOf(equation).flatMap(identity(_, grouped))
        chained <- Conv.trans(equation, regrouped)
      } yield chained
  }

  private object Vocabulary {

    def over(
      ring: Ring,
      theory: Theory,
      definition: Kernel.Thm
    ): Either[LogicError, Vocabulary] =
      for {
        logic <- ring.reals.logic.over(theory)
        multiply <- LogicError.lift(theory.constant(Real.Multiplication, binary))
        add <- LogicError.lift(theory.constant(Real.Addition, binary))
      } yield new Vocabulary(ring, theory, definition, logic, multiply, add)
  }

  private def variable(name: String): FVar = Term.variable(name, real)

  /* -------------------------------------------------------------------- lemmas */

  /**
   * `|- !a b k. b = a * k ==> Divides a b`.
   *
   * The witness goes in and the relation comes out: an existential introduction against the
   * definition's own predicate, then the defining equation read right to left.
   *
   * The predicate is a parameter of [[garden.xeno.symbolum.logic.Rules.existsIntro]] and cannot be recovered
   * from a theorem, so it is taken from the unfolded definition rather than built here. That is the
   * reason this is a theorem at all: a caller specialising it never has to say which existential
   * was meant.
   */
  private def introduce(vocabulary: Vocabulary): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")
    val k = variable("k")

    for {
      unfolded <- vocabulary.unfoldedAt(a, b)
      folded <- Conv.sym(unfolded)
      predicate <- vocabulary.rightOf(unfolded).flatMap(vocabulary.predicateOf)

      applied <- LogicError.lift(Term.app(predicate, k))
      contraction <- Conv.betaRoot(applied)
      equation <- vocabulary.rightOf(contraction)
      assumed <- LogicError.lift(Kernel.assume(equation))

      witnessed <- rules.existsIntro(predicate, k, assumed)
      related <- LogicError.lift(Kernel.eqMp(folded, witnessed))
      discharged <- rules.disch(equation, related)
      general <- rules.genAll(discharged, List(a, b, k))
    } yield general
  }

  /**
   * `|- !a b. Divides a b ==> (?k. b = a * k)`.
   *
   * The definition read left to right, which is one step. A named fact anyway: a consumer holding
   * the relation and wanting a witness should not have to know the constant is defined, and the
   * derivations below go through it rather than through the defining equation.
   */
  private def eliminate(vocabulary: Vocabulary): Either[LogicError, Kernel.Thm] = {
    val a = variable("a")
    val b = variable("b")

    for {
      opened <- vocabulary.open(a, b, variable("k"))
      discharged <- vocabulary.rules.disch(opened.premise, opened.existential)
      general <- vocabulary.rules.genAll(discharged, List(a, b))
    } yield general
  }

  /**
   * `|- !a. Divides a a`.
   *
   * `1` is the witness and `a = a * 1` is a field axiom read backwards, which the ring does. True
   * at zero as well, and that is not a special case: `Divides 0 0` has the same witness, and
   * [[ZeroDivides]] agrees with it since `0 = 0`.
   */
  private def reflexive(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val a = variable("a")

    for {
      unit <- vocabulary.one
      scaled <- vocabulary.product(a, unit)
      equation <- vocabulary.identity(a, scaled)
      related <- vocabulary.conclude(introduction, a, a, unit, equation)
      general <- vocabulary.rules.gen(a, related)
    } yield general
  }

  /**
   * `|- !a b c. Divides a b ==> Divides b c ==> Divides a c`.
   *
   * Two witnesses multiplied. `b = a * k` scaled on the right by `m` gives `b * m = (a * k) * m`,
   * which chains onto `c = b * m`, and the ring regroups the result to `c = a * (k * m)`.
   *
   * The two eliminations nest, the inner one first, and both side conditions hold for the same
   * reason: neither witness occurs in `Divides a c`, and neither occurs in the predicate of the
   * other's existential. Doing them the other way round refuses rather than misleads, since the
   * generalisation would find the outer witness still free in a surviving hypothesis.
   */
  private def transitive(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")
    val c = variable("c")
    val k = variable("k")
    val m = variable("m")

    for {
      first <- vocabulary.open(a, b, k)
      second <- vocabulary.open(b, c, m)

      scaled <- vocabulary.scaleOnTheRight(first.equation, m)
      chained <- Conv.trans(second.equation, scaled)

      witness <- vocabulary.product(k, m)
      equation <- vocabulary.asMultipleOf(chained, a, witness)

      related <- vocabulary.conclude(introduction, a, c, witness, equation)
      withoutSecond <- vocabulary.close(second, related)
      withoutFirst <- vocabulary.close(first, withoutSecond)

      dischargedSecond <- rules.disch(second.premise, withoutFirst)
      dischargedFirst <- rules.disch(first.premise, dischargedSecond)
      general <- rules.genAll(dischargedFirst, List(a, b, c))
    } yield general
  }

  /**
   * `|- !a b c. Divides a b ==> Divides a (c * b)`.
   *
   * The witness is `c * k`, and the only step before the ring is a congruence putting `c` on the
   * left of the witness equation.
   */
  private def multiplyLeft(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")
    val c = variable("c")
    val k = variable("k")

    for {
      opened <- vocabulary.open(a, b, k)
      scaled <- vocabulary.scaleOnTheLeft(c, opened.equation)

      witness <- vocabulary.product(c, k)
      equation <- vocabulary.asMultipleOf(scaled, a, witness)

      dividend <- vocabulary.product(c, b)
      related <- vocabulary.conclude(introduction, a, dividend, witness, equation)
      closed <- vocabulary.close(opened, related)
      discharged <- rules.disch(opened.premise, closed)
      general <- rules.genAll(discharged, List(a, b, c))
    } yield general
  }

  /** `|- !a b c. Divides a b ==> Divides a (b * c)`, the mirror of [[multiplyLeft]]. */
  private def multiplyRight(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")
    val c = variable("c")
    val k = variable("k")

    for {
      opened <- vocabulary.open(a, b, k)
      scaled <- vocabulary.scaleOnTheRight(opened.equation, c)

      witness <- vocabulary.product(k, c)
      equation <- vocabulary.asMultipleOf(scaled, a, witness)

      dividend <- vocabulary.product(b, c)
      related <- vocabulary.conclude(introduction, a, dividend, witness, equation)
      closed <- vocabulary.close(opened, related)
      discharged <- rules.disch(opened.premise, closed)
      general <- rules.genAll(discharged, List(a, b, c))
    } yield general
  }

  /**
   * `|- !a b c x y. Divides a b ==> Divides a c ==> Divides a (x * b + y * c)`.
   *
   * The witness is `x * k + y * m`. Each premise is scaled on the left, the two scaled equations
   * are joined by one congruence step on the addition, and the ring pulls `a` out of the sum.
   *
   * The scalars are unconstrained, which is what makes this usable: an invariant that changes by a
   * negative multiple or by a fraction is still a linear combination, and `x` and `y` range over
   * every real rather than over a set of coefficients this file would then owe a definition for.
   */
  private def linearCombination(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")
    val c = variable("c")
    val x = variable("x")
    val y = variable("y")
    val k = variable("k")
    val m = variable("m")

    for {
      first <- vocabulary.open(a, b, k)
      second <- vocabulary.open(a, c, m)

      left <- vocabulary.scaleOnTheLeft(x, first.equation)
      right <- vocabulary.scaleOnTheLeft(y, second.equation)
      combined <- vocabulary.addSides(left, right)

      scaledFirst <- vocabulary.product(x, k)
      scaledSecond <- vocabulary.product(y, m)
      witness <- vocabulary.sum(scaledFirst, scaledSecond)
      equation <- vocabulary.asMultipleOf(combined, a, witness)

      scaledB <- vocabulary.product(x, b)
      scaledC <- vocabulary.product(y, c)
      dividend <- vocabulary.sum(scaledB, scaledC)
      related <- vocabulary.conclude(introduction, a, dividend, witness, equation)

      withoutSecond <- vocabulary.close(second, related)
      withoutFirst <- vocabulary.close(first, withoutSecond)
      dischargedSecond <- rules.disch(second.premise, withoutFirst)
      dischargedFirst <- rules.disch(first.premise, dischargedSecond)
      general <- rules.genAll(dischargedFirst, List(a, b, c, x, y))
    } yield general
  }

  /**
   * `|- !a. Divides a 0`.
   *
   * Zero is the witness, and nothing here is conditional on `a`: zero divides zero too, by the same
   * witness rather than as a case of its own.
   */
  private def dividesZero(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val a = variable("a")

    for {
      nought <- vocabulary.zero
      scaled <- vocabulary.product(a, nought)
      equation <- vocabulary.identity(nought, scaled)
      related <- vocabulary.conclude(introduction, a, nought, nought, equation)
      general <- vocabulary.rules.gen(a, related)
    } yield general
  }

  /**
   * `|- !b. Divides 0 b = (b = 0)`.
   *
   * Both directions, then antisymmetry. Forwards, the witness equation is `b = 0 * k` and the ring
   * collapses that product whatever the witness was, so nothing needs to be known about it, which
   * is exactly the condition the elimination asks for. Backwards, `b = 0` chains onto `0 = 0 * 0`
   * and zero is the witness.
   */
  private def zeroDivides(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val b = variable("b")
    val k = variable("k")

    for {
      nought <- vocabulary.zero
      opened <- vocabulary.open(nought, b, k)

      vanishes <- vocabulary.rightOf(opened.equation).flatMap(vocabulary.identity(_, nought))
      forwardCase <- Conv.trans(opened.equation, vanishes)
      forward <- vocabulary.close(opened, forwardCase)

      target <- LogicError.lift(Term.eq(b, nought))
      assumed <- LogicError.lift(Kernel.assume(target))
      squared <- vocabulary.product(nought, nought)
      trivial <- vocabulary.identity(nought, squared)
      chained <- Conv.trans(assumed, trivial)
      backward <- vocabulary.conclude(introduction, nought, b, nought, chained)

      both = Kernel.deductAntisym(backward, forward)
      general <- vocabulary.rules.gen(b, both)
    } yield general
  }

  /**
   * `|- !a b. ~(a = 0) ==> Divides a b`.
   *
   * The witness is `inv a * b` and the inverse axiom is the one premise: assume `~(a = 0)`, detach
   * `a * inv a = 1`, and use that as a rewrite rule on a regrouping the ring proves
   * unconditionally. `inv a` is an atom to the ring, so `a * (inv a * b) = a * inv a * b` is an
   * identity in three atoms and needs nothing about any of them; the hypothesis enters only where
   * `a * inv a` is replaced by `1`.
   *
   * The antecedent is read off the specialised axiom rather than written again, so what is
   * discharged at the end is exactly what was detached at the start.
   *
   * This is the only derivation in the file that mentions `inv`, and therefore the only one that
   * will not survive a move to a type of integers. That is the point of having it: it is what makes
   * the relation trivial here, and a consumer reading only the other facts would not know.
   */
  private def nonZeroDivides(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic
    val a = variable("a")
    val b = variable("b")

    for {
      axiom <- vocabulary.reals.axiom("MUL_INVERSE")
      atA <- rules.spec(a, axiom)
      parts <- logic.destImp(atA.conclusion).toRight(NotOfForm("an implication", atA.conclusion))
      (antecedent, _) = parts
      assumed <- LogicError.lift(Kernel.assume(antecedent))
      cancels <- rules.mp(atA, assumed)

      reciprocal <- vocabulary.inverse(a)
      witness <- vocabulary.product(reciprocal, b)
      whole <- vocabulary.product(a, witness)
      unit <- vocabulary.product(a, reciprocal)
      regrouped <- vocabulary.product(unit, b)
      grouping <- vocabulary.identity(whole, regrouped)

      rule <- Rewrite.Rule.of(logic, cancels)
      cancelled <- Rewrite.inTheorem(Vector(rule), grouping)
      absorbs <- vocabulary.rightOf(cancelled).flatMap(vocabulary.identity(_, b))
      reached <- Conv.trans(cancelled, absorbs)
      equation <- Conv.sym(reached)

      related <- vocabulary.conclude(introduction, a, b, witness, equation)
      discharged <- rules.disch(antecedent, related)
      general <- rules.genAll(discharged, List(a, b))
    } yield general
  }
}
