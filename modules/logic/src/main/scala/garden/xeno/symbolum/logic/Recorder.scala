package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * The derived rules, with each application written down as it happens.
 *
 * Every operation here is the one of the same meaning in `Rules`, `Conv` or `Rewrite`, wrapped so
 * that it leaves a [[Step]] behind. Nothing is decided differently: the theorem that comes out is
 * the theorem those return, and the account is a side product that no inference reads.
 *
 * == Why a facade and not a change to `Rules` ==
 *
 * Because the record is a caller's concern and not the rule's. `Rules.specAll` is used by tactics
 * that produce hundreds of specialisations nobody wants a line about, and making it record would
 * put the cost on all of them and then need a way to turn it off. What a development wants is the
 * opposite default: this one derivation, written out. Taking the operations from here instead of
 * from `rules` is the whole of the change at a call site, and `Recorded`'s `flatMap` is what keeps
 * a chained `.flatMap(rules.mp(_, x))` reading the way it did.
 *
 * == What it does not cover, on purpose ==
 *
 * Everything. [[step]] is the escape hatch, and it is public because a facade that pretended to be
 * complete would be a facade somebody works around silently: a derivation that needs an operation
 * nobody wrapped names it, hands over its premises, and gets a line in the account like any other.
 * A step taken with a bare `Rules` call instead is invisible, and the account is then a description
 * of a derivation that is missing a line, which is the one failure mode worth guarding against.
 */
final class Recorder(val rules: Rules, val notation: Notation) {

  private def show(term: Term): String = Show.show(notation, term)

  /**
   * An operation the facade does not wrap, recorded by the caller.
   *
   * The premises are what the line will cite, so a caller that hands over none gets a line that
   * cites none, which is right for an assumption and wrong for everything else.
   */
  def step(
    rule: String,
    detail: Option[String],
    premises: Vector[Kernel.Thm],
    names: Map[Kernel.Thm, String] = Map.empty
  )(
    outcome: Either[LogicError, Kernel.Thm]
  ): Recorded[Kernel.Thm] = outcome match {
    case Left(error) => Recorded(Vector.empty, Left(error))
    case Right(theorem) =>
      Recorded(
        Vector(Step(rule, detail, premises.filterNot(isTrivial), theorem, names)),
        Right(theorem)
      )
  }

  /* ------------------------------------------------------------------ quantifiers */

  /** `Rules.specAll`, recorded with the arguments it was given. */
  def specialise(theorem: Kernel.Thm, arguments: List[Term]): Recorded[Kernel.Thm] =
    step("specialise", Some("at " + arguments.map(show).mkString(", ")), Vector(theorem))(
      rules.specAll(theorem, arguments)
    )

  /** `Rules.genAll`, recorded with the variables it closed over. */
  def generalise(theorem: Kernel.Thm, variables: List[FVar]): Recorded[Kernel.Thm] =
    step("generalise", Some("over " + variables.map(_.name).mkString(", ")), Vector(theorem))(
      rules.genAll(theorem, variables)
    )

  /* ------------------------------------------------------------------ propositions */

  /** `Rules.mp`. */
  def modusPonens(implication: Kernel.Thm, antecedent: Kernel.Thm): Recorded[Kernel.Thm] =
    step("modus ponens", None, Vector(implication, antecedent))(rules.mp(implication, antecedent))

  /** `Rules.spec`, where one argument is being supplied rather than the whole prefix. */
  def specialiseOne(argument: Term, theorem: Kernel.Thm): Recorded[Kernel.Thm] =
    step("specialise", Some(s"at ${show(argument)}"), Vector(theorem))(rules.spec(argument, theorem))

  /** `Rules.disjElim`: the two branches prove the same thing, so the disjunction does. */
  def caseSplit(
    disjunction: Kernel.Thm,
    leftCase: Kernel.Thm,
    rightCase: Kernel.Thm
  ): Recorded[Kernel.Thm] =
    step("either way", None, Vector(disjunction, leftCase, rightCase))(
      rules.disjElim(disjunction, leftCase, rightCase)
    )

  /** `Rules.conjIntro`. */
  def both(left: Kernel.Thm, right: Kernel.Thm): Recorded[Kernel.Thm] =
    step("and", None, Vector(left, right))(rules.conjIntro(left, right))

  /** `Rules.conjElim1`. */
  def firstHalf(theorem: Kernel.Thm): Recorded[Kernel.Thm] =
    step("the first half", None, Vector(theorem))(rules.conjElim1(theorem))

  /** `Rules.conjElim2`. */
  def secondHalf(theorem: Kernel.Thm): Recorded[Kernel.Thm] =
    step("the second half", None, Vector(theorem))(rules.conjElim2(theorem))

  /**
   * `Rules.disjIntro1`: this theorem, or the other thing.
   *
   * Read as a line of an account, "or" and "after" said too little: the first page generated from
   * one of these read "after y = x, or", which is the operation and not a sentence. What a reader
   * needs is which side of the disjunction was proved, so that is what the line says.
   */
  def orElse(other: Term, theorem: Kernel.Thm): Recorded[Kernel.Thm] =
    step("on the left of", Some(show(other)), Vector(theorem))(rules.disjIntro1(other, theorem))

  /** `Rules.disjIntro2`: the other thing, or this theorem. */
  def orElseBefore(other: Term, theorem: Kernel.Thm): Recorded[Kernel.Thm] =
    step("on the right of", Some(show(other)), Vector(theorem))(rules.disjIntro2(other, theorem))

  /** `Rules.existsIntro`: the witness is what makes the claim true. */
  def witnessed(predicate: Term, witness: Term, theorem: Kernel.Thm): Recorded[Kernel.Thm] =
    step("so there is one", Some(s"namely ${show(witness)}"), Vector(theorem))(
      rules.existsIntro(predicate, witness, theorem)
    )

  /** `Rules.disch`: a hypothesis moved to the left of an implication. */
  def discharge(premise: Term, theorem: Kernel.Thm): Recorded[Kernel.Thm] =
    step("discharge", Some(show(premise)), Vector(theorem))(rules.disch(premise, theorem))

  /** `Rules.notElim`: something and its negation. */
  def contradiction(negation: Kernel.Thm, theorem: Kernel.Thm): Recorded[Kernel.Thm] =
    step("contradiction", None, Vector(negation, theorem))(rules.notElim(negation, theorem))

  /** `Rules.falsityElim`: anything at all, once falsity is on the table. */
  def fromFalsity(goal: Term, falsity: Kernel.Thm): Recorded[Kernel.Thm] =
    step("from falsity", Some(show(goal)), Vector(falsity))(rules.falsityElim(goal, falsity))

  /** `Kernel.assume`, which cites nothing because it is where a hypothesis enters. */
  def assume(proposition: Term): Recorded[Kernel.Thm] =
    step("assume", Some(show(proposition)), Vector.empty)(
      LogicError.lift(Kernel.assume(proposition))
    )

  /* ------------------------------------------------------------------ equations */

  /** `Conv.sym`. */
  def symmetry(theorem: Kernel.Thm): Recorded[Kernel.Thm] =
    step("read backwards", None, Vector(theorem))(Conv.sym(theorem))

  /** `Conv.trans`. */
  def chain(left: Kernel.Thm, right: Kernel.Thm): Recorded[Kernel.Thm] =
    step("chain", None, Vector(left, right))(Conv.trans(left, right))

  /**
   * `Conv.refl`, and it is deliberately **not** a step.
   *
   * `|- t = t` says nothing happened, and it is the single commonest node in a kernel proof: 9% of
   * the library's inferences. A line of an account that reads "t is t" is the noise the account
   * exists to remove, so this returns the theorem and records nothing.
   */
  def reflexivity(term: Term): Kernel.Thm = Conv.refl(term)

  /** `Conv.rewriteSides`. */
  def rewriteSides(
    left: Kernel.Thm,
    right: Kernel.Thm,
    theorem: Kernel.Thm
  ): Recorded[Kernel.Thm] =
    step("rewrite both sides", None, Vector(theorem, left, right))(
      Conv.rewriteSides(left, right, theorem)
    )

  /** `Conv.rewriteRight`. */
  def rewriteRight(theorem: Kernel.Thm, equation: Kernel.Thm): Recorded[Kernel.Thm] =
    step("rewrite the right side", None, Vector(theorem, equation))(
      Conv.rewriteRight(theorem, equation)
    )

  /**
   * One rewriting rule applied everywhere it matches inside a term, as an equation.
   *
   * The detail is what the caller calls the rule, because the rule itself is a theorem and its
   * name is not on it: `Rewrite.Rule` carries the theorem it came from and drops the name it was
   * held under, which is why a caller has to say.
   *
   * That name is also attached to the theorem, and the first run of the spike is why: the equation
   * driving a rewrite is often a definition **unfolded** at arguments, which no library holds, so
   * without this the line cited a bare sequent. See [[Step.names]].
   */
  def rewrite(detail: String, rule: Rewrite.Rule, term: Term): Recorded[Kernel.Thm] =
    step(
      "rewrite",
      Some(s"$detail in ${show(term)}"),
      Vector(rule.theorem),
      Map(rule.theorem -> detail)
    )(
      Rewrite.depthConv(Rewrite.rewriteConv(rule))(term)
    )

  /**
   * Rewriting inside a theorem with rules the caller names.
   *
   * `Rewrite.inTheorem`, and the commonest thing it is given here is a hypothesis read as a rule:
   * `abs x = 0` assumed, then used to rewrite `x <= abs x` into `x <= 0`. The name is the caller's
   * for the same reason [[rewrite]]'s is, and the equations are cited as premises so that a reader
   * sees what the line leant on.
   */
  def rewriteIn(
    detail: String,
    equations: Vector[Kernel.Thm],
    theorem: Kernel.Thm
  ): Recorded[Kernel.Thm] =
    step(
      "rewrite",
      Some(s"with $detail"),
      theorem +: equations,
      equations.map(_ -> detail).toMap
    )(
      Rewrite.Rule.all(rules.logic, equations).flatMap(Rewrite.inTheorem(_, theorem))
    )

  /** `Kernel.eqMp`: an equation between propositions, and one of them. */
  def replace(equivalence: Kernel.Thm, antecedent: Kernel.Thm): Recorded[Kernel.Thm] =
    step("replace", None, Vector(equivalence, antecedent))(
      LogicError.lift(Kernel.eqMp(equivalence, antecedent))
    )

  /* ------------------------------------------------------------------ procedures */

  /**
   * A decision procedure's answer, recorded as one line however long its own proof is.
   *
   * This is where the compression the account is for actually comes from. `RING` proving
   * `-x + -y = -(x + y)` is hundreds of inferences and is one sentence to a reader, and the
   * sentence is true: the procedure decided it, and which procedure is the part worth printing.
   */
  def procedure(name: String, claim: String)(
    outcome: Either[LogicError, Kernel.Thm]
  ): Recorded[Kernel.Thm] =
    step(name, Some(claim), Vector.empty)(outcome)

  /** A theorem that is quoted rather than derived here: a fact of a development below. */
  def quoted(detail: String)(outcome: Either[LogicError, Kernel.Thm]): Recorded[Kernel.Thm] =
    step("by", Some(detail), Vector.empty)(outcome)

  /**
   * Whether a premise is punctuation rather than a citation.
   *
   * `|- t = t` says nothing happened, and a line that cites one reads "by the fact that x is x".
   * Filtered in [[step]] rather than at each call site, because every rule that takes a theorem can
   * be handed one: the three `disjIntro` sites, `mp` against a reflexivity, and `rewriteSides`,
   * which is where it was first noticed. What the step concluded still shows the equation, so
   * nothing a reader needs is lost.
   */
  private def isTrivial(theorem: Kernel.Thm): Boolean =
    theorem.hypotheses.isEmpty && (Term.destEq(theorem.conclusion) match {
      case Some((left, right)) => left == right
      case None => false
    })
}
