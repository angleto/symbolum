package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A type with infinitely many elements, and the naturals carved out of it.
 *
 * Step two and three of `docs/adr/0007`. The reals are to be constructed rather than assumed, and
 * everything that construction needs starts here: a type that is not finite, a successor on it, and
 * a point outside the successor's image.
 *
 * == The one axiom, and why it is not the one HOL Light asserts ==
 *
 * One axiom is asserted in this file. The development holds three, the other two being the choice
 * operator and eta of the classical logic it is built over, and `NaturalSpec` writes out all three.
 *
 * Upstream states infinity as `?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`, defines `ONE_ONE` and `ONTO`
 * on the way, and then **derives** the form the construction actually uses: a one-one `f` together
 * with a `z` that is not `f` of anything. That derivation turns `~(!y. ?x. y = f x)` into
 * `?y. ~(?x. y = f x)`, which is the excluded middle.
 *
 * So the axiom here is the form the construction uses:
 *
 * {{{
 *   INFINITY : ?f:ind->ind. ?z:ind. (!x y. f x = f y ==> x = y) /\ (!x. ~(f x = z))
 * }}}
 *
 * **The divergence from upstream stands, and the reason recorded for it does not.** What stood here
 * said this logic does not have the excluded middle, because `Classical` asserts a choice operator
 * and Diaconescu's argument wants extensionality as well, which was asserted nowhere. **That was
 * wrong**, and `docs/adr/0009` is the correction: the two predicates Diaconescu compares are
 * literal abstractions, `Kernel.abs` supplies extensionality for exactly those, and
 * `Classical.EXCLUDED_MIDDLE` is a theorem resting on the choice axiom and nothing else. It was
 * reachable from the moment choice landed, which is before this file, choice having been asserted
 * for this file's sake. `docs/adr/0007` had it right and this comment contradicted the record.
 *
 * So the count argument that decided this divergence is gone. It read "assert upstream's form and
 * the excluded middle beside it, and that is two axioms where this is one", and it is now one axiom
 * and a derivation either way: what the alternative costs is the two definitions below plus a
 * derivation, not a second thing to believe. Both forms hold in the intended model, with `ind` the
 * naturals, `f` the successor and `z` zero, and over a logic with the excluded middle the two are
 * interchangeable, which is why upstream can prefer the weaker-looking one.
 *
 * **And since 2026-09-11 the other half of the comparison is measured rather than supposed.**
 * `InfinitySpec` writes the derivation out — the weak form **assumed** rather than asserted, so the
 * trusted base is untouched and what comes back carries the weak form on its left — and it is
 * **1957 inferences, reaching one axiom**, which is choice and which this development already has.
 * It read 1648 on 2026-09-24, the rules under it having got cheaper; the one axiom is what
 * `InfinitySpec` asserts and the count is what it prints.
 *
 * That number settles the shape of the argument. It is not a cost paid per development, because a
 * derived strong form would be a fact in this file like any other and derived once. So the reason
 * to keep the divergence is neither the missing excluded middle, which was wrong, nor the cost of
 * repeating the derivation, which is paid once: it is that **the asserted form is the one the
 * construction reads**, and a trusted base is a thing somebody reads.
 *
 * What the measurement buys, beyond the number, is that the divergence is now **checked**. A reader
 * comparing this file against Harrison had to take it on trust that the two forms agree; the test
 * derives one from the other, so they agree or the suite is red.
 *
 * **The divergence may still be the right one; what is recorded here is that its original reason no
 * longer holds and that the alternative now has a price tag.** Switching is a decision of its own
 * and was deliberately not made in passing, which `docs/adr/0009` records under that heading rather
 * than leaving to a reader of this comment.
 *
 * Two definitions do not appear as a result. `ONE_ONE` and `ONTO` exist upstream to state the
 * weaker form and are not otherwise needed, so they are not defined.
 *
 * == The successor and zero are named, not assumed ==
 *
 * The axiom says a suitable `f` and `z` exist and gives no term for either. `Classical.witness`
 * turns each existential into a name, which is the operation the choice axiom was asserted for and
 * the reason it had to land first: `Kernel.defineType` wants a closed predicate, and a witness
 * pulled out by eliminating an existential is a variable.
 */
final class Natural private (
  val classical: Classical,
  val theory: Theory,
  val notation: Notation,
  val axioms: Map[String, Kernel.Thm],
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) {

  import Natural.*

  /**
   * The logic, reading and building against **this** theory rather than the bare one.
   *
   * A rule that has to build a quantifier at `num` asks a theory for the constant at that type, and
   * the logic's own theory has never heard of `num`. So the connectives are taken over the theory
   * that has, which `Logic.over` checks is an extension rather than assuming it.
   */
  val logic: Logic = classical.logic
    .over(theory)
    .fold(error => throw new IllegalStateException(s"the logic does not extend: ${error.message}"), identity)

  /** The axiom named, as a theorem with no hypotheses. */
  def axiom(name: String): Either[LogicError, Kernel.Thm] =
    axioms.get(name).toRight(MissingDefinition(name))

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /**
   * `|- !e f. ?fn. fn ZERO = e /\ (!n. fn (SUC n) = f (fn n) n)`.
   *
   * Definition by recursion, derived rather than assumed, and computed once per development because
   * it is the one fact here that is expensive and not everything wants it. `Recursion` is the file.
   */
  lazy val recursion: Either[LogicError, Kernel.Thm] = Recursion.theorem(this)

  /** A derived fact of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** Read a proposition in this theory's notation. */
  def proposition(text: String): Either[LogicError, Term] =
    Parser.proposition(theory, notation, text)

  /** Read a term of any type in this theory's notation. */
  def term(text: String): Either[LogicError, Term] =
    Parser.term(theory, notation, text)

  /** Print a term in this theory's notation. */
  def show(term: Term): String = Show.show(notation, term)
}

object Natural {

  /** The type the naturals are carved out of, which nothing else interprets. */
  val Individuals: String = "ind"

  /** The axiom's name. */
  val Infinity: String = "INFINITY"

  /** The successor on `ind`, named out of the axiom. */
  val Successor: String = "IND_SUC"

  /** The point of `ind` that is no successor, named out of the axiom. */
  val Zero: String = "IND_0"

  /** The two properties the axiom asserts of that pair, as one derived fact. */
  val SuccessorProperties: String = "IND_SUC_0"

  /** The predicate that picks the naturals out of `ind`: the smallest inductive set. */
  val Representation: String = "NUM_REP"

  /** The type carved out by that predicate. */
  val TypeName: String = "num"

  /** The two halves of the bijection, as `Kernel.defineType` names them. */
  val Abstraction: String = "mk_num"
  val RepresentationFunction: String = "dest_num"

  /** `|- NUM_REP IND_0`, the witness the type definition needs. */
  val ZeroIsRepresented: String = "NUM_REP_0"

  /** The two theorems `Kernel.defineType` returns. */
  val AbstractionOfRepresentation: String = "NUM_ABS_REP"
  val Characterisation: String = "NUM_REP_ABS"

  /** Zero and the successor, on the new type rather than on `ind`. */
  val NumberZero: String = "ZERO"
  val NumberSuccessor: String = "SUC"

  /** `|- !j. NUM_REP j ==> NUM_REP (IND_SUC j)`, which the induction step needs. */
  val RepresentationClosed: String = "NUM_REP_SUC"

  /** `|- !n:num. NUM_REP (dest_num n)`, which is how a number reaches its representative. */
  val RepresentationOfNumber: String = "NUM_REP_DEST"

  /** `|- !P. P ZERO /\ (!n. P n ==> P (SUC n)) ==> !n. P n`. */
  val Induction: String = "NUM_INDUCTION"

  /** `|- !n. ~(SUC n = ZERO)`, the first of Peano's that is not induction. */
  val SuccessorNotZero: String = "NUM_SUC_NOT_ZERO"

  /** `|- !m n. SUC m = SUC n ==> m = n`. */
  val SuccessorInjective: String = "NUM_SUC_INJECTIVE"

  /** `|- !n. n = ZERO \/ ?m. n = SUC m`, which is how a proof splits on a number. */
  val ZeroOrSuccessor: String = "NUM_CASES"

  /** The induction principle, as the text a person checks it by. */
  val InductionStatement: String =
    "!P:num->bool. P ZERO /\\ (!n:num. P n ==> P (SUC n)) ==> !n:num. P n"

  /**
   * Everything this development asks anyone to believe, as text.
   *
   * One statement, in the concrete syntax, for the reason `docs/adr/0004` gives for the sixteen: it
   * is checked by reading it against a source, and builder calls are not read.
   */
  val Axioms: Vector[(String, String)] = Vector(
    Infinity ->
      "?f:ind->ind. ?z:ind. (!x:ind. !y:ind. f x = f y ==> x = y) /\\ (!x:ind. ~(f x = z))"
  )

  /** The standard development, over the standard classical logic. */
  lazy val standard: Natural =
    construct(Classical.standard).fold(
      error => throw new IllegalStateException(s"the naturals do not build: ${error.message}"),
      identity
    )

  /** The development over a classical logic of one's own. */
  def construct(classical: Classical): Either[LogicError, Natural] =
    construct(classical, classical.theory, classical.notation)

  /**
   * The same, over a theory that already holds something else.
   *
   * What it is for: `Real.construct(classical.logic, classical.theory)` and then this over the
   * result puts the reals and the naturals in **one** signature, where a function from one to the
   * other can be stated. Two chains from one root cannot do that, however compatible they are:
   * neither theory can read the other's theorems, which is a fact about the signature and not
   * about the mathematics.
   *
   * **The notation comes with the theory and is not the logic's.** A chain that goes through the
   * reals reads `0 < x + 1`, and the logic's notation does not know `<` or `+`; a version of this
   * that kept `classical.notation` built the theory and then could not read a proposition in it,
   * which is how that came to be a parameter.
   */
  def construct(
    classical: Classical,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Natural] = {
    /**
     * Replace the chosen term by the constant just defined for it.
     *
     * `witness` gives `|- A (select A)`, and the whole of that term is written out at every
     * occurrence, which is why upstream names the two immediately. The definition is
     * `|- name = select A`, so its symmetric form rewrites the argument and congruence carries the
     * rewrite into the application: two kernel steps and no rewriter.
     */
    def named(
      theory: Theory,
      name: String,
      chosen: Kernel.Thm
    ): Either[LogicError, (Theory, Kernel.Thm, Kernel.Thm)] =
      chosen.conclusion match {
        case App(predicate, term) =>
          for {
            defined <- LogicError.lift(Kernel.defineConstant(theory, name, term))
            (extended, definition) = defined
            symmetric <- Conv.sym(definition)
            congruence <- Conv.apTerm(predicate, symmetric)
            over <- LogicError.lift(Kernel.eqMp(congruence, chosen))
            reduction <- Conv.betaRoot(over.conclusion)
            reduced <- LogicError.lift(Kernel.eqMp(reduction, over))
          } yield (extended, definition, reduced)

        case other => Left(NotOfForm("a predicate applied to what was chosen", other))
      }

    for {
      declared <- LogicError.lift(base.declareTypeOperator(Individuals, 0))

      asserted <- Axioms.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](
        Right((declared, Map.empty))
      ) { (acc, entry) =>
        val (name, text) = entry
        for {
          current <- acc
          statement <- Parser.proposition(current._1, notation, text)
          added <- LogicError.lift(Kernel.assertAxiom(current._1, statement))
        } yield (added._1, current._2.updated(name, added._2))
      }
      (withAxiom, axioms) = asserted
      infinity <- axioms.get(Infinity).toRight(MissingDefinition(Infinity))

      // `?f. ?z. P f z` names `f` first, and what comes back still says `?z`, so the second call
      // names that. Each is the choice operator doing the one thing it was asserted for.
      chosenSuccessor <- classical.witness(infinity)
      successor <- named(withAxiom, Successor, chosenSuccessor)
      (withSuccessor, successorDefinition, remaining) = successor

      chosenZero <- classical.witness(remaining)
      zero <- named(withSuccessor, Zero, chosenZero)
      (withZero, zeroDefinition, properties) = zero

      // The naturals are the smallest subset of `ind` holding zero and closed under the successor,
      // said as a predicate rather than as a construction: `x` is one exactly when every inductive
      // predicate holds of it. Induction is then not a further assumption, it is this definition
      // read back.
      representationBody <- Parser.term(
        withZero,
        notation,
        "\\x:ind. !P:ind->bool. P IND_0 /\\ (!j:ind. P j ==> P (IND_SUC j)) ==> P x"
      )
      defined <- LogicError.lift(Kernel.defineConstant(withZero, Representation, representationBody))
      (withRepresentation, representationDefinition) = defined

      individuals = TyApp(Individuals, Nil)
      zeroTerm <- LogicError.lift(withRepresentation.constant(Zero, individuals))
      represented <- zeroIsRepresented(classical, representationDefinition, zeroTerm)

      typed <- LogicError.lift(
        Kernel.defineType(
          withRepresentation,
          TypeName,
          Abstraction,
          RepresentationFunction,
          represented
        )
      )
      (withType, bijection) = typed

      // Zero and the successor, carried across the bijection. Definitions and not assumptions: the
      // successor of a number is what the successor on `ind` does to its representative, read back.
      numbers = TyApp(TypeName, Nil)
      zeroBody <- Parser.term(withType, notation, "mk_num IND_0")
      withNumberZero <- LogicError.lift(Kernel.defineConstant(withType, NumberZero, zeroBody))
      successorBody <- Parser.term(
        withNumberZero._1,
        notation,
        "\\n:num. mk_num (IND_SUC (dest_num n))"
      )
      withNumberSuccessor <- LogicError.lift(
        Kernel.defineConstant(withNumberZero._1, NumberSuccessor, successorBody)
      )
      complete = withNumberSuccessor._1

      closed <- closedUnderSuccessor(classical, complete, representationDefinition)
      represents <- representsEveryNumber(classical, complete, bijection._1, bijection._2)
      // The connectives, built against the theory that has `num` rather than the bare one, which is
      // what lets a rule construct a quantifier over the new type. `Logic.over` checks the extension.
      wider <- classical.logic.over(complete)

      peano <- peanoFacts(
        wider,
        complete,
        properties,
        bijection,
        (withNumberZero._2, withNumberSuccessor._2),
        closed,
        represents,
        represented
      )
      induction <- inductionPrinciple(
        classical,
        complete,
        notation,
        representationDefinition,
        bijection,
        (withNumberZero._2, withNumberSuccessor._2),
        (represented, closed, represents)
      )
      splitting <- zeroOrSuccessor(wider, complete, notation, induction)
    } yield new Natural(
      classical,
      withNumberSuccessor._1,
      notation,
      axioms,
      Map(
        Successor -> successorDefinition,
        Zero -> zeroDefinition,
        Representation -> representationDefinition,
        NumberZero -> withNumberZero._2,
        NumberSuccessor -> withNumberSuccessor._2
      ),
      Map(
        SuccessorProperties -> properties,
        ZeroIsRepresented -> represented,
        AbstractionOfRepresentation -> bijection._1,
        Characterisation -> bijection._2,
        RepresentationClosed -> closed,
        RepresentationOfNumber -> represents,
        Induction -> induction,
        SuccessorNotZero -> peano._1,
        SuccessorInjective -> peano._2,
        ZeroOrSuccessor -> splitting
      )
    )
  }

  /**
   * `|- !j. NUM_REP j ==> NUM_REP (IND_SUC j)`.
   *
   * The half of induction that lives below the type. Unfolded, being represented means that every
   * inductive predicate holds of you, so given one it holds of `j` because `j` is represented, and
   * then of `IND_SUC j` because it is inductive. Nothing about the new type appears in it, which is
   * why it comes first.
   */
  private def closedUnderSuccessor(
    classical: Classical,
    theory: Theory,
    definition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = classical.logic
    val rules = logic.rules
    val individuals = TyApp(Individuals, Nil)
    val j = Term.variable("j", individuals)

    for {
      successor <- LogicError.lift(theory.constant(Successor, Type.fun(individuals, individuals)))
      successorOfJ <- LogicError.lift(Term.app(successor, j))

      atSuccessor <- Conv.unfold(definition, List(successorOfJ))
      claim <- rightOf(atSuccessor)
      stripped <- Logic.stripForall(claim)
      predicate <- stripped._1.headOption.toRight(NotOfForm("a claim about every predicate", claim))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (inductive, _) = parts

      atJ <- Conv.unfold(definition, List(j))
      represented <- leftOf(atJ)
      assumed <- LogicError.lift(Kernel.assume(represented))
      opened <- LogicError.lift(Kernel.eqMp(atJ, assumed))

      assumedInductive <- LogicError.lift(Kernel.assume(inductive))
      holdsAtJ <- rules.spec(predicate, opened).flatMap(rules.mp(_, assumedInductive))
      step <- rules.conjElim2(assumedInductive)
      holdsAtSuccessor <- rules.spec(j, step).flatMap(rules.mp(_, holdsAtJ))

      body <- rules.disch(inductive, holdsAtSuccessor).flatMap(rules.gen(predicate, _))
      folded <- Conv.sym(atSuccessor).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, body)))
      result <- rules.disch(represented, folded).flatMap(rules.gen(j, _))
    } yield result
  }

  /**
   * `|- !n:num. NUM_REP (dest_num n)`.
   *
   * The bridge the other way. `mk_num (dest_num n) = n` is one of the two theorems the type
   * definition returns, and applying `dest_num` to both sides gives exactly the right-hand side of
   * the characterisation at `dest_num n`, so being represented follows from it rather than being
   * assumed anywhere.
   */
  private def representsEveryNumber(
    classical: Classical,
    theory: Theory,
    abstraction: Kernel.Thm,
    characterisation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = classical.logic.rules
    val individuals = TyApp(Individuals, Nil)
    val numbers = TyApp(TypeName, Nil)
    val n = Term.variable("n", numbers)

    for {
      representation <- LogicError.lift(
        theory.constant(RepresentationFunction, Type.fun(numbers, individuals))
      )
      representative <- LogicError.lift(Term.app(representation, n))

      // The two theorems come back over the variables `Kernel.defineType` names them with, and those
      // are free rather than bound, so a use site instantiates instead of specialising.
      atNumber <- LogicError.lift(
        Kernel.inst(Map(Term.variable("a", numbers) -> n), abstraction)
      )
      applied <- Conv.apTerm(representation, atNumber)

      atRepresentative <- LogicError.lift(
        Kernel.inst(
          Map(Term.variable("r", individuals) -> representative),
          characterisation
        )
      )
      represented <- Conv
        .sym(atRepresentative)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, applied)))
      result <- rules.gen(n, represented)
    } yield result
  }

  /**
   * `|- !P. P ZERO /\ (!n. P n ==> P (SUC n)) ==> !n. P n`.
   *
   * Induction, and it is the definition of `NUM_REP` read back rather than anything new to believe.
   *
   * The predicate that does the work is `\x. NUM_REP x /\ P (mk_num x)`, over `ind` and not over
   * the new type. It holds of `IND_0`, because zero is represented and `ZERO` is `mk_num IND_0`; it
   * is closed under `IND_SUC`, because representation is and because `SUC (mk_num k)` is
   * `mk_num (IND_SUC k)` once `k` is known to be represented; so every representative satisfies it,
   * and every number has one. The bijection carries the result back.
   *
   * **The statement is read from text and every piece is taken off it** rather than built. The
   * connectives and quantifiers of `Logic` are constructed against the logic's own theory, which has
   * never heard of `num`, so a quantifier over the new type cannot be built there at all. It is also
   * the form a person checks the theorem by, and the last line asserts that what came out is what
   * was written.
   */
  private def inductionPrinciple(
    classical: Classical,
    theory: Theory,
    notation: Notation,
    definition: Kernel.Thm,
    bijection: (Kernel.Thm, Kernel.Thm),
    numbers: (Kernel.Thm, Kernel.Thm),
    lemmas: (Kernel.Thm, Kernel.Thm, Kernel.Thm)
  ): Either[LogicError, Kernel.Thm] = {
    val logic = classical.logic
    val rules = logic.rules
    val individuals = TyApp(Individuals, Nil)
    val numberType = TyApp(TypeName, Nil)
    val (abstraction, characterisation) = bijection
    val (zeroDefinition, successorDefinition) = numbers
    val (zeroRepresented, closed, represents) = lemmas

    def normalised(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv.betaNormalise(theorem.conclusion).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, theorem)))

    for {
      goal <- Parser.proposition(theory, notation, InductionStatement)
      stripped <- Logic.stripForall(goal)
      predicate <- stripped._1.headOption.toRight(NotOfForm("a claim about every predicate", goal))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (hypothesis, conclusion) = parts
      overNumbers <- Logic.stripForall(conclusion)
      number <- overNumbers._1.headOption.toRight(NotOfForm("a claim about every number", conclusion))

      assumed <- LogicError.lift(Kernel.assume(hypothesis))
      base <- rules.conjElim1(assumed)
      step <- rules.conjElim2(assumed)

      makeNumber <- LogicError.lift(theory.constant(Abstraction, Type.fun(individuals, numberType)))
      takeApart <- LogicError.lift(
        theory.constant(RepresentationFunction, Type.fun(numberType, individuals))
      )
      representation <- LogicError.lift(
        theory.constant(Representation, Type.fun(individuals, Type.Bool))
      )
      successor <- LogicError.lift(theory.constant(Successor, Type.fun(individuals, individuals)))

      x = Term.variable("x", individuals)
      representedAt <- LogicError.lift(Term.app(representation, x))
      holdsAt <- LogicError.lift(Term.app(makeNumber, x).flatMap(Term.app(predicate, _)))
      inductive <- logic
        .mkConj(representedAt, holdsAt)
        .flatMap(conj => LogicError.lift(Term.abs(x, conj)))

      // Being represented, at that predicate, with the redexes contracted so that what it says is
      // comparable with what is derived below.
      representative <- LogicError.lift(Term.app(takeApart, number))
      isRepresented <- rules.spec(number, represents)
      unfolded <- Conv.unfold(definition, List(representative))
      opened <- LogicError.lift(Kernel.eqMp(unfolded, isRepresented))
      instance <- rules.spec(inductive, opened).flatMap(normalised)

      premises <- logic
        .destImp(instance.conclusion)
        .toRight(NotOfForm("an implication", instance.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      atZero <- Conv
        .apTerm(predicate, zeroDefinition)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, base)))
      baseHalf <- rules.conjIntro(zeroRepresented, atZero)
      _ <-
        if (baseHalf.conclusion == baseTerm) Right(())
        else Left(NotOfForm("the base case as the predicate states it", baseHalf.conclusion))

      stepStripped <- Logic.stripForall(stepTerm)
      k <- stepStripped._1.headOption
        .toRight(NotOfForm("a claim about every representative", stepTerm))
      stepParts <- logic.destImp(stepStripped._2).toRight(NotOfForm("an implication", stepStripped._2))
      (before, after) = stepParts

      assumedBefore <- LogicError.lift(Kernel.assume(before))
      representedK <- rules.conjElim1(assumedBefore)
      holdsAtK <- rules.conjElim2(assumedBefore)

      representedSuccessor <- rules.spec(k, closed).flatMap(rules.mp(_, representedK))

      atK <- LogicError.lift(
        Kernel.inst(Map(Term.variable("r", individuals) -> k), characterisation)
      )
      takenApart <- LogicError.lift(Kernel.eqMp(atK, representedK))

      madeK <- LogicError.lift(Term.app(makeNumber, k))
      atSuccessorOfK <- rules.spec(madeK, step).flatMap(rules.mp(_, holdsAtK))
      successorUnfolded <- Conv.unfold(successorDefinition, List(madeK))
      inSuccessor <- Conv.apTerm(successor, takenApart)
      inNumber <- Conv.apTerm(makeNumber, inSuccessor)
      successorIs <- Conv.trans(successorUnfolded, inNumber)
      carried <- Conv.apTerm(predicate, successorIs)
      holdsAtSuccessor <- LogicError.lift(Kernel.eqMp(carried, atSuccessorOfK))

      stepBody <- rules.conjIntro(representedSuccessor, holdsAtSuccessor)
      _ <-
        if (stepBody.conclusion == after) Right(())
        else Left(NotOfForm("the step as the predicate states it", stepBody.conclusion))
      stepHalf <- rules.disch(before, stepBody).flatMap(rules.gen(k, _))

      both <- rules.conjIntro(baseHalf, stepHalf)
      atRepresentative <- rules.mp(instance, both)
      holdsThere <- rules.conjElim2(atRepresentative)

      backAt <- LogicError.lift(
        Kernel.inst(Map(Term.variable("a", numberType) -> number), abstraction)
      )
      back <- Conv.apTerm(predicate, backAt)
      holdsAtNumber <- LogicError.lift(Kernel.eqMp(back, holdsThere))

      result <- rules
        .gen(number, holdsAtNumber)
        .flatMap(rules.disch(hypothesis, _))
        .flatMap(rules.gen(predicate, _))

      _ <-
        if (result.conclusion == goal) Right(())
        else Left(NotOfForm("the induction principle as it is written", result.conclusion))
    } yield result
  }

  /**
   * `|- !n. ~(SUC n = ZERO)` and `|- !m n. SUC m = SUC n ==> m = n`.
   *
   * Peano's other two, carried across the bijection from the pair the axiom of infinity gave. Both
   * run the same way: apply `dest_num` to an assumed equation between numbers, collapse each side
   * to the `ind` behind it, and use there the property the axiom asserts of `IND_SUC` and `IND_0`.
   *
   * Collapsing a side is where the representation is needed, and it is the only interesting step:
   * `dest_num (mk_num r) = r` holds for a represented `r` and for nothing else, so each side has to
   * be shown represented first, which is what [[closedUnderSuccessor]] and [[representsEveryNumber]]
   * are for and why they come before this.
   */
  private def peanoFacts(
    logic: Logic,
    theory: Theory,
    properties: Kernel.Thm,
    bijection: (Kernel.Thm, Kernel.Thm),
    definitions: (Kernel.Thm, Kernel.Thm),
    closed: Kernel.Thm,
    represents: Kernel.Thm,
    zeroRepresented: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val individuals = TyApp(Individuals, Nil)
    val numbers = TyApp(TypeName, Nil)
    val (abstraction, characterisation) = bijection
    val (zeroDefinition, successorDefinition) = definitions
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    /** `|- dest_num (mk_num r) = r`, given that `r` is represented. */
    def unwrap(proof: Kernel.Thm, subject: Term): Either[LogicError, Kernel.Thm] =
      LogicError
        .lift(
          Kernel.inst(Map(Term.variable("r", individuals) -> subject), characterisation)
        )
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, proof)))

    for {
      makeNumber <- LogicError.lift(theory.constant(Abstraction, Type.fun(individuals, numbers)))
      takeApart <- LogicError.lift(theory.constant(RepresentationFunction, Type.fun(numbers, individuals)))
      successor <- LogicError.lift(theory.constant(Successor, Type.fun(individuals, individuals)))
      indZero <- LogicError.lift(theory.constant(Zero, individuals))
      numberSuccessor <- LogicError.lift(theory.constant(NumberSuccessor, Type.fun(numbers, numbers)))
      numberZero <- LogicError.lift(theory.constant(NumberZero, numbers))

      // `|- dest_num (SUC k) = IND_SUC (dest_num k)`, which both facts start from.
      collapse = (k: Term) =>
        for {
          representative <- LogicError.lift(Term.app(takeApart, k))
          inside <- LogicError.lift(Term.app(successor, representative))
          isRepresented <- rules.spec(k, represents)
          closedThere <- rules.spec(representative, closed).flatMap(rules.mp(_, isRepresented))
          unfolded <- Conv.unfold(successorDefinition, List(k))
          applied <- Conv.apTerm(takeApart, unfolded)
          value <- unwrap(closedThere, inside)
          result <- Conv.trans(applied, value)
        } yield result

      atM <- collapse(m)
      atN <- collapse(n)

      // `|- dest_num ZERO = IND_0`, the other side of the first equation. Two steps and not one:
      // unfolding zero gives `dest_num (mk_num IND_0)`, and getting from there to `IND_0` is the
      // characterisation, which holds because zero is represented. Leaving the second step out
      // produced an equation that did not meet the property, and what reported it was a variable
      // that would not generalise several inferences later rather than the step itself.
      atMakeZero <- Conv.apTerm(takeApart, zeroDefinition)
      zeroValue <- unwrap(zeroRepresented, indZero)
      atZero <- Conv.trans(atMakeZero, zeroValue)

      // Never zero. The assumption is carried into `ind` and meets `~(IND_SUC x = IND_0)`.
      successorOfN <- LogicError.lift(Term.app(numberSuccessor, n))
      isZero <- LogicError.lift(Term.eq(successorOfN, numberZero))
      assumedZero <- LogicError.lift(Kernel.assume(isZero))
      carriedZero <- Conv.apTerm(takeApart, assumedZero)
      fromSuccessor <- Conv.sym(atN)
      throughZero <- Conv.trans(fromSuccessor, carriedZero)
      insideZero <- Conv.trans(throughZero, atZero)

      representativeN <- LogicError.lift(Term.app(takeApart, n))
      never <- rules.conjElim2(properties).flatMap(rules.spec(representativeN, _))
      absurd <- rules.notElim(never, insideZero)
      notZero <- rules.notIntro(isZero, absurd).flatMap(rules.gen(n, _))

      // Injective. The same carrying, then the property on the other conjunct, then back across
      // the bijection.
      successorOfM <- LogicError.lift(Term.app(numberSuccessor, m))
      same <- LogicError.lift(Term.eq(successorOfM, successorOfN))
      assumedSame <- LogicError.lift(Kernel.assume(same))
      carriedSame <- Conv.apTerm(takeApart, assumedSame)
      fromM <- Conv.sym(atM)
      throughSame <- Conv.trans(fromM, carriedSame)
      insideSame <- Conv.trans(throughSame, atN)

      representativeM <- LogicError.lift(Term.app(takeApart, m))
      sameRepresentative <- rules
        .conjElim1(properties)
        .flatMap(rules.specAll(_, List(representativeM, representativeN)))
        .flatMap(rules.mp(_, insideSame))

      carriedBack <- Conv.apTerm(makeNumber, sameRepresentative)
      backM <- LogicError.lift(
        Kernel.inst(Map(Term.variable("a", numbers) -> m), abstraction)
      )
      backN <- LogicError.lift(
        Kernel.inst(Map(Term.variable("a", numbers) -> n), abstraction)
      )
      fromNumber <- Conv.sym(backM)
      throughMake <- Conv.trans(fromNumber, carriedBack)
      equal <- Conv.trans(throughMake, backN)
      injective <- rules.disch(same, equal).flatMap(rules.genAll(_, List(m, n)))
    } yield (notZero, injective)
  }

  /**
   * `|- !n. n = ZERO \/ ?m. n = SUC m`.
   *
   * How a proof splits on a number, and an induction whose step never uses its hypothesis: the
   * successor of anything is a successor, whatever the thing was.
   */
  private def zeroOrSuccessor(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    induction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(TypeName, Nil)

    for {
      predicate <- Parser.term(theory, notation, "\\k:num. k = ZERO \\/ ?j:num. k = SUC j")
      instance <- rules.spec(predicate, induction)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))

      premises <- logic.destImp(opened.conclusion).toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      (baseTerm, stepTerm) = halves

      zero <- LogicError.lift(theory.constant(NumberZero, numbers))
      baseSides <- logic.destDisj(baseTerm).toRight(NotOfForm("a disjunction", baseTerm))
      base <- rules.disjIntro1(baseSides._2, Conv.refl(zero))

      stripped <- Logic.stripForall(stepTerm)
      k <- stripped._1.headOption.toRight(NotOfForm("a claim about every number", stepTerm))
      stepParts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (before, after) = stepParts
      sides <- logic.destDisj(after).toRight(NotOfForm("a disjunction", after))
      existential <- logic.destExistsPredicate(sides._2).toRight(NotOfForm("an existential", sides._2))

      successor <- LogicError.lift(theory.constant(NumberSuccessor, Type.fun(numbers, numbers)))
      successorOfK <- LogicError.lift(Term.app(successor, k))
      witnessed <- rules.existsIntro(existential, k, Conv.refl(successorOfK))
      injected <- rules.disjIntro2(sides._1, witnessed)
      step <- rules.disch(before, injected).flatMap(rules.gen(k, _))

      result <- rules.conjIntro(base, step).flatMap(rules.mp(opened, _))
    } yield result
  }

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  /**
   * `|- NUM_REP IND_0`, which is what makes the type inhabited.
   *
   * Zero satisfies every inductive predicate because every inductive predicate holds of zero: the
   * derivation is the definition unfolded, the conjunction assumed, and its first half taken. It is
   * the shortest proof in this file and the one without which nothing else here is allowed to
   * happen, since a type defined over a predicate nothing satisfies is a bijection with the empty.
   */
  private def zeroIsRepresented(
    classical: Classical,
    definition: Kernel.Thm,
    zero: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = classical.logic.rules

    for {
      unfolded <- Conv.unfold(definition, List(zero))
      claim <- Term.destEq(unfolded.conclusion).map(_._2).toRight(NotOfForm("an equation", unfolded.conclusion))

      stripped <- Logic.stripForall(claim)
      (variables, body) = stripped
      predicate <- variables.headOption.toRight(NotOfForm("a claim about every predicate", claim))

      parts <- classical.logic.destImp(body).toRight(NotOfForm("an implication", body))
      (inductive, atZero) = parts

      assumed <- LogicError.lift(Kernel.assume(inductive))
      base <- rules.conjElim1(assumed)
      _ <-
        if (base.conclusion == atZero) Right(())
        else Left(NotOfForm("the base case as the first conjunct", base.conclusion))

      discharged <- rules.disch(inductive, base)
      generalised <- rules.gen(predicate, discharged)

      symmetric <- Conv.sym(unfolded)
      result <- LogicError.lift(Kernel.eqMp(symmetric, generalised))
    } yield result
  }
}
