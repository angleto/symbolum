package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The type of a pair, carved out of the functions that recognise one component pair.
 *
 * The second use of `Kernel.defineType` in this repository and the first that is not the naturals.
 * A gap audit of a consumer found that lists, finite words, matrices and index types are all
 * unstatable here and traced every one of them to the same absence, which its item A10 wrote as
 * *"inductive data types and user-defined relations do not exist, so a rewriting system is not even
 * statable in the kernel"*. The primitive underneath all four is the product: a finite word is a
 * length together with a function, a matrix is a function on a pair of indices, and neither can be
 * written down until a pair is a term rather than a pair of terms.
 *
 * == The construction, and why it is this one ==
 *
 * Transcribed from HOL Light's `pair.ml`. A pair `(x, y)` is represented by the function
 * `\u v. u = x /\ v = y`, which is `true` at exactly one argument pair, and the type is the image
 * of that representation inside `'a -> 'b -> bool`:
 *
 * {{{
 *   mk_pair = \x. \y. \u. \v. u = x /\ v = y
 *   prod    = { p : 'a -> 'b -> bool | ?x y. p = mk_pair x y }
 * }}}
 *
 * Nothing else in this file is a choice. `PAIR`, `FST` and `SND` are **defined constants**, the six
 * facts of [[Product.Statements]] are derived, the two the rule returns are not asserted either, and `Theory.axioms` does not move: `ProductSpec` compares it against the
 * classical theory this was built over rather than against a number written down here.
 *
 * **What the type definition needs before it will run is a witness**, and that is the whole of the
 * work the rule pushes onto a caller. `Kernel.defineType` takes `|- P w` rather than `|- ?x. P x`,
 * for the reason `docs/adr/0006` gives — the kernel knows equality and has no existential — so
 * [[Product.pairIsRepresented]] proves `|- P (mk_pair x y)` and hands that down. The two free
 * variables in the argument are not a defect and are not checked by the rule: the witness appears
 * in neither theorem the rule returns, so nothing about `x` and `y` escapes into the type. What is
 * checked, and what matters, is that the **predicate** is closed.
 *
 * == The choice operator is paid for once, by the projections ==
 *
 * `FST` and `SND` are defined by choice, `FST p = select (\x. ?y. p = PAIR x y)`, which is
 * upstream's definition and the only route this logic has: the components of a pair exist by
 * [[Product.Cases]] and no term denotes them until something names them. So the projection facts
 * reach `SELECT` and [[Product.Cases]] and [[Product.PairInjective]] reach no axiom at all, which
 * `ProductSpec` measures by walking each proof rather than by reading the imports. Eta is not
 * reached by anything here.
 *
 * == What is not here ==
 *
 * No notation. `(x, y)` is written `PAIR x y`, because a comma is already the structural separator
 * `Notation.Structural` uses inside a type application and giving it a second meaning in terms is a
 * change to the reader of every existing statement rather than to this file. A consumer that wants
 * the infix form is the reason to make that change, and there is not one yet.
 *
 * No currying, no `UNCURRY` and no pair-induction. Each is a further step and each would be derived
 * rather than assumed; what is here is the floor the audit asked for: the type, the constructor,
 * the two projections, and the six laws that make them usable.
 *
 * `prod` was on that list of absences until 2026-09-12, as "no `prod` in `Chain.standard`". It is
 * in it now, third of the five developments that were threaded in that day and directly under `Word`,
 * which is the one consumer that needs it. See `Chain`'s own comment for the order and for what
 * being in the chain buys that being beside it did not.
 */
final class Product private (
  val classical: Classical,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /**
   * The logic, reading and building against **this** theory rather than the bare one.
   *
   * Same widening `Natural` performs and for the same reason: a rule that has to build a quantifier
   * over `prod('a,'b)` asks a theory for the quantifier at that type, and the classical logic's own
   * theory has never heard of `prod`.
   */
  val logic: Logic = classical.logic
    .over(theory)
    .fold(
      error => throw new IllegalStateException(s"the logic does not extend: ${error.message}"),
      identity
    )

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

}

object Product {

  /** The representation of a pair as a function: `\x y u v. u = x /\ v = y`. */
  val PairFunction: String = "mk_pair"

  /** The type carved out of `'a -> 'b -> bool` by the image of that function. */
  val TypeName: String = "prod"

  /** The two halves of the bijection, as `Kernel.defineType` names them. */
  val Abstraction: String = "mk_prod"
  val RepresentationFunction: String = "dest_prod"

  /** The constructor and the two projections, all three defined. */
  val Pairing: String = "PAIR"
  val First: String = "FST"
  val Second: String = "SND"

  /** The two theorems `Kernel.defineType` returns, named as `Natural` names its pair. */
  val AbstractionOfRepresentation: String = "PROD_ABS_REP"
  val Characterisation: String = "PROD_REP_ABS"

  /** `|- !x y. dest_prod (PAIR x y) = mk_pair x y`, the bridge every other fact crosses. */
  val RepresentationOfPair: String = "PROD_REP_PAIR"

  /**
   * `|- !x y u v. (PAIR x y = PAIR u v) = (x = u /\ y = v)`.
   *
   * Stated as a biconditional rather than as the implication `Natural.SuccessorInjective` uses,
   * because the converse here is one congruence step and a consumer rewriting with the law wants
   * both directions. It is spelled `_INJECTIVE` and not `_EQ` because `docs/naming.md` forbids a
   * second spelling of a concept the corpus already spells one way.
   */
  val PairInjective: String = "PAIR_INJECTIVE"

  /** `|- !x y. FST (PAIR x y) = x` and `|- !x y. SND (PAIR x y) = y`. */
  val FirstOfPair: String = "FST_PAIR"
  val SecondOfPair: String = "SND_PAIR"

  /** `|- !p. ?x y. p = PAIR x y`, which is how a proof splits on a pair. */
  val Cases: String = "PROD_CASES"

  /** `|- !p. p = PAIR (FST p) (SND p)`: surjective pairing. */
  val Surjective: String = "PAIR_SURJECTIVE"

  /**
   * The type variables the development is stated over, as the parser names them.
   *
   * They are the classical extension's two, which is not a coincidence to be tidied away: the
   * choice axiom is stated over `'a` and [[First]] is defined by choice at `'a`, so a disagreement
   * about the name would look like the axiom failing to apply.
   */
  val Domain: Type = TyVar(Classical.TypeVariable)
  val Codomain: Type = TyVar(Classical.CodomainVariable)

  /** `'a -> 'b -> bool`, the type the new one is carved out of. */
  val Representing: Type = Type.fun(Domain, Type.fun(Codomain, Type.Bool))

  /** `prod('a,'b)`, the type this file exists to define. */
  val Pairs: Type = TyApp(TypeName, List(Domain, Codomain))

  /** The bodies of the four definitions, as text, in the order they are introduced. */
  val Definitions: Vector[(String, String)] = Vector(
    PairFunction -> "\\x:'a. \\y:'b. \\u:'a. \\v:'b. u = x /\\ v = y",
    Pairing -> "\\x:'a. \\y:'b. mk_prod (mk_pair x y)",
    First -> "\\p:prod('a,'b). select (\\x:'a. ?y:'b. p = PAIR x y)",
    Second -> "\\p:prod('a,'b). select (\\y:'b. ?x:'a. p = PAIR x y)"
  )

  /**
   * The predicate the type is the image of, as text.
   *
   * Kept as a lambda rather than given a constant of its own, which is where this diverges from
   * `Natural`: `NUM_REP` is defined because induction is that definition read back and a dozen
   * derivations unfold it, while nothing here ever mentions this predicate except the three steps
   * that cross the bijection. Upstream makes the same choice in `pair.ml`, and a constant would put
   * a name in the signature that no statement in this file uses.
   */
  val RepresentationBody: String = "\\p:'a->'b->bool. ?x:'a. ?y:'b. p = mk_pair x y"

  /**
   * What every derived fact says, as text, in the order they are derived.
   *
   * The device `Classical.Statements` uses and for its stated purpose: the kernel checked that each
   * of these is a theorem, and what is unchecked is that the **derivation arrived at the statement
   * intended**. `ProductSpec` parses each of these and compares it with what came out, so a proof
   * that reaches a true theorem about the wrong thing fails the build.
   *
   * Compared as terms rather than as printed text, which the monomorphic developments do not need
   * to do. A type variable is written `'a` and printed `a`, so a printed statement here does not
   * read back, and comparing the parse is the stronger check of the two anyway.
   */
  val Statements: Vector[(String, String)] = Vector(
    RepresentationOfPair -> "!x:'a. !y:'b. dest_prod (PAIR x y) = mk_pair x y",
    PairInjective ->
      "!x:'a. !y:'b. !u:'a. !v:'b. (PAIR x y = PAIR u v) = (x = u /\\ y = v)",
    FirstOfPair -> "!x:'a. !y:'b. FST (PAIR x y) = x",
    SecondOfPair -> "!x:'a. !y:'b. SND (PAIR x y) = y",
    Cases -> "!p:prod('a,'b). ?x:'a. ?y:'b. p = PAIR x y",
    Surjective -> "!p:prod('a,'b). p = PAIR (FST p) (SND p)"
  )

  /** The standard development, over the standard classical logic. */
  lazy val standard: Product =
    construct(Classical.standard).fold(
      error => throw new IllegalStateException(s"the product type does not build: ${error.message}"),
      identity
    )

  /** The development over a classical logic of one's own. */
  def construct(classical: Classical): Either[LogicError, Product] =
    construct(classical, classical.theory, classical.notation)

  /**
   * The same, over a theory that already holds something else.
   *
   * The chain entry point, for the reason `Natural.construct` documents: two developments built
   * beside each other cannot read each other's theorems, so a pair of naturals needs `prod` and
   * `num` in one signature and that means this over that rather than both over `Classical`.
   */
  def construct(
    classical: Classical,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Product] = {
    def define(
      theory: Theory,
      name: String,
      text: String
    ): Either[LogicError, (Theory, Kernel.Thm)] =
      for {
        body <- Parser.term(theory, notation, text)
        defined <- LogicError.lift(Kernel.defineConstant(theory, name, body))
      } yield defined

    for {
      pair <- define(base, PairFunction, Definitions(0)._2)
      (withPair, pairDefinition) = pair

      predicate <- Parser.term(withPair, notation, RepresentationBody)
      narrow <- classical.logic.over(withPair)
      witness <- pairIsRepresented(narrow, withPair, predicate, sample(Domain), sample(Codomain))

      typed <- LogicError.lift(
        Kernel.defineType(withPair, TypeName, Abstraction, RepresentationFunction, witness)
      )
      (withType, bijection) = typed

      pairing <- define(withType, Pairing, Definitions(1)._2)
      (withPairing, pairingDefinition) = pairing
      first <- define(withPairing, First, Definitions(2)._2)
      (withFirst, firstDefinition) = first
      second <- define(withFirst, Second, Definitions(3)._2)
      (complete, secondDefinition) = second

      wider <- classical.logic.over(complete)

      representation <- representationOfPair(
        wider,
        complete,
        predicate,
        bijection._2,
        pairingDefinition
      )
      injective <- pairInjective(wider, complete, pairDefinition, representation)
      firstFact <- projection(classical, wider, complete, firstDefinition, injective, taking = 1)
      secondFact <- projection(classical, wider, complete, secondDefinition, injective, taking = 2)
      cases <- productCases(wider, complete, bijection, pairingDefinition)
      surjective <- surjectivePairing(wider, complete, cases, firstFact, secondFact)

      facts = Map(
        AbstractionOfRepresentation -> bijection._1,
        Characterisation -> bijection._2,
        RepresentationOfPair -> representation,
        PairInjective -> injective,
        FirstOfPair -> firstFact,
        SecondOfPair -> secondFact,
        Cases -> cases,
        Surjective -> surjective
      )

      // Each statement checked against the text a person reads it by, here rather than in the spec:
      // a development that built something other than what it says it built must not be handed out
      // at all, which is the guard `Induct.proveBy` and `Bounded.prove` both end with.
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { (acc, entry) =>
        val (name, text) = entry
        for {
          _ <- acc
          expected <- Parser.proposition(complete, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Product(
      classical,
      complete,
      notation,
      Map(
        PairFunction -> pairDefinition,
        Pairing -> pairingDefinition,
        First -> firstDefinition,
        Second -> secondDefinition
      ),
      facts
    )
  }

  /* --------------------------------------------------------------- the derivations */

  /**
   * `|- P (mk_pair x y)`, with `P` the representation predicate and the application left standing.
   *
   * What `Kernel.defineType` will not run without, and the shortest derivation in the file: the
   * predicate says something is `mk_pair` of two things, and `mk_pair x y` is `mk_pair` of two
   * things by reflexivity. The two existentials are introduced against the predicates read off the
   * contraction rather than against predicates built here, so that what is proved is syntactically
   * the instance the rule will take apart; building the same term twice and trusting that they
   * agree is how `Rules.existsIntro` comes to refuse a correct step.
   *
   * **The application is not contracted**, for the reason `Classical.witness` documents: the rule
   * reads `P` off the outermost application, so the reduced form would define the type of things
   * equal to this one pair rather than the type of pairs.
   */
  private def pairIsRepresented(
    logic: Logic,
    theory: Theory,
    predicate: Term,
    x: FVar,
    y: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      pairFunction <- LogicError.lift(theory.constant(PairFunction, pairFunctionType))
      representative <- LogicError.lift(Term.appAll(pairFunction, List(x, y)))

      applied <- LogicError.lift(Term.app(predicate, representative))
      contraction <- Conv.betaRoot(applied)
      goal <- rightOf(contraction)

      outer <- logic
        .destExistsPredicate(goal)
        .toRight(NotOfForm("a claim that something is a pair", goal))
      atFirst <- LogicError.lift(Term.app(outer, x))
      innerContraction <- Conv.betaRoot(atFirst)
      innerGoal <- rightOf(innerContraction)
      inner <- logic
        .destExistsPredicate(innerGoal)
        .toRight(NotOfForm("a claim about a second component", innerGoal))

      second <- rules.existsIntro(inner, y, Conv.refl(representative))
      both <- rules.existsIntro(outer, x, second)
      result <- Conv.sym(contraction).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, both)))
    } yield result
  }

  /**
   * `|- !x y. dest_prod (PAIR x y) = mk_pair x y`.
   *
   * The bridge from the constructor to the representation, and the fact every other derivation here
   * crosses. `PAIR x y` unfolds to `mk_prod (mk_pair x y)`, and `dest_prod` undoes `mk_prod` on a
   * term that satisfies the predicate and on nothing else, which is what the characterisation the
   * type definition returned says and why [[pairIsRepresented]] is needed a second time.
   */
  private def representationOfPair(
    logic: Logic,
    theory: Theory,
    predicate: Term,
    characterisation: Kernel.Thm,
    pairingDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = sample(Domain)
    val y = sample(Codomain)

    for {
      pairFunction <- LogicError.lift(theory.constant(PairFunction, pairFunctionType))
      takeApart <- LogicError.lift(
        theory.constant(RepresentationFunction, Type.fun(Pairs, Representing))
      )
      representative <- LogicError.lift(Term.appAll(pairFunction, List(x, y)))

      holds <- pairIsRepresented(logic, theory, predicate, x, y)
      // The characterisation comes back over the variable `Kernel.defineType` names it with, which
      // is free rather than bound, so a use site instantiates instead of specialising.
      at <- LogicError.lift(
        Kernel.inst(Map(Term.variable("r", Representing) -> representative), characterisation)
      )
      equation <- LogicError.lift(Kernel.eqMp(at, holds))

      unfolded <- Conv.unfold(pairingDefinition, List(x, y))
      carried <- Conv.apTerm(takeApart, unfolded)
      joined <- Conv.trans(carried, equation)
      result <- rules.genAll(joined, List(x, y))
    } yield result
  }

  /**
   * `|- !x y u v. (PAIR x y = PAIR u v) = (x = u /\ y = v)`.
   *
   * Both directions, put together by `Kernel.deductAntisym`, which is what a biconditional is in
   * this kernel: equality at `bool`. There is no `mkIff` in the repository and none was added, the
   * two-theorem form being one primitive call.
   *
   * The forward direction is the one with content. Apply `dest_prod` to the assumed equation, cross
   * to `mk_pair x y = mk_pair u v` by [[RepresentationOfPair]], then apply **both** sides to `x` and
   * `y`: the left reduces to `x = x /\ y = y` and the right to `x = u /\ y = v`, so the pair of
   * reflexivities transports across the equation into the conclusion. Applying at `u` and `v`
   * instead would reduce the left to `u = x /\ v = y` and prove the same thing the other way round;
   * applying at anything else proves nothing.
   *
   * The converse is congruence and needs no property of pairs at all.
   */
  private def pairInjective(
    logic: Logic,
    theory: Theory,
    pairDefinition: Kernel.Thm,
    representation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = sample(Domain)
    val y = sample(Codomain)
    val u = Term.variable("u", Domain)
    val v = Term.variable("v", Codomain)

    for {
      pairing <- LogicError.lift(theory.constant(Pairing, pairingType))
      takeApart <- LogicError.lift(
        theory.constant(RepresentationFunction, Type.fun(Pairs, Representing))
      )

      left <- LogicError.lift(Term.appAll(pairing, List(x, y)))
      right <- LogicError.lift(Term.appAll(pairing, List(u, v)))
      same <- LogicError.lift(Term.eq(left, right))

      assumed <- LogicError.lift(Kernel.assume(same))
      carried <- Conv.apTerm(takeApart, assumed)
      atLeft <- rules.specAll(representation, List(x, y))
      atRight <- rules.specAll(representation, List(u, v))
      fromLeft <- Conv.sym(atLeft)
      throughLeft <- Conv.trans(fromLeft, carried)
      representatives <- Conv.trans(throughLeft, atRight)

      appliedFirst <- Conv.apThm(representatives, x)
      applied <- Conv.apThm(appliedFirst, y)
      trivial <- Conv.unfold(pairDefinition, List(x, y, x, y))
      wanted <- Conv.unfold(pairDefinition, List(u, v, x, y))
      fromTrivial <- Conv.sym(trivial)
      chained <- Conv.trans(fromTrivial, applied)
      whole <- Conv.trans(chained, wanted)

      reflexive <- rules.conjIntro(Conv.refl(x), Conv.refl(y))
      forward <- LogicError.lift(Kernel.eqMp(whole, reflexive))

      firstEqual <- LogicError.lift(Term.eq(x, u))
      secondEqual <- LogicError.lift(Term.eq(y, v))
      both <- logic.mkConj(firstEqual, secondEqual)
      assumedBoth <- LogicError.lift(Kernel.assume(both))
      firstHalf <- rules.conjElim1(assumedBoth)
      secondHalf <- rules.conjElim2(assumedBoth)
      partial <- Conv.apTerm(pairing, firstHalf)
      backward <- LogicError.lift(Kernel.mkComb(partial, secondHalf))

      equivalence = Kernel.deductAntisym(backward, forward)
      result <- rules.genAll(equivalence, List(x, y, u, v))
    } yield result
  }

  /**
   * `|- !x y. FST (PAIR x y) = x`, and with `taking = 2` the same for `SND`.
   *
   * One function for both, because the two derivations differ in three places and agree in eleven,
   * and a copy would be a copy that drifts. The three: which half of [[PairInjective]] is taken,
   * which of the two components is the witness that the chosen predicate holds of something, and
   * which position the chosen term occupies in the pair the existential produces.
   *
   * The shape is the one the definition forces. `FST p` is `select Q` for `Q u` saying that `p` is
   * a pair with `u` in front; `Q` holds of `x` by reflexivity, so the choice axiom gives `Q` of what
   * it selected, and injectivity turns that into `select Q = x`. The choice axiom is specialised at
   * the predicate read off the unfolded definition rather than at one built here, for the reason
   * `Rules.mp` gives: an antecedent that does not match is left standing as a hypothesis instead of
   * being reported, so a predicate that is equal-looking and not equal comes back as a true theorem
   * with a premise nobody asked for.
   */
  private def projection(
    classical: Classical,
    logic: Logic,
    theory: Theory,
    definition: Kernel.Thm,
    injective: Kernel.Thm,
    taking: Int
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = sample(Domain)
    val y = sample(Codomain)
    val chosenType = if (taking == 1) Domain else Codomain
    val witnessType = if (taking == 1) Codomain else Domain

    for {
      pairing <- LogicError.lift(theory.constant(Pairing, pairingType))
      subject <- LogicError.lift(Term.appAll(pairing, List(x, y)))

      unfolded <- Conv.unfold(definition, List(subject))
      chosen <- rightOf(unfolded)
      predicate <- chosen match {
        case App(_, predicate) if Term.typeOf(chosen) == chosenType => Right(predicate)
        case other => Left(NotOfForm(s"a choice at $chosenType", other))
      }

      // `Q x` for `FST`, `Q y` for `SND`: the component this projection is about is the one the
      // predicate is known to hold of.
      known = if (taking == 1) x else y
      atKnown <- LogicError.lift(Term.app(predicate, known))
      contraction <- Conv.betaRoot(atKnown)
      goal <- rightOf(contraction)
      inner <- logic
        .destExistsPredicate(goal)
        .toRight(NotOfForm("a claim that the other component exists", goal))
      other = if (taking == 1) y else x
      exists <- rules.existsIntro(inner, other, Conv.refl(subject))
      holds <- Conv.sym(contraction).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, exists)))

      // At `'b` for `SND`, where the axiom is stated over `'a`. Without it the specialisation is
      // a type error rather than a wrong theorem, which is the good case and still a refusal.
      choice <- classical.axiom(Classical.Choice)
      atType = Kernel.instType(Map(Classical.TypeVariable -> chosenType), choice)
      instance <- rules.specAll(atType, List(predicate, known))
      selected <- rules.mp(instance, holds)

      opened <- Conv
        .betaRoot(selected.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, selected)))
      witnessed <- logic
        .destExistsPredicate(opened.conclusion)
        .toRight(NotOfForm("a claim about the other component", opened.conclusion))

      w = Conv.freshVariable("w", witnessType, freeIn(opened) ++ Term.freeVariables(witnessed))
      instanceTerm <- LogicError.lift(Term.app(witnessed, w)).flatMap(Conv.betaRoot).flatMap(rightOf)
      assumed <- LogicError.lift(Kernel.assume(instanceTerm))

      arguments = if (taking == 1) List(x, y, chosen, w) else List(x, y, w, chosen)
      law <- rules.specAll(injective, arguments)
      components <- LogicError.lift(Kernel.eqMp(law, assumed))
      half <- if (taking == 1) rules.conjElim1(components) else rules.conjElim2(components)
      flipped <- Conv.sym(half)

      eliminated <- rules.existsElim(opened, w, flipped)
      joined <- Conv.trans(unfolded, eliminated)
      result <- rules.genAll(joined, List(x, y))
    } yield result
  }

  /**
   * `|- !p. ?x y. p = PAIR x y`.
   *
   * How a proof splits on a pair, and the fact that makes the type worth having rather than merely
   * inhabited: every element of it is a pair of something. It is the characterisation read the
   * other way round. `mk_prod (dest_prod p) = p` is the first theorem the type definition returned,
   * so `dest_prod (mk_prod (dest_prod p)) = dest_prod p` is one congruence step, and that is
   * exactly the right-hand side of the characterisation at `dest_prod p` — so the predicate holds
   * there, which says `dest_prod p` is `mk_pair` of two things, and `mk_prod` carries that back.
   *
   * No axiom is reached. `ProductSpec` measures it rather than taking this sentence for it.
   */
  private def productCases(
    logic: Logic,
    theory: Theory,
    bijection: (Kernel.Thm, Kernel.Thm),
    pairingDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val (abstraction, characterisation) = bijection
    val p = Term.variable("p", Pairs)

    for {
      makePair <- LogicError.lift(theory.constant(Abstraction, Type.fun(Representing, Pairs)))
      takeApart <- LogicError.lift(
        theory.constant(RepresentationFunction, Type.fun(Pairs, Representing))
      )
      representative <- LogicError.lift(Term.app(takeApart, p))

      atPair <- LogicError.lift(
        Kernel.inst(Map(Term.variable("a", Pairs) -> p), abstraction)
      )
      carried <- Conv.apTerm(takeApart, atPair)
      at <- LogicError.lift(
        Kernel.inst(Map(Term.variable("r", Representing) -> representative), characterisation)
      )
      holds <- Conv.sym(at).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, carried)))
      opened <- Conv
        .betaRoot(holds.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, holds)))

      outer <- logic
        .destExistsPredicate(opened.conclusion)
        .toRight(NotOfForm("a claim that the representative is a pair", opened.conclusion))
      taken = freeIn(opened) ++ Term.freeVariables(outer)
      x = Conv.freshVariable("x", Domain, taken)
      innerTerm <- LogicError.lift(Term.app(outer, x)).flatMap(Conv.betaRoot).flatMap(rightOf)
      assumedInner <- LogicError.lift(Kernel.assume(innerTerm))
      inner <- logic
        .destExistsPredicate(innerTerm)
        .toRight(NotOfForm("a claim about a second component", innerTerm))
      y = Conv.freshVariable("y", Codomain, taken + x)
      equationTerm <- LogicError.lift(Term.app(inner, y)).flatMap(Conv.betaRoot).flatMap(rightOf)
      assumedEquation <- LogicError.lift(Kernel.assume(equationTerm))

      lifted <- Conv.apTerm(makePair, assumedEquation)
      fromPair <- Conv.sym(atPair)
      through <- Conv.trans(fromPair, lifted)
      unfolded <- Conv.unfold(pairingDefinition, List(x, y))
      target <- Conv.sym(unfolded).flatMap(Conv.trans(through, _))

      innerPredicate <- LogicError.lift(Term.abs(y, target.conclusion))
      introduced <- rules.existsIntro(innerPredicate, y, target)
      outerPredicate <- LogicError.lift(Term.abs(x, introduced.conclusion))
      both <- rules.existsIntro(outerPredicate, x, introduced)

      withoutSecond <- rules.existsElim(assumedInner, y, both)
      withoutFirst <- rules.existsElim(opened, x, withoutSecond)
      result <- rules.gen(p, withoutFirst)
    } yield result
  }

  /**
   * `|- !p. p = PAIR (FST p) (SND p)`: surjective pairing, and the fact a consumer needs.
   *
   * [[Cases]] says a pair is *some* pair and gives no name to either component; this says it is the
   * pair of its own projections, which is what lets a proof rewrite `p` away without introducing a
   * variable. It costs the projections and therefore costs `SELECT`, where [[Cases]] costs nothing.
   */
  private def surjectivePairing(
    logic: Logic,
    theory: Theory,
    cases: Kernel.Thm,
    firstFact: Kernel.Thm,
    secondFact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val p = Term.variable("p", Pairs)

    for {
      pairing <- LogicError.lift(theory.constant(Pairing, pairingType))
      takeFirst <- LogicError.lift(theory.constant(First, Type.fun(Pairs, Domain)))
      takeSecond <- LogicError.lift(theory.constant(Second, Type.fun(Pairs, Codomain)))

      instance <- rules.spec(p, cases)
      outer <- logic
        .destExistsPredicate(instance.conclusion)
        .toRight(NotOfForm("a claim that it is a pair", instance.conclusion))
      taken = freeIn(instance) ++ Term.freeVariables(outer)
      x = Conv.freshVariable("x", Domain, taken)
      innerTerm <- LogicError.lift(Term.app(outer, x)).flatMap(Conv.betaRoot).flatMap(rightOf)
      assumedInner <- LogicError.lift(Kernel.assume(innerTerm))
      inner <- logic
        .destExistsPredicate(innerTerm)
        .toRight(NotOfForm("a claim about a second component", innerTerm))
      y = Conv.freshVariable("y", Codomain, taken + x)
      equationTerm <- LogicError.lift(Term.app(inner, y)).flatMap(Conv.betaRoot).flatMap(rightOf)
      assumedEquation <- LogicError.lift(Kernel.assume(equationTerm))

      atFirst <- rules.specAll(firstFact, List(x, y))
      atSecond <- rules.specAll(secondFact, List(x, y))
      carriedFirst <- Conv.apTerm(takeFirst, assumedEquation).flatMap(Conv.trans(_, atFirst))
      carriedSecond <- Conv.apTerm(takeSecond, assumedEquation).flatMap(Conv.trans(_, atSecond))

      partial <- Conv.apTerm(pairing, carriedFirst)
      rebuilt <- LogicError.lift(Kernel.mkComb(partial, carriedSecond))
      back <- Conv.sym(assumedEquation).flatMap(Conv.trans(rebuilt, _))
      target <- Conv.sym(back)

      withoutSecond <- rules.existsElim(assumedInner, y, target)
      withoutFirst <- rules.existsElim(instance, x, withoutSecond)
      result <- rules.gen(p, withoutFirst)
    } yield result
  }

  /* ------------------------------------------------------------------- internals */

  /**
   * Every variable free anywhere in a theorem.
   *
   * `Rules.freeIn` is the same function and is `private[logic]`, so it does not reach here. Copied
   * rather than widened: the four lines are not the part of that file worth sharing, and widening
   * an access modifier for a caller outside the module is a change to the logic's surface.
   */
  private def freeIn(theorem: Kernel.Thm): Set[FVar] =
    theorem.hypotheses.foldLeft(Term.freeVariables(theorem.conclusion)) { (acc, hypothesis) =>
      acc ++ Term.freeVariables(hypothesis)
    }

  /** `'a -> 'b -> 'a -> 'b -> bool`. */
  private def pairFunctionType: Type =
    Type.fun(Domain, Type.fun(Codomain, Representing))

  /** `'a -> 'b -> prod('a,'b)`. */
  private def pairingType: Type = Type.fun(Domain, Type.fun(Codomain, Pairs))

  /** The variable a statement about an arbitrary component is stated over. */
  private def sample(ty: Type): FVar =
    Term.variable(if (ty == Domain) "x" else "y", ty)

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
