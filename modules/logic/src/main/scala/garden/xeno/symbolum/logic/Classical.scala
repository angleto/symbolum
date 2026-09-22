package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * The classical half of the logic: a choice operator, eta, and what the two of them buy.
 *
 * Everything in [[Logic]] is a definitional extension: eight connectives, no axiom, and a theory
 * that proves exactly what the empty one proves. This file breaks that, deliberately and twice, and
 * `docs/adr/0007` is the record of why.
 *
 * == What is asserted ==
 *
 * Two axioms, both HOL Light's and both about the formalism rather than about a domain.
 *
 * {{{
 *   select : ('a -> bool) -> 'a
 *   SELECT : !P x. P x ==> P (select P)
 *   ETA    : !t:'a->'b. (\x. t x) = t
 * }}}
 *
 * `SELECT` says nothing about what `select P` is when `P` holds of nothing, exactly as the field
 * axioms say nothing about `inv 0`: the constant is total because every function in this logic is,
 * and the theory constrains it only where something satisfies the predicate.
 *
 * `ETA` is the weaker of the two forms extensionality comes in, and it is the one upstream asserts.
 * The pointwise statement, `(!x. f x = g x) ==> f = g`, is what callers want and is **derived** from
 * it below, as [[Classical.FunctionExtensionality]] and as the rule [[ext]]. Asserting the small
 * statement and deriving the large one is the trade this project makes everywhere else.
 *
 * == What is defined, which is one constant and costs nothing ==
 *
 * {{{
 *   COND : bool -> 'a -> 'a -> 'a
 *   COND p a b = select (\x. (p ==> x = a) /\ (~p ==> x = b))
 * }}}
 *
 * The conditional, and until 2026-09-12 **the chain had none at all**: a `grep` over `modules/logic`
 * and `modules/theories` found no constant of that shape anywhere, so a function defined by cases
 * had nothing to write its cases with. The case that surfaced it was extending a word by one
 * letter, which is three branches on a condition.
 *
 * It is a definition and not an axiom, so the count of nineteen `CLAUDE.md` describes does not move
 * and `ChainSpec` says so. What it does cost is a constant in the trusted signature and a row in
 * `docs/reading-register.md`, which enters as `NOT READ` like every other row there.
 *
 * == Why the conditional is here and not in a development ==
 *
 * Because the definition mentions `select` and nothing else. Every alternative home is a
 * development in `modules/theories`, and a constant defined there is unavailable to everything
 * **below** it in `Chain`: a conditional living in `Word` could not be used by `Peano`, and one
 * living in `Peano` could not be used by `Natural`. Defined here it sits under every link there is,
 * which is the property a conditional has to have, since anything at all can be defined by cases.
 * Upstream makes the same call and for the same reason: `COND` is in `class.ml`, beside the choice
 * operator it is built from.
 *
 * == Its precedence, which is that it has none ==
 *
 * `COND p a b` is written as an ordinary application and is read and printed at
 * `Notation.ApplicationPrecedence` like any other constant. **No row was added to the precedence
 * table**, and that is a decision rather than an omission.
 *
 * What a reader coming from another system expects is `if p then a else b`, and this notation
 * cannot express it. [[Notation]] offers four shapes, infix, prefix, binder and numerals, and
 * every one of them is fixed at one or two arguments; a three-place mixfix with two keywords is a
 * change to the parser's grammar and to the printer, not an entry in a table. That is a worthwhile
 * change and it is a different one from this, which is why it is written down here instead of done:
 * it would have to carry its own round-trip evidence, and `NotationRoundTripSpec` currently gets
 * `parse(show(t)) == t` for this constant free, because an application is what the printer already
 * writes and what the parser already reads.
 *
 * == What is derived, and what each derivation rests on ==
 *
 * Nothing below this line is asserted. Each of [[Classical.Statements]] is a theorem,
 * `Derivation.axiomsOf` says which of the two axioms it reaches, and `Derivation.size` says what it
 * cost.
 *
 * **The table is in `docs/proving.md`, under "The excluded middle is derived", and it is
 * generated**: `sbt "theories/runMain garden.xeno.symbolum.theories.Guide"` writes it and `GuideSpec` fails
 * when the document and the derivations disagree. It used to be written out here as well, and the
 * two copies are why: on 2026-09-11 `Conv.refl` began sharing the reflexivity of an atom, every
 * step count in both moved, and both were repaired by hand afterwards because nothing compared
 * either with a derivation. A rule with two implementation sites is a defect while the two agree,
 * and a Scaladoc cannot carry a splice marker without the marker showing up in the rendered page.
 *
 * What is here instead is the division, which `ClassicalSpec` asserts against the derivations
 * themselves: two of the nine reach **no axiom at all** and are collected by this extension rather
 * than bought by it, [[Classical.Eta]] pays for [[Classical.FunctionExtensionality]], and
 * [[Classical.Choice]] pays for the other six. Neither axiom appears in the other's derivations,
 * and the two conditional equations are on choice's side of that line: they go to `SELECT` directly
 * and never through the excluded middle, which a case split would have made them pay for twice.
 *
 * Beside them are three derived rules a caller reasons with rather than a theorem they instantiate:
 * [[cases]], which every tactic wanting a case split will reach for, [[contradiction]], and [[ext]].
 *
 * `~` takes the widest argument this notation allows, which is why a negated side of an equation is
 * parenthesised in [[Classical.Statements]]: `~(p \/ q) = (~p /\ ~q)` reads as `~((p \/ q) = (~p /\
 * ~q))`.
 *
 * == The excluded middle costs no axiom of its own, and this file used to say otherwise ==
 *
 * The note that stood here said `p \/ ~p` was out of reach because Diaconescu's argument wants
 * extensionality as well as choice. That is true of the argument and false of this kernel, and the
 * derivation below is the correction. Diaconescu compares two predicates over `bool`,
 *
 * {{{
 *   U = \x. x = T \/ p        V = \x. x = F \/ p
 * }}}
 *
 * and needs `U = V` from the fact that each holds of everything when `p` does. Both are **literal
 * abstractions**, and `Kernel.abs` takes `s = t` to `(\x. s) = (\x. t)`: that is function
 * extensionality already, restricted to functions that are written as lambdas. What `ETA` adds is
 * the rest of the range, a function arriving as a variable or a constant, by letting any `f` be
 * read as `\x. f x`. Diaconescu never needs that, so the argument goes through on `SELECT` and the
 * kernel's ten rules, and the two eliminations that finish it need no decision about whether the
 * two chosen values are equal.
 *
 * Propositional extensionality, the other half people count, is `Kernel.deductAntisym` and has been
 * in the trusted base since the beginning: two propositions each derivable from the other are
 * equal, which is what makes `bool` a type of truth values rather than of proofs.
 *
 * **So `ETA` is not what the excluded middle is bought with, and its justification is elsewhere.**
 * It is `SUM_CONGRUENCE` in `modules/theories/.../Series.scala`, which exists only because
 * extensionality was absent: the rewriter goes into the lambda `Sum` binds, so a summand written
 * out moves where it stands, and a summand that arrives as a bare symbol does not. That lemma is an
 * induction, and every future operator that binds a variable was going to want its own, products
 * and integrals and maxima. With [[ext]] the pointwise hypothesis gives the two functions equal and
 * congruence carries that into any binder at all, which is one rule instead of a lemma per
 * operator. **Nothing has cashed that in yet**: `Series.congruent` still proves `SUM_CONGRUENCE` by
 * induction, so what is delivered here is the rule and not yet the saving.
 *
 * == Why they are here and not in `Logic` ==
 *
 * So that a development can be asked which of its results need them. `Logic.standard` stays free of
 * axioms and this is an extension beside it, which costs a caller one more thing to construct and
 * buys the property that the classical commitment is visible in the module graph rather than global.
 * `RealSpec`'s scan of the sources for `Kernel.assertAxiom` names this file, and `ClassicalSpec`
 * runs the same scan over this module alone; the file list did not change when the second axiom
 * landed, because the second axiom is in the file the first is in, and the counts changed instead.
 *
 * == Why choice came before the naturals, which is the reason it exists at all ==
 *
 * `Kernel.defineType` requires a **closed** predicate. A witness obtained by eliminating an
 * existential is a variable, so a predicate built from it is not closed and cannot define a type.
 * The naturals are carved out of a type whose successor function the axiom of infinity says
 * *exists*, and that function therefore has to be **named** before anything can be carved with it.
 * Naming a witness is what a choice operator is for, and [[witness]] below is that operation.
 *
 * == The divergences from HOL Light, and both are spellings ==
 *
 * Upstream calls the choice operator `@` and writes `(@) P`. Measured on 2026-09-10, this system's
 * lexer cannot read that character at all, so the constant is `select`. Upstream states eta over
 * the type variables `A` and `B`; this parser spells a type variable `'a`, so the axiom is written
 * over `'a` and `'b`. Neither axiom differs from upstream's in what it says.
 *
 * == What is still not asserted ==
 *
 * The third of HOL Light's three axioms is infinity, and it is not here: it belongs with the
 * naturals and `modules/theories/.../Natural.scala` has it. Nothing else about the formalism is
 * asserted anywhere, and in particular `bool` having exactly two elements is not: `!t. t = T \/ t =
 * F` is upstream's `BOOL_CASES_AX` and is a theorem here, reachable from [[cases]], though nothing
 * has yet needed it enough for it to be derived and pinned.
 */
final class Classical private (
  val logic: Logic,
  val theory: Theory,
  val notation: Notation,
  val axioms: Map[String, Kernel.Thm],
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) {

  import Classical.*

  /** The axiom named, as a theorem with no hypotheses. */
  def axiom(name: String): Either[LogicError, Kernel.Thm] =
    axioms.get(name).toRight(MissingDefinition(name))

  /**
   * The equation defining a constant this extension introduced, as proved when it was introduced.
   *
   * Held here rather than reachable through [[logic]]. `Logic.definitionOf` answers out of the map
   * `Logic.construct` closed over, which holds the eight connectives and nothing added later, so a
   * caller wanting to unfold [[Classical.Conditional]] has to be handed the theorem rather than
   * able to look it up. Adding to that map instead would mean a `Logic` whose definitions depend on
   * which extension was built over it, which is the thing `docs/adr/0008` is about one level down.
   */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived theorem of this extension, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** The choice operator at the type it picks from. */
  def select(ty: Type): Either[LogicError, Term] =
    LogicError.lift(theory.constant(Select, Type.fun(Type.fun(ty, Type.Bool), ty)))

  /** The conditional at the type of its two branches. */
  def conditional(ty: Type): Either[LogicError, Term] =
    LogicError.lift(theory.constant(Conditional, Type.fun(Type.Bool, Type.fun(ty, Type.fun(ty, ty)))))

  /** Read a proposition in this theory's notation. */
  def proposition(text: String): Either[LogicError, Term] =
    Parser.proposition(theory, notation, text)

  /** Read a term of any type in this theory's notation. */
  def term(text: String): Either[LogicError, Term] =
    Parser.term(theory, notation, text)

  /** Print a term in this theory's notation. */
  def show(term: Term): String = Show.show(notation, term)

  /**
   * `|- ?x. P x` becomes `|- P (select P)`: the witness, named.
   *
   * The derived rule the choice axiom exists for, and the operation `Kernel.defineType` cannot do
   * without. An existential says something satisfies the predicate and gives no term for it, and
   * eliminating it gives a *variable*, which is exactly what a rule wanting a closed predicate
   * cannot use. What comes back here names it with a closed term instead.
   *
   * The derivation is the shape the axiom was written for: assume the instance at a fresh variable,
   * specialise the axiom at the predicate and that variable, detach, and eliminate the existential
   * against the result. The variable is free in neither the conclusion nor the predicate, which is
   * what `Rules.existsElim` checks and refuses.
   *
   * **What comes back is the unreduced application, `P (select P)`, and that is deliberate.** Beta
   * reducing it would be tidier to read and would destroy the thing it is for: `Kernel.defineType`
   * takes the predicate off the witness theorem by looking at the outermost application, so
   * `(\x. x = T) (select ...)` hands it the predicate the caller meant, while the reduced
   * `select ... = T` hands it `(= (select ...))`, the predicate that holds of that one term. The
   * first defines the type the caller asked for and the second defines a singleton. A caller who
   * wants the reduced form has `Conv.betaRoot` and should know which of the two they are holding.
   */
  def witness(existential: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    chooseWitness(logic, axioms, existential)

  /**
   * `G |- !x. f x = g x` gives `G |- f = g`: function extensionality, as a rule.
   *
   * What [[Classical.FunctionExtensionality]] says, in the form a derivation uses. The theorem has
   * to be instantiated at two types and two functions before it can be detached, and every caller
   * would write the same four lines; this writes them once.
   *
   * Three things are read off the theorem rather than passed in, and each one is refused when it is
   * not there: the quantification, and that each side of the body is an application of something to
   * the variable quantified. The last is the interesting refusal. `!x. f x = g x` is the shape eta
   * can close, and `!x. f x = c` is not, so a rule that guessed would produce a theorem about
   * `\x. c` rather than about `c`.
   *
   * The variable must also not occur free in either function, which cannot happen for a variable
   * this rule picked fresh unless the quantified body puts it there: `!x. (\y. y + x) x = g x` has
   * `f` mentioning `x`, and then `\x. f x` captures rather than eta-expands. Refused with
   * [[EscapingVariable]], because the alternative is a `trans` that fails to line up several steps
   * later and reports the wrong thing.
   */
  def ext(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      eta <- axiom(Eta)
      result <- extend(logic, eta, theorem)
    } yield result

  /**
   * The same, reading against a signature wider than this one.
   *
   * Detaching eta means specialising it **at the function type**, and a theory refuses a quantifier
   * at a type operator it has never heard of. `Classical.standard` has never heard of `num` or
   * `real`, so a development built over it that wants extensionality between two functions
   * `num -> real` cannot reach it through [[ext]] at all: the axiom is held here and the types are
   * held there.
   *
   * `Divisibility` documents the same widening for quantifier introduction and `Prove.construct`
   * for lemma application. The pattern is the same each time and the reason is the boundary rather
   * than the logic: a polymorphic axiom is stated once and instantiated where the types live.
   */
  def ext(wider: Logic, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      eta <- axiom(Eta)
      result <- extend(wider, eta, theorem)
    } yield result

  /** `|- p \/ ~p` at one proposition, from [[Classical.ExcludedMiddle]]. */
  def excludedMiddleAt(proposition: Term): Either[LogicError, Kernel.Thm] =
    if (!Term.isProposition(proposition)) Left(NotOfForm("a proposition", proposition))
    else fact(ExcludedMiddle).flatMap(logic.rules.spec(proposition, _))

  /**
   * `D |- r` and `E |- r` give `D - {p}, E - {~p} |- r`: the case split.
   *
   * The rule the classical axioms are worth their cost for. Every tactic that wants to know
   * whether something holds before it reasons about it wants this, and until the excluded middle
   * was derived the theory of the reals was the only supplier of a case split: `LT_TOTAL` gave a
   * disjunction about an order, and there was nothing at all for a proposition.
   *
   * A branch that did not use its hypothesis is accepted, which is `Rules.disjElim`'s behaviour and
   * the right one here: a case analysis where one side happens not to need its assumption is still
   * a case analysis. Both branches must prove the same conclusion, which `Rules.disjElim` checks.
   */
  def cases(
    proposition: Term,
    positive: Kernel.Thm,
    negative: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      middle <- excludedMiddleAt(proposition)
      result <- logic.rules.disjElim(middle, positive, negative)
    } yield result

  /**
   * `G |- F` gives `G - {~p} |- p`: proof by contradiction.
   *
   * The converse of `Rules.falsityElim` and the direction this logic could not reach before. Ex
   * falso is intuitionistic and has been available since the connectives were defined; concluding
   * `p` from the absurdity of `~p` is what needs [[Classical.DoubleNegation]] and so needs
   * `SELECT`.
   *
   * `~p` is discharged whether or not it was assumed, which is `Rules.disch`'s behaviour. Unlike
   * the same latitude in `Rules.existsElim`, it cannot mislead: a caller who proved `G |- F`
   * without assuming `~p` gets `G |- p`, which is what they asked for and is true of every `p`.
   */
  def contradiction(proposition: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    if (theorem.conclusion != logic.falsity)
      Left(NotOfForm("a proof of falsity", theorem.conclusion))
    else
      for {
        negation <- logic.mkNot(proposition)
        doubled <- logic.rules.notIntro(negation, theorem)
        general <- fact(DoubleNegation)
        elimination <- logic.rules.spec(proposition, general)
        result <- logic.rules.mp(elimination, doubled)
      } yield result
}

object Classical {

  /** The choice operator's name. HOL Light spells it `@`; this lexer cannot read that character. */
  val Select: String = "select"

  /** The choice axiom's name, as `Theory.axioms` and the test that pins it hold it. */
  val Choice: String = "SELECT"

  /** The eta axiom's name, which is upstream's. */
  val Eta: String = "ETA"

  /**
   * The type variables the axioms are stated over, as the parser names them.
   *
   * Written `'a` and `'b` in the source strings and held as `a` and `b` in the terms, which is what
   * a caller instantiating an axiom has to pass. Named here rather than spelled at each use site,
   * since a disagreement about one would look like the axiom not applying.
   */
  val TypeVariable: String = "a"

  /** The second type variable, which only [[Eta]] has: the codomain of the function. */
  val CodomainVariable: String = "b"

  /** The conditional's name, which is upstream's. */
  val Conditional: String = "COND"

  /**
   * What `COND` is, as text, and the one definition this extension makes.
   *
   * `COND p a b` is the thing that satisfies `(p ==> x = a) /\ (~p ==> x = b)`, named by the choice
   * operator. Something does satisfy it whichever way `p` falls, which is what the two equations
   * below are, and nothing else in the chain could have written this: `select` is declared here and
   * the definition mentions no type but `bool` and its own type variable.
   *
   * **Upstream spells the guards `t <=> T` and `t <=> F` and this spells them `p` and `~p`.** The
   * two say the same thing here (`Kernel.deductAntisym` makes a provable proposition equal to `T`
   * and has been in the trusted base from the start) and the difference is which form a caller
   * meets in [[CondTrue]] and [[CondFalse]]. A caller has a proof of `p`, not a proof of `p = T`,
   * so the guard that detaches without a step in between is the one written here.
   */
  val ConditionalDefinition: String =
    "\\p:bool a:'a b:'a. select (\\x:'a. (p ==> x = a) /\\ (~p ==> x = b))"

  /**
   * Everything this extension asks anyone to believe, as text.
   *
   * Two statements, in the concrete syntax, so that each is checked by reading it against a source
   * rather than by reading builder calls. That is the mitigation `docs/adr/0004` rests on for the
   * sixteen and it is the same one here. Both are transcribed from HOL Light's `class.ml`.
   *
   * The order is the order they were asserted in, which is the order `Theory.axioms` reports and
   * `ClassicalSpec` pins. Choice landed first because `Kernel.defineType` could not name a witness
   * without it; eta landed second because nothing had asked for it until `SUM_CONGRUENCE` did.
   */
  val Axioms: Vector[(String, String)] = Vector(
    Choice -> "!P:'a->bool. !x:'a. P x ==> P (select P)",
    Eta -> "!t:'a->'b. (\\x. t x) = t"
  )

  /** `|- ~(T = F)`. */
  val TruthNotFalsity: String = "TRUTH_NOT_FALSITY"

  /** `|- !f g. (!x. f x = g x) ==> f = g`, from [[Eta]] alone. */
  val FunctionExtensionality: String = "FUNCTION_EXTENSIONALITY"

  /** `|- !p. p \/ ~p`, from [[Choice]] alone. */
  val ExcludedMiddle: String = "EXCLUDED_MIDDLE"

  /** `|- !p. ~~p ==> p`. */
  val DoubleNegation: String = "DOUBLE_NEGATION"

  /** `|- !p q. (~(p \/ q)) = (~p /\ ~q)`, which needs no axiom: it is intuitionistically valid. */
  val DeMorganDisjunction: String = "DE_MORGAN_DISJUNCTION"

  /** `|- !p q. (~(p /\ q)) = (~p \/ ~q)`, which holds the direction that needs the classical step. */
  val DeMorganConjunction: String = "DE_MORGAN_CONJUNCTION"

  /**
   * `|- !P. ~(!x. P x) ==> ?x. ~(P x)`: De Morgan for the universal quantifier.
   *
   * The one this logic did not have, and the absence was load-bearing rather than incidental.
   * `Peano.NUM_ARCHIMEDES` records it in as many words, that the textbook step "`s - 1` is not an
   * upper bound, so take a natural above it" needs exactly this and that the derivation was turned
   * around to avoid it. Turning it around works where the witness is not wanted; the monotone
   * convergence theorem wants the witness, so `Limit` is what finally paid for this.
   *
   * It is classical and cannot be otherwise: the proof assumes the existential is false, derives
   * the universal from it one point at a time through [[DoubleNegation]], and contradicts the
   * hypothesis. Both uses of double negation are the classical step, and the intuitionistic
   * direction, `(?x. ~P x) ==> ~(!x. P x)`, is the one nobody needed.
   */
  val NotForall: String = "NOT_FORALL"

  /** `|- !p a b. p ==> COND p a b = a`, from [[Choice]] alone. */
  val CondTrue: String = "COND_TRUE"

  /** `|- !p a b. ~p ==> COND p a b = b`, from [[Choice]] alone. */
  val CondFalse: String = "COND_FALSE"

  /**
   * What every derived theorem here says, as text, in the order they are derived.
   *
   * The same device as [[Axioms]] used for the opposite purpose. An axiom is written out so that a
   * reader can check it is the statement that was meant; a theorem needs no such check, since the
   * kernel checked it. What this pins is that the **derivation arrived at the statement intended**,
   * which is a different mistake and one nothing else catches: a proof that reaches
   * `!p. p \/ ~p \/ p` is a fine theorem and not the excluded middle. `ClassicalSpec` parses each
   * of these and compares it with what came out.
   *
   * **The parentheses around a negated side of an equation are not decoration.** `~` takes the
   * widest argument this notation allows, so `~(p \/ q) = (~p /\ ~q)` reads as
   * `~((p \/ q) = (~p /\ ~q))`, which is a different and false statement. Measured here on
   * 2026-09-10 by writing the two De Morgan entries without them and watching the comparison fail,
   * which is the check doing its job on the text rather than on the derivation.
   */
  val Statements: Vector[(String, String)] = Vector(
    TruthNotFalsity -> "~(T = F)",
    DeMorganDisjunction -> "!p:bool. !q:bool. (~(p \\/ q)) = (~p /\\ ~q)",
    FunctionExtensionality ->
      "!f:'a->'b. !g:'a->'b. (!x:'a. f x = g x) ==> f = g",
    ExcludedMiddle -> "!p:bool. p \\/ ~p",
    DoubleNegation -> "!p:bool. ~~p ==> p",
    DeMorganConjunction -> "!p:bool. !q:bool. (~(p /\\ q)) = (~p \\/ ~q)",
    NotForall -> "!P:'a->bool. ~(!x:'a. P x) ==> ?x:'a. ~(P x)",
    CondTrue -> "!p:bool. !a:'a. !b:'a. p ==> COND p a b = a",
    CondFalse -> "!p:bool. !a:'a. !b:'a. ~p ==> COND p a b = b"
  )

  /** The standard logic with the classical axioms over it. */
  lazy val standard: Classical =
    construct(Logic.standard).fold(
      error => throw new IllegalStateException(s"the classical theory does not build: ${error.message}"),
      identity
    )

  /** The given logic with the choice operator and the two axioms over it. */
  def construct(logic: Logic): Either[LogicError, Classical] =
    construct(logic, logic.theory, Notation.standard)

  /**
   * The same, over a theory that already holds something else, with the notation that reads it.
   *
   * A development is built **over** another rather than beside it, and this is the entry point for
   * doing that with the choice operator in the middle of a chain. Restarting from `logic.theory`
   * instead, which is what the one-argument form does, silently drops everything the caller had
   * already built: a session tried `Classical.construct(reals.logic)` on 2026-09-10 expecting the
   * reals to come with it, and got a theory that had never heard of them.
   *
   * **The derivations run here rather than on demand**, so a development that does not build is a
   * refusal from this function and not a `Left` from [[Classical.fact]] months later. The largest
   * of the nine is 1155 inference steps and they share most of their nodes, which is small enough
   * that no development is going to want a variant of this that skips them. That figure said 1275
   * until 2026-09-12, which is what it was before the two repairs of 2026-09-11, and 1089 until
   * [[NotForall]] landed on 2026-09-15 and took the top from `DE_MORGAN_CONJUNCTION`;
   * `ClassicalSpec` spells it out of the derivations, so it cannot sit here being wrong again.
   *
   * **The conditional is defined here, between the axioms and the derivations.** A definition is
   * conservative, so the order costs nothing to the trusted base and buys the two equations below
   * the constant they are about.
   */
  def construct(logic: Logic, base: Theory, notation: Notation): Either[LogicError, Classical] = {
    val alpha = TyVar(TypeVariable)
    val schema = Type.fun(Type.fun(alpha, Type.Bool), alpha)

    for {
      declared <- LogicError.lift(base.declareConstant(Select, schema))

      built <- Axioms.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](
        Right((declared, Map.empty))
      ) { (acc, entry) =>
        val (name, text) = entry
        for {
          current <- acc
          statement <- Parser.proposition(current._1, notation, text)
          asserted <- LogicError.lift(Kernel.assertAxiom(current._1, statement))
        } yield (asserted._1, current._2.updated(name, asserted._2))
      }

      (extended, asserted) = built

      body <- Parser.term(extended, notation, ConditionalDefinition)
      defined <- LogicError.lift(Kernel.defineConstant(extended, Conditional, body))
      (withConditional, conditionalDefinition) = defined

      derived <- derive(logic, withConditional, asserted, conditionalDefinition)
    } yield new Classical(
      logic,
      withConditional,
      notation,
      asserted,
      Map(Conditional -> conditionalDefinition),
      derived
    )
  }

  /* ------------------------------------------------------------------ the derivations */

  /**
   * Every theorem this extension offers, proved.
   *
   * Written as one function taking the axioms rather than as methods on the class, because the
   * class holds the results and cannot exist before they are proved. Each step below names what it
   * feeds, and the order is a dependency order: `~(T = F)` is the contradiction the excluded middle
   * ends at, the excluded middle is what the last two want, and eta stands apart from all of it.
   * The two conditional equations stand apart from all of it as well: they go back to the choice
   * axiom directly rather than through the excluded middle, which is why they are last rather than
   * because anything above them feeds them.
   */
  private def derive(
    logic: Logic,
    theory: Theory,
    axioms: Map[String, Kernel.Thm],
    conditional: Kernel.Thm
  ): Either[LogicError, Map[String, Kernel.Thm]] =
    for {
      eta <- axioms.get(Eta).toRight(MissingDefinition(Eta))

      notFalsity <- truthNotFalsity(logic)
      deMorganDisj <- deMorganDisjunction(logic)
      extensionality <- functionExtensionality(logic, eta)
      middle <- excludedMiddle(logic, theory, axioms, notFalsity)
      doubleNegation <- doubleNegationElimination(logic, middle)
      deMorganConj <- deMorganConjunction(logic, middle)
      notForall <- notForallQuantifier(logic, doubleNegation)
      equations <- conditionalEquations(logic, axioms, conditional)
      (condTrue, condFalse) = equations
    } yield Map(
      TruthNotFalsity -> notFalsity,
      DeMorganDisjunction -> deMorganDisj,
      FunctionExtensionality -> extensionality,
      ExcludedMiddle -> middle,
      DoubleNegation -> doubleNegation,
      DeMorganConjunction -> deMorganConj,
      NotForall -> notForall,
      CondTrue -> condTrue,
      CondFalse -> condFalse
    )

  /**
   * `|- !P. ~(!x. P x) ==> ?x. ~(P x)`, and the shape is the double negation used twice.
   *
   * Assume the universal is false and assume the existential is false too. Under both, a point is
   * enough: `~(P x)` would witness the existential, so `~~(P x)` holds, so `P x` by
   * [[DoubleNegation]], and the point was arbitrary, so `!x. P x` follows and contradicts the
   * first assumption. That discharges the second into `~~(?x. ~P x)` and double negation gives the
   * existential.
   *
   * **The generalisation is where this could silently go wrong**, and it is the step to check: `x`
   * is generalised while two hypotheses are still standing, and it is legitimate only because
   * neither of them mentions `x`. They are `~(!x. P x)` and `~(?x. ~P x)`, both closed in `x` by
   * construction, and `Rules.gen` refuses rather than producing a weaker theorem if that ever
   * stops being true.
   */
  private def notForallQuantifier(
    logic: Logic,
    doubleNegation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val element = TyVar(TypeVariable)
    val predicate = Term.variable("P", Type.fun(element, Type.Bool))
    val point = Term.variable("x", element)

    for {
      applied <- LogicError.lift(Term.app(predicate, point))
      negatedPoint <- logic.mkNot(applied)
      universal <- logic.mkForall(point, applied)
      negatedUniversal <- logic.mkNot(universal)
      existential <- logic.mkExists(point, negatedPoint)
      negatedExistential <- logic.mkNot(existential)

      assumedNotUniversal <- LogicError.lift(Kernel.assume(negatedUniversal))
      assumedNotExistential <- LogicError.lift(Kernel.assume(negatedExistential))

      // At an arbitrary point: a counterexample there would witness the existential.
      existentialPredicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      assumedNegatedPoint <- LogicError.lift(Kernel.assume(negatedPoint))
      witnessed <- rules.existsIntro(existentialPredicate, point, assumedNegatedPoint)
      clashAtPoint <- rules.notElim(assumedNotExistential, witnessed)
      doubledPoint <- rules.notIntro(negatedPoint, clashAtPoint)
      atPoint <- rules.spec(applied, doubleNegation).flatMap(rules.mp(_, doubledPoint))

      // The point was arbitrary, and neither standing hypothesis mentions it.
      everywhere <- rules.gen(point, atPoint)
      clash <- rules.notElim(assumedNotUniversal, everywhere)
      doubled <- rules.notIntro(negatedExistential, clash)
      result <- rules
        .spec(existential, doubleNegation)
        .flatMap(rules.mp(_, doubled))
        .flatMap(rules.disch(negatedUniversal, _))
        .flatMap(rules.gen(predicate, _))
    } yield result
  }

  /**
   * `|- ~(T = F)`, which is where the excluded middle's contradiction comes from.
   *
   * Four steps and no axiom. `T` is provable and `F` is `!x:bool. x`, so an equation between them
   * carries the first across into the second, and `Rules.notIntro` discharges the equation. It is
   * the shortest derivation in this file and it was written first, because everything the rest
   * needs goes through it: assuming, eliminating an equation, and discharging.
   */
  private def truthNotFalsity(logic: Logic): Either[LogicError, Kernel.Thm] =
    for {
      statement <- LogicError.lift(Term.eq(logic.truth, logic.falsity))
      assumed <- LogicError.lift(Kernel.assume(statement))
      isTruth <- logic.rules.truth
      absurd <- LogicError.lift(Kernel.eqMp(assumed, isTruth))
      result <- logic.rules.notIntro(statement, absurd)
    } yield result

  /**
   * `|- !f g. (!x. f x = g x) ==> f = g`, from [[Eta]].
   *
   * Assume the pointwise equation, specialise it at a variable, and abstract that variable back
   * out: `Kernel.abs` gives `(\x. f x) = (\x. g x)`, which is the statement about the two
   * eta-expansions. Eta at `f` and at `g` says each expansion is the function it expands, and two
   * transitivities close the gap. That is the whole of it, and it is the shape of the argument
   * upstream uses.
   *
   * The theorem is stated over the axiom's own type variables, so no type instantiation happens
   * here. [[Classical.ext]] is where one does.
   */
  private def functionExtensionality(logic: Logic, eta: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val fnType = Type.fun(TyVar(TypeVariable), TyVar(CodomainVariable))
    val f = Term.variable("f", fnType)
    val g = Term.variable("g", fnType)
    val x = Term.variable("x", TyVar(TypeVariable))

    for {
      atF <- LogicError.lift(Term.app(f, x))
      atG <- LogicError.lift(Term.app(g, x))
      body <- LogicError.lift(Term.eq(atF, atG))
      pointwise <- logic.mkForall(x, body)

      assumed <- LogicError.lift(Kernel.assume(pointwise))
      specialised <- logic.rules.spec(x, assumed)
      // The bound variable of the hypothesis is bound, so `x` is free in nothing the kernel's side
      // condition on abstraction looks at.
      abstracted <- LogicError.lift(Kernel.abs(x, specialised))

      expandedF <- logic.rules.spec(f, eta)
      expandedG <- logic.rules.spec(g, eta)
      fromF <- Conv.sym(expandedF)
      throughLambda <- LogicError.lift(Kernel.trans(fromF, abstracted))
      equal <- LogicError.lift(Kernel.trans(throughLambda, expandedG))

      implied <- logic.rules.disch(pointwise, equal)
      result <- logic.rules.genAll(implied, List(f, g))
    } yield result
  }

  /**
   * `|- !p. p \/ ~p`, from [[Choice]] and the kernel's ten rules.
   *
   * Diaconescu's argument, and the file's scaladoc says what it does and does not need. Over a
   * free `p`, two predicates on `bool`:
   *
   * {{{
   *   U = \x. x = T \/ p        V = \x. x = F \/ p
   * }}}
   *
   *  1. `U` holds of `T` by reflexivity into the left disjunct, so choice gives
   *     `|- select U = T \/ p`.
   *  2. `V` holds of `F` likewise, so `|- select V = F \/ p`.
   *  3. `p |- select U = select V`. Under `p` both predicates hold of every `x`, by the right
   *     disjunct; `Kernel.deductAntisym` makes the two bodies equal, `Kernel.abs` makes the two
   *     predicates equal, and congruence on `select` carries that to the two chosen values.
   *  4. Eliminate the disjunction of 1. Under `p` the goal is the left injection. Under
   *     `select U = T`, eliminate the disjunction of 2: under `p` the goal again, and under
   *     `select V = F` the equation of 3 collapses to `T = F`, which `~(T = F)` refutes, so `~p`
   *     and the goal is the right injection. Every branch reaches `p \/ ~p`, the two eliminations
   *     discharge the four hypotheses, and generalising over `p` finishes.
   *
   * Nothing anywhere in it decides whether `select U` and `select V` are equal, which is the step
   * the argument is usually presented as needing and does not.
   */
  private def excludedMiddle(
    logic: Logic,
    theory: Theory,
    axioms: Map[String, Kernel.Thm],
    notFalsity: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val p = Term.variable("p", Type.Bool)
    val x = Term.variable("x", Type.Bool)

    for {
      chooser <- LogicError.lift(
        theory.constant(Select, Type.fun(Type.fun(Type.Bool, Type.Bool), Type.Bool))
      )

      isTruth <- LogicError.lift(Term.eq(x, logic.truth))
      isFalsity <- LogicError.lift(Term.eq(x, logic.falsity))
      leftBody <- logic.mkDisj(isTruth, p)
      rightBody <- logic.mkDisj(isFalsity, p)
      u <- LogicError.lift(Term.abs(x, leftBody))
      v <- LogicError.lift(Term.abs(x, rightBody))

      // 1 and 2. Each predicate holds of one of the two constants, so choice holds of it.
      atTruth <- rules.disjIntro1(p, Conv.refl(logic.truth))
      chosenTruth <- chosenSatisfies(logic, axioms, u, logic.truth, atTruth)
      atFalsity <- rules.disjIntro1(p, Conv.refl(logic.falsity))
      chosenFalsity <- chosenSatisfies(logic, axioms, v, logic.falsity, atFalsity)

      // 3. Under `p` the two predicates are equal, so the two chosen values are.
      assumedP <- LogicError.lift(Kernel.assume(p))
      leftPointwise <- rules.disjIntro2(isTruth, assumedP)
      rightPointwise <- rules.disjIntro2(isFalsity, assumedP)
      bodiesEqual = Kernel.deductAntisym(leftPointwise, rightPointwise)
      predicatesEqual <- LogicError.lift(Kernel.abs(x, bodiesEqual))
      chosenEqual <- Conv.apTerm(chooser, predicatesEqual)

      // 4. The goal, and the branch that reaches it from `p`.
      negated <- logic.mkNot(p)
      fromP <- rules.disjIntro1(negated, assumedP)

      // The branch that reaches it from the two equations, through `T = F`.
      chosenFromU <- LogicError.lift(Term.app(chooser, u))
      chosenFromV <- LogicError.lift(Term.app(chooser, v))
      uIsTruth <- LogicError.lift(Term.eq(chosenFromU, logic.truth))
      vIsFalsity <- LogicError.lift(Term.eq(chosenFromV, logic.falsity))
      assumedTruth <- LogicError.lift(Kernel.assume(uIsTruth))
      assumedFalsity <- LogicError.lift(Kernel.assume(vIsFalsity))
      collapsed <- Conv.rewriteSides(assumedTruth, assumedFalsity, chosenEqual)
      absurd <- rules.notElim(notFalsity, collapsed)
      notP <- rules.notIntro(p, absurd)
      fromNotP <- rules.disjIntro2(p, notP)

      inner <- rules.disjElim(chosenFalsity, fromNotP, fromP)
      outer <- rules.disjElim(chosenTruth, inner, fromP)
      result <- rules.gen(p, outer)
    } yield result
  }

  /**
   * `|- !p. ~~p ==> p`.
   *
   * A case split on `p` and nothing else. Under `p` the conclusion is the assumption; under `~p`
   * the double negation contradicts it, and `Rules.falsityElim` gives the conclusion from that,
   * which is the intuitionistic direction and was always available. What the excluded middle
   * supplies is the right to make the split at all.
   */
  private def doubleNegationElimination(
    logic: Logic,
    middle: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val p = Term.variable("p", Type.Bool)

    for {
      negated <- logic.mkNot(p)
      doubled <- logic.mkNot(negated)
      assumedDoubled <- LogicError.lift(Kernel.assume(doubled))
      assumedNegated <- LogicError.lift(Kernel.assume(negated))
      absurd <- rules.notElim(assumedDoubled, assumedNegated)
      fromNotP <- rules.falsityElim(p, absurd)

      assumedP <- LogicError.lift(Kernel.assume(p))
      atP <- rules.spec(p, middle)
      combined <- rules.disjElim(atP, assumedP, fromNotP)
      implied <- rules.disch(doubled, combined)
      result <- rules.gen(p, implied)
    } yield result
  }

  /**
   * `|- !p q. (~(p \/ q)) = (~p /\ ~q)`, which reaches no axiom at all.
   *
   * Here because De Morgan is asked for as a pair, and pinned here rather than in [[Logic]] because
   * that would suggest it needed something this file has. It does not, and `ClassicalSpec` measures
   * that: a proof with an empty axiom set. Both directions are ordinary intuitionistic reasoning,
   * each disjunct refuted from the negated disjunction on one side and a disjunction eliminated
   * into falsity on the other, and `Kernel.deductAntisym` turns the two into the equation.
   */
  private def deMorganDisjunction(logic: Logic): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val p = Term.variable("p", Type.Bool)
    val q = Term.variable("q", Type.Bool)

    for {
      disjunction <- logic.mkDisj(p, q)
      negatedDisjunction <- logic.mkNot(disjunction)
      notP <- logic.mkNot(p)
      notQ <- logic.mkNot(q)
      conjunction <- logic.mkConj(notP, notQ)

      assumedNegated <- LogicError.lift(Kernel.assume(negatedDisjunction))
      assumedP <- LogicError.lift(Kernel.assume(p))
      assumedQ <- LogicError.lift(Kernel.assume(q))

      leftInjection <- rules.disjIntro1(q, assumedP)
      absurdFromP <- rules.notElim(assumedNegated, leftInjection)
      provedNotP <- rules.notIntro(p, absurdFromP)
      rightInjection <- rules.disjIntro2(p, assumedQ)
      absurdFromQ <- rules.notElim(assumedNegated, rightInjection)
      provedNotQ <- rules.notIntro(q, absurdFromQ)
      forward <- rules.conjIntro(provedNotP, provedNotQ)

      assumedConjunction <- LogicError.lift(Kernel.assume(conjunction))
      firstHalf <- rules.conjElim1(assumedConjunction)
      secondHalf <- rules.conjElim2(assumedConjunction)
      absurdLeft <- rules.notElim(firstHalf, assumedP)
      absurdRight <- rules.notElim(secondHalf, assumedQ)
      assumedDisjunction <- LogicError.lift(Kernel.assume(disjunction))
      absurdFromDisjunction <- rules.disjElim(assumedDisjunction, absurdLeft, absurdRight)
      backward <- rules.notIntro(disjunction, absurdFromDisjunction)

      equated = Kernel.deductAntisym(backward, forward)
      result <- rules.genAll(equated, List(p, q))
    } yield result
  }

  /**
   * `|- !p q. (~(p /\ q)) = (~p \/ ~q)`, and this is the one that needs the classical step.
   *
   * The direction from the negated conjunction to the disjunction is where an intuitionistic proof
   * stops: from `~(p /\ q)` nothing says which of the two fails. Two nested case splits say it,
   * `p` and then `q`, and the branch where both hold is the one the hypothesis refutes. The other
   * direction is two detachments and needs nothing.
   */
  private def deMorganConjunction(
    logic: Logic,
    middle: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val p = Term.variable("p", Type.Bool)
    val q = Term.variable("q", Type.Bool)

    def splitOn(
      proposition: Term,
      positive: Kernel.Thm,
      negative: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      rules.spec(proposition, middle).flatMap(rules.disjElim(_, positive, negative))

    for {
      conjunction <- logic.mkConj(p, q)
      negatedConjunction <- logic.mkNot(conjunction)
      notP <- logic.mkNot(p)
      notQ <- logic.mkNot(q)
      disjunction <- logic.mkDisj(notP, notQ)

      assumedNegated <- LogicError.lift(Kernel.assume(negatedConjunction))
      assumedP <- LogicError.lift(Kernel.assume(p))
      assumedQ <- LogicError.lift(Kernel.assume(q))
      assumedNotP <- LogicError.lift(Kernel.assume(notP))
      assumedNotQ <- LogicError.lift(Kernel.assume(notQ))

      fromNotP <- rules.disjIntro1(notQ, assumedNotP)
      fromNotQ <- rules.disjIntro2(notP, assumedNotQ)
      both <- rules.conjIntro(assumedP, assumedQ)
      absurdFromBoth <- rules.notElim(assumedNegated, both)
      fromBoth <- rules.falsityElim(disjunction, absurdFromBoth)
      underP <- splitOn(q, fromBoth, fromNotQ)
      forward <- splitOn(p, underP, fromNotP)

      assumedConjunction <- LogicError.lift(Kernel.assume(conjunction))
      firstHalf <- rules.conjElim1(assumedConjunction)
      secondHalf <- rules.conjElim2(assumedConjunction)
      absurdLeft <- rules.notElim(assumedNotP, firstHalf)
      absurdRight <- rules.notElim(assumedNotQ, secondHalf)
      assumedDisjunction <- LogicError.lift(Kernel.assume(disjunction))
      absurdFromDisjunction <- rules.disjElim(assumedDisjunction, absurdLeft, absurdRight)
      backward <- rules.notIntro(conjunction, absurdFromDisjunction)

      equated = Kernel.deductAntisym(backward, forward)
      result <- rules.genAll(equated, List(p, q))
    } yield result
  }

  /**
   * `|- !p a b. p ==> COND p a b = a` and `|- !p a b. ~p ==> COND p a b = b`.
   *
   * The two halves of one argument, so they are proved together: both unfold the same definition,
   * both put the same predicate to the same axiom, and the only difference between them is which
   * value is offered as the witness and which conjunct is read off the answer.
   *
   * `COND p a b` unfolds to `select P` with `P = \x. (p ==> x = a) /\ (~p ==> x = b)`, and the
   * choice axiom says that if anything satisfies `P` then `select P` does. Under `p` the value `a`
   * satisfies it: the first conjunct is reflexivity discharged under `p`, and the second is
   * **vacuous** rather than proved, since `p` and `~p` together give falsity and falsity gives
   * `a = b`. So `P (select P)` holds under `p`, its first conjunct detaches against `p`, and
   * transitivity with the unfolding gives the equation. Under `~p` the same with `b`, the conjuncts
   * the other way round.
   *
   * **The predicate is read off the unfolding rather than built a second time.** Building it here
   * would be a term that has to be equal to the one the definition produced, node for node, or the
   * axiom instance is about a different predicate and the `trans` at the end fails several steps
   * after the mistake. Taking it apart cannot disagree with itself.
   *
   * Neither equation reaches eta, which `ClassicalSpec` measures rather than takes on trust: this
   * goes to `SELECT` and the kernel's rules and never through [[ExcludedMiddle]], although a case
   * split would have proved both and would have cost the excluded middle's whole derivation twice
   * over. The figure is in the generated table of `docs/proving.md` and is not repeated here.
   */
  private def conditionalEquations(
    logic: Logic,
    axioms: Map[String, Kernel.Thm],
    definition: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val alpha = TyVar(TypeVariable)
    val p = Term.variable("p", Type.Bool)
    val a = Term.variable("a", alpha)
    val b = Term.variable("b", alpha)

    for {
      unfolded <- Conv.unfold(definition, List(p, a, b))
      sides <- Term.destEq(unfolded.conclusion)
        .toRight(NotOfForm("an equation", unfolded.conclusion))
      predicate <- sides._2 match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("the chooser applied to a predicate", other))
      }

      negated <- logic.mkNot(p)
      assumedP <- LogicError.lift(Kernel.assume(p))
      assumedNotP <- LogicError.lift(Kernel.assume(negated))
      absurd <- rules.notElim(assumedNotP, assumedP)

      // `a` satisfies the predicate under `p`: reflexivity on the left, vacuity on the right.
      aIsB <- LogicError.lift(Term.eq(a, b))
      vacuousUnderP <- rules.falsityElim(aIsB, absurd).flatMap(rules.disch(negated, _))
      reflexiveUnderP <- rules.disch(p, Conv.refl(a))
      atA <- rules.conjIntro(reflexiveUnderP, vacuousUnderP)
      chosenFromA <- chosenSatisfies(logic, axioms, predicate, a, atA)
      positiveHalf <- rules.conjElim1(chosenFromA)
      chosenIsA <- rules.mp(positiveHalf, assumedP)
      isA <- LogicError.lift(Kernel.trans(unfolded, chosenIsA))
      positive <- rules.disch(p, isA).flatMap(rules.genAll(_, List(p, a, b)))

      // And `b` under `~p`, which is the same three lines with the conjuncts swapped.
      bIsA <- LogicError.lift(Term.eq(b, a))
      vacuousUnderNotP <- rules.falsityElim(bIsA, absurd).flatMap(rules.disch(p, _))
      reflexiveUnderNotP <- rules.disch(negated, Conv.refl(b))
      atB <- rules.conjIntro(vacuousUnderNotP, reflexiveUnderNotP)
      chosenFromB <- chosenSatisfies(logic, axioms, predicate, b, atB)
      negativeHalf <- rules.conjElim2(chosenFromB)
      chosenIsB <- rules.mp(negativeHalf, assumedNotP)
      isB <- LogicError.lift(Kernel.trans(unfolded, chosenIsB))
      negative <- rules.disch(negated, isB).flatMap(rules.genAll(_, List(p, a, b)))
    } yield (positive, negative)
  }

  /* -------------------------------------------------------------------- the plumbing */

  /**
   * The body of [[Classical.witness]], where the derivations can reach it.
   *
   * On the object rather than the class because [[derive]] needs it before an instance exists, and
   * one implementation rather than two because a second copy of a derivation is a second thing to
   * keep right.
   */
  private def chooseWitness(
    logic: Logic,
    axioms: Map[String, Kernel.Thm],
    existential: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    axioms
      .get(Choice)
      .toRight(MissingDefinition(Choice))
      .flatMap(witnessFrom(logic, _, existential))

  /**
   * The same derivation, given the choice axiom rather than a table to look it up in.
   *
   * **The sentence above says one implementation rather than two, and there were two.**
   * `Modular` carried a copy of this, differing in the two variable names and in how the axiom
   * arrived, because what it holds is the axiom itself: it builds a quantifier at `num`, and
   * `Classical.standard` has never heard of that type, so there is no table there to look it up
   * in. The split was over an argument, and an argument is a parameter.
   *
   * Reachable outside this module for that reason, which is what the copy was working around.
   *
   * What comes back is the **unreduced** application, and that is deliberate here: a caller
   * defining a type off the result needs it that way, and a caller that does not reduces it at its
   * own call site, which is what the one in `Modular` does.
   */
  private[symbolum] def witnessFrom(
    logic: Logic,
    choice: Kernel.Thm,
    existential: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    logic.destExistsPredicate(existential.conclusion) match {
      case None => Left(NotOfForm("an existential quantification", existential.conclusion))

      case Some(predicate) =>
        Type.destFun(Term.typeOf(predicate)) match {
          case None => Left(NotOfForm("a predicate", predicate))

          case Some((domain, _)) =>
            val taken =
              Term.freeVariables(predicate) ++
                existential.hypotheses.flatMap(Term.freeVariables).toSet
            val variable = Conv.freshVariable("w", domain, taken)

            for {
              instantiated <- Right(Kernel.instType(Map(TypeVariable -> domain), choice))

              atPredicate <- logic.rules.spec(predicate, instantiated)
              atVariable <- logic.rules.spec(variable, atPredicate)

              applied <- LogicError.lift(Term.app(predicate, variable))
              instance <- Term.betaReduce(applied).toRight(NotOfForm("a redex", applied))
              assumed <- LogicError.lift(Kernel.assume(instance))

              chosen <- logic.rules.mp(atVariable, assumed)
              result <- logic.rules.existsElim(existential, variable, chosen)
            } yield result
        }
    }

  /**
   * `|- P w` becomes `|- P (select P)`, beta reduced.
   *
   * The form Diaconescu's argument wants, which is the opposite of the form
   * [[Classical.witness]] hands back for the reason its scaladoc gives: nothing here is going to
   * define a type off the result, and what the two eliminations need is a disjunction they can take
   * apart. Private, so that the choice between the two forms stays where the reason for it is.
   */
  private def chosenSatisfies(
    logic: Logic,
    axioms: Map[String, Kernel.Thm],
    predicate: Term,
    witnessTerm: Term,
    proof: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      existential <- logic.rules.existsIntro(predicate, witnessTerm, proof)
      named <- chooseWitness(logic, axioms, existential)
      reduction <- Conv.betaRoot(named.conclusion)
      result <- LogicError.lift(Kernel.eqMp(reduction, named))
    } yield result

  /** The body of [[Classical.ext]]: `G |- !x. f x = g x` gives `G |- f = g`. */
  private def extend(
    logic: Logic,
    eta: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    logic.destForallPredicate(theorem.conclusion) match {
      case None => Left(NotOfForm("a universal quantification", theorem.conclusion))

      case Some(predicate) =>
        Type.destFun(Term.typeOf(predicate)) match {
          case None => Left(NotOfForm("a predicate", predicate))

          case Some((domain, _)) =>
            val variable = Conv.freshVariable("x", domain, Rules.freeIn(theorem))

            for {
              specialised <- logic.rules.spec(variable, theorem)
              sides <- Term.destEq(specialised.conclusion)
                .toRight(NotOfForm("a pointwise equation", specialised.conclusion))
              (left, right) = sides

              f <- appliedTo(variable, left)
              g <- appliedTo(variable, right)
              _ <- if (!Term.occursFree(variable, f) && !Term.occursFree(variable, g)) Right(())
                   else Left(EscapingVariable(variable, "one of the two functions it is applied to"))

              abstracted <- LogicError.lift(Kernel.abs(variable, specialised))
              atTypes = Kernel.instType(
                Map(TypeVariable -> domain, CodomainVariable -> Term.typeOf(left)),
                eta
              )
              expandedF <- logic.rules.spec(f, atTypes)
              expandedG <- logic.rules.spec(g, atTypes)
              fromF <- Conv.sym(expandedF)
              throughLambda <- LogicError.lift(Kernel.trans(fromF, abstracted))
              result <- LogicError.lift(Kernel.trans(throughLambda, expandedG))
            } yield result
        }
    }

  /** The function of an application of something to `variable`, refused if it is anything else. */
  private def appliedTo(variable: FVar, term: Term): Either[LogicError, Term] = term match {
    case App(fn, argument) if argument == variable => Right(fn)
    case other => Left(NotOfForm(s"an application to ${variable.name}", other))
  }
}
