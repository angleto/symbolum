package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Derivations **of** the embedded theory, built rather than described.
 *
 * Everything below [[Provability]] is about the object language: what a term is, what a formula is,
 * which formulas are axioms, what it means for one to be derivable. Nothing there ever derives
 * anything, and the two closures that landed with it are what makes deriving possible: with
 * `NUM_PROV_PA` and `NUM_PROV_LOGIC` supplying axioms, `NUM_PROV_MP` chaining and `NUM_PROV_GEN`
 * generalising, a Hilbert derivation can be assembled a step at a time.
 *
 * **It is a development of its own because `docs/adr/0013` decided that**, and the decision is
 * worth restating where the work starts: D2 and D3 are theorems of PA, so producing them means
 * building PA-derivations in quantity, and a layer that does that has to be reusable rather than a
 * helper inside whichever development first needed one. This file is the beginning of that layer.
 *
 * **It is the first link that declares nothing**, which is what "the product is derivations" means
 * concretely: no type, no constant, no definition, no axiom, so it does not **become** the widest
 * signature. A reader who expects the last link to be the widest one should read `Chain.widest`
 * rather than assume, here or anywhere: which development is widest changes whenever a link
 * declaring a constant is added, and naming it in prose has gone stale three times already.
 *
 * == What is here ==
 *
 * Two schemes, each proved once for **every** formula rather than at a code:
 *
 *  - [[SelfImplication]], that PA proves `p ==> p`. The classic three-line Hilbert derivation, and
 *    the reason it is three lines rather than one is that `p ==> p` is not an instance of any
 *    axiom: the system has no reflexivity for implication, only weakening and distribution, and
 *    getting from those to the identity is the standard exercise.
 *  - [[Syllogism]], that provable `p ==> q` and provable `q ==> r` give provable `p ==> r`. The
 *    workhorse: every derivation of any length is a chain of these.
 *
 * Both cost the naturals' two axioms and nothing else, which `DeductionSpec` asserts as an equality
 * rather than as a ceiling.
 *
 * And the three rules the **deduction theorem** is assembled from, one per way a step can be
 * justified: [[Weaken]] for the axiom cases, [[ImplicationModusPonens]] for the modus ponens case,
 * and [[ImplicationGeneralisation]] for the generalisation case, which is the one that carries the
 * side condition every textbook statement of that theorem carries.
 *
 * == What is not here, and what it is in front of ==
 *
 * The deduction theorem itself. Its three rules are above; what is missing is the thing they would
 * be applied to, which is a notion of derivation **from hypotheses** that [[Provability]] does not
 * have: `NUM_PROV` takes a formula and not a set. That wants a `NUM_PROV_FROM` beside the three
 * definitions there, with a fifth clause on a step saying it is the hypothesis itself, and then an
 * induction over the derivation whose five cases are the three rules above, the hypothesis case
 * (which is [[SelfImplication]]) and nothing else.
 *
 * And, further up, the thing Goedel's argument actually needs, which is **not** reachable from
 * here without a large piece of work in between: `Prov` as a formula **of the object language**,
 * with one free variable, rather than as the predicate `NUM_PROV` of the ambient logic. D1, D2 and
 * D3 are statements about that formula, so none of the three can be stated yet, and a reader
 * arriving at this file looking for them should read `docs/adr/0013` first.
 */
final class Deduction private (
  val provability: Provability,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  val language: Language = provability.language

  /** A derived fact of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Deduction {

  /**
   * `|- !p. NUM_FORM p ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR p p))`
   *
   * PA proves `p ==> p`, for every formula `p`. The first theorem of the embedded theory derived
   * here that is neither an axiom nor one step from one, and the smallest thing that exercises the
   * whole apparatus at once: two logical axioms, one distribution, and two detachments.
   *
   * The derivation is the textbook one and it is worth having in front of a reader, because the
   * shape is not guessable from the statement. Writing `K x y` for `x ==> (y ==> x)` and `S x y z`
   * for `(x ==> (y ==> z)) ==> ((x ==> y) ==> (x ==> z))`:
   *
   * {{{
   * S p (p ==> p) p  :  (p ==> ((p ==> p) ==> p)) ==> ((p ==> (p ==> p)) ==> (p ==> p))
   * K p (p ==> p)    :  p ==> ((p ==> p) ==> p)
   * detach           :  (p ==> (p ==> p)) ==> (p ==> p)
   * K p p            :  p ==> (p ==> p)
   * detach           :  p ==> p
   * }}}
   *
   * `NUM_FORM (p ==> p)` is needed twice on the way and comes from `NUM_FORM_IMP`, which is the
   * side condition every scheme of `NUM_LOGIC` carries being paid rather than assumed.
   */
  val SelfImplication: String = "NUM_PROV_SELF"

  /**
   * `|- !p q r. NUM_FORM p ==> NUM_FORM q ==> NUM_FORM r ==>
   * NUM_PROV (p ==> q) ==> NUM_PROV (q ==> r) ==> NUM_PROV (p ==> r)`
   *
   * Implication is transitive **inside** the embedded theory, which is the rule every derivation of
   * any length is made of. Three lines again: weaken `q ==> r` under `p`, distribute, detach twice.
   *
   * It is stated over `NUM_PROV` of the two implications rather than as an object-level formula
   * `(p ==> q) ==> ((q ==> r) ==> (p ==> r))`. The second is also a theorem and is **not** the same
   * statement: this one is a rule a caller can apply, that one is a formula a caller would then
   * have to detach twice. The rule is what the next derivation wants; the formula is worth having
   * when something has to reason about it inside the theory, which is the object level and is not
   * here yet.
   */
  val Syllogism: String = "NUM_PROV_SYLL"

  /**
   * `|- !h p. NUM_FORM h ==> NUM_FORM p ==> NUM_PROV p ==> NUM_PROV (h ==> p)`
   *
   * Anything provable is provable under any hypothesis. One line: weakening is a logical axiom, so
   * `p ==> (h ==> p)` is provable and detaching `p` leaves the rest.
   *
   * It is the first of the three rules the **deduction theorem** needs, and they are here ahead of
   * it because each is small and independently what a caller building an object derivation reaches
   * for. This one discharges the axiom cases: a step justified by being an axiom is provable
   * outright, and the hypothesis is carried along it.
   */
  val Weaken: String = "NUM_PROV_WEAKEN"

  /**
   * `|- !h p q. NUM_FORM h ==> NUM_FORM p ==> NUM_FORM q ==>
   * NUM_PROV (h ==> (p ==> q)) ==> NUM_PROV (h ==> p) ==> NUM_PROV (h ==> q)`
   *
   * Modus ponens carried out **under** a hypothesis, which is what distribution is an axiom for:
   * `(h ==> (p ==> q)) ==> ((h ==> p) ==> (h ==> q))` is an instance of it, and the rest is two
   * detachments.
   *
   * The second of the deduction theorem's three rules, and the one its modus ponens case needs.
   * Where the induction has `NUM_PROV (h ==> beta x)` and `NUM_PROV (h ==> beta y)` with the first
   * an implication onto the step being justified, this is what closes it.
   */
  val ImplicationModusPonens: String = "NUM_PROV_IMP_MP"

  /**
   * `|- !i h p. NUM_FORM h ==> NUM_FORM p ==> ~(NUM_FREE_FORM i h) ==>
   * NUM_PROV (h ==> p) ==> NUM_PROV (h ==> (!i. p))`
   *
   * Generalisation carried out under a hypothesis, and the **side condition is the whole subject**:
   * the index must not occur free in the hypothesis. Without it the rule is false, and it is the
   * restriction every textbook statement of the deduction theorem carries.
   *
   * Three steps and each is one of the pieces that landed before it. Generalise the whole
   * implication with [[Provability.Generalisation]]; distribute the quantifier over it with
   * `NUM_LOGIC_UNIVERSAL`, which leaves `(!i. h) ==> (!i. p)`; and get from `h` to `!i. h` with
   * `NUM_LOGIC_VACUOUS`, which is exactly where the side condition is spent. [[Syllogism]] joins
   * the last two.
   *
   * The third of the deduction theorem's three rules.
   */
  val ImplicationGeneralisation: String = "NUM_PROV_IMP_GEN"

  /**
   * The deduction theorem.
   *
   * `|- !h p. NUM_FORM h ==> (!i. ~(NUM_FREE_FORM i h)) ==> NUM_PROV_FROM h p ==>
   * NUM_PROV (h ==> p)`
   *
   * What a derivation **from** an assumption gives you is an implication with that assumption in
   * front, which is the tool that makes object-level derivations tractable: to prove `h ==> p` you
   * assume `h` and work forwards, instead of assembling the implication out of weakening and
   * distribution by hand.
   *
   * The proof is strong induction on the index of a step, and the five cases are exactly the five
   * ways a step of a derivation-from-`h` can be justified. Each is one line because the rule it
   * needs is already published here: [[Weaken]] for an axiom of either set,
   * [[ImplicationModusPonens]] for a modus ponens, [[ImplicationGeneralisation]] for a
   * generalisation, and [[SelfImplication]] for the step that **is** `h`. That the induction is
   * five one-liners is the return on proving those four separately first.
   *
   * **Two conditions on the hypothesis, and they are different in kind.** That `h` is a formula is
   * what every scheme of `NUM_LOGIC` asks of it. That no index occurs free in it is the restriction
   * the textbook statement carries, and dropping it makes the theorem false: the generalisation
   * case would let a derivation generalise over a variable the assumption constrains. It is spent
   * in exactly one place, `NUM_LOGIC_VACUOUS` inside [[ImplicationGeneralisation]].
   *
   * It is stated with `!i. ~(NUM_FREE_FORM i h)` written out rather than through a constant.
   * `NUM_CLOSED` exists and is about **terms**, so it is not this; introducing a second constant
   * for the formula case would be a definition in a development that declares nothing, and the
   * condition is one line either way.
   */
  val DeductionTheorem: String = "NUM_PROV_DEDUCTION"

  /**
   * Specialisation as a rule of the embedded theory rather than as a scheme about it.
   *
   * `|- !i t p. NUM_FORM p ==> NUM_TERM t ==> NUM_CLOSED t ==>`
   * `NUM_PROV (NUM_CODE 8 (NUM_PAIR i p)) ==> NUM_PROV (NUM_SUBST_FORM i t p)`
   *
   * `NUM_LOGIC_SPECIALISE` says the implication from the quantified formula to its instance is a
   * logical axiom. This detaches it, which is the form every derivation actually wants: what a
   * consumer holds is a proof of `!i. p`, not a proof of an implication it then has to take apart.
   * Three lines, being the scheme, `NUM_PROV_LOGIC` and one `NUM_PROV_MP`.
   *
   * **What it could not be used for until 2026-09-15 is worth recording beside it**, because the
   * shape of the gap repeats. The scheme's third condition is `NUM_CLOSED t` and nothing in the
   * library discharged one, so this rule would have been a theorem nobody could apply; that is
   * `NUM_NUMERAL_CLOSED`'s doing. The condition and the conclusion are the same kind of obstacle
   * seen from two sides: a side condition nothing can meet stops a caller at the front, and a
   * conclusion carrying an unevaluated `NUM_SUBST_FORM` stops the next caller at the back.
   * `Language.substituteIn` is what answers the second.
   */
  val Specialisation: String = "NUM_PROV_SPECIALISE"

  /**
   * The embedded theory's equality is symmetric.
   *
   * `NUM_LOGIC` has reflexivity and ONE replacement scheme, and two is the economical choice
   * `Language` records: symmetry, transitivity and the congruence of every function symbol are
   * consequences rather than axioms. This is the first of those consequences to be derived, and
   * until it was, "consequences" was a claim in a docstring.
   *
   * The derivation is the textbook one and is worth reading once, because the same trick gives the
   * other two. Replacement is applied to the formula `v_i = t`, which has a hole where the index
   * is: putting `t` in the hole gives `t = t`, which reflexivity proves, and putting `u` in it
   * gives `u = t`, which is what was wanted. So `t = u` carries the first to the second.
   *
   * **What it cost in front of it was [[Language.SubstituteIdle]]**, and the reason is the whole
   * argument for stating that lemma over every closed term rather than over numerals. The hole
   * formula MENTIONS `t`, so computing either instance means substituting into a term that must
   * come back unchanged, and nothing said that a substitution leaves a closed term alone.
   */
  val Symmetry: String = "NUM_PROV_SYMM"

  /**
   * The embedded theory's equality is transitive, which is the second consequence.
   *
   * The same trick as [[Symmetry]] with a different hole: replacement at `v_i = w` turns `u = t`
   * into a passage from `u = w` to `t = w`. What it needs first is `u = t`, so this rule is built
   * ON symmetry rather than beside it, which is why the two are in this order.
   */
  val Transitivity: String = "NUM_PROV_TRANS"

  /**
   * The successor respects the embedded theory's equality.
   *
   * `Language` records that two equality axioms are enough because reflexivity and one replacement
   * scheme give the congruence of every function symbol, so writing `x = y ==> S x = S y` as an
   * axiom would be writing down a consequence. This is that sentence discharged for the successor,
   * and it is the one of the three consequences the arithmetic actually needs: proving
   * `numeral m + numeral n = numeral (m + n)` by induction on `n` reaches its step by putting a
   * successor around an equality the hypothesis already gives.
   *
   * The hole is `S t = S v_i`, so both instances have a substitution under a constructor rather
   * than at the top, which is the only way this differs from the two above it.
   */
  val SuccessorCongruence: String = "NUM_PROV_SUC_CONG"

  val Statements: Vector[(String, String)] = Vector(
    SelfImplication -> "!p:num. NUM_FORM p ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR p p))",
    Weaken ->
      ("!h:num p:num. NUM_FORM h ==> NUM_FORM p ==> NUM_PROV p ==> " +
        "NUM_PROV (NUM_CODE 7 (NUM_PAIR h p))"),
    ImplicationModusPonens ->
      ("!h:num p:num q:num. NUM_FORM h ==> NUM_FORM p ==> NUM_FORM q ==> " +
        "NUM_PROV (NUM_CODE 7 (NUM_PAIR h (NUM_CODE 7 (NUM_PAIR p q)))) ==> " +
        "NUM_PROV (NUM_CODE 7 (NUM_PAIR h p)) ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR h q))"),
    ImplicationGeneralisation ->
      ("!i:num h:num p:num. NUM_FORM h ==> NUM_FORM p ==> ~(NUM_FREE_FORM i h) ==> " +
        "NUM_PROV (NUM_CODE 7 (NUM_PAIR h p)) ==> " +
        "NUM_PROV (NUM_CODE 7 (NUM_PAIR h (NUM_CODE 8 (NUM_PAIR i p))))"),
    DeductionTheorem ->
      ("!h:num p:num. NUM_FORM h ==> (!i:num. ~(NUM_FREE_FORM i h)) ==> " +
        "NUM_PROV_FROM h p ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR h p))"),
    Syllogism ->
      ("!p:num q:num r:num. NUM_FORM p ==> NUM_FORM q ==> NUM_FORM r ==> " +
        "NUM_PROV (NUM_CODE 7 (NUM_PAIR p q)) ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR q r)) ==> " +
        "NUM_PROV (NUM_CODE 7 (NUM_PAIR p r))"),
    Specialisation ->
      ("!i:num t:num p:num. NUM_FORM p ==> NUM_TERM t ==> NUM_CLOSED t ==> " +
        "NUM_PROV (NUM_CODE 8 (NUM_PAIR i p)) ==> NUM_PROV (NUM_SUBST_FORM i t p)"),
    Symmetry ->
      ("!t:num u:num. NUM_TERM t ==> NUM_TERM u ==> NUM_CLOSED t ==> NUM_CLOSED u ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR t u)) ==> NUM_PROV (NUM_CODE 5 (NUM_PAIR u t))"),
    Transitivity ->
      ("!t:num u:num w:num. NUM_TERM t ==> NUM_TERM u ==> NUM_TERM w ==> " +
        "NUM_CLOSED t ==> NUM_CLOSED u ==> NUM_CLOSED w ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR t u)) ==> NUM_PROV (NUM_CODE 5 (NUM_PAIR u w)) ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR t w))"),
    SuccessorCongruence ->
      ("!t:num u:num. NUM_TERM t ==> NUM_TERM u ==> NUM_CLOSED t ==> NUM_CLOSED u ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR t u)) ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR (NUM_CODE 2 t) (NUM_CODE 2 u)))")
  )

  /** Build it over what the embedded theory can prove. It extends nothing. */
  def construct(provability: Provability): Either[LogicError, Deduction] = {
    val builder = new Builder(provability)
    try
      Right(
        new Deduction(
          provability,
          provability.theory,
          provability.notation,
          provability.logic,
          Map(
            SelfImplication -> builder.checked(SelfImplication, builder.selfImplication),
            Syllogism -> builder.checked(Syllogism, builder.syllogism),
            Weaken -> builder.checked(Weaken, builder.weaken),
            ImplicationModusPonens ->
              builder.checked(ImplicationModusPonens, builder.implicationModusPonens),
            ImplicationGeneralisation ->
              builder.checked(ImplicationGeneralisation, builder.implicationGeneralisation),
            DeductionTheorem -> builder.checked(DeductionTheorem, builder.deductionTheorem),
            Specialisation -> builder.checked(Specialisation, builder.specialisation),
            Symmetry -> builder.checked(Symmetry, builder.symmetry),
            Transitivity -> builder.checked(Transitivity, builder.transitivity),
            SuccessorCongruence ->
              builder.checked(SuccessorCongruence, builder.successorCongruence)
          )
        )
      )
    catch { case refused: RefusedHere => Left(refused.error) }
  }

  /** Carry a refusal out of a derivation written in direct style. */
  private final class RefusedHere(val error: LogicError) extends RuntimeException

  /**
   * The object language's propositional rules, as operations on theorems about codes.
   *
   * Each method here is one line of a Hilbert derivation, and the point of having them is that the
   * derivations above then read like the textbook proofs they are. Every one of them discharges the
   * `NUM_FORM` side conditions its scheme carries, so a caller supplies those and never a code the
   * language would refuse.
   *
   * **Specialisation is by the instance wanted and never by position.** Every scheme here binds two
   * or three variables of one type, which is exactly the case `CLAUDE.md` records as invisible when
   * it goes wrong: a positional call would produce a true theorem about the wrong formula. So each
   * call builds the statement it wants and hands it to `Rules.specTo`.
   */
  private final class Builder(provability: Provability) {
    private val theory = provability.theory
    private val notation = provability.notation
    private val logic = provability.logic
    private val rules = logic.rules
    private val language = provability.language
    private val numbers = TyApp(Natural.TypeName, Nil)
    private val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))

    private def force[T](result: Either[LogicError, T]): T =
      result.fold(error => throw new RefusedHere(error), identity)

    private def constant(name: String, ty: Type): Term =
      force(LogicError.lift(theory.constant(name, ty)))
    private def applied(head: Term, arguments: List[Term]): Term =
      force(LogicError.lift(Term.appAll(head, arguments)))

    private val pairing = constant(Numbering.PairName, arithmetic)
    private val coding = constant(Numbering.CodeName, arithmetic)
    private val seven = force(Parser.term(theory, notation, "7", numbers))

    /** The object language's implication, as a code. */
    private def imp(left: Term, right: Term): Term =
      applied(coding, List(seven, applied(pairing, List(left, right))))

    private val eight = force(Parser.term(theory, notation, "8", numbers))

    /** The object language's universal quantifier, over an index. */
    private def forAll(index: Term, body: Term): Term =
      applied(coding, List(eight, applied(pairing, List(index, body))))

    private def predicate(name: String)(subject: Term): Term =
      applied(constant(name, Type.fun(numbers, Type.Bool)), List(subject))

    private val isFormula = predicate(Language.FormulaName)
    private val isLogical = predicate(Language.LogicName)
    private val isProvable = predicate(Provability.ProvableName)

    private def imply(left: Term, right: Term): Term = force(logic.mkImp(left, right))
    private def assumed(claim: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(claim)))

    private val formulaOfImplication = force(language.fact("NUM_FORM_IMP"))
    private val weakening = force(language.fact("NUM_LOGIC_WEAKEN"))
    private val distribution = force(language.fact("NUM_LOGIC_DISTRIBUTE"))
    private val logicalIsProvable = force(provability.fact(Provability.ProvableLogic))
    private val modusPonens = force(provability.fact(Provability.ModusPonens))
    private val generalisation = force(provability.fact(Provability.Generalisation))
    private val vacuous = force(language.fact("NUM_LOGIC_VACUOUS"))
    private val specialising = force(language.fact("NUM_LOGIC_SPECIALISE"))
    private val replacing = force(language.fact("NUM_LOGIC_REPLACE"))
    private val reflexive = force(language.fact("NUM_LOGIC_REFLEXIVE"))
    private val formulaOfEquality = force(language.fact(Language.FormulaEquality))
    private val variableIsTerm = force(language.fact(Language.TermVariable))
    private val substituteIsIdle = force(language.fact(Language.SubstituteIdle))
    private val closedCases = force(language.fact(Language.ClosedCases))
    private val substituteEquality = force(language.fact(Language.FormulaSubstituteEquality))
    private val substituteVariable = force(language.fact(Language.SubstituteVariable))
    private val classical = language.numbering.peano.naturals.classical

    private val five = force(Parser.term(theory, notation, "5", numbers))
    private val two = force(Parser.term(theory, notation, "2", numbers))
    private val successorIsTerm = force(language.fact(Language.TermSuccessor))
    private val substituteSuccessor = force(language.fact(Language.SubstituteSuccessor))
    private val zeroTag = force(Parser.term(theory, notation, "0", numbers))

    /** The object language's equality, as a code. */
    private def objEq(left: Term, right: Term): Term =
      applied(coding, List(five, applied(pairing, List(left, right))))

    /** The object language's variable at an index, as a code. */
    private def objVar(index: Term): Term = applied(coding, List(zeroTag, index))

    /** The object language's successor, as a code. */
    private def objSucc(inner: Term): Term = applied(coding, List(two, inner))

    /** What substituting under a successor gives, with the inside already settled. */
    private def acrossSuccessor(
      index: Term, replacement: Term, inner: Term, innerDone: Kernel.Thm
    ): Kernel.Thm = {
      val clause = force(rules.specAll(substituteSuccessor, List(index, replacement, inner)))
      val lifted = force(Conv.apTerm(applied(coding, List(two)), innerDone))
      force(Conv.trans(clause, lifted))
    }

    /**
     * Replacement applied at a hole, detached, with both instances computed away.
     *
     * The three rules of equality differ only in the hole they choose and in what they feed the
     * result to; everything between is this. The two equations say what the hole becomes when the
     * index is filled with `from` and with `to`, and they are computed here rather than left
     * standing so that what comes out is a code a reader can see.
     */
    private def replaced(
      index: Term, from: Term, to: Term, hole: Term,
      holeIsFormula: Kernel.Thm,
      fromIsTerm: Kernel.Thm, toIsTerm: Kernel.Thm,
      fromIsClosed: Kernel.Thm, toIsClosed: Kernel.Thm,
      premise: Kernel.Thm,
      atFrom: Kernel.Thm, atTo: Kernel.Thm
    ): Kernel.Thm = {
      val substituting = constant(
        Language.FormulaSubstituteName,
        Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, numbers))))
      val left = applied(substituting, List(index, from, hole))
      val right = applied(substituting, List(index, to, hole))

      val instance = force(
        rules
          .specAll(replacing, List(index, from, to, hole))
          .flatMap(rules.mp(_, holeIsFormula))
          .flatMap(rules.mp(_, fromIsTerm))
          .flatMap(rules.mp(_, toIsTerm))
          .flatMap(rules.mp(_, fromIsClosed))
          .flatMap(rules.mp(_, toIsClosed))
      )
      val carried = detach(
        objEq(from, to), imp(left, right),
        axiom(imp(objEq(from, to), imp(left, right)), instance), premise)

      // A rewriting that ran out of steps leaves a substitution standing, and then `checked`
      // refuses the rule against its published statement rather than publishing a code nobody
      // can read. That is this call site's answer to the step limit.
      val ruleSet = force(Rewrite.Rule.all(logic, Vector(atFrom, atTo)))
      force(Rewrite.inTheorem(ruleSet, carried))
    }

    /**
     * `NUM_SUBST_TERM i r s = s` at a closed term, which is what the hole formula needs.
     *
     * The condition [[Language.SubstituteIdle]] asks for is freeness at one index; what a caller
     * here holds is `NUM_CLOSED s`, which is freeness at every index, so the step between them is
     * one specialisation of the definition.
     */
    private def idle(
      index: Term, replacement: Term, subject: Term,
      subjectIsTerm: Kernel.Thm, subjectIsClosed: Kernel.Thm
    ): Kernel.Thm = {
      val nowhere = force(
        rules
          .spec(subject, closedCases)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, subjectIsClosed)))
          .flatMap(rules.spec(index, _))
      )
      force(
        rules
          .specAll(substituteIsIdle, List(index, replacement, subject))
          .flatMap(rules.mp(_, subjectIsTerm))
          .flatMap(rules.mp(_, nowhere))
      )
    }

    /** `NUM_SUBST_TERM i r (NUM_CODE 0 i) = r`: the hole, filled. */
    private def filled(index: Term, replacement: Term): Kernel.Thm = {
      val clause = force(rules.specAll(substituteVariable, List(index, replacement, index)))
      val guard = force(LogicError.lift(Term.eq(index, index)))
      val scheme = Kernel.instType(
        Map(Classical.TypeVariable -> numbers), force(classical.fact(Classical.CondTrue)))
      val taken = force(
        rules
          .specAll(scheme, List(guard, replacement, objVar(index)))
          .flatMap(rules.mp(_, Kernel.refl(index)))
      )
      force(Conv.trans(clause, taken))
    }

    /** What substituting into an equality gives, with both sides already settled. */
    private def acrossEquality(
      index: Term, replacement: Term, left: Term, right: Term,
      leftDone: Kernel.Thm, rightDone: Kernel.Thm
    ): Kernel.Thm = {
      val clause =
        force(rules.specAll(substituteEquality, List(index, replacement, left, right)))
      val paired = force(
        Conv
          .apTerm(pairing, leftDone)
          .flatMap(half => LogicError.lift(Kernel.mkComb(half, rightDone)))
      )
      val lifted = force(Conv.apTerm(applied(coding, List(five)), paired))
      force(Conv.trans(clause, lifted))
    }
    private val isTerm = predicate(Language.TermName)
    private val isClosed = predicate(Language.ClosedName)
    private val substituting = force(LogicError.lift(theory.constant(
      Language.FormulaSubstituteName,
      Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, numbers))))))

    /** `NUM_SUBST_FORM i t p`, left standing: evaluating it is `Language.substituteIn`'s work. */
    private def substituted(index: Term, replacement: Term, formula: Term): Term =
      applied(substituting, List(index, replacement, formula))
    private val universal = force(language.fact("NUM_LOGIC_UNIVERSAL"))
    private val freeConstant = force(LogicError.lift(theory.constant(
      Language.FormulaFreeName, Type.fun(numbers, Type.fun(numbers, Type.Bool)))))

    private def isFree(index: Term, formula: Term): Term =
      applied(freeConstant, List(index, formula))

    private val peano = provability.language.numbering.peano
    private def pf(name: String): Kernel.Thm = force(peano.fact(name))
    private def vf(name: String): Kernel.Thm = force(provability.fact(name))

    private val betaConstant = force(LogicError.lift(theory.constant(Coding.BetaName,
      Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, numbers))))))
    private val atMostConstant = force(LogicError.lift(theory.constant(Peano.NonStrictOrder,
      Type.fun(numbers, Type.fun(numbers, Type.Bool)))))
    private val provableConstant = force(LogicError.lift(
      theory.constant(Provability.ProvableName, Type.fun(numbers, Type.Bool))))

    private def beta(a: Term, b: Term, j: Term): Term = applied(betaConstant, List(a, b, j))
    private def atMost(x: Term, y: Term): Term = applied(atMostConstant, List(x, y))
    private def isProvableFrom(h: Term, n: Term): Term =
      applied(
        force(LogicError.lift(theory.constant(
          Provability.ProvableFromName, Type.fun(numbers, Type.fun(numbers, Type.Bool))))),
        List(h, n))

    private def openAt(existential: Kernel.Thm, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val inner = logic.destExistsPredicate(existential.conclusion)
        .getOrElse(throw new RefusedHere(NotOfForm("an existential", existential.conclusion)))
      val fresh = Conv.freshVariable(
        name, numbers, taken ++ Term.freeVariables(existential.conclusion))
      val body = Term
        .destEq(force(Conv.betaRoot(applied(inner, List(fresh)))).conclusion)
        .map(_._2)
        .getOrElse(throw new RefusedHere(NotOfForm("an equation", fresh)))
      force(rules.existsElim(existential, fresh, reach(fresh, assumed(body))))
    }

    private def disjunctsOf(subject: Term, count: Int): Vector[Term] =
      if (count == 1) Vector(subject)
      else {
        val (first, rest) = logic.destDisj(subject)
          .getOrElse(throw new RefusedHere(NotOfForm("a disjunction", subject)))
        first +: disjunctsOf(rest, count - 1)
      }

    private def normalised(theorem: Kernel.Thm): Kernel.Thm =
      force(Conv.betaNormalise(theorem.conclusion)
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, theorem))))

    /** `NUM_FORM x` and `NUM_FORM y` give `NUM_FORM (x ==> y)`. */
    private def formImp(x: Term, y: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
      force(
        rules
          .specTo(
            formulaOfImplication,
            imply(isFormula(x), imply(isFormula(y), isFormula(imp(x, y)))))
          .flatMap(rules.mp(_, left))
          .flatMap(rules.mp(_, right))
      )

    /** A logical axiom is provable, which is the one step every line below starts from. */
    private def axiom(code: Term, logical: Kernel.Thm): Kernel.Thm =
      force(rules.spec(code, logicalIsProvable).flatMap(rules.mp(_, logical)))

    /** `|- NUM_PROV (x ==> (y ==> x))`, weakening at two formulas. */
    private def weaken(x: Term, y: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm = {
      val code = imp(x, imp(y, x))
      axiom(
        code,
        force(
          rules
            .specTo(weakening, imply(isFormula(x), imply(isFormula(y), isLogical(code))))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right))
        )
      )
    }

    /** `|- NUM_PROV ((x ==> (y ==> z)) ==> ((x ==> y) ==> (x ==> z)))`. */
    private def distribute(
      x: Term, y: Term, z: Term,
      left: Kernel.Thm, middle: Kernel.Thm, right: Kernel.Thm
    ): Kernel.Thm = {
      val code = imp(imp(x, imp(y, z)), imp(imp(x, y), imp(x, z)))
      axiom(
        code,
        force(
          rules
            .specTo(
              distribution,
              imply(
                isFormula(x),
                imply(isFormula(y), imply(isFormula(z), isLogical(code)))))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, middle))
            .flatMap(rules.mp(_, right))
        )
      )
    }

    /** Modus ponens at the object level: `NUM_PROV (x ==> y)` and `NUM_PROV x` give `NUM_PROV y`. */
    private def detach(x: Term, y: Term, implication: Kernel.Thm, antecedent: Kernel.Thm)
      : Kernel.Thm =
      force(
        rules
          .specTo(modusPonens, imply(isProvable(imp(x, y)), imply(isProvable(x), isProvable(y))))
          .flatMap(rules.mp(_, implication))
          .flatMap(rules.mp(_, antecedent))
      )

    /** [[SelfImplication]]. The derivation is written out in that name's docstring. */
    lazy val selfImplication: Kernel.Thm = {
      val p = Term.variable("p", numbers)
      val formula = assumed(isFormula(p))
      val self = imp(p, p)
      val formulaOfSelf = formImp(p, p, formula, formula)

      val shape = distribute(p, self, p, formula, formulaOfSelf, formula)
      val first = weaken(p, self, formula, formulaOfSelf)
      val middle =
        detach(imp(p, imp(self, p)), imp(imp(p, self), self), shape, first)
      val second = weaken(p, p, formula, formula)
      val reached = detach(imp(p, self), self, middle, second)

      force(rules.disch(isFormula(p), reached).flatMap(rules.gen(p, _)))
    }

    /** [[Specialisation]]. The scheme, made provable, then detached. */
    lazy val specialisation: Kernel.Thm = {
      val i = Term.variable("i", numbers)
      val t = Term.variable("t", numbers)
      val p = Term.variable("p", numbers)
      val formula = assumed(isFormula(p))
      val term = assumed(isTerm(t))
      val closed = assumed(isClosed(t))
      val quantified = forAll(i, p)
      val instance = substituted(i, t, p)
      val quantifiedIsProvable = assumed(isProvable(quantified))

      val logical = force(
        rules
          .specTo(
            specialising,
            imply(
              isFormula(p),
              imply(isTerm(t), imply(isClosed(t), isLogical(imp(quantified, instance))))))
          .flatMap(rules.mp(_, formula))
          .flatMap(rules.mp(_, term))
          .flatMap(rules.mp(_, closed))
      )
      val reached = detach(
        quantified, instance, axiom(imp(quantified, instance), logical), quantifiedIsProvable)

      force(
        rules
          .disch(isProvable(quantified), reached)
          .flatMap(rules.disch(isClosed(t), _))
          .flatMap(rules.disch(isTerm(t), _))
          .flatMap(rules.disch(isFormula(p), _))
          .flatMap(rules.genAll(_, List(i, t, p)))
      )
    }

    /** [[Symmetry]]. Replacement at the formula `v_0 = t`, carried by reflexivity. */
    lazy val symmetry: Kernel.Thm = {
      val t = Term.variable("t", numbers)
      val u = Term.variable("u", numbers)
      val index = zeroTag
      val termT = assumed(isTerm(t))
      val termU = assumed(isTerm(u))
      val closedT = assumed(isClosed(t))
      val closedU = assumed(isClosed(u))
      val premise = assumed(isProvable(objEq(t, u)))

      val hole = objEq(objVar(index), t)
      val holeIsFormula = force(
        rules
          .specAll(formulaOfEquality, List(objVar(index), t))
          .flatMap(rules.mp(_, force(rules.spec(index, variableIsTerm))))
          .flatMap(rules.mp(_, termT))
      )

      // The hole filled with `t` is `t = t`, and with `u` is `u = t`. The right-hand `t` comes
      // back untouched both times, which is the idleness lemma being spent.
      val atT = acrossEquality(
        index, t, objVar(index), t, filled(index, t), idle(index, t, t, termT, closedT))
      val atU = acrossEquality(
        index, u, objVar(index), t, filled(index, u), idle(index, u, t, termT, closedT))

      val opened = replaced(
        index, t, u, hole, holeIsFormula, termT, termU, closedT, closedU, premise, atT, atU)

      val reflexivity = force(
        rules
          .specTo(reflexive, imply(isTerm(t), isLogical(objEq(t, t))))
          .flatMap(rules.mp(_, termT))
      )
      val reached = detach(
        objEq(t, t), objEq(u, t), opened, axiom(objEq(t, t), reflexivity))

      force(
        rules
          .disch(isProvable(objEq(t, u)), reached)
          .flatMap(rules.disch(isClosed(u), _))
          .flatMap(rules.disch(isClosed(t), _))
          .flatMap(rules.disch(isTerm(u), _))
          .flatMap(rules.disch(isTerm(t), _))
          .flatMap(rules.genAll(_, List(t, u)))
      )
    }

    /** [[Transitivity]]. Symmetry first, then replacement at the hole `v_0 = w`. */
    lazy val transitivity: Kernel.Thm = {
      val t = Term.variable("t", numbers)
      val u = Term.variable("u", numbers)
      val w = Term.variable("w", numbers)
      val index = zeroTag
      val termT = assumed(isTerm(t))
      val termU = assumed(isTerm(u))
      val termW = assumed(isTerm(w))
      val closedT = assumed(isClosed(t))
      val closedU = assumed(isClosed(u))
      val closedW = assumed(isClosed(w))
      val first = assumed(isProvable(objEq(t, u)))
      val second = assumed(isProvable(objEq(u, w)))

      val reversed = force(
        rules
          .specAll(symmetry, List(t, u))
          .flatMap(rules.mp(_, termT))
          .flatMap(rules.mp(_, termU))
          .flatMap(rules.mp(_, closedT))
          .flatMap(rules.mp(_, closedU))
          .flatMap(rules.mp(_, first))
      )

      val hole = objEq(objVar(index), w)
      val holeIsFormula = force(
        rules
          .specAll(formulaOfEquality, List(objVar(index), w))
          .flatMap(rules.mp(_, force(rules.spec(index, variableIsTerm))))
          .flatMap(rules.mp(_, termW))
      )
      val atU = acrossEquality(
        index, u, objVar(index), w, filled(index, u), idle(index, u, w, termW, closedW))
      val atT = acrossEquality(
        index, t, objVar(index), w, filled(index, t), idle(index, t, w, termW, closedW))

      val opened = replaced(
        index, u, t, hole, holeIsFormula, termU, termT, closedU, closedT, reversed, atU, atT)
      val reached = detach(objEq(u, w), objEq(t, w), opened, second)

      force(
        rules
          .disch(isProvable(objEq(u, w)), reached)
          .flatMap(rules.disch(isProvable(objEq(t, u)), _))
          .flatMap(rules.disch(isClosed(w), _))
          .flatMap(rules.disch(isClosed(u), _))
          .flatMap(rules.disch(isClosed(t), _))
          .flatMap(rules.disch(isTerm(w), _))
          .flatMap(rules.disch(isTerm(u), _))
          .flatMap(rules.disch(isTerm(t), _))
          .flatMap(rules.genAll(_, List(t, u, w)))
      )
    }

    /** [[SuccessorCongruence]]. The hole is `S t = S v_0`, so both instances substitute inside. */
    lazy val successorCongruence: Kernel.Thm = {
      val t = Term.variable("t", numbers)
      val u = Term.variable("u", numbers)
      val index = zeroTag
      val termT = assumed(isTerm(t))
      val termU = assumed(isTerm(u))
      val closedT = assumed(isClosed(t))
      val closedU = assumed(isClosed(u))
      val premise = assumed(isProvable(objEq(t, u)))

      val successorOf = (inner: Term, isTerm: Kernel.Thm) =>
        force(rules.spec(inner, successorIsTerm).flatMap(rules.mp(_, isTerm)))

      val hole = objEq(objSucc(t), objSucc(objVar(index)))
      val holeIsFormula = force(
        rules
          .specAll(formulaOfEquality, List(objSucc(t), objSucc(objVar(index))))
          .flatMap(rules.mp(_, successorOf(t, termT)))
          .flatMap(rules.mp(_, successorOf(objVar(index), force(rules.spec(index, variableIsTerm)))))
      )

      def instanceAt(replacement: Term, replacementIsTerm: Kernel.Thm): Kernel.Thm =
        acrossEquality(
          index, replacement, objSucc(t), objSucc(objVar(index)),
          acrossSuccessor(index, replacement, t, idle(index, replacement, t, termT, closedT)),
          acrossSuccessor(index, replacement, objVar(index), filled(index, replacement)))

      val atT = instanceAt(t, termT)
      val atU = instanceAt(u, termU)

      val opened = replaced(
        index, t, u, hole, holeIsFormula, termT, termU, closedT, closedU, premise, atT, atU)

      val reflexivity = force(
        rules
          .specTo(reflexive, imply(isTerm(objSucc(t)), isLogical(objEq(objSucc(t), objSucc(t)))))
          .flatMap(rules.mp(_, successorOf(t, termT)))
      )
      val reached = detach(
        objEq(objSucc(t), objSucc(t)), objEq(objSucc(t), objSucc(u)),
        opened, axiom(objEq(objSucc(t), objSucc(t)), reflexivity))

      force(
        rules
          .disch(isProvable(objEq(t, u)), reached)
          .flatMap(rules.disch(isClosed(u), _))
          .flatMap(rules.disch(isClosed(t), _))
          .flatMap(rules.disch(isTerm(u), _))
          .flatMap(rules.disch(isTerm(t), _))
          .flatMap(rules.genAll(_, List(t, u)))
      )
    }

    /** [[Syllogism]]. Weaken the second implication under `p`, distribute, detach twice. */
    lazy val syllogism: Kernel.Thm = {
      val p = Term.variable("p", numbers)
      val q = Term.variable("q", numbers)
      val r = Term.variable("r", numbers)
      val formulaP = assumed(isFormula(p))
      val formulaQ = assumed(isFormula(q))
      val formulaR = assumed(isFormula(r))
      val firstStep = assumed(isProvable(imp(p, q)))
      val secondStep = assumed(isProvable(imp(q, r)))

      val formulaQR = formImp(q, r, formulaQ, formulaR)
      val lifted = detach(
        imp(q, r), imp(p, imp(q, r)),
        weaken(imp(q, r), p, formulaQR, formulaP), secondStep)
      val spread = detach(
        imp(p, imp(q, r)), imp(imp(p, q), imp(p, r)),
        distribute(p, q, r, formulaP, formulaQ, formulaR), lifted)
      val chained = detach(imp(p, q), imp(p, r), spread, firstStep)

      force(
        rules
          .disch(isProvable(imp(q, r)), chained)
          .flatMap(rules.disch(isProvable(imp(p, q)), _))
          .flatMap(rules.disch(isFormula(r), _))
          .flatMap(rules.disch(isFormula(q), _))
          .flatMap(rules.disch(isFormula(p), _))
          .flatMap(rules.genAll(_, List(p, q, r)))
      )
    }

    /** [[Weaken]]: weakening is an axiom, so detaching the theorem leaves the implication. */
    lazy val weaken: Kernel.Thm = {
      val h = Term.variable("h", numbers)
      val p = Term.variable("p", numbers)
      val formulaH = assumed(isFormula(h))
      val formulaP = assumed(isFormula(p))
      val held = assumed(isProvable(p))

      val reached = detach(p, imp(h, p), weaken(p, h, formulaP, formulaH), held)

      force(
        rules
          .disch(isProvable(p), reached)
          .flatMap(rules.disch(isFormula(p), _))
          .flatMap(rules.disch(isFormula(h), _))
          .flatMap(rules.genAll(_, List(h, p)))
      )
    }

    /** [[ImplicationModusPonens]]: distribution, then two detachments. */
    lazy val implicationModusPonens: Kernel.Thm = {
      val h = Term.variable("h", numbers)
      val p = Term.variable("p", numbers)
      val q = Term.variable("q", numbers)
      val formulaH = assumed(isFormula(h))
      val formulaP = assumed(isFormula(p))
      val formulaQ = assumed(isFormula(q))
      val implication = assumed(isProvable(imp(h, imp(p, q))))
      val antecedent = assumed(isProvable(imp(h, p)))

      val spread = detach(
        imp(h, imp(p, q)), imp(imp(h, p), imp(h, q)),
        distribute(h, p, q, formulaH, formulaP, formulaQ), implication)
      val reached = detach(imp(h, p), imp(h, q), spread, antecedent)

      force(
        rules
          .disch(isProvable(imp(h, p)), reached)
          .flatMap(rules.disch(isProvable(imp(h, imp(p, q))), _))
          .flatMap(rules.disch(isFormula(q), _))
          .flatMap(rules.disch(isFormula(p), _))
          .flatMap(rules.disch(isFormula(h), _))
          .flatMap(rules.genAll(_, List(h, p, q)))
      )
    }

    /** [[ImplicationGeneralisation]]: generalise, distribute the quantifier, then chain. */
    lazy val implicationGeneralisation: Kernel.Thm = {
      val i = Term.variable("i", numbers)
      val h = Term.variable("h", numbers)
      val p = Term.variable("p", numbers)
      val formulaH = assumed(isFormula(h))
      val formulaP = assumed(isFormula(p))
      val notFreeTerm = force(logic.mkNot(isFree(i, h)))
      val notFree = assumed(notFreeTerm)
      val held = assumed(isProvable(imp(h, p)))

      // `!i. (h ==> p)` is provable, by closure under the other rule of inference.
      val generalised = force(
        rules
          .specTo(generalisation,
            imply(isProvable(imp(h, p)), isProvable(forAll(i, imp(h, p)))))
          .flatMap(rules.mp(_, held)))

      // The quantifier distributes over the implication, leaving `(!i. h) ==> (!i. p)`.
      val distributedCode = imp(forAll(i, imp(h, p)), imp(forAll(i, h), forAll(i, p)))
      val distributedAxiom = axiom(
        distributedCode,
        force(
          rules
            .specTo(universal,
              imply(isFormula(h), imply(isFormula(p), isLogical(distributedCode))))
            .flatMap(rules.mp(_, formulaH))
            .flatMap(rules.mp(_, formulaP))))
      val spread = detach(
        forAll(i, imp(h, p)), imp(forAll(i, h), forAll(i, p)), distributedAxiom, generalised)

      // And the hypothesis reaches its own generalisation, which is where the condition is spent.
      val vacuousCode = imp(h, forAll(i, h))
      val vacuousAxiom = axiom(
        vacuousCode,
        force(
          rules
            .specTo(vacuous, imply(isFormula(h), imply(notFreeTerm, isLogical(vacuousCode))))
            .flatMap(rules.mp(_, formulaH))
            .flatMap(rules.mp(_, notFree))))

      val formulaOfAll = force(
        rules
          .specTo(force(language.fact("NUM_FORM_ALL")),
            imply(isFormula(h), isFormula(forAll(i, h))))
          .flatMap(rules.mp(_, formulaH)))
      val formulaOfAllP = force(
        rules
          .specTo(force(language.fact("NUM_FORM_ALL")),
            imply(isFormula(p), isFormula(forAll(i, p))))
          .flatMap(rules.mp(_, formulaP)))

      val reached = force(
        rules
          .specTo(
            syllogism,
            imply(
              isFormula(h),
              imply(
                isFormula(forAll(i, h)),
                imply(
                  isFormula(forAll(i, p)),
                  imply(
                    isProvable(imp(h, forAll(i, h))),
                    imply(
                      isProvable(imp(forAll(i, h), forAll(i, p))),
                      isProvable(imp(h, forAll(i, p)))))))))
          .flatMap(rules.mp(_, formulaH))
          .flatMap(rules.mp(_, formulaOfAll))
          .flatMap(rules.mp(_, formulaOfAllP))
          .flatMap(rules.mp(_, vacuousAxiom))
          .flatMap(rules.mp(_, spread)))

      force(
        rules
          .disch(isProvable(imp(h, p)), reached)
          .flatMap(rules.disch(notFreeTerm, _))
          .flatMap(rules.disch(isFormula(p), _))
          .flatMap(rules.disch(isFormula(h), _))
          .flatMap(rules.genAll(_, List(i, h, p)))
      )
    }

    /** [[DeductionTheorem]]. The five cases are the five ways a step can be justified. */
    lazy val deductionTheorem: Kernel.Thm = {
      val h = Term.variable("h", numbers)
      val p = Term.variable("p", numbers)
      val formulaH = assumed(isFormula(h))
      val index = Conv.freshVariable("i", numbers, Set(h, p))
      val notFreeTerm = force(logic.mkForall(index, force(logic.mkNot(isFree(index, h)))))
      val notFree = assumed(notFreeTerm)
      val fromTerm = isProvableFrom(h, p)
      val fromH = assumed(fromTerm)

      /** `NUM_PROV (h ==> x)` carried along an equation `x = y`. */
      def under(equation: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
        force(Conv
          .apTerm(provableConstant, force(Conv.apTerm(applied(coding, List(seven)),
            force(Conv.apTerm(applied(pairing, List(h)), equation)))))
          .flatMap(step => LogicError.lift(Kernel.eqMp(step, held))))

      val opened = force(rules.specAll(vf(Provability.ProvableFromCases), List(h, p))
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, fromH))))

      val settled = openAt(opened, "k", Set(h, p)) { (k, atK) =>
        openAt(atK, "a", Set(h, p, k)) { (a, atA) =>
          openAt(atA, "b", Set(h, p, k, a)) { (b, atB) =>
            val last = force(rules.conjElim1(atB))
            val steps = force(rules.conjElim2(atB))
            val taken = Set(h, p, k, a, b)

            def unfoldedAt(x: Term, small: Kernel.Thm): Kernel.Thm =
              force(rules.specAll(vf(Provability.StepFromCases), List(h, a, b, x))
                .flatMap(step => LogicError.lift(Kernel.eqMp(step,
                  force(rules.spec(x, steps).flatMap(rules.mp(_, small)))))))

            def formulaAt(x: Term, small: Kernel.Thm): Kernel.Thm =
              force(rules.conjElim1(unfoldedAt(x, small)))

            val marker = Conv.freshVariable("j", numbers, taken)
            def claimAt(x: Term): Term =
              imply(atMost(x, k), isProvable(imp(h, beta(a, b, x))))
            val property = force(LogicError.lift(Term.abs(marker, claimAt(marker))))

            // The induction's shape is read off its own instance rather than rebuilt, because
            // `Logic.stripForall` refreshes the binder and the proof has to use the one it gives.
            val instance = normalised(force(rules.spec(property, pf(Peano.StrongInduction))))
            val stepTerm = logic.destImp(instance.conclusion)
              .getOrElse(throw new RefusedHere(NotOfForm("an implication", instance.conclusion)))
              ._1
            val stripped = force(Logic.stripForall(stepTerm))
            val j = stripped._1.headOption
              .getOrElse(throw new RefusedHere(NotOfForm("a universal", stepTerm)))
            val inner = logic.destImp(stripped._2)
              .getOrElse(throw new RefusedHere(NotOfForm("an implication", stripped._2)))
            val hypothesis = assumed(inner._1)
            val goal = logic.destImp(inner._2)
              .getOrElse(throw new RefusedHere(NotOfForm("an implication", inner._2)))
            val atMostK = assumed(goal._1)
            val target = goal._2

            def earlier(x: Term, belowJ: Kernel.Thm, small: Kernel.Thm): Kernel.Thm =
              force(rules.spec(x, hypothesis)
                .flatMap(rules.mp(_, belowJ))
                .map(normalised)
                .flatMap(rules.mp(_, small)))

            /** From `x < j` and `j <= k`, that `x <= k`. */
            def within(x: Term, belowJ: Kernel.Thm): Kernel.Thm = {
              val strict = force(rules.specAll(pf(Peano.BelowThenAtMost), List(x, j, k))
                .flatMap(rules.mp(_, force(rules.conjIntro(belowJ, atMostK)))))
              force(rules.specAll(pf(Peano.AtMostFromBelow), List(x, k))
                .flatMap(rules.mp(_, strict)))
            }

            val unfolded = unfoldedAt(j, atMostK)
            val formulaJ = force(rules.conjElim1(unfolded))
            val choice = force(rules.conjElim2(unfolded))
            val choiceParts = disjunctsOf(choice.conclusion, 2)

            /** An axiom of either set, carried under the hypothesis. */
            def fromAxiom(membership: Kernel.Thm, provable: Kernel.Thm): Kernel.Thm = {
              val held =
                force(rules.spec(beta(a, b, j), provable).flatMap(rules.mp(_, membership)))
              force(rules.specTo(weaken,
                imply(isFormula(h), imply(isFormula(beta(a, b, j)),
                  imply(isProvable(beta(a, b, j)), target))))
                .flatMap(rules.mp(_, formulaH))
                .flatMap(rules.mp(_, formulaJ))
                .flatMap(rules.mp(_, held)))
            }

            val whenStep = {
              val cases = force(rules.specAll(vf(Provability.StepCases), List(a, b, j)))
              val four = disjunctsOf(
                Term.destEq(cases.conclusion).map(_._2)
                  .getOrElse(throw new RefusedHere(NotOfForm("an equation", cases.conclusion))),
                4)
              val entered = force(LogicError.lift(Kernel.eqMp(cases, assumed(choiceParts(0)))))

              val fromModusPonens = openAt(assumed(four(2)), "x", taken + j) { (x, atX) =>
                openAt(atX, "y", taken + j + x) { (y, atY) =>
                  val belowJ = force(rules.conjElim1(atY))
                  val rest = force(rules.conjElim2(atY))
                  val secondBelow = force(rules.conjElim1(rest))
                  val equation = force(rules.conjElim2(rest))
                  val small = within(y, secondBelow)

                  force(rules.specTo(implicationModusPonens,
                    imply(isFormula(h), imply(isFormula(beta(a, b, y)),
                      imply(isFormula(beta(a, b, j)),
                        imply(isProvable(imp(h, imp(beta(a, b, y), beta(a, b, j)))),
                          imply(isProvable(imp(h, beta(a, b, y))), target))))))
                    .flatMap(rules.mp(_, formulaH))
                    .flatMap(rules.mp(_, formulaAt(y, small)))
                    .flatMap(rules.mp(_, formulaJ))
                    .flatMap(rules.mp(_,
                      under(equation, earlier(x, belowJ, within(x, belowJ)))))
                    .flatMap(rules.mp(_, earlier(y, secondBelow, small))))
                }
              }

              val fromGeneralisation = openAt(assumed(four(3)), "x", taken + j) { (x, atX) =>
                openAt(atX, "i", taken + j + x) { (i, atI) =>
                  val belowJ = force(rules.conjElim1(atI))
                  val equation = force(rules.conjElim2(atI))
                  val small = within(x, belowJ)
                  val generalised = force(rules.specTo(implicationGeneralisation,
                    imply(isFormula(h), imply(isFormula(beta(a, b, x)),
                      imply(force(logic.mkNot(isFree(i, h))),
                        imply(isProvable(imp(h, beta(a, b, x))),
                          isProvable(imp(h, forAll(i, beta(a, b, x)))))))))
                    .flatMap(rules.mp(_, formulaH))
                    .flatMap(rules.mp(_, formulaAt(x, small)))
                    .flatMap(rules.mp(_, force(rules.spec(i, notFree))))
                    .flatMap(rules.mp(_, earlier(x, belowJ, small))))
                  under(force(Conv.sym(equation)), generalised)
                }
              }

              val tail = assumed(force(logic.mkDisj(four(2), four(3))))
              val rest = assumed(
                force(logic.mkDisj(four(1), force(logic.mkDisj(four(2), four(3))))))
              force(rules.disjElim(entered,
                fromAxiom(assumed(four(0)), vf(Provability.ProvablePeano)),
                force(rules.disjElim(rest,
                  fromAxiom(assumed(four(1)), vf(Provability.ProvableLogic)),
                  force(rules.disjElim(tail, fromModusPonens, fromGeneralisation))))))
            }

            val whenHypothesis = under(
              force(Conv.sym(assumed(choiceParts(1)))),
              force(rules.specTo(selfImplication, imply(isFormula(h), isProvable(imp(h, h))))
                .flatMap(rules.mp(_, formulaH))))

            val stepProof = force(rules
              .disch(goal._1, force(rules.disjElim(choice, whenStep, whenHypothesis)))
              .flatMap(rules.disch(inner._1, _))
              .flatMap(rules.gen(j, _)))

            val everywhere = force(rules.mp(instance, stepProof))
            under(last, force(rules.spec(k, everywhere)
              .map(normalised)
              .flatMap(rules.mp(_, force(rules.spec(k, pf(Peano.Reflexive)))))))
          }
        }
      }

      force(rules.disch(fromTerm, settled)
        .flatMap(rules.disch(notFreeTerm, _))
        .flatMap(rules.disch(isFormula(h), _))
        .flatMap(rules.genAll(_, List(h, p))))
    }

    /** A finished derivation against the statement this development publishes for it. */
    def checked(name: String, theorem: Kernel.Thm): Kernel.Thm = {
      val wanted = force(
        Statements
          .collectFirst { case (published, source) if published == name => source }
          .toRight(MissingDefinition(name))
          .flatMap(Parser.proposition(theory, notation, _))
      )
      if (theorem.conclusion == wanted) theorem
      else
        throw new RefusedHere(
          NotOfForm(s"the statement published for $name", theorem.conclusion))
    }
  }
}
