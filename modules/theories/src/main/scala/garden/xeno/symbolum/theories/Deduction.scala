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
 * concretely: no type, no constant, no definition, no axiom. `Chain.widest` therefore stays at
 * [[Provability]], and a reader who expects the last link to be the widest signature should read
 * that field rather than assume it moved.
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
 * == What is not here, and what it is in front of ==
 *
 * The deduction theorem, which is the tool that makes object-level derivations tractable, and which
 * needs a notion of derivation-from-hypotheses that [[Provability]] does not have: `NUM_PROV` takes
 * a formula and not a set.
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

  val Statements: Vector[(String, String)] = Vector(
    SelfImplication -> "!p:num. NUM_FORM p ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR p p))",
    Syllogism ->
      ("!p:num q:num r:num. NUM_FORM p ==> NUM_FORM q ==> NUM_FORM r ==> " +
        "NUM_PROV (NUM_CODE 7 (NUM_PAIR p q)) ==> NUM_PROV (NUM_CODE 7 (NUM_PAIR q r)) ==> " +
        "NUM_PROV (NUM_CODE 7 (NUM_PAIR p r))")
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
            Syllogism -> builder.checked(Syllogism, builder.syllogism)
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
    def selfImplication: Kernel.Thm = {
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

    /** [[Syllogism]]. Weaken the second implication under `p`, distribute, detach twice. */
    def syllogism: Kernel.Thm = {
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
