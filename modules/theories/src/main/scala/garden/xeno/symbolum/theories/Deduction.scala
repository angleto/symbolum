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
 *  - [[Deduction.SelfImplication]], that PA proves `p ==> p`. The classic three-line Hilbert
 *    derivation, and the reason it is three lines rather than one is that `p ==> p` is not an
 *    instance of any axiom: the system has no reflexivity for implication, only weakening and
 *    distribution, and getting from those to the identity is the standard exercise.
 *  - [[Deduction.Syllogism]], that provable `p ==> q` and provable `q ==> r` give provable `p ==>
 *    r`. The workhorse: every derivation of any length is a chain of these.
 *
 * Both cost the naturals' two axioms and nothing else, which `DeductionSpec` asserts as an equality
 * rather than as a ceiling.
 *
 * And the three rules the **deduction theorem** is assembled from, one per way a step can be
 * justified: [[Deduction.Weaken]] for the axiom cases, [[Deduction.ImplicationModusPonens]] for the
 * modus ponens case, and [[Deduction.ImplicationGeneralisation]] for the generalisation case, which
 * is the one that carries the side condition every textbook statement of that theorem carries.
 *
 * == What is not here, and what it is in front of ==
 *
 * The deduction theorem itself. Its three rules are above; what is missing is the thing they would
 * be applied to, which is a notion of derivation **from hypotheses** that [[Provability]] does not
 * have: `NUM_PROV` takes a formula and not a set. That wants a `NUM_PROV_FROM` beside the three
 * definitions there, with a fifth clause on a step saying it is the hypothesis itself, and then an
 * induction over the derivation whose five cases are the three rules above, the hypothesis case
 * (which is [[Deduction.SelfImplication]]) and nothing else.
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
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

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

  /**
   * PA's first axiom for addition, at any closed term rather than at a variable.
   *
   * `NUM_PA_ADD_ZERO` says `!v0. v0 + 0 = v0` and is a fact about a code; this is that axiom put
   * to work, which is a different thing and is what every arithmetic derivation actually reaches
   * for. One specialisation and the substitution computed.
   */
  val AdditionAtZero: String = "NUM_PROV_ADD_ZERO"

  /**
   * PA's second axiom for addition, at two closed terms.
   *
   * The same as [[AdditionAtZero]] with one more quantifier, and the extra quantifier is the whole
   * difference: the first substitution has to descend UNDER a binder for another index, and the
   * second has to pass over the term the first put in. The second is where
   * [[Language.SubstituteIdle]] is spent, and it is the reason that lemma had to be about every
   * closed term: what the first substitution leaves behind is an arbitrary `t`, not a numeral.
   */
  val AdditionAtSuccessor: String = "NUM_PROV_ADD_SUC"

  /**
   * PA proves its own addition on numerals, which is the first brick of Sigma-1 completeness.
   *
   * `|- !m n. NUM_PROV (code of "numeral m + numeral n = numeral (m + n)")`
   *
   * This is the embedded theory proving a general fact about itself rather than one instance of
   * one axiom, and it is the first statement here of that kind. The meta level knows `m + n`
   * because `Peano` computes it; the object level has to DERIVE the corresponding equation, and
   * the two are connected by nothing except this theorem.
   *
   * The induction is on `n` at the meta level and its two cases are the object theory's two
   * addition axioms. The base is [[AdditionAtZero]] at the numeral of `m`, with
   * `NUM_NUMERAL_ZERO` and `NUM_ADD_ZERO` turning what it gives into what was wanted. The step is
   * [[AdditionAtSuccessor]] followed by the hypothesis under [[SuccessorCongruence]], joined by
   * [[Transitivity]]: `t + S u` is provably `S (t + u)`, the hypothesis makes `t + u` provably the
   * numeral, and the successor carries across.
   *
   * **Every piece of it is something that did not exist this morning**, which is worth recording
   * because the theorem itself is three lines of mathematics. The schemes needed a closed term and
   * nothing was closed; instantiating one left a substitution nothing could compute; the equality
   * needed symmetry and congruence and had only reflexivity and replacement; and the step needs
   * closure of a SUM of two numerals, which wanted the four closure introduction rules. The
   * statement is short and the layer beneath it is the work.
   */
  val NumeralAddition: String = "NUM_PROV_NUMERAL_ADD"

  /**
   * A sum's left summand replaced by anything the embedded theory proves equal to it.
   *
   * `|- !t u w. ... ==> NUM_PROV (t = u) ==> NUM_PROV (t + w = u + w)`
   *
   * [[SuccessorCongruence]] one arity up, and it is here for the same reason that one is: the
   * replacement scheme of `NUM_LOGIC` gives the congruence of every function symbol, and what a
   * derivation reaches for is the congruence rather than the scheme. The induction below is what
   * wanted it — `t * S u` is `t * u + t`, so the hypothesis has to be carried into the LEFT
   * summand of a sum whose right summand is not what changed.
   */
  val SumCongruence: String = "NUM_PROV_ADD_CONG"

  /**
   * A sum's right summand replaced by anything the embedded theory proves equal to it.
   *
   * `|- !t u w. ... ==> NUM_PROV (t = u) ==> NUM_PROV (w + t = w + u)`
   *
   * [[SumCongruence]] with the hole on the other side, and it is not that one read through
   * commutativity: `x + y = y + x` is a theorem of PA only by induction, and nothing here derives
   * it. What wanted it is evaluating a closed term, where both summands of a sum are replaced by
   * their numerals, one after the other.
   */
  val SumCongruenceRight: String = "NUM_PROV_ADD_CONG_RIGHT"

  /** [[SumCongruence]] for a product: `NUM_PROV (t = u) ==> NUM_PROV (t * w = u * w)`. */
  val ProductCongruence: String = "NUM_PROV_MUL_CONG"

  /** [[SumCongruenceRight]] for a product: `NUM_PROV (t = u) ==> NUM_PROV (w * t = w * u)`. */
  val ProductCongruenceRight: String = "NUM_PROV_MUL_CONG_RIGHT"

  /**
   * `|- !t. NUM_TERM t ==> NUM_PROV (t = t)`
   *
   * The reflexivity axiom of `NUM_LOGIC` as a fact about provability, which every derivation here
   * reached for as two lines of its own. Unlike the congruences it asks nothing of `t` but being a
   * term: the axiom is a scheme over every term, closed or not.
   */
  val Reflexivity: String = "NUM_PROV_REFL"

  /** PA's first axiom for multiplication, at a closed term. [[AdditionAtZero]]'s counterpart. */
  val MultiplicationAtZero: String = "NUM_PROV_MUL_ZERO"

  /**
   * PA's second axiom for multiplication, at two closed terms.
   *
   * `[[AdditionAtSuccessor]]`'s counterpart and one step harder in the substitution: the axiom is
   * `v0 * S v1 = v0 * v1 + v0`, so the right side is a **sum of a product**, and the walk that
   * computes the substitution descends through both.
   */
  val MultiplicationAtSuccessor: String = "NUM_PROV_MUL_SUC"

  /**
   * PA proves its own multiplication on numerals, which is the second brick of Sigma-1 completeness.
   *
   * `|- !m n. NUM_PROV (code of "numeral m * numeral n = numeral (m * n)")`
   *
   * [[NumeralAddition]] is the first and this one stands on it. The induction is again on `n` at
   * the meta level and its two cases are the object theory's two multiplication axioms, but the
   * step needs one thing addition's did not: `t * S u` is provably `t * u + t`, so the hypothesis
   * has to travel into the left summand of a sum ([[SumCongruence]]), and what comes out is
   * `numeral (m * n) + numeral m`, which is a **sum of two numerals** and therefore exactly what
   * [[NumeralAddition]] settles. Addition's brick is not cited by multiplication's for elegance:
   * without it the step stops one equation short.
   *
   * Why it matters beyond itself: every pure-arithmetic representation the Goedel stack needs —
   * `NUM_TRI`, `NUM_PAIR`, `NUM_CODE` and the projections — is written with `*`, so no
   * representability proof above this could be discharged while the object theory could add its
   * numerals and not multiply them.
   */
  val NumeralMultiplication: String = "NUM_PROV_NUMERAL_MUL"

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
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR (NUM_CODE 2 t) (NUM_CODE 2 u)))"),
    AdditionAtZero ->
      ("!t:num. NUM_TERM t ==> NUM_CLOSED t ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR (NUM_CODE 3 (NUM_PAIR t (NUM_CODE 1 0))) t))"),
    AdditionAtSuccessor ->
      ("!t:num u:num. NUM_TERM t ==> NUM_CLOSED t ==> NUM_TERM u ==> NUM_CLOSED u ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 3 (NUM_PAIR t (NUM_CODE 2 u))) " +
        "(NUM_CODE 2 (NUM_CODE 3 (NUM_PAIR t u)))))"),
    NumeralAddition ->
      ("!m:num n:num. NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 3 (NUM_PAIR (NUM_NUMERAL m) (NUM_NUMERAL n))) " +
        "(NUM_NUMERAL (NUM_ADD m n))))"),
    SumCongruence ->
      ("!t:num u:num w:num. NUM_TERM t ==> NUM_CLOSED t ==> NUM_TERM u ==> NUM_CLOSED u ==> " +
        "NUM_TERM w ==> NUM_CLOSED w ==> NUM_PROV (NUM_CODE 5 (NUM_PAIR t u)) ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 3 (NUM_PAIR t w)) (NUM_CODE 3 (NUM_PAIR u w))))"),
    SumCongruenceRight ->
      ("!t:num u:num w:num. NUM_TERM t ==> NUM_CLOSED t ==> NUM_TERM u ==> NUM_CLOSED u ==> " +
        "NUM_TERM w ==> NUM_CLOSED w ==> NUM_PROV (NUM_CODE 5 (NUM_PAIR t u)) ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 3 (NUM_PAIR w t)) (NUM_CODE 3 (NUM_PAIR w u))))"),
    ProductCongruence ->
      ("!t:num u:num w:num. NUM_TERM t ==> NUM_CLOSED t ==> NUM_TERM u ==> NUM_CLOSED u ==> " +
        "NUM_TERM w ==> NUM_CLOSED w ==> NUM_PROV (NUM_CODE 5 (NUM_PAIR t u)) ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 4 (NUM_PAIR t w)) (NUM_CODE 4 (NUM_PAIR u w))))"),
    ProductCongruenceRight ->
      ("!t:num u:num w:num. NUM_TERM t ==> NUM_CLOSED t ==> NUM_TERM u ==> NUM_CLOSED u ==> " +
        "NUM_TERM w ==> NUM_CLOSED w ==> NUM_PROV (NUM_CODE 5 (NUM_PAIR t u)) ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 4 (NUM_PAIR w t)) (NUM_CODE 4 (NUM_PAIR w u))))"),
    Reflexivity -> "!t:num. NUM_TERM t ==> NUM_PROV (NUM_CODE 5 (NUM_PAIR t t))",
    MultiplicationAtZero ->
      ("!t:num. NUM_TERM t ==> NUM_CLOSED t ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR (NUM_CODE 4 (NUM_PAIR t (NUM_CODE 1 0))) (NUM_CODE 1 0)))"),
    MultiplicationAtSuccessor ->
      ("!t:num u:num. NUM_TERM t ==> NUM_CLOSED t ==> NUM_TERM u ==> NUM_CLOSED u ==> " +
        "NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 4 (NUM_PAIR t (NUM_CODE 2 u))) " +
        "(NUM_CODE 3 (NUM_PAIR (NUM_CODE 4 (NUM_PAIR t u)) t))))"),
    NumeralMultiplication ->
      ("!m:num n:num. NUM_PROV (NUM_CODE 5 (NUM_PAIR " +
        "(NUM_CODE 4 (NUM_PAIR (NUM_NUMERAL m) (NUM_NUMERAL n))) " +
        "(NUM_NUMERAL (NUM_MUL m n))))")
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
              builder.checked(SuccessorCongruence, builder.successorCongruence),
            AdditionAtZero -> builder.checked(AdditionAtZero, builder.additionAtZero),
            AdditionAtSuccessor ->
              builder.checked(AdditionAtSuccessor, builder.additionAtSuccessor),
            NumeralAddition -> builder.checked(NumeralAddition, builder.numeralAddition),
            SumCongruence -> builder.checked(SumCongruence, builder.sumCongruence),
            SumCongruenceRight ->
              builder.checked(SumCongruenceRight, builder.sumCongruenceRight),
            ProductCongruence -> builder.checked(ProductCongruence, builder.productCongruence),
            ProductCongruenceRight ->
              builder.checked(ProductCongruenceRight, builder.productCongruenceRight),
            Reflexivity -> builder.checked(Reflexivity, builder.reflexivity),
            MultiplicationAtZero ->
              builder.checked(MultiplicationAtZero, builder.multiplicationAtZero),
            MultiplicationAtSuccessor ->
              builder.checked(MultiplicationAtSuccessor, builder.multiplicationAtSuccessor),
            NumeralMultiplication ->
              builder.checked(NumeralMultiplication, builder.numeralMultiplication)
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
    private val three = force(Parser.term(theory, notation, "3", numbers))
    private val four = force(Parser.term(theory, notation, "4", numbers))
    private val oneTag = force(Parser.term(theory, notation, "1", numbers))
    private val substituteSum = force(language.fact(Language.SubstituteSum))
    private val substituteZero = force(language.fact(Language.SubstituteZero))
    private val substituteUniversal =
      force(language.fact(Language.FormulaSubstituteUniversal))
    private val formulaOfUniversal = force(language.fact(Language.FormulaUniversal))
    private val sumIsTerm = force(language.fact(Language.TermSum))
    private val productIsTerm = force(language.fact(Language.TermProduct))
    private val substituteProduct = force(language.fact(Language.SubstituteProduct))
    private val zeroIsTerm = force(language.fact(Language.TermZero))
    private val peanoIsProvable = force(provability.fact(Provability.ProvablePeano))
    private lazy val specialisingRule = checked(Specialisation, specialisation)
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

    /** The object language's sum, as a code. */
    private def objSum(left: Term, right: Term): Term =
      applied(coding, List(three, applied(pairing, List(left, right))))

    /** The object language's product, as a code. */
    private def objProd(left: Term, right: Term): Term =
      applied(coding, List(four, applied(pairing, List(left, right))))

    /** The object language's zero, as a code. */
    private val objZero: Term = applied(coding, List(oneTag, zeroTag))

    /** `NUM_PROV` of what an axiom of PA says, which is one step. */
    private def provesAxiom(name: String): Kernel.Thm = {
      val membership = force(language.fact(name))
      val code = membership.conclusion match {
        case App(_, argument) => argument
        case other => throw new RefusedHere(NotOfForm("a membership", other))
      }
      force(rules.spec(code, peanoIsProvable).flatMap(rules.mp(_, membership)))
    }

    /**
     * A provable quantified formula instantiated at a closed term, with the substitution computed.
     *
     * The rule is [[Specialisation]] and the rest is arithmetic on codes: without `computed` the
     * conclusion carries a `NUM_SUBST_FORM` and says nothing a reader can check.
     */
    private def atClosedTerm(
      provable: Kernel.Thm, index: Term, replacement: Term, body: Term,
      bodyIsFormula: Kernel.Thm, replacementIsTerm: Kernel.Thm, replacementIsClosed: Kernel.Thm,
      computed: Kernel.Thm
    ): Kernel.Thm = {
      val specialised = force(
        rules
          .specAll(specialisingRule, List(index, replacement, body))
          .flatMap(rules.mp(_, bodyIsFormula))
          .flatMap(rules.mp(_, replacementIsTerm))
          .flatMap(rules.mp(_, replacementIsClosed))
          .flatMap(rules.mp(_, provable))
      )
      force(
        Conv
          .apTerm(provableConstant, computed)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, specialised)))
      )
    }

    /** An axiom of PA with its outermost quantifier instantiated at a closed term. */
    private def axiomAt(
      name: String, index: Term, replacement: Term, body: Term,
      bodyIsFormula: Kernel.Thm, replacementIsTerm: Kernel.Thm, replacementIsClosed: Kernel.Thm,
      computed: Kernel.Thm
    ): Kernel.Thm =
      atClosedTerm(
        provesAxiom(name), index, replacement, body,
        bodyIsFormula, replacementIsTerm, replacementIsClosed, computed)

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

    /**
     * What substituting into a two-argument constructor gives, with both sides already settled.
     *
     * The equality of formulas and the sum of terms differ only in which clause and which tag they
     * are handed, so they are one function. The rebuilding is a congruence in both arguments of the
     * pairing, which is why it is `mkComb` over an `apTerm` rather than two `apTerm`s.
     */
    private def acrossBinary(
      clause: Kernel.Thm, tag: Term,
      index: Term, replacement: Term, left: Term, right: Term,
      leftDone: Kernel.Thm, rightDone: Kernel.Thm
    ): Kernel.Thm = {
      val instance = force(rules.specAll(clause, List(index, replacement, left, right)))
      force(Conv.trans(instance, pairCongruence(tag, leftDone, rightDone)))
    }

    /** `NUM_CODE k (NUM_PAIR a b) = NUM_CODE k (NUM_PAIR a' b')` from the two components. */
    private def pairCongruence(tag: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm = {
      val paired = force(
        Conv
          .apTerm(pairing, left)
          .flatMap(half => LogicError.lift(Kernel.mkComb(half, right))))
      force(Conv.apTerm(applied(coding, List(tag)), paired))
    }

    /** `NUM_CODE k a = NUM_CODE k a'` from the one component. */
    private def codeCongruence(tag: Term, inner: Kernel.Thm): Kernel.Thm =
      force(Conv.apTerm(applied(coding, List(tag)), inner))

    /** What substituting into an equality gives, with both sides already settled. */
    private def acrossEquality(
      index: Term, replacement: Term, left: Term, right: Term,
      leftDone: Kernel.Thm, rightDone: Kernel.Thm
    ): Kernel.Thm =
      acrossBinary(substituteEquality, five, index, replacement, left, right, leftDone, rightDone)

    /** The same for a sum of two terms. */
    private def acrossSum(
      index: Term, replacement: Term, left: Term, right: Term,
      leftDone: Kernel.Thm, rightDone: Kernel.Thm
    ): Kernel.Thm =
      acrossBinary(substituteSum, three, index, replacement, left, right, leftDone, rightDone)

    /** The same for a product, which is the same clause at the other tag. */
    private def acrossProd(
      index: Term, replacement: Term, left: Term, right: Term,
      leftDone: Kernel.Thm, rightDone: Kernel.Thm
    ): Kernel.Thm =
      acrossBinary(substituteProduct, four, index, replacement, left, right, leftDone, rightDone)

    /**
     * `NUM_SUBST_TERM i r (NUM_CODE 0 j) = NUM_CODE 0 j`, where `j` is some other index.
     *
     * The companion of [[filled]]: that one is the variable the substitution is FOR, this one is
     * every other variable. The guard is decided by `Successor.distinct`, which is why the two
     * indices have to be numerals rather than variables.
     */
    private def missed(index: Term, replacement: Term, other: Term): Kernel.Thm = {
      val clause = force(rules.specAll(substituteVariable, List(index, replacement, other)))
      val apart = force(language.successor.distinct(other, index))
      val guard = force(LogicError.lift(Term.eq(other, index)))
      val scheme = Kernel.instType(
        Map(Classical.TypeVariable -> numbers), force(classical.fact(Classical.CondFalse)))
      val taken = force(
        rules
          .specAll(scheme, List(guard, replacement, objVar(other)))
          .flatMap(rules.mp(_, apart))
      )
      force(Conv.trans(clause, taken))
    }

    /**
     * What substituting under a quantifier binding some OTHER index gives.
     *
     * The clause leaves the formula alone where the two indices agree and descends where they do
     * not, so this is the second branch with the guard decided. A quantifier binding the index
     * being replaced needs the first branch and no caller here wants it.
     */
    private def acrossUniversal(
      index: Term, replacement: Term, bound: Term, body: Term, bodyDone: Kernel.Thm
    ): Kernel.Thm = {
      val clause = force(
        rules.specAll(substituteUniversal, List(index, replacement, bound, body)))
      val apart = force(language.successor.distinct(bound, index))
      val guard = force(LogicError.lift(Term.eq(bound, index)))
      val unchanged = applied(coding, List(eight, applied(pairing, List(bound, body))))
      val descended = applied(coding, List(eight, applied(pairing, List(
        bound,
        applied(
          constant(Language.FormulaSubstituteName,
            Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, numbers)))),
          List(index, replacement, body))))))
      val scheme = Kernel.instType(
        Map(Classical.TypeVariable -> numbers), force(classical.fact(Classical.CondFalse)))
      val taken = force(
        rules
          .specAll(scheme, List(guard, unchanged, descended))
          .flatMap(rules.mp(_, apart))
      )
      val moved = force(Conv.trans(clause, taken))
      val lifted = force(
        Conv
          .apTerm(pairing, Conv.refl(bound))
          .flatMap(_ => Conv.apTerm(force(LogicError.lift(Term.app(pairing, bound))), bodyDone))
          .flatMap(inner => Conv.apTerm(applied(coding, List(eight)), inner))
      )
      force(Conv.trans(moved, lifted))
    }

    /** `NUM_SUBST_TERM i r (NUM_CODE 1 0) = NUM_CODE 1 0`: the object zero is untouched. */
    private def zeroStays(index: Term, replacement: Term): Kernel.Thm =
      force(rules.specAll(substituteZero, List(index, replacement)))
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

    /** [[AdditionAtZero]]. One specialisation of `NUM_PA_ADD_ZERO`, with the substitution done. */
    lazy val additionAtZero: Kernel.Thm = {
      val t = Term.variable("t", numbers)
      val index = zeroTag
      val termT = assumed(isTerm(t))
      val closedT = assumed(isClosed(t))

      val variable = objVar(index)
      val variableIsATerm = force(rules.spec(index, variableIsTerm))
      val body = objEq(objSum(variable, objZero), variable)
      val bodyIsFormula = force(
        rules
          .specAll(formulaOfEquality, List(objSum(variable, objZero), variable))
          .flatMap(rules.mp(_, force(
            rules
              .specAll(sumIsTerm, List(variable, objZero))
              .flatMap(rules.mp(_, variableIsATerm))
              .flatMap(rules.mp(_, zeroIsTerm)))))
          .flatMap(rules.mp(_, variableIsATerm))
      )

      val computed = acrossEquality(
        index, t, objSum(variable, objZero), variable,
        acrossSum(index, t, variable, objZero, filled(index, t), zeroStays(index, t)),
        filled(index, t))

      val reached = axiomAt(
        "NUM_PA_ADD_ZERO", index, t, body, bodyIsFormula, termT, closedT, computed)

      force(
        rules
          .disch(isClosed(t), reached)
          .flatMap(rules.disch(isTerm(t), _))
          .flatMap(rules.gen(t, _))
      )
    }

    /** [[AdditionAtSuccessor]]. Two specialisations, one under a binder and one over a term. */
    lazy val additionAtSuccessor: Kernel.Thm = {
      val t = Term.variable("t", numbers)
      val u = Term.variable("u", numbers)
      val outer = zeroTag
      val inner = oneTag
      val termT = assumed(isTerm(t))
      val closedT = assumed(isClosed(t))
      val termU = assumed(isTerm(u))
      val closedU = assumed(isClosed(u))

      val first = objVar(outer)
      val second = objVar(inner)
      val firstIsTerm = force(rules.spec(outer, variableIsTerm))
      val secondIsTerm = force(rules.spec(inner, variableIsTerm))

      def succOf(x: Term, isTermThm: Kernel.Thm): Kernel.Thm =
        force(rules.spec(x, successorIsTerm).flatMap(rules.mp(_, isTermThm)))
      def sumOf(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .specAll(sumIsTerm, List(a, b))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right)))
      def equalityOf(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .specAll(formulaOfEquality, List(a, b))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right)))

      // The axiom's innermost formula, `v0 + S v1 = S (v0 + v1)`.
      val leftSide = objSum(first, objSucc(second))
      val rightSide = objSucc(objSum(first, second))
      val core = objEq(leftSide, rightSide)
      val coreIsFormula = equalityOf(
        leftSide, rightSide,
        sumOf(first, objSucc(second), firstIsTerm, succOf(second, secondIsTerm)),
        succOf(objSum(first, second), sumOf(first, second, firstIsTerm, secondIsTerm)))

      val body = applied(coding, List(eight, applied(pairing, List(inner, core))))
      val bodyIsFormula = force(
        rules
          .specAll(formulaOfUniversal, List(inner, core))
          .flatMap(rules.mp(_, coreIsFormula)))

      // First: `v0` becomes `t`, which means going under the binder for `v1`.
      val coreAtT = acrossEquality(
        outer, t, leftSide, rightSide,
        acrossSum(
          outer, t, first, objSucc(second),
          filled(outer, t), acrossSuccessor(outer, t, second, missed(outer, t, inner))),
        acrossSuccessor(
          outer, t, objSum(first, second),
          acrossSum(outer, t, first, second, filled(outer, t), missed(outer, t, inner))))
      val underBinder = acrossUniversal(outer, t, inner, core, coreAtT)

      val once = axiomAt(
        "NUM_PA_ADD_SUC", outer, t, body, bodyIsFormula, termT, closedT, underBinder)

      // Second: `v1` becomes `u`, and `t` has to come back untouched, which is idleness.
      val leftAtT = objSum(t, objSucc(second))
      val rightAtT = objSucc(objSum(t, second))
      val coreAtTIsFormula = equalityOf(
        leftAtT, rightAtT,
        sumOf(t, objSucc(second), termT, succOf(second, secondIsTerm)),
        succOf(objSum(t, second), sumOf(t, second, termT, secondIsTerm)))

      val stays = idle(inner, u, t, termT, closedT)
      val coreAtU = acrossEquality(
        inner, u, leftAtT, rightAtT,
        acrossSum(
          inner, u, t, objSucc(second),
          stays, acrossSuccessor(inner, u, second, filled(inner, u))),
        acrossSuccessor(
          inner, u, objSum(t, second),
          acrossSum(inner, u, t, second, stays, filled(inner, u))))

      val reached = atClosedTerm(
        once, inner, u, objEq(leftAtT, rightAtT), coreAtTIsFormula, termU, closedU, coreAtU)

      force(
        rules
          .disch(isClosed(u), reached)
          .flatMap(rules.disch(isTerm(u), _))
          .flatMap(rules.disch(isClosed(t), _))
          .flatMap(rules.disch(isTerm(t), _))
          .flatMap(rules.genAll(_, List(t, u)))
      )
    }

    /** [[SumCongruence]]. [[successorCongruence]] with a binary hole, so the other summand idles. */
    lazy val sumCongruence: Kernel.Thm =
      binaryCongruence(objSum, sumIsTerm, acrossSum, onLeft = true)

    /** [[SumCongruenceRight]], the same hole on the other side. */
    lazy val sumCongruenceRight: Kernel.Thm =
      binaryCongruence(objSum, sumIsTerm, acrossSum, onLeft = false)

    /** [[ProductCongruence]], the same hole at the other tag. */
    lazy val productCongruence: Kernel.Thm =
      binaryCongruence(objProd, productIsTerm, acrossProd, onLeft = true)

    /** [[ProductCongruenceRight]]. */
    lazy val productCongruenceRight: Kernel.Thm =
      binaryCongruence(objProd, productIsTerm, acrossProd, onLeft = false)

    /**
     * One operand of a binary term replaced by a provably equal one, the other operand idling.
     *
     * The four congruences differ in the constructor and in which side the hole is on, and in
     * nothing else: the hole is `op(t, w) = op(v0, w)` or `op(w, t) = op(w, v0)`, one side already
     * what it will be and the other where the replacement goes, and `w` comes back untouched in
     * both instances because it is closed.
     */
    private def binaryCongruence(
      operation: (Term, Term) => Term,
      operationIsTerm: Kernel.Thm,
      across: (Term, Term, Term, Term, Kernel.Thm, Kernel.Thm) => Kernel.Thm,
      onLeft: Boolean
    ): Kernel.Thm = {
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
      val premise = assumed(isProvable(objEq(t, u)))

      def built(x: Term): Term = if (onLeft) operation(x, w) else operation(w, x)
      def builtIsTerm(x: Term, xIsTerm: Kernel.Thm): Kernel.Thm = {
        val (first, second, firstIsTerm, secondIsTerm) =
          if (onLeft) (x, w, xIsTerm, termW) else (w, x, termW, xIsTerm)
        force(
          rules
            .specAll(operationIsTerm, List(first, second))
            .flatMap(rules.mp(_, firstIsTerm))
            .flatMap(rules.mp(_, secondIsTerm)))
      }

      val variableIsATerm = force(rules.spec(index, variableIsTerm))
      val hole = objEq(built(t), built(objVar(index)))
      val holeIsFormula = force(
        rules
          .specAll(formulaOfEquality, List(built(t), built(objVar(index))))
          .flatMap(rules.mp(_, builtIsTerm(t, termT)))
          .flatMap(rules.mp(_, builtIsTerm(objVar(index), variableIsATerm))))

      /** Substituting into `built(x)`, given what substituting into `x` gives. */
      def acrossBuilt(replacement: Term, x: Term, xDone: Kernel.Thm): Kernel.Thm = {
        val wStays = idle(index, replacement, w, termW, closedW)
        if (onLeft) across(index, replacement, x, w, xDone, wStays)
        else across(index, replacement, w, x, wStays, xDone)
      }

      def instanceAt(replacement: Term): Kernel.Thm =
        acrossEquality(
          index, replacement, built(t), built(objVar(index)),
          acrossBuilt(replacement, t, idle(index, replacement, t, termT, closedT)),
          acrossBuilt(replacement, objVar(index), filled(index, replacement)))

      val opened = replaced(
        index, t, u, hole, holeIsFormula, termT, termU, closedT, closedU, premise,
        instanceAt(t), instanceAt(u))

      val start = built(t)
      val reflexivity = force(
        rules
          .specTo(reflexive, imply(isTerm(start), isLogical(objEq(start, start))))
          .flatMap(rules.mp(_, builtIsTerm(t, termT))))
      val reached = detach(
        objEq(start, start), objEq(start, built(u)),
        opened, axiom(objEq(start, start), reflexivity))

      force(
        rules
          .disch(isProvable(objEq(t, u)), reached)
          .flatMap(rules.disch(isClosed(w), _))
          .flatMap(rules.disch(isTerm(w), _))
          .flatMap(rules.disch(isClosed(u), _))
          .flatMap(rules.disch(isTerm(u), _))
          .flatMap(rules.disch(isClosed(t), _))
          .flatMap(rules.disch(isTerm(t), _))
          .flatMap(rules.genAll(_, List(t, u, w))))
    }

    /** [[Reflexivity]]: the scheme at `t`, and one step from an axiom to a theorem. */
    lazy val reflexivity: Kernel.Thm = {
      val t = Term.variable("t", numbers)
      val termT = assumed(isTerm(t))
      val logical = force(
        rules
          .specTo(reflexive, imply(isTerm(t), isLogical(objEq(t, t))))
          .flatMap(rules.mp(_, termT)))
      force(
        rules
          .disch(isTerm(t), axiom(objEq(t, t), logical))
          .flatMap(rules.gen(t, _)))
    }

    /** [[MultiplicationAtZero]]. [[additionAtZero]] at the other tag, and the answer is `0`. */
    lazy val multiplicationAtZero: Kernel.Thm = {
      val t = Term.variable("t", numbers)
      val index = zeroTag
      val termT = assumed(isTerm(t))
      val closedT = assumed(isClosed(t))

      val variable = objVar(index)
      val variableIsATerm = force(rules.spec(index, variableIsTerm))
      val body = objEq(objProd(variable, objZero), objZero)
      val bodyIsFormula = force(
        rules
          .specAll(formulaOfEquality, List(objProd(variable, objZero), objZero))
          .flatMap(rules.mp(_, force(
            rules
              .specAll(productIsTerm, List(variable, objZero))
              .flatMap(rules.mp(_, variableIsATerm))
              .flatMap(rules.mp(_, zeroIsTerm)))))
          .flatMap(rules.mp(_, zeroIsTerm)))

      // The right side is `0` and not the variable, so both halves of the equality are walked with
      // the zero staying put rather than one of them being the replacement.
      val computed = acrossEquality(
        index, t, objProd(variable, objZero), objZero,
        acrossProd(index, t, variable, objZero, filled(index, t), zeroStays(index, t)),
        zeroStays(index, t))

      val reached = axiomAt(
        "NUM_PA_MUL_ZERO", index, t, body, bodyIsFormula, termT, closedT, computed)

      force(
        rules
          .disch(isClosed(t), reached)
          .flatMap(rules.disch(isTerm(t), _))
          .flatMap(rules.gen(t, _)))
    }

    /** [[MultiplicationAtSuccessor]]. [[additionAtSuccessor]]'s shape over a sum of a product. */
    lazy val multiplicationAtSuccessor: Kernel.Thm = {
      val t = Term.variable("t", numbers)
      val u = Term.variable("u", numbers)
      val outer = zeroTag
      val inner = oneTag
      val termT = assumed(isTerm(t))
      val closedT = assumed(isClosed(t))
      val termU = assumed(isTerm(u))
      val closedU = assumed(isClosed(u))

      val first = objVar(outer)
      val second = objVar(inner)
      val firstIsTerm = force(rules.spec(outer, variableIsTerm))
      val secondIsTerm = force(rules.spec(inner, variableIsTerm))

      def succOf(x: Term, isTermThm: Kernel.Thm): Kernel.Thm =
        force(rules.spec(x, successorIsTerm).flatMap(rules.mp(_, isTermThm)))
      def sumOf(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .specAll(sumIsTerm, List(a, b))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right)))
      def prodOf(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .specAll(productIsTerm, List(a, b))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right)))
      def equalityOf(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .specAll(formulaOfEquality, List(a, b))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right)))

      // The axiom's innermost formula, `v0 * S v1 = v0 * v1 + v0`.
      val leftSide = objProd(first, objSucc(second))
      val rightSide = objSum(objProd(first, second), first)
      val core = objEq(leftSide, rightSide)
      val coreIsFormula = equalityOf(
        leftSide, rightSide,
        prodOf(first, objSucc(second), firstIsTerm, succOf(second, secondIsTerm)),
        sumOf(
          objProd(first, second), first,
          prodOf(first, second, firstIsTerm, secondIsTerm), firstIsTerm))

      val body = applied(coding, List(eight, applied(pairing, List(inner, core))))
      val bodyIsFormula = force(
        rules
          .specAll(formulaOfUniversal, List(inner, core))
          .flatMap(rules.mp(_, coreIsFormula)))

      // First: `v0` becomes `t`, under the binder for `v1`. It occurs three times on the two
      // sides, which is the only difference from addition's walk and is why the right side
      // descends through a sum AND a product.
      val coreAtT = acrossEquality(
        outer, t, leftSide, rightSide,
        acrossProd(
          outer, t, first, objSucc(second),
          filled(outer, t), acrossSuccessor(outer, t, second, missed(outer, t, inner))),
        acrossSum(
          outer, t, objProd(first, second), first,
          acrossProd(outer, t, first, second, filled(outer, t), missed(outer, t, inner)),
          filled(outer, t)))
      val underBinder = acrossUniversal(outer, t, inner, core, coreAtT)

      val once = axiomAt(
        "NUM_PA_MUL_SUC", outer, t, body, bodyIsFormula, termT, closedT, underBinder)

      // Second: `v1` becomes `u`, and every occurrence of `t` has to come back untouched.
      val leftAtT = objProd(t, objSucc(second))
      val rightAtT = objSum(objProd(t, second), t)
      val coreAtTIsFormula = equalityOf(
        leftAtT, rightAtT,
        prodOf(t, objSucc(second), termT, succOf(second, secondIsTerm)),
        sumOf(objProd(t, second), t, prodOf(t, second, termT, secondIsTerm), termT))

      val stays = idle(inner, u, t, termT, closedT)
      val coreAtU = acrossEquality(
        inner, u, leftAtT, rightAtT,
        acrossProd(
          inner, u, t, objSucc(second),
          stays, acrossSuccessor(inner, u, second, filled(inner, u))),
        acrossSum(
          inner, u, objProd(t, second), t,
          acrossProd(inner, u, t, second, stays, filled(inner, u)),
          stays))

      val reached = atClosedTerm(
        once, inner, u, objEq(leftAtT, rightAtT), coreAtTIsFormula, termU, closedU, coreAtU)

      force(
        rules
          .disch(isClosed(u), reached)
          .flatMap(rules.disch(isTerm(u), _))
          .flatMap(rules.disch(isClosed(t), _))
          .flatMap(rules.disch(isTerm(t), _))
          .flatMap(rules.genAll(_, List(t, u))))
    }

    /** [[NumeralAddition]]. Induction on `n`, whose two cases are the object theory's two axioms. */
    lazy val numeralAddition: Kernel.Thm = {
      val peanoTheory = language.numbering.peano
      val driver = Induct.overNaturals(
        logic, force(peanoTheory.naturals.fact(Natural.Induction)))

      val numeralConstant = constant(Language.NumeralName, Type.fun(numbers, numbers))
      def numeral(x: Term): Term = applied(numeralConstant, List(x))
      def numeralIsATerm(x: Term): Kernel.Thm =
        force(rules.spec(x, force(language.fact(Language.NumeralIsTerm))))
      def numeralIsAClosed(x: Term): Kernel.Thm =
        force(rules.spec(x, force(language.fact(Language.NumeralIsClosed))))

      def sumIsATerm(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules.specAll(sumIsTerm, List(a, b)).flatMap(rules.mp(_, left)).flatMap(rules.mp(_, right)))
      def sumIsAClosed(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .specAll(force(language.fact(Language.ClosedSum)), List(a, b))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right)))
      def succIsATerm(a: Term, inner: Kernel.Thm): Kernel.Thm =
        force(rules.spec(a, successorIsTerm).flatMap(rules.mp(_, inner)))
      def succIsAClosed(a: Term, inner: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .spec(a, force(language.fact(Language.ClosedSuccessor)))
            .flatMap(rules.mp(_, inner)))

      /** Carry a theorem about `NUM_PROV` backwards along an equation between codes. */
      def backwards(equation: Kernel.Thm, proved: Kernel.Thm): Kernel.Thm =
        force(
          Conv
            .sym(equation)
            .flatMap(reversed => Conv.apTerm(provableConstant, reversed))
            .flatMap(reversed => LogicError.lift(Kernel.eqMp(reversed, proved))))

      val statement = force(
        Parser.proposition(theory, notation, Statements.toMap.apply(NumeralAddition)))

      force(driver.proveBy(
        statement,
        goal => {
          // `m` is the quantifier the driver left free. It is read off the goal's free variables
          // rather than by taking the term apart, because a numeral is itself an application and
          // a pattern that walks the code has to know the shape of `5` as well as of the sum.
          val subject: Term = Term.freeVariables(goal).toList match {
            case one :: Nil => one
            case other => throw new RefusedHere(
              NotOfForm("a claim about one free number", goal))
          }
          val atZero = force(
            rules
              .specAll(checked(AdditionAtZero, additionAtZero), List(numeral(subject)))
              .flatMap(rules.mp(_, numeralIsATerm(subject)))
              .flatMap(rules.mp(_, numeralIsAClosed(subject))))

          val zeroIsNumeral = force(language.fact(Language.NumeralAtZero))
          val summandMoves = pairCongruence(
            three, Conv.refl(numeral(subject)), zeroIsNumeral)
          val answerMoves = force(
            Conv.apTerm(
              numeralConstant,
              force(rules.spec(subject, force(peanoTheory.fact(Peano.AddAtZero))))))
          val bridge = pairCongruence(five, summandMoves, answerMoves)
          Right(backwards(bridge, atZero))
        },
        step => {
          val k = step.variable
          val subject: Term = (Term.freeVariables(step.goal) - k).toList match {
            case one :: Nil => one
            case other => throw new RefusedHere(
              NotOfForm("a claim about one free number beside the induction variable", step.goal))
          }
          val sumOfNumerals = objSum(numeral(subject), numeral(k))
          val total = numeral(applied(
            constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers))),
            List(subject, k)))

          // `numeral m + S (numeral k)` is provably `S (numeral m + numeral k)`.
          val axiom = force(
            rules
              .specAll(
                checked(AdditionAtSuccessor, additionAtSuccessor),
                List(numeral(subject), numeral(k)))
              .flatMap(rules.mp(_, numeralIsATerm(subject)))
              .flatMap(rules.mp(_, numeralIsAClosed(subject)))
              .flatMap(rules.mp(_, numeralIsATerm(k)))
              .flatMap(rules.mp(_, numeralIsAClosed(k))))

          // The hypothesis, with a successor around both sides.
          val lifted = force(
            rules
              .specAll(
                checked(SuccessorCongruence, successorCongruence), List(sumOfNumerals, total))
              .flatMap(rules.mp(_, sumIsATerm(
                numeral(subject), numeral(k),
                numeralIsATerm(subject), numeralIsATerm(k))))
              .flatMap(rules.mp(_, numeralIsATerm(applied(
                constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers))),
                List(subject, k)))))
              .flatMap(rules.mp(_, sumIsAClosed(
                numeral(subject), numeral(k),
                numeralIsAClosed(subject), numeralIsAClosed(k))))
              .flatMap(rules.mp(_, numeralIsAClosed(applied(
                constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers))),
                List(subject, k)))))
              .flatMap(rules.mp(_, step.hypothesis)))

          val chained = force(
            rules
              .specAll(
                checked(Transitivity, transitivity),
                List(objSum(numeral(subject), objSucc(numeral(k))),
                  objSucc(sumOfNumerals), objSucc(total)))
              .flatMap(rules.mp(_, sumIsATerm(
                numeral(subject), objSucc(numeral(k)),
                numeralIsATerm(subject), succIsATerm(numeral(k), numeralIsATerm(k)))))
              .flatMap(rules.mp(_, succIsATerm(sumOfNumerals, sumIsATerm(
                numeral(subject), numeral(k), numeralIsATerm(subject), numeralIsATerm(k)))))
              .flatMap(rules.mp(_, succIsATerm(total, numeralIsATerm(applied(
                constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers))),
                List(subject, k))))))
              .flatMap(rules.mp(_, sumIsAClosed(
                numeral(subject), objSucc(numeral(k)),
                numeralIsAClosed(subject), succIsAClosed(numeral(k), numeralIsAClosed(k)))))
              .flatMap(rules.mp(_, succIsAClosed(sumOfNumerals, sumIsAClosed(
                numeral(subject), numeral(k), numeralIsAClosed(subject), numeralIsAClosed(k)))))
              .flatMap(rules.mp(_, succIsAClosed(total, numeralIsAClosed(applied(
                constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers))),
                List(subject, k))))))
              .flatMap(rules.mp(_, axiom))
              .flatMap(rules.mp(_, lifted)))

          // What the numerals of `SUC k` and of `m + SUC k` are, so the goal is the code above.
          val numeralOfSuccessor = force(
            rules.spec(k, force(language.fact(Language.NumeralAtSuccessor))))
          val totalMoves = force(
            Conv
              .apTerm(
                numeralConstant,
                force(rules.specAll(force(peanoTheory.fact(Peano.AddAtSuccessor)), List(subject, k))))
              .flatMap(equation =>
                Conv.trans(
                  equation,
                  force(rules.spec(
                    applied(
                      constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers))),
                      List(subject, k)),
                    force(language.fact(Language.NumeralAtSuccessor)))))))
          val bridge = pairCongruence(
            five,
            pairCongruence(three, Conv.refl(numeral(subject)), numeralOfSuccessor),
            totalMoves)
          Right(backwards(bridge, chained))
        }
      ))
    }

    /**
     * [[NumeralMultiplication]]. The same induction, and the step goes through a sum.
     *
     * Addition's step needed the hypothesis under a successor; this one needs it under the left
     * summand of a sum whose right summand does not change, which is [[sumCongruence]], and then
     * what stands there is `numeral (m * k) + numeral m` — a sum of two numerals, which is exactly
     * the statement [[numeralAddition]] settles. The two bricks are in the order they are because
     * the second cannot be laid without the first.
     */
    lazy val numeralMultiplication: Kernel.Thm = {
      val peanoTheory = language.numbering.peano
      val driver = Induct.overNaturals(
        logic, force(peanoTheory.naturals.fact(Natural.Induction)))

      val numeralConstant = constant(Language.NumeralName, Type.fun(numbers, numbers))
      val addition = constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      val multiplication =
        constant(Peano.Multiplication, Type.fun(numbers, Type.fun(numbers, numbers)))

      def numeral(x: Term): Term = applied(numeralConstant, List(x))
      def numeralIsATerm(x: Term): Kernel.Thm =
        force(rules.spec(x, force(language.fact(Language.NumeralIsTerm))))
      def numeralIsAClosed(x: Term): Kernel.Thm =
        force(rules.spec(x, force(language.fact(Language.NumeralIsClosed))))

      def sumIsATerm(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules.specAll(sumIsTerm, List(a, b)).flatMap(rules.mp(_, left)).flatMap(rules.mp(_, right)))
      def sumIsAClosed(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .specAll(force(language.fact(Language.ClosedSum)), List(a, b))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right)))
      def prodIsATerm(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .specAll(productIsTerm, List(a, b))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right)))
      def prodIsAClosed(a: Term, b: Term, left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .specAll(force(language.fact(Language.ClosedProduct)), List(a, b))
            .flatMap(rules.mp(_, left))
            .flatMap(rules.mp(_, right)))
      def succIsATerm(a: Term, inner: Kernel.Thm): Kernel.Thm =
        force(rules.spec(a, successorIsTerm).flatMap(rules.mp(_, inner)))
      def succIsAClosed(a: Term, inner: Kernel.Thm): Kernel.Thm =
        force(
          rules
            .spec(a, force(language.fact(Language.ClosedSuccessor)))
            .flatMap(rules.mp(_, inner)))

      def backwards(equation: Kernel.Thm, proved: Kernel.Thm): Kernel.Thm =
        force(
          Conv
            .sym(equation)
            .flatMap(reversed => Conv.apTerm(provableConstant, reversed))
            .flatMap(reversed => LogicError.lift(Kernel.eqMp(reversed, proved))))

      val statement = force(
        Parser.proposition(theory, notation, Statements.toMap.apply(NumeralMultiplication)))

      force(driver.proveBy(
        statement,
        goal => {
          val subject: Term = Term.freeVariables(goal).toList match {
            case one :: Nil => one
            case other => throw new RefusedHere(
              NotOfForm("a claim about one free number", goal))
          }

          // `numeral m * 0 = 0` from the axiom, and the goal wants `numeral (m * 0)`, which is
          // `numeral 0`, which is the object language's zero.
          val atZero = force(
            rules
              .specAll(checked(MultiplicationAtZero, multiplicationAtZero), List(numeral(subject)))
              .flatMap(rules.mp(_, numeralIsATerm(subject)))
              .flatMap(rules.mp(_, numeralIsAClosed(subject))))

          val zeroIsNumeral = force(language.fact(Language.NumeralAtZero))
          val factorMoves = pairCongruence(four, Conv.refl(numeral(subject)), zeroIsNumeral)
          val answerMoves = force(
            Conv
              .apTerm(
                numeralConstant,
                force(rules.spec(subject, force(peanoTheory.fact(Peano.MulAtZero)))))
              .flatMap(equation => Conv.trans(equation, zeroIsNumeral)))
          val bridge = pairCongruence(five, factorMoves, answerMoves)
          Right(backwards(bridge, atZero))
        },
        step => {
          val k = step.variable
          val subject: Term = (Term.freeVariables(step.goal) - k).toList match {
            case one :: Nil => one
            case other => throw new RefusedHere(
              NotOfForm("a claim about one free number beside the induction variable", step.goal))
          }

          val productOfNumerals = objProd(numeral(subject), numeral(k))
          val partial = numeral(applied(multiplication, List(subject, k)))

          // `numeral m * S (numeral k)` is provably `numeral m * numeral k + numeral m`.
          val axiomStep = force(
            rules
              .specAll(
                checked(MultiplicationAtSuccessor, multiplicationAtSuccessor),
                List(numeral(subject), numeral(k)))
              .flatMap(rules.mp(_, numeralIsATerm(subject)))
              .flatMap(rules.mp(_, numeralIsAClosed(subject)))
              .flatMap(rules.mp(_, numeralIsATerm(k)))
              .flatMap(rules.mp(_, numeralIsAClosed(k))))

          // The hypothesis carried into the left summand, the right one being `numeral m` itself.
          val lifted = force(
            rules
              .specAll(
                checked(SumCongruence, sumCongruence),
                List(productOfNumerals, partial, numeral(subject)))
              .flatMap(rules.mp(_, prodIsATerm(
                numeral(subject), numeral(k), numeralIsATerm(subject), numeralIsATerm(k))))
              .flatMap(rules.mp(_, prodIsAClosed(
                numeral(subject), numeral(k), numeralIsAClosed(subject), numeralIsAClosed(k))))
              .flatMap(rules.mp(_, numeralIsATerm(applied(multiplication, List(subject, k)))))
              .flatMap(rules.mp(_, numeralIsAClosed(applied(multiplication, List(subject, k)))))
              .flatMap(rules.mp(_, numeralIsATerm(subject)))
              .flatMap(rules.mp(_, numeralIsAClosed(subject)))
              .flatMap(rules.mp(_, step.hypothesis)))

          // And the sum of two numerals is the numeral of the sum, which is the first brick.
          val summed = force(
            rules
              .specAll(
                checked(NumeralAddition, numeralAddition),
                List(applied(multiplication, List(subject, k)), subject)))

          // **Transitivity asks for six side conditions before its two premises**, which is what
          // the first run of this induction walked into: the specialisation was handed the two
          // proofs straight away and the kernel reported the antecedent it actually wanted. Each
          // of the three terms in a chain owes a `NUM_TERM` and a `NUM_CLOSED`.
          final case class Closed(term: Term, isTerm: Kernel.Thm, isClosedThm: Kernel.Thm)

          def chain(left: Closed, middle: Closed, right: Closed, first: Kernel.Thm, second: Kernel.Thm)
            : Kernel.Thm =
            force(
              rules
                .specAll(
                  checked(Transitivity, transitivity),
                  List(left.term, middle.term, right.term))
                .flatMap(rules.mp(_, left.isTerm))
                .flatMap(rules.mp(_, middle.isTerm))
                .flatMap(rules.mp(_, right.isTerm))
                .flatMap(rules.mp(_, left.isClosedThm))
                .flatMap(rules.mp(_, middle.isClosedThm))
                .flatMap(rules.mp(_, right.isClosedThm))
                .flatMap(rules.mp(_, first))
                .flatMap(rules.mp(_, second)))

          val product = applied(multiplication, List(subject, k))
          val sumOfPartials = objSum(productOfNumerals, numeral(subject))
          val sumOfNumerals = objSum(partial, numeral(subject))
          val total = numeral(applied(addition, List(product, subject)))

          val start = Closed(
            objProd(numeral(subject), objSucc(numeral(k))),
            prodIsATerm(
              numeral(subject), objSucc(numeral(k)),
              numeralIsATerm(subject), succIsATerm(numeral(k), numeralIsATerm(k))),
            prodIsAClosed(
              numeral(subject), objSucc(numeral(k)),
              numeralIsAClosed(subject), succIsAClosed(numeral(k), numeralIsAClosed(k))))

          val throughProduct = Closed(
            sumOfPartials,
            sumIsATerm(
              productOfNumerals, numeral(subject),
              prodIsATerm(numeral(subject), numeral(k), numeralIsATerm(subject), numeralIsATerm(k)),
              numeralIsATerm(subject)),
            sumIsAClosed(
              productOfNumerals, numeral(subject),
              prodIsAClosed(
                numeral(subject), numeral(k), numeralIsAClosed(subject), numeralIsAClosed(k)),
              numeralIsAClosed(subject)))

          val throughNumerals = Closed(
            sumOfNumerals,
            sumIsATerm(partial, numeral(subject), numeralIsATerm(product), numeralIsATerm(subject)),
            sumIsAClosed(
              partial, numeral(subject), numeralIsAClosed(product), numeralIsAClosed(subject)))

          val answer = Closed(
            total,
            numeralIsATerm(applied(addition, List(product, subject))),
            numeralIsAClosed(applied(addition, List(product, subject))))

          val toPartial = chain(start, throughProduct, throughNumerals, axiomStep, lifted)
          val chained = chain(start, throughNumerals, answer, toPartial, summed)

          // What the numerals of `SUC k` and of `m * SUC k` are, so the goal is the code above.
          val numeralOfSuccessor = force(
            rules.spec(k, force(language.fact(Language.NumeralAtSuccessor))))
          val totalMoves = force(
            Conv.apTerm(
              numeralConstant,
              force(rules.specAll(force(peanoTheory.fact(Peano.MulAtSuccessor)), List(subject, k)))))
          val bridge = pairCongruence(
            five,
            pairCongruence(four, Conv.refl(numeral(subject)), numeralOfSuccessor),
            totalMoves)
          Right(backwards(bridge, chained))
        }
      ))
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
