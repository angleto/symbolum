package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The reals as Dedekind cuts on the rationals: the type, its order, the rationals inside it, least
 * upper bounds as a theorem, and the arithmetic, which is what `Real` defines its constants over.
 *
 * == The route ==
 *
 * `docs/adr/0016` left two routes open and named the first the one to beat: cuts on the rationals,
 * with multiplication defined on the positive cone and extended by sign, against the positive
 * rationals first and a completion of that cone. What decided between them was whether the integers
 * and the rationals would arrive as a by-product; they have both arrived, `Fraction` is an ordered
 * field that is Archimedean and dense, so the first route costs nothing the second would have
 * saved. `docs/adr/0052` is the record.
 *
 * == What a cut is here ==
 *
 * A **lower** cut: a set of rationals that holds something, does not hold everything, is closed
 * downwards and has no greatest element. `IS_CUT` says those four things and the type is carved out
 * of `rat -> bool` by it; the witness is the cut of zero, and the fourth clause of it is `RAT_DENSE`,
 * which is what that fact was built for. The type is `real`: it was called `cut` until
 * `docs/adr/0053` made it the one type of real number, which `Real` defines its constants over.
 *
 * The order is inclusion, which is why three of its four laws are one line each and the fourth is
 * the one argument in the file: two cuts are comparable because if `x` is not inside `y` then some
 * `t` is in `x` and not in `y`, and every member of `y` is then below `t`, since otherwise the
 * closure of `y` would put `t` in it. That needs the excluded middle twice, and the laws of `rat`
 * need none, so `CUT_LE_TOTAL` is where this development's classical cost is spent.
 *
 * == The one fact worth the file ==
 *
 * `CUT_COMPLETE` is `COMPLETENESS`, the sixteenth of `Real.scala`, stated word for word over the
 * cuts and `CUT_LE`, and **proved**: the least upper bound of a non-empty bounded family of cuts is
 * the union of their members. It is the axiom that separates an ordered field from the reals, and
 * on this type it is not assumed.
 *
 * == The arithmetic ==
 *
 * Addition holds `r` when some `p` in `x` leaves `r - p` in `y`, and negation holds `p` when some
 * `r > 0` leaves `-p - r` outside `x`. The product is built in two layers. `CUT_PMUL` is the product
 * on the **non-negative** cone rather than the positive one, so that zero needs no case of its own:
 * the negatives, and every `r` below `p * q` for positive members. `CUT_MUL` then reads the signs with
 * `COND` and puts the sign back on the core of the absolute values, and every law off the cone comes
 * from the one on it through `(-x) * y = -(x * y)`, closed by a normaliser for the additive group.
 * `CUT_INV` is `CUT_PINV` above zero, its negation's negated below, and zero at zero, which the
 * definition writes. Both inverses spend `CUT_ESCAPE`, the one place the rationals being Archimedean
 * reaches the cuts. `Real` proves the statements of `Real.Axioms` from these, as theorems about this
 * type under their old names, which is `docs/adr/0053`.
 */
final class Cut private (
  val classical: Classical,
  val fractions: Fraction,
  val theory: Theory,
  val notation: Notation,
  /** The classical logic read against [[theory]], which is wider than the one `classical` holds. */
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** A definition of this development, or a refusal naming it. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A published fact of this development, or a refusal naming it. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** A proposition read against this development's signature. */
  def proposition(text: String): Either[LogicError, Term] =
    Parser.proposition(theory, notation, text)

  /** A term read against this development's signature. */
  def term(text: String, expected: Type): Either[LogicError, Term] =
    Parser.term(theory, notation, text, expected)

  /** A term as this development prints it. */
  def show(term: Term): String = Show.show(notation, term)
}

object Cut {

  /* ------------------------------------------------------------------ the names */

  /** The type operator, and the two halves of the bijection the kernel returns for it. */
  /**
   * `real`: since phase 5 (`docs/adr/0053`) the type the cuts are carved as **is** the type of the
   * real numbers, so there is one type of real and `Real` defines its constants over this one.
   */
  val TypeName: String = Real.TypeName
  val Abstraction: String = "mk_cut"
  val Representation: String = "dest_cut"

  /** `IS_CUT S`: `S` holds something, not everything, is closed downwards and has no greatest element. */
  val IsCut: String = "IS_CUT"

  /** `CUT_LE x y`: every member of `x` is a member of `y`. */
  val AtMost: String = "CUT_LE"

  /** `CUT_OF_RAT q`: the cut of the rationals below `q`. */
  val OfRational: String = "CUT_OF_RAT"

  /** `|- !x. IS_CUT (dest_cut x)`. */
  val Represents: String = "CUT_IS_CUT"

  /** `|- !S. IS_CUT S ==> dest_cut (mk_cut S) = S`. */
  val Rebuilds: String = "CUT_DEST_MK"

  /** `|- !q. IS_CUT (\p. RAT_LT p q)`: the rationals below one are a cut, which is where density is spent. */
  val BelowIsCut: String = "CUT_BELOW"

  val AtMostReflexive: String = "CUT_LE_REFL"
  val AtMostTransitive: String = "CUT_LE_TRANS"
  val AtMostAntisymmetric: String = "CUT_LE_ANTISYM"
  val AtMostTotal: String = "CUT_LE_TOTAL"

  /** `|- !q. dest_cut (CUT_OF_RAT q) = (\p. RAT_LT p q)`. */
  val OfRationalMembers: String = "CUT_OF_RAT_DEST"

  /** `|- !p q. CUT_LE (CUT_OF_RAT p) (CUT_OF_RAT q) = RAT_LE p q`. */
  val OfRationalOrder: String = "CUT_OF_RAT_LE"

  /** `|- !p q. CUT_OF_RAT p = CUT_OF_RAT q ==> p = q`. */
  val OfRationalInjective: String = "CUT_OF_RAT_INJ"

  /** `COMPLETENESS` over the cuts: a non-empty family with an upper bound has a least one. */
  val Complete: String = "CUT_COMPLETE"

  /** `CUT_ADD x y`: the rationals `r` with some `p` in `x` and `r - p` in `y`. */
  val Addition: String = "CUT_ADD"

  /** `|- !x y. IS_CUT (\r. ?p. dest_cut x p /\ dest_cut y (r + -p))`. */
  val AddIsCut: String = "CUT_ADD_IS_CUT"

  /** `|- !x y. dest_cut (CUT_ADD x y) = (\r. ?p. dest_cut x p /\ dest_cut y (r + -p))`. */
  val AddMembers: String = "CUT_ADD_DEST"

  val AddCommutative: String = "CUT_ADD_SYM"
  val AddAssociative: String = "CUT_ADD_ASSOC"

  /** `|- !x. CUT_ADD x (CUT_OF_RAT RAT_ZERO) = x`. */
  val AddZero: String = "CUT_ADD_ZERO"

  /** `|- !x y z. CUT_LE x y ==> CUT_LE (CUT_ADD x z) (CUT_ADD y z)`. */
  val AtMostAdd: String = "CUT_LE_ADD"

  /** `|- !p q. CUT_OF_RAT (RAT_ADD p q) = CUT_ADD (CUT_OF_RAT p) (CUT_OF_RAT q)`. */
  val OfRationalAdd: String = "CUT_OF_RAT_ADD"

  /** `CUT_NEG x`: the rationals `p` with some `r > 0` leaving `-p - r` outside `x`. */
  val Negation: String = "CUT_NEG"

  /** `|- !x. IS_CUT (\p. ?r. 0 < r /\ ~(dest_cut x (-p + -r)))`. */
  val NegIsCut: String = "CUT_NEG_IS_CUT"

  /** `|- !x. dest_cut (CUT_NEG x) = (\p. ?r. 0 < r /\ ~(dest_cut x (-p + -r)))`. */
  val NegMembers: String = "CUT_NEG_DEST"

  /** `|- !x. CUT_ADD x (CUT_NEG x) = CUT_OF_RAT RAT_ZERO`: the additive inverse, where Archimedes is spent. */
  val AddNegation: String = "CUT_ADD_NEG"

  /**
   * `|- !x e f. dest_cut x e ==> 0 < f ==> ?p. dest_cut x p /\ e <= p /\ ~(dest_cut x (p + f))`: a
   * member at least `e` whose step by `f` leaves the cut, which is where Archimedes is spent.
   */
  val Escape: String = "CUT_ESCAPE"

  /** `|- !x y. 0 <= x ==> 0 <= y ==> 0 <= CUT_ADD x y`. */
  val AddNonNegative: String = "CUT_ADD_NONNEG"

  /**
   * `CUT_PMUL x y`: the product on the non-negative cone, the negative rationals together with every
   * `r` below `p * q` for positive members `p` of `x` and `q` of `y`. A cut whenever both are at least
   * zero, including zero itself, which is why the cone is the non-negative one and not the positive.
   */
  val PosMul: String = "CUT_PMUL"

  val PosMulIsCut: String = "CUT_PMUL_IS_CUT"
  val PosMulMembers: String = "CUT_PMUL_DEST"
  val PosMulCommutative: String = "CUT_PMUL_SYM"
  val PosMulZero: String = "CUT_PMUL_ZERO"
  val PosMulNonNegative: String = "CUT_PMUL_NONNEG"
  val PosMulOne: String = "CUT_PMUL_ONE"
  val PosMulAssociative: String = "CUT_PMUL_ASSOC"
  val PosMulDistributive: String = "CUT_PMUL_ADD"

  /** `|- !x. CUT_NEG (CUT_NEG x) = x`, and the two below: the additive group, derived from its four laws. */
  val NegNeg: String = "CUT_NEG_NEG"
  val NegZero: String = "CUT_NEG_ZERO"
  val NegAdd: String = "CUT_NEG_ADD"

  /** `|- !x y. CUT_LE x y ==> CUT_LE (CUT_NEG y) (CUT_NEG x)`. */
  val AtMostNeg: String = "CUT_LE_NEG"

  /** `|- !x. CUT_LE 0 x \/ CUT_LE 0 (CUT_NEG x)`: every cut has a sign, zero having both. */
  val SignCases: String = "CUT_SIGN_CASES"

  /**
   * `CUT_MUL x y`: the product, the core on the signs' absolute values with the sign put back. Written
   * with `COND` on `CUT_LE 0 x` and `CUT_LE 0 y`, so that at a non-negative pair it is the core.
   */
  val Multiplication: String = "CUT_MUL"

  /** `|- !x y. 0 <= x ==> 0 <= y ==> CUT_MUL x y = CUT_PMUL x y`. */
  val MulOnCone: String = "CUT_MUL_PMUL"

  val MulCommutative: String = "CUT_MUL_SYM"
  val MulOne: String = "CUT_MUL_ONE"
  val MulZero: String = "CUT_MUL_ZERO"

  /** `|- !x y. CUT_MUL (CUT_NEG x) y = CUT_NEG (CUT_MUL x y)`: what carries every law off the cone. */
  val MulNegLeft: String = "CUT_MUL_NEG_LEFT"

  val MulAssociative: String = "CUT_MUL_ASSOC"

  /** `|- !x y z. CUT_MUL x (CUT_ADD y z) = CUT_ADD (CUT_MUL x y) (CUT_MUL x z)`. */
  val MulDistributive: String = "CUT_MUL_ADD"

  /** `CUT_LT x y`, defined as `~(CUT_LE y x)`: the strict order, which on a total order is that. */
  val LessThan: String = "CUT_LT"

  /** `|- !x y. 0 < x ==> 0 < y ==> 0 < CUT_PMUL x y`: a positive member of each puts zero in the core. */
  val PosMulPositive: String = "CUT_PMUL_POSITIVE"

  /** `|- !x y. CUT_LT 0 x /\ CUT_LT 0 y ==> CUT_LT 0 (CUT_MUL x y)`: `LT_MUL` of `Real.scala`, over cuts. */
  val LessMul: String = "CUT_LT_MUL"

  /**
   * `CUT_PINV x`: the inverse of a positive cut, the non-positive rationals together with every `r`
   * that some positive non-member `s` of `x` keeps below `1 / s`.
   */
  val PosInverse: String = "CUT_PINV"
  val PosInverseIsCut: String = "CUT_PINV_IS_CUT"
  val PosInverseMembers: String = "CUT_PINV_DEST"
  val PosInverseNonNegative: String = "CUT_PINV_NONNEG"

  /** `|- !x. 0 < x ==> CUT_PMUL x (CUT_PINV x) = CUT_OF_RAT RAT_ONE`. */
  val PosMulInverse: String = "CUT_PMUL_PINV"

  /** `CUT_INV x`: `CUT_PINV x` above zero, its negation's negated below, and zero at zero, which the definition writes. */
  val Inverse: String = "CUT_INV"

  /** `|- CUT_INV (CUT_OF_RAT RAT_ZERO) = CUT_OF_RAT RAT_ZERO`. */
  val InverseZero: String = "CUT_INV_ZERO"

  /** `|- !x. ~(x = 0) ==> CUT_MUL x (CUT_INV x) = CUT_OF_RAT RAT_ONE`: `MUL_INVERSE` of `Real.scala`, over cuts. */
  val MulInverse: String = "CUT_MUL_INV"

  private val IsCutBody: String =
    "\\S:rat->bool. (?a:rat. S a) /\\ (?b:rat. ~(S b)) /\\ " +
      "(!a:rat. !b:rat. S b /\\ RAT_LT a b ==> S a) /\\ (!a:rat. S a ==> (?b:rat. S b /\\ RAT_LT a b))"
  private val AtMostBody: String = "\\x:real. \\y:real. !q:rat. dest_cut x q ==> dest_cut y q"
  private val OfRationalBody: String = "\\q:rat. mk_cut (\\p:rat. RAT_LT p q)"
  private val SumSetText: String = "\\r:rat. ?p:rat. dest_cut x p /\\ dest_cut y (RAT_ADD r (RAT_NEG p))"
  private val AdditionBody: String = "\\x:real. \\y:real. mk_cut (" + SumSetText + ")"
  private val NegSetText: String =
    "\\p:rat. ?r:rat. RAT_LT RAT_ZERO r /\\ ~(dest_cut x (RAT_ADD (RAT_NEG p) (RAT_NEG r)))"
  private val NegationBody: String = "\\x:real. mk_cut (" + NegSetText + ")"
  private val CoreMemberText: String =
    "RAT_LT r RAT_ZERO \\/ (?p:rat. ?q:rat. dest_cut x p /\\ dest_cut y q /\\ " +
      "RAT_LT RAT_ZERO p /\\ RAT_LT RAT_ZERO q /\\ RAT_LT r (RAT_MUL p q))"
  private val CoreSetText: String = "\\r:rat. " + CoreMemberText
  private val PosMulBody: String = "\\x:real. \\y:real. mk_cut (" + CoreSetText + ")"
  private val NonNegativeX: String = "CUT_LE (CUT_OF_RAT RAT_ZERO) x"
  private val NonNegativeY: String = "CUT_LE (CUT_OF_RAT RAT_ZERO) y"
  private val NonNegativeZ: String = "CUT_LE (CUT_OF_RAT RAT_ZERO) z"
  private val LessThanBody: String = "\\x:real. \\y:real. ~(CUT_LE y x)"
  private val PinvMemberText: String =
    "RAT_LE r RAT_ZERO \\/ (?s:rat. ~(dest_cut x s) /\\ RAT_LT RAT_ZERO s /\\ RAT_LT (RAT_MUL r s) RAT_ONE)"
  private val PinvSetText: String = "\\r:rat. " + PinvMemberText
  private val PosInverseBody: String = "\\x:real. mk_cut (" + PinvSetText + ")"
  private val InverseBody: String =
    "\\x:real. COND (CUT_LT (CUT_OF_RAT RAT_ZERO) x) (CUT_PINV x) " +
      "(COND (CUT_LT x (CUT_OF_RAT RAT_ZERO)) (CUT_NEG (CUT_PINV (CUT_NEG x))) (CUT_OF_RAT RAT_ZERO))"
  private val PositiveX: String = "CUT_LT (CUT_OF_RAT RAT_ZERO) x"
  private val PositiveY: String = "CUT_LT (CUT_OF_RAT RAT_ZERO) y"
  private val MultiplicationBody: String =
    "\\x:real. \\y:real. COND (CUT_LE (CUT_OF_RAT RAT_ZERO) x) " +
      "(COND (CUT_LE (CUT_OF_RAT RAT_ZERO) y) (CUT_PMUL x y) (CUT_NEG (CUT_PMUL x (CUT_NEG y)))) " +
      "(COND (CUT_LE (CUT_OF_RAT RAT_ZERO) y) (CUT_NEG (CUT_PMUL (CUT_NEG x) y)) (CUT_PMUL (CUT_NEG x) (CUT_NEG y)))"

  /** Each fact with the text it is published as, which the construction compares against. */
  val Statements: Vector[(String, String)] = Vector(
    BelowIsCut -> "!q:rat. IS_CUT (\\p:rat. RAT_LT p q)",
    Represents -> "!x:real. IS_CUT (dest_cut x)",
    Rebuilds -> "!S:rat->bool. IS_CUT S ==> dest_cut (mk_cut S) = S",
    AtMostReflexive -> "!x:real. CUT_LE x x",
    AtMostTransitive -> "!x:real. !y:real. !z:real. CUT_LE x y ==> CUT_LE y z ==> CUT_LE x z",
    AtMostAntisymmetric -> "!x:real. !y:real. CUT_LE x y ==> CUT_LE y x ==> x = y",
    AtMostTotal -> "!x:real. !y:real. CUT_LE x y \\/ CUT_LE y x",
    OfRationalMembers -> "!q:rat. dest_cut (CUT_OF_RAT q) = (\\p:rat. RAT_LT p q)",
    OfRationalOrder -> "!p:rat. !q:rat. CUT_LE (CUT_OF_RAT p) (CUT_OF_RAT q) = RAT_LE p q",
    OfRationalInjective -> "!p:rat. !q:rat. CUT_OF_RAT p = CUT_OF_RAT q ==> p = q",
    Complete ->
      ("!P:real->bool. (?x:real. P x) /\\ (?b:real. !x:real. P x ==> CUT_LE x b) ==> " +
        "(?s:real. (!x:real. P x ==> CUT_LE x s) /\\ (!b:real. (!x:real. P x ==> CUT_LE x b) ==> CUT_LE s b))"),
    AddIsCut -> ("!x:real. !y:real. IS_CUT (" + SumSetText + ")"),
    AddMembers -> ("!x:real. !y:real. dest_cut (CUT_ADD x y) = (" + SumSetText + ")"),
    AddCommutative -> "!x:real. !y:real. CUT_ADD x y = CUT_ADD y x",
    AddAssociative -> "!x:real. !y:real. !z:real. CUT_ADD (CUT_ADD x y) z = CUT_ADD x (CUT_ADD y z)",
    AddZero -> "!x:real. CUT_ADD x (CUT_OF_RAT RAT_ZERO) = x",
    AtMostAdd -> "!x:real. !y:real. !z:real. CUT_LE x y ==> CUT_LE (CUT_ADD x z) (CUT_ADD y z)",
    OfRationalAdd -> "!p:rat. !q:rat. CUT_OF_RAT (RAT_ADD p q) = CUT_ADD (CUT_OF_RAT p) (CUT_OF_RAT q)",
    NegIsCut -> ("!x:real. IS_CUT (" + NegSetText + ")"),
    NegMembers -> ("!x:real. dest_cut (CUT_NEG x) = (" + NegSetText + ")"),
    AddNegation -> "!x:real. CUT_ADD x (CUT_NEG x) = CUT_OF_RAT RAT_ZERO",
    Escape ->
      ("!x:real. !e:rat. !f:rat. dest_cut x e ==> RAT_LT RAT_ZERO f ==> " +
        "(?p:rat. dest_cut x p /\\ RAT_LE e p /\\ ~(dest_cut x (RAT_ADD p f)))"),
    AddNonNegative -> ("!x:real. !y:real. " + NonNegativeX + " ==> " + NonNegativeY + " ==> CUT_LE (CUT_OF_RAT RAT_ZERO) (CUT_ADD x y)"),
    PosMulIsCut -> ("!x:real. !y:real. " + NonNegativeX + " ==> " + NonNegativeY + " ==> IS_CUT (" + CoreSetText + ")"),
    PosMulMembers ->
      ("!x:real. !y:real. " + NonNegativeX + " ==> " + NonNegativeY + " ==> dest_cut (CUT_PMUL x y) = (" + CoreSetText + ")"),
    PosMulCommutative -> "!x:real. !y:real. CUT_PMUL x y = CUT_PMUL y x",
    PosMulZero -> "!x:real. CUT_PMUL x (CUT_OF_RAT RAT_ZERO) = CUT_OF_RAT RAT_ZERO",
    PosMulNonNegative ->
      ("!x:real. !y:real. " + NonNegativeX + " ==> " + NonNegativeY + " ==> CUT_LE (CUT_OF_RAT RAT_ZERO) (CUT_PMUL x y)"),
    PosMulOne -> ("!x:real. " + NonNegativeX + " ==> CUT_PMUL x (CUT_OF_RAT RAT_ONE) = x"),
    PosMulAssociative ->
      ("!x:real. !y:real. !z:real. " + NonNegativeX + " ==> " + NonNegativeY + " ==> " + NonNegativeZ +
        " ==> CUT_PMUL (CUT_PMUL x y) z = CUT_PMUL x (CUT_PMUL y z)"),
    PosMulDistributive ->
      ("!x:real. !y:real. !z:real. " + NonNegativeX + " ==> " + NonNegativeY + " ==> " + NonNegativeZ +
        " ==> CUT_PMUL x (CUT_ADD y z) = CUT_ADD (CUT_PMUL x y) (CUT_PMUL x z)"),
    NegNeg -> "!x:real. CUT_NEG (CUT_NEG x) = x",
    NegZero -> "CUT_NEG (CUT_OF_RAT RAT_ZERO) = CUT_OF_RAT RAT_ZERO",
    NegAdd -> "!x:real. !y:real. CUT_NEG (CUT_ADD x y) = CUT_ADD (CUT_NEG x) (CUT_NEG y)",
    AtMostNeg -> "!x:real. !y:real. CUT_LE x y ==> CUT_LE (CUT_NEG y) (CUT_NEG x)",
    SignCases -> ("!x:real. " + NonNegativeX + " \\/ CUT_LE (CUT_OF_RAT RAT_ZERO) (CUT_NEG x)"),
    MulOnCone -> ("!x:real. !y:real. " + NonNegativeX + " ==> " + NonNegativeY + " ==> CUT_MUL x y = CUT_PMUL x y"),
    MulCommutative -> "!x:real. !y:real. CUT_MUL x y = CUT_MUL y x",
    MulOne -> "!x:real. CUT_MUL x (CUT_OF_RAT RAT_ONE) = x",
    MulZero -> "!x:real. CUT_MUL x (CUT_OF_RAT RAT_ZERO) = CUT_OF_RAT RAT_ZERO",
    MulNegLeft -> "!x:real. !y:real. CUT_MUL (CUT_NEG x) y = CUT_NEG (CUT_MUL x y)",
    MulAssociative -> "!x:real. !y:real. !z:real. CUT_MUL (CUT_MUL x y) z = CUT_MUL x (CUT_MUL y z)",
    MulDistributive -> "!x:real. !y:real. !z:real. CUT_MUL x (CUT_ADD y z) = CUT_ADD (CUT_MUL x y) (CUT_MUL x z)",
    PosMulPositive -> ("!x:real. !y:real. " + PositiveX + " ==> " + PositiveY + " ==> CUT_LT (CUT_OF_RAT RAT_ZERO) (CUT_PMUL x y)"),
    LessMul -> ("!x:real. !y:real. " + PositiveX + " /\\ " + PositiveY + " ==> CUT_LT (CUT_OF_RAT RAT_ZERO) (CUT_MUL x y)"),
    PosInverseIsCut -> ("!x:real. " + PositiveX + " ==> IS_CUT (" + PinvSetText + ")"),
    PosInverseMembers -> ("!x:real. " + PositiveX + " ==> dest_cut (CUT_PINV x) = (" + PinvSetText + ")"),
    PosInverseNonNegative -> ("!x:real. " + PositiveX + " ==> CUT_LE (CUT_OF_RAT RAT_ZERO) (CUT_PINV x)"),
    PosMulInverse -> ("!x:real. " + PositiveX + " ==> CUT_PMUL x (CUT_PINV x) = CUT_OF_RAT RAT_ONE"),
    InverseZero -> "CUT_INV (CUT_OF_RAT RAT_ZERO) = CUT_OF_RAT RAT_ZERO",
    MulInverse -> "!x:real. ~(x = CUT_OF_RAT RAT_ZERO) ==> CUT_MUL x (CUT_INV x) = CUT_OF_RAT RAT_ONE"
  )

  private def statementOf(name: String): String =
    Statements.collectFirst { case (`name`, text) => text }.getOrElse(name)

  val Classes: Type = TyApp(TypeName, Nil)

  /* ------------------------------------------------------------------ the construction */

  def construct(fractions: Fraction, peano: NaturalArithmetic): Either[LogicError, Cut] = {
    val classical = fractions.classical
    val notation = fractions.notation

    def define(theory: Theory, name: String, text: String): Either[LogicError, (Theory, Kernel.Thm)] =
      for {
        body <- Parser.term(theory, notation, text)
        defined <- LogicError.lift(Kernel.defineConstant(theory, name, body))
      } yield defined

    for {
      ring <- fractions.ring
      isCut <- define(fractions.theory, IsCut, IsCutBody)
      (withIsCut, isCutDefinition) = isCut
      narrow <- classical.logic.over(withIsCut)
      rationals = Rationals(narrow, withIsCut, notation, classical, fractions, ring)
      below <- Sets(rationals, isCutDefinition).belowIsCut
      atZero <- Parser.term(withIsCut, notation, "RAT_ZERO", Fraction.Classes).flatMap(narrow.rules.spec(_, below))

      typed <- LogicError.lift(Kernel.defineType(withIsCut, TypeName, Abstraction, Representation, atZero))
      (withType, bijection) = typed
      atMost <- define(withType, AtMost, AtMostBody)
      (withAtMost, atMostDefinition) = atMost
      ofRational <- define(withAtMost, OfRational, OfRationalBody)
      (withOfRational, ofRationalDefinition) = ofRational
      lessThan <- define(withOfRational, LessThan, LessThanBody)
      (withLessThan, lessThanDefinition) = lessThan
      addition <- define(withLessThan, Addition, AdditionBody)
      (withAddition, additionDefinition) = addition
      negation <- define(withAddition, Negation, NegationBody)
      (withNegation, negationDefinition) = negation
      posMul <- define(withNegation, PosMul, PosMulBody)
      (withPosMul, posMulDefinition) = posMul
      multiplication <- define(withPosMul, Multiplication, MultiplicationBody)
      (withMultiplication, multiplicationDefinition) = multiplication
      posInverse <- define(withMultiplication, PosInverse, PosInverseBody)
      (withPosInverse, posInverseDefinition) = posInverse
      inverse <- define(withPosInverse, Inverse, InverseBody)
      (complete, inverseDefinition) = inverse
      induction <- peano.naturals.fact(Natural.Induction)

      wider <- classical.logic.over(complete)
      widerRationals = Rationals(wider, complete, notation, classical, fractions, ring)
      sets = Sets(widerRationals, isCutDefinition)
      proved <- Cuts(
        sets, bijection, atMostDefinition, ofRationalDefinition, additionDefinition, negationDefinition,
        posMulDefinition, multiplicationDefinition, lessThanDefinition, posInverseDefinition, inverseDefinition, induction
      )
        .facts(below)

      checked <- proved.foldRight[Either[LogicError, Vector[(String, Kernel.Thm)]]](Right(Vector.empty)) {
        case ((name, theorem), rest) =>
          for {
            statement <- Parser.proposition(complete, notation, statementOf(name))
            _ <-
              if (theorem.conclusion == statement) Right(())
              else Left(NotOfForm(s"the statement published for $name", theorem.conclusion))
            _ <-
              if (theorem.hypotheses.isEmpty) Right(())
              else Left(NotOfForm(s"$name with nothing assumed", theorem.conclusion))
            more <- rest
          } yield (name, theorem) +: more
      }
    } yield new Cut(
      classical,
      fractions,
      complete,
      notation,
      wider,
      Map(
        IsCut -> isCutDefinition,
        AtMost -> atMostDefinition,
        OfRational -> ofRationalDefinition,
        Addition -> additionDefinition,
        Negation -> negationDefinition,
        PosMul -> posMulDefinition,
        Multiplication -> multiplicationDefinition,
        LessThan -> lessThanDefinition,
        PosInverse -> posInverseDefinition,
        Inverse -> inverseDefinition
      ),
      checked.toMap
    )
  }

  /* ------------------------------------------------------------------ the rationals' order */

  /**
   * The facts about `RAT_LT` a cut needs and `Fraction` does not publish: its transitivity with the
   * non-strict order on either side, its irreflexivity, that its failure is the other order, and a
   * rational below every rational. All but the third are negations proved by refutation; the third is
   * the one classical step, a double negation, because `~(RAT_LT p q)` is `~~(RAT_LE q p)`.
   */
  private final case class Rationals(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    classical: Classical,
    fractions: Fraction,
    ring: CommutativeRing
  ) {
    val rules = logic.rules

    def lift[T](result: Either[KernelError, T]): Either[LogicError, T] = LogicError.lift(result)
    def read(text: String, expected: Type): Either[LogicError, Term] = Parser.term(theory, notation, text, expected)
    def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)
    def assume(term: Term): Either[LogicError, Kernel.Thm] = lift(Kernel.assume(term))
    def app(fn: Term, arguments: Term*): Either[LogicError, Term] = lift(Term.appAll(fn, arguments.toList))
    def fact(name: String): Either[LogicError, Kernel.Thm] = fractions.fact(name)
    def eqMp(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] = lift(Kernel.eqMp(equation, theorem))

    def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
      Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

    def binary(term: Term): Either[LogicError, (Term, Term)] =
      term match {
        case App(App(_, left), right) => Right((left, right))
        case other => Left(NotOfForm("an application of two arguments", other))
      }

    /** From `|- R a b`, `|- a = a'` and `|- b = b'`, the theorem `|- R a' b'`. */
    def compared(order: Kernel.Thm, left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      order.conclusion match {
        case App(App(relation, _), _) =>
          for {
            both <- Conv.apTerm(relation, left).flatMap(partial => lift(Kernel.mkComb(partial, right)))
            result <- eqMp(both, order)
          } yield result
        case other => Left(NotOfForm("a comparison", other))
      }

    def le(a: Term, b: Term): Either[LogicError, Term] = read(Fraction.AtMost, Type.fun(Fraction.Classes, Type.fun(Fraction.Classes, Type.Bool))).flatMap(app(_, a, b))
    def lt(a: Term, b: Term): Either[LogicError, Term] = read(Fraction.LessThan, Type.fun(Fraction.Classes, Type.fun(Fraction.Classes, Type.Bool))).flatMap(app(_, a, b))

    /** `|- RAT_LT a b = ~(RAT_LE b a)`. */
    def opened(a: Term, b: Term): Either[LogicError, Kernel.Thm] =
      fractions.definition(Fraction.LessThan).flatMap(Conv.unfold(_, List(a, b)))

    /** `a < b` from a refutation of `b <= a`. */
    def strict(a: Term, b: Term)(refute: Kernel.Thm => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for {
        backwardsTerm <- le(b, a)
        backwards <- assume(backwardsTerm)
        absurd <- refute(backwards)
        negated <- rules.notIntro(backwardsTerm, absurd)
        result <- opened(a, b).flatMap(Conv.sym).flatMap(eqMp(_, negated))
      } yield result

    /** Falsity from `a < b` and `b <= a`. */
    def contradicts(less: Kernel.Thm, order: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(less.conclusion)
        negation <- opened(ab._1, ab._2).flatMap(eqMp(_, less))
        result <- rules.notElim(negation, order)
      } yield result

    def transitive(first: Kernel.Thm, second: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(first.conclusion)
        bc <- binary(second.conclusion)
        result <- fact(Fraction.AtMostTransitive)
          .flatMap(rules.specAll(_, List(ab._1, ab._2, bc._2)))
          .flatMap(rules.mp(_, first))
          .flatMap(rules.mp(_, second))
      } yield result

    /** `a < b` and `b <= c` give `a < c`: if `c <= a` then `b <= a`. */
    def lessThenAtMost(less: Kernel.Thm, order: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(less.conclusion)
        c <- binary(order.conclusion).map(_._2)
        result <- strict(ab._1, c)(backwards => transitive(order, backwards).flatMap(contradicts(less, _)))
      } yield result

    /** `a < b` and `b < c` give `a < c`. */
    def lessTransitive(first: Kernel.Thm, second: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        bc <- binary(second.conclusion)
        weak <- fact(Fraction.LessWeakens).flatMap(rules.specAll(_, List(bc._1, bc._2))).flatMap(rules.mp(_, second))
        result <- lessThenAtMost(first, weak)
      } yield result

    /** `|- ~(RAT_LT q q)`. */
    def irreflexive(q: Term): Either[LogicError, Kernel.Thm] =
      for {
        selfTerm <- lt(q, q)
        self <- assume(selfTerm)
        reflexive <- fact(Fraction.AtMostReflexive).flatMap(rules.spec(q, _))
        absurd <- contradicts(self, reflexive)
        result <- rules.notIntro(selfTerm, absurd)
      } yield result

    /** `~(RAT_LT p q)` gives `RAT_LE q p`, by the double negation the definition leaves. */
    def notLess(negation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      negation.conclusion match {
        case App(not, less) =>
          for {
            pq <- binary(less)
            doubled <- opened(pq._1, pq._2).flatMap(Conv.apTerm(not, _)).flatMap(eqMp(_, negation))
            order <- le(pq._2, pq._1)
            result <- classical.fact(Classical.DoubleNegation).flatMap(rules.spec(order, _)).flatMap(rules.mp(_, doubled))
          } yield result
        case other => Left(NotOfForm("a negation", other))
      }

    private def binaryConstant(name: String): Either[LogicError, Term] =
      read(name, Type.fun(Fraction.Classes, Type.fun(Fraction.Classes, Fraction.Classes)))

    def plus(a: Term, b: Term): Either[LogicError, Term] = binaryConstant(Fraction.Addition).flatMap(app(_, a, b))
    def minus(a: Term): Either[LogicError, Term] =
      read(Fraction.Negation, Type.fun(Fraction.Classes, Fraction.Classes)).flatMap(app(_, a))
    def difference(a: Term, b: Term): Either[LogicError, Term] = minus(b).flatMap(plus(a, _))

    /** `|- a = b` by the ring of `rat`, reflexivity where the two are already one term. */
    def same(a: Term, b: Term): Either[LogicError, Kernel.Thm] = if (a == b) Right(Conv.refl(a)) else ring.prove(a, b)

    /** `S t` and a ring identity `t = t'` give `S t'`, for a membership or any predicate applied last. */
    def carried(held: Kernel.Thm, target: Term): Either[LogicError, Kernel.Thm] =
      held.conclusion match {
        case App(set, at) => same(at, target).flatMap(Conv.apTerm(set, _)).flatMap(eqMp(_, held))
        case other => Left(NotOfForm("a membership", other))
      }

    /** A comparison with both sides rewritten by the ring of `rat`. */
    def rearranged(order: Kernel.Thm, left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(order.conclusion)
        leftEqual <- same(ab._1, left)
        rightEqual <- same(ab._2, right)
        result <- compared(order, leftEqual, rightEqual)
      } yield result

    /** `a < b` gives `a + c < b + c`: if `b + c <= a + c`, taking `c` away gives `b <= a`. */
    def lessShifted(less: Kernel.Thm, c: Term): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(less.conclusion)
        (a, b) = ab
        ac <- plus(a, c)
        bc <- plus(b, c)
        negated <- minus(c)
        result <- strict(ac, bc) { backwards =>
          for {
            moved <- fact(Fraction.AtMostAdd).flatMap(rules.specAll(_, List(bc, ac, negated))).flatMap(rules.mp(_, backwards))
            reversed <- rearranged(moved, b, a)
            falsity <- contradicts(less, reversed)
          } yield falsity
        }
      } yield result

    /** `S t` and `t = t'` following from premises by the ring, with coefficients, give `S t'`. */
    def carriedUnder(held: Kernel.Thm, target: Term, premises: List[(Kernel.Thm, Term)]): Either[LogicError, Kernel.Thm] =
      held.conclusion match {
        case App(set, at) => ring.consequence(at, target, premises).flatMap(Conv.apTerm(set, _)).flatMap(eqMp(_, held))
        case other => Left(NotOfForm("a membership", other))
      }

    /** `~(S t)` and a ring identity `t = t'` give `~(S t')`. */
    def carriedNot(held: Kernel.Thm, target: Term): Either[LogicError, Kernel.Thm] =
      held.conclusion match {
        case App(not, App(set, at)) =>
          same(at, target).flatMap(Conv.apTerm(set, _)).flatMap(Conv.apTerm(not, _)).flatMap(eqMp(_, held))
        case other => Left(NotOfForm("a negated membership", other))
      }

    /** `a < b` gives `a <= b`. */
    def weakened(less: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      binary(less.conclusion).flatMap(ab =>
        fact(Fraction.LessWeakens).flatMap(rules.specAll(_, List(ab._1, ab._2))).flatMap(rules.mp(_, less)))

    /** `|- RAT_LT RAT_ZERO RAT_ONE`, from the definition and the refusal of `1 <= 0`. */
    def zeroBelowOne: Either[LogicError, Kernel.Thm] =
      for {
        zero <- read(Fraction.Zero, Fraction.Classes)
        one <- read(Fraction.One, Fraction.Classes)
        refused <- fact(Fraction.OneNotAtMostZero)
        result <- opened(zero, one).flatMap(Conv.sym).flatMap(eqMp(_, refused))
      } yield result

    /** `0 < f` gives `~(f = 0)`: at zero it is `0 < 0`. */
    def positiveNonZero(positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      positive.conclusion match {
        case App(App(lessThan, zero), f) =>
          for {
            isZeroTerm <- lift(Term.eq(f, zero))
            isZero <- assume(isZeroTerm)
            atZero <- app(lessThan, zero).flatMap(Conv.apTerm(_, isZero)).flatMap(eqMp(_, positive))
            reflexive <- fact(Fraction.AtMostReflexive).flatMap(rules.spec(zero, _))
            falsity <- contradicts(atZero, reflexive)
            result <- rules.notIntro(isZeroTerm, falsity)
          } yield result
        case other => Left(NotOfForm("a comparison", other))
      }

    def times(a: Term, b: Term): Either[LogicError, Term] = binaryConstant(Fraction.Multiplication).flatMap(app(_, a, b))

    /**
     * `0 < c` and `a < b` give `c * a < c * b`: if `c * b <= c * a`, scaling by `RAT_INV c`, which is
     * not negative, gives `b <= a`. `RAT_LE_MUL_LEFT` is the non-strict half and this is its strict one.
     */
    def timesLeft(positive: Kernel.Thm, less: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        c <- binary(positive.conclusion).map(_._2)
        ab <- binary(less.conclusion)
        (a, b) = ab
        ca <- times(c, a)
        cb <- times(c, b)
        inverse <- read(Fraction.Inverse, Type.fun(Fraction.Classes, Fraction.Classes)).flatMap(app(_, c))
        inverseAbove <- fact(Fraction.InversePositive).flatMap(rules.spec(c, _)).flatMap(rules.mp(_, positive)).flatMap(weakened)
        unit <- positiveNonZero(positive).flatMap(nonZero => fact(Fraction.MulInverse).flatMap(rules.spec(c, _)).flatMap(rules.mp(_, nonZero)))
        result <- strict(ca, cb) { backwards =>
          for {
            scaled <- fact(Fraction.MulLeftMonotone)
              .flatMap(rules.specAll(_, List(inverse, cb, ca)))
              .flatMap(rules.mp(_, inverseAbove))
              .flatMap(rules.mp(_, backwards))
            sides <- binary(scaled.conclusion)
            leftIs <- ring.consequence(sides._1, b, List(unit -> b))
            rightIs <- ring.consequence(sides._2, a, List(unit -> a))
            reversed <- compared(scaled, leftIs, rightIs)
            falsity <- contradicts(less, reversed)
          } yield falsity
        }
      } yield result

    /** `0 < a` and `0 < b` give `0 < a * b`. */
    def timesPositive(first: Kernel.Thm, second: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        a <- binary(first.conclusion).map(_._2)
        b <- binary(second.conclusion).map(_._2)
        zero <- read(Fraction.Zero, Fraction.Classes)
        product <- times(a, b)
        result <- timesLeft(first, second).flatMap(rearranged(_, zero, product))
      } yield result

    /** `0 < p < a` and `0 < q < b` give `p * q < a * b`: through `a * q`. */
    def productBelow(pPositive: Kernel.Thm, pBelow: Kernel.Thm, qPositive: Kernel.Thm, qBelow: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        pa <- binary(pBelow.conclusion)
        qb <- binary(qBelow.conclusion)
        pq <- times(pa._1, qb._1)
        aq <- times(pa._2, qb._1)
        ab <- times(pa._2, qb._2)
        first <- timesLeft(qPositive, pBelow).flatMap(rearranged(_, pq, aq))
        aPositive <- lessTransitive(pPositive, pBelow)
        second <- timesLeft(aPositive, qBelow).flatMap(rearranged(_, aq, ab))
        result <- lessTransitive(first, second)
      } yield result

    /** `0 < p` and `q <= 0` give `p * q <= 0`. */
    def productNonPositive(pPositive: Kernel.Thm, qAtMostZero: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        p <- binary(pPositive.conclusion).map(_._2)
        q <- binary(qAtMostZero.conclusion).map(_._1)
        zero <- read(Fraction.Zero, Fraction.Classes)
        pNonNegative <- weakened(pPositive)
        scaled <- fact(Fraction.MulLeftMonotone)
          .flatMap(rules.specAll(_, List(p, q, zero)))
          .flatMap(rules.mp(_, pNonNegative))
          .flatMap(rules.mp(_, qAtMostZero))
        product <- times(p, q)
        result <- rearranged(scaled, product, zero)
      } yield result

    /** `a <= b` and `b < c` give `a < c`: if `c <= a` then `c <= b`. */
    def atMostThenLess(order: Kernel.Thm, less: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        a <- binary(order.conclusion).map(_._1)
        c <- binary(less.conclusion).map(_._2)
        result <- strict(a, c)(backwards => transitive(backwards, order).flatMap(contradicts(less, _)))
      } yield result

    /** `|- RAT_LT (RAT_ADD q (RAT_NEG RAT_ONE)) q`: if `q <= q - 1`, adding `1 - q` gives `1 <= 0`. */
    def below(q: Term): Either[LogicError, Kernel.Thm] =
      for {
        one <- read(Fraction.One, Fraction.Classes)
        zero <- read(Fraction.Zero, Fraction.Classes)
        add <- read(Fraction.Addition, Type.fun(Fraction.Classes, Type.fun(Fraction.Classes, Fraction.Classes)))
        neg <- read(Fraction.Negation, Type.fun(Fraction.Classes, Fraction.Classes))
        minusOne <- app(neg, one)
        lower <- app(add, q, minusOne)
        minusQ <- app(neg, q)
        shift <- app(add, one, minusQ)
        result <- strict(lower, q) { backwards =>
          for {
            moved <- fact(Fraction.AtMostAdd).flatMap(rules.specAll(_, List(q, lower, shift))).flatMap(rules.mp(_, backwards))
            sides <- binary(moved.conclusion)
            leftIsOne <- ring.prove(sides._1, one)
            rightIsZero <- ring.prove(sides._2, zero)
            oneBelowZero <- compared(moved, leftIsOne, rightIsZero)
            falsity <- fact(Fraction.OneNotAtMostZero).flatMap(rules.notElim(_, oneBelowZero))
          } yield falsity
        }
      } yield result
  }

  /* ------------------------------------------------------------------ sets of rationals */

  /** `IS_CUT`, opened into its four clauses and closed from them. */
  private final case class Sets(rationals: Rationals, isCutDefinition: Kernel.Thm) {
    import rationals.*

    /** `|- IS_CUT S = (four clauses, reduced)`. */
    def unfolded(set: Term): Either[LogicError, Kernel.Thm] =
      for {
        opened <- Conv.unfold(isCutDefinition, List(set))
        body <- rightOf(opened)
        reduced <- Conv.betaNormalise(body)
        result <- Conv.trans(opened, reduced)
      } yield result

    /** The four clauses of `|- IS_CUT S`: inhabited, not everything, closed downwards, no greatest. */
    def clauses(held: Kernel.Thm): Either[LogicError, Clauses] =
      held.conclusion match {
        case App(_, set) =>
          for {
            body <- unfolded(set).flatMap(eqMp(_, held))
            inhabited <- rules.conjElim1(body)
            rest <- rules.conjElim2(body)
            proper <- rules.conjElim1(rest)
            last <- rules.conjElim2(rest)
            closed <- rules.conjElim1(last)
            open <- rules.conjElim2(last)
          } yield Clauses(inhabited, proper, closed, open)
        case other => Left(NotOfForm("an application of IS_CUT", other))
      }

    /** `|- IS_CUT S` from its four clauses, each in the reduced form [[unfolded]] gives. */
    def closedFrom(set: Term, inhabited: Kernel.Thm, proper: Kernel.Thm, closed: Kernel.Thm, open: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        last <- rules.conjIntro(closed, open)
        rest <- rules.conjIntro(proper, last)
        body <- rules.conjIntro(inhabited, rest)
        result <- unfolded(set).flatMap(Conv.sym).flatMap(eqMp(_, body))
      } yield result

    /** `S b` and `a < b` give `S a`. */
    def downwards(clauses: Clauses, a: Term, b: Term, member: Kernel.Thm, less: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      rules.specAll(clauses.closed, List(a, b)).flatMap(implication => rules.conjIntro(member, less).flatMap(rules.mp(implication, _)))

    /** `S b` and `a <= b` give `S a`: equal, or strictly below by antisymmetry. */
    def downwardsAtMost(clauses: Clauses, set: Term, a: Term, b: Term, member: Kernel.Thm, order: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        equalTerm <- lift(Term.eq(a, b))
        equal <- assume(equalTerm)
        atA <- Conv.apTerm(set, equal).flatMap(Conv.sym).flatMap(eqMp(_, member))
        different <- logic.mkNot(equalTerm).flatMap(assume)
        less <- strict(a, b) { backwards =>
          fact(Fraction.AtMostAntisymmetric)
            .flatMap(rules.specAll(_, List(a, b)))
            .flatMap(rules.mp(_, order))
            .flatMap(rules.mp(_, backwards))
            .flatMap(rules.notElim(different, _))
        }
        viaLess <- downwards(clauses, a, b, member, less)
        result <- classical.cases(equalTerm, atA, viaLess)
      } yield result

    /** [[Cut.BelowIsCut]]: something below `q`, `q` itself not, transitivity, and density. */
    def belowIsCut: Either[LogicError, Kernel.Thm] = {
      val q = Term.variable("q", Fraction.Classes)
      val a = Term.variable("a", Fraction.Classes)
      val b = Term.variable("b", Fraction.Classes)
      for {
        set <- read("\\p:rat. RAT_LT p q", Type.fun(Fraction.Classes, Type.Bool))
        body <- unfolded(set).flatMap(rightOf)
        clauseTerms <- body match {
          case App(App(_, inhabited), App(App(_, proper), App(App(_, closed), open))) => Right((inhabited, proper, closed, open))
          case other => Left(NotOfForm("the four clauses of IS_CUT", other))
        }
        (inhabitedTerm, properTerm, _, _) = clauseTerms

        lowered <- below(q)
        lower <- binary(lowered.conclusion).map(_._1)
        inhabited <- logic.destExistsPredicate(inhabitedTerm).toRight(NotOfForm("an existential", inhabitedTerm))
          .flatMap(rules.existsIntro(_, lower, lowered))
        proper <- logic.destExistsPredicate(properTerm).toRight(NotOfForm("an existential", properTerm))
          .flatMap(predicate => irreflexive(q).flatMap(rules.existsIntro(predicate, q, _)))

        closed <- for {
          bq <- lt(b, q)
          ab <- lt(a, b)
          both <- logic.mkConj(bq, ab).flatMap(assume)
          first <- rules.conjElim1(both)
          second <- rules.conjElim2(both)
          aq <- lessTransitive(second, first)
          result <- rules.disch(both.conclusion, aq).flatMap(rules.gen(b, _)).flatMap(rules.gen(a, _))
        } yield result

        open <- for {
          aq <- lt(a, q).flatMap(assume)
          between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(a, q))).flatMap(rules.mp(_, aq))
          goal <- proposition("?b:rat. RAT_LT b q /\\ RAT_LT a b")
          predicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
          z = Term.variable("z", Fraction.Classes)
          middle <- lt(a, z).flatMap(az => lt(z, q).flatMap(zq => logic.mkConj(az, zq))).flatMap(assume)
          az <- rules.conjElim1(middle)
          zq <- rules.conjElim2(middle)
          swapped <- rules.conjIntro(zq, az)
          introduced <- rules.existsIntro(predicate, z, swapped)
          eliminated <- rules.existsElim(between, z, introduced)
          result <- rules.disch(aq.conclusion, eliminated).flatMap(rules.gen(a, _))
        } yield result

        isCut <- closedFrom(set, inhabited, proper, closed, open)
        result <- rules.gen(q, isCut)
      } yield result
    }
  }

  private final case class Clauses(inhabited: Kernel.Thm, proper: Kernel.Thm, closed: Kernel.Thm, open: Kernel.Thm)

  /* ------------------------------------------------------------------ cuts */

  private final case class Cuts(
    sets: Sets,
    bijection: (Kernel.Thm, Kernel.Thm),
    atMostDefinition: Kernel.Thm,
    ofRationalDefinition: Kernel.Thm,
    additionDefinition: Kernel.Thm,
    negationDefinition: Kernel.Thm,
    posMulDefinition: Kernel.Thm,
    multiplicationDefinition: Kernel.Thm,
    lessThanDefinition: Kernel.Thm,
    posInverseDefinition: Kernel.Thm,
    inverseDefinition: Kernel.Thm,
    induction: Kernel.Thm
  ) {
    import sets.rationals.*

    private val cutType = Classes
    private val setType = Type.fun(Fraction.Classes, Type.Bool)
    private val x = Term.variable("x", cutType)
    private val y = Term.variable("y", cutType)
    private val z = Term.variable("z", cutType)
    private val p = Term.variable("p", Fraction.Classes)
    private val q = Term.variable("q", Fraction.Classes)
    private val t = Term.variable("t", Fraction.Classes)
    /** The rational an inclusion quantifies over, apart from every rational a statement names. */
    private val u = Term.variable("u", Fraction.Classes)
    private val set = Term.variable("S", setType)

    private def dest: Either[LogicError, Term] = read(Representation, Type.fun(cutType, setType))
    private def make: Either[LogicError, Term] = read(Abstraction, Type.fun(setType, cutType))
    private def member(cut: Term, rational: Term): Either[LogicError, Term] = dest.flatMap(app(_, cut, rational))

    /** `|- mk_cut (dest_cut c) = c`. */
    private def rebuilt(cut: Term): Either[LogicError, Kernel.Thm] =
      rules.gen(Term.variable("a", cutType), bijection._1).flatMap(rules.spec(cut, _))

    /** `|- IS_CUT r = (dest_cut (mk_cut r) = r)`. */
    private def characterised(candidate: Term): Either[LogicError, Kernel.Thm] =
      rules.gen(Term.variable("r", setType), bijection._2).flatMap(rules.spec(candidate, _))

    /** `|- CUT_LE a b = !q. dest_cut a q ==> dest_cut b q`. */
    private def atMostOpened(a: Term, b: Term): Either[LogicError, Kernel.Thm] = Conv.unfold(atMostDefinition, List(a, b))

    /** `CUT_LE a b` from a derivation of `dest_cut b u` under `dest_cut a u`, for the variable `u`. */
    private def included(a: Term, b: Term)(inside: Kernel.Thm => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
      for {
        inA <- member(a, u).flatMap(assume)
        inB <- inside(inA)
        general <- rules.disch(inA.conclusion, inB).flatMap(rules.gen(u, _))
        result <- atMostOpened(a, b).flatMap(Conv.sym).flatMap(eqMp(_, general))
      } yield result

    /** `CUT_LE a b` and `dest_cut a r` give `dest_cut b r`. */
    private def inside(order: Kernel.Thm, rational: Term, inA: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ab <- binary(order.conclusion)
        result <- atMostOpened(ab._1, ab._2)
          .flatMap(eqMp(_, order))
          .flatMap(rules.spec(rational, _))
          .flatMap(rules.mp(_, inA))
      } yield result

    def facts(belowIsCut: Kernel.Thm): Either[LogicError, Vector[(String, Kernel.Thm)]] =
      for {
        represents <- representsFact
        rebuilds <- rebuildsFact
        reflexive <- included(x, x)(Right(_)).flatMap(rules.gen(x, _))
        transitive <- transitiveFact
        antisymmetric <- antisymmetricFact
        total <- totalFact(represents)
        members <- membersFact(belowIsCut, rebuilds)
        order <- orderFact(members)
        injective <- injectiveFact(reflexive, order)
        complete <- completeFact(represents, rebuilds)
        sums <- Sums(represents, rebuilds, antisymmetric, members, total, transitive, reflexive).facts
      } yield Vector(
        (BelowIsCut, belowIsCut),
        (Represents, represents),
        (Rebuilds, rebuilds),
        (AtMostReflexive, reflexive),
        (AtMostTransitive, transitive),
        (AtMostAntisymmetric, antisymmetric),
        (AtMostTotal, total),
        (OfRationalMembers, members),
        (OfRationalOrder, order),
        (OfRationalInjective, injective),
        (Complete, complete)
      ) ++ sums

    /**
     * Addition. `CUT_ADD x y` holds `r` when some `p` in `x` leaves `r - p` in `y`, which is one
     * existential rather than the two of `p + q` with each in its cut, and every rearrangement of
     * rationals below is the ring of `rat` carried into a membership.
     */
    private final case class Sums(
      represents: Kernel.Thm,
      rebuilds: Kernel.Thm,
      antisymmetric: Kernel.Thm,
      members: Kernel.Thm,
      total: Kernel.Thm,
      transitive: Kernel.Thm,
      reflexive: Kernel.Thm
    ) {
      private val r = Term.variable("r", Fraction.Classes)
      private val e = Term.variable("e", Fraction.Classes)
      private val f = Term.variable("f", Fraction.Classes)
      private val s = Term.variable("s", Fraction.Classes)
      private val a = Term.variable("a", Fraction.Classes)
      private val b = Term.variable("b", Fraction.Classes)

      private def substituted(text: String, ty: Option[Type], bindings: Map[FVar, Term]): Either[LogicError, Term] =
        ty.fold(proposition(text))(read(text, _)).flatMap(t => lift(Term.substitute(bindings, t)))

      /** `\r. ?p. dest_cut left p /\ dest_cut right (r + -p)`. */
      private def sumSet(left: Term, right: Term): Either[LogicError, Term] =
        substituted(SumSetText, Some(setType), Map(x -> left, y -> right))

      /** `?p. dest_cut left p /\ dest_cut right (at + -p)`. */
      private def inSumTerm(left: Term, right: Term, at: Term): Either[LogicError, Term] =
        substituted("?p:rat. dest_cut x p /\\ dest_cut y (RAT_ADD r (RAT_NEG p))", None, Map(x -> left, y -> right, r -> at))

      /** The membership from its witness: `dest_cut left p` and `dest_cut right (at + -p)`. */
      private def intoSum(left: Term, right: Term, at: Term, witness: Term, inLeft: Kernel.Thm, inRight: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          target <- inSumTerm(left, right, at)
          predicate <- logic.destExistsPredicate(target).toRight(NotOfForm("an existential", target))
          both <- rules.conjIntro(inLeft, inRight)
          result <- rules.existsIntro(predicate, witness, both)
        } yield result

      /** A case under an existential: the instance at `variable` assumed, the result discharged. */
      private def choosing(existential: Kernel.Thm, variable: FVar)(body: Kernel.Thm => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
        for {
          predicate <- logic.destExistsPredicate(existential.conclusion).toRight(NotOfForm("an existential", existential.conclusion))
          applied <- app(predicate, variable)
          instance <- Conv.betaRoot(applied).flatMap(rightOf)
          held <- assume(instance)
          reached <- body(held)
          result <- rules.existsElim(existential, variable, reached)
        } yield result

      /** A conjunction taken apart. */
      private def halves(both: Kernel.Thm): Either[LogicError, (Kernel.Thm, Kernel.Thm)] =
        rules.conjElim1(both).flatMap(first => rules.conjElim2(both).map(second => (first, second)))

      private def clausesOf(cut: Term): Either[LogicError, Clauses] = rules.spec(cut, represents).flatMap(sets.clauses)

      private def addition: Either[LogicError, Term] = read(Addition, Type.fun(cutType, Type.fun(cutType, cutType)))

      /** `|- dest_cut (CUT_ADD left right) at = ?p. dest_cut left p /\ dest_cut right (at + -p)`. */
      private def inSum(addMembers: Kernel.Thm, left: Term, right: Term, at: Term): Either[LogicError, Kernel.Thm] =
        for {
          atCuts <- rules.specAll(addMembers, List(left, right))
          applied <- Conv.apThm(atCuts, at)
          reduced <- rightOf(applied).flatMap(Conv.betaRoot)
          result <- Conv.trans(applied, reduced)
        } yield result

      private def fromSum(addMembers: Kernel.Thm, held: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        held.conclusion match {
          case App(App(_, App(App(_, left), right)), at) => inSum(addMembers, left, right, at).flatMap(eqMp(_, held))
          case other => Left(NotOfForm("a membership of a sum", other))
        }

      private def toSum(addMembers: Kernel.Thm, left: Term, right: Term, at: Term, existential: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        inSum(addMembers, left, right, at).flatMap(Conv.sym).flatMap(eqMp(_, existential))

      /** Two cuts are equal when each is inside the other. */
      private def equalCuts(left: Term, right: Term)(
        forwards: Kernel.Thm => Either[LogicError, Kernel.Thm],
        backwards: Kernel.Thm => Either[LogicError, Kernel.Thm]
      ): Either[LogicError, Kernel.Thm] =
        for {
          first <- included(left, right)(forwards)
          second <- included(right, left)(backwards)
          result <- rules.specAll(antisymmetric, List(left, right)).flatMap(rules.mp(_, first)).flatMap(rules.mp(_, second))
        } yield result

      def facts: Either[LogicError, Vector[(String, Kernel.Thm)]] =
        for {
          isCut <- sumIsCut
          addMembers <- sumMembers(isCut)
          commutative <- commutativeFact(addMembers)
          associative <- associativeFact(addMembers)
          zero <- zeroFact(addMembers)
          order <- orderFact(addMembers)
          embedded <- embeddedFact(addMembers)
          negIsCut <- negationIsCut
          negMembers <- negationMembers(negIsCut)
          escape <- escapeFact
          inverse <- inverseFact(addMembers, negMembers, escape)
          addNonNegative <- addNonNegativeFact(addMembers)
          products <- Products(addMembers, addNonNegative, escape).facts
          group <- groupOf(associative, commutative, zero, inverse)
          signed <- Signs(group, order, addNonNegative, products.toMap).facts
        } yield Vector(
          (AddIsCut, isCut),
          (AddMembers, addMembers),
          (AddCommutative, commutative),
          (AddAssociative, associative),
          (AddZero, zero),
          (AtMostAdd, order),
          (OfRationalAdd, embedded),
          (NegIsCut, negIsCut),
          (NegMembers, negMembers),
          (Escape, escape),
          (AddNegation, inverse),
          (AddNonNegative, addNonNegative)
        ) ++ products ++ group.facts ++ signed

      /**
       * [[Cut.AddIsCut]]. Inhabited by `e + f` for members `e`, `f`; not everything, since for
       * non-members `e`, `f` a witness `p` of `e + f` is below `e` and then `f` is below
       * `e + f - p`, which would put `f` in `y`; closed downwards and without a greatest element
       * because `y` is, shifted by the witness.
       */
      private def sumIsCut: Either[LogicError, Kernel.Thm] =
        for {
          clausesX <- clausesOf(x)
          clausesY <- clausesOf(y)
          destX <- dest.flatMap(app(_, x))
          set <- sumSet(x, y)
          body <- sets.unfolded(set).flatMap(rightOf)
          clauseTerms <- body match {
            case App(App(_, inhabited), App(App(_, proper), App(App(_, closed), open))) => Right((inhabited, proper, closed, open))
            case other => Left(NotOfForm("the four clauses of IS_CUT", other))
          }
          (inhabitedTerm, properTerm, _, _) = clauseTerms

          inhabited <- choosing(clausesX.inhabited, e) { inE =>
            choosing(clausesY.inhabited, f) { inF =>
              for {
                total <- plus(e, f)
                shifted <- difference(total, e).flatMap(carried(inF, _))
                inside <- intoSum(x, y, total, e, inE, shifted)
                predicate <- logic.destExistsPredicate(inhabitedTerm).toRight(NotOfForm("an existential", inhabitedTerm))
                result <- rules.existsIntro(predicate, total, inside)
              } yield result
            }
          }

          proper <- choosing(clausesX.proper, e) { notE =>
            choosing(clausesY.proper, f) { notF =>
              for {
                total <- plus(e, f)
                memberTerm <- inSumTerm(x, y, total)
                memberHeld <- assume(memberTerm)
                falsity <- choosing(memberHeld, p) { pair =>
                  for {
                    parts <- halves(pair)
                    (inP, inRest) = parts
                    below <- strict(p, e) { backwards =>
                      sets.downwardsAtMost(clausesX, destX, e, p, inP, backwards).flatMap(rules.notElim(notE, _))
                    }
                    shift <- difference(f, p)
                    moved <- lessShifted(below, shift)
                    rest <- difference(total, p)
                    fBelow <- rearranged(moved, f, rest)
                    inF <- sets.downwards(clausesY, f, rest, inRest, fBelow)
                    result <- rules.notElim(notF, inF)
                  } yield result
                }
                notIn <- rules.notIntro(memberTerm, falsity)
                predicate <- logic.destExistsPredicate(properTerm).toRight(NotOfForm("an existential", properTerm))
                result <- rules.existsIntro(predicate, total, notIn)
              } yield result
            }
          }

          closed <- for {
            inB <- inSumTerm(x, y, b)
            less <- lt(a, b)
            both <- logic.mkConj(inB, less).flatMap(assume)
            parts <- halves(both)
            (member, ab) = parts
            reached <- choosing(member, p) { pair =>
              for {
                inner <- halves(pair)
                (inP, inRest) = inner
                negated <- minus(p)
                shifted <- lessShifted(ab, negated)
                lowered <- binary(shifted.conclusion)
                inLower <- sets.downwards(clausesY, lowered._1, lowered._2, inRest, shifted)
                result <- intoSum(x, y, a, p, inP, inLower)
              } yield result
            }
            result <- rules.disch(both.conclusion, reached).flatMap(rules.gen(b, _)).flatMap(rules.gen(a, _))
          } yield result

          open <- for {
            inA <- inSumTerm(x, y, a).flatMap(assume)
            goal <- inSumTerm(x, y, b).flatMap(ib => lt(a, b).flatMap(ab => logic.mkConj(ib, ab))).flatMap(body => lift(Term.abs(b, body)))
            reached <- choosing(inA, p) { pair =>
              for {
                inner <- halves(pair)
                (inP, inRest) = inner
                rest <- difference(a, p)
                higher <- rules.spec(rest, clausesY.open).flatMap(rules.mp(_, inRest))
                result <- choosing(higher, s) { pairS =>
                  for {
                    partsS <- halves(pairS)
                    (inS, restBelow) = partsS
                    total <- plus(p, s)
                    shifted <- difference(total, p).flatMap(carried(inS, _))
                    inTotal <- intoSum(x, y, total, p, inP, shifted)
                    raised <- lessShifted(restBelow, p).flatMap(rearranged(_, a, total))
                    both <- rules.conjIntro(inTotal, raised)
                    result <- rules.existsIntro(goal, total, both)
                  } yield result
                }
              } yield result
            }
            result <- rules.disch(inA.conclusion, reached).flatMap(rules.gen(a, _))
          } yield result

          isCut <- sets.closedFrom(set, inhabited, proper, closed, open)
          result <- rules.gen(y, isCut).flatMap(rules.gen(x, _))
        } yield result

      /** [[Cut.AddMembers]]: the definition, then the characterisation at a set that is a cut. */
      private def sumMembers(isCut: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          unfolded <- Conv.unfold(additionDefinition, List(x, y))
          carriedDest <- dest.flatMap(Conv.apTerm(_, unfolded))
          set <- sumSet(x, y)
          atSet <- rules.specAll(isCut, List(x, y))
          back <- rules.spec(set, rebuilds).flatMap(rules.mp(_, atSet))
          result <- Conv.trans(carriedDest, back).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
        } yield result

      /** One direction of commutativity: a witness `p` for `left + right` gives `u - p` for the other. */
      private def swapped(addMembers: Kernel.Thm, left: Term, right: Term)(held: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          existential <- fromSum(addMembers, held)
          result <- choosing(existential, p) { pair =>
            for {
              parts <- halves(pair)
              (inP, inRest) = parts
              rest <- difference(u, p)
              back <- difference(u, rest).flatMap(carried(inP, _))
              inside <- intoSum(right, left, u, rest, inRest, back)
              result <- toSum(addMembers, right, left, u, inside)
            } yield result
          }
        } yield result

      private def commutativeFact(addMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          sum <- addition
          xy <- app(sum, x, y)
          yx <- app(sum, y, x)
          result <- equalCuts(xy, yx)(swapped(addMembers, x, y), swapped(addMembers, y, x))
            .flatMap(rules.gen(y, _))
            .flatMap(rules.gen(x, _))
        } yield result

      /** [[Cut.AddAssociative]]: a witness `s` of `x + y` and its own `p` become `p` and `s - p`, and back. */
      private def associativeFact(addMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          sum <- addition
          xy <- app(sum, x, y)
          yz <- app(sum, y, z)
          left <- app(sum, xy, z)
          right <- app(sum, x, yz)
          q2 = Term.variable("q", Fraction.Classes)
          result <- equalCuts(left, right)(
            held =>
              for {
                outer <- fromSum(addMembers, held)
                result <- choosing(outer, s) { pairS =>
                  for {
                    partsS <- halves(pairS)
                    (inXY, inZ) = partsS
                    inner <- fromSum(addMembers, inXY)
                    result <- choosing(inner, p) { pairP =>
                      for {
                        partsP <- halves(pairP)
                        (inP, inY) = partsP
                        restU <- difference(u, p)
                        restS <- difference(s, p)
                        target <- difference(restU, restS)
                        inZMoved <- carried(inZ, target)
                        inYZ <- intoSum(y, z, restU, restS, inY, inZMoved).flatMap(toSum(addMembers, y, z, restU, _))
                        inside <- intoSum(x, yz, u, p, inP, inYZ)
                        result <- toSum(addMembers, x, yz, u, inside)
                      } yield result
                    }
                  } yield result
                }
              } yield result,
            held =>
              for {
                outer <- fromSum(addMembers, held)
                result <- choosing(outer, p) { pairP =>
                  for {
                    partsP <- halves(pairP)
                    (inP, inYZ) = partsP
                    inner <- fromSum(addMembers, inYZ)
                    result <- choosing(inner, q2) { pairQ =>
                      for {
                        partsQ <- halves(pairQ)
                        (inQ, inZ) = partsQ
                        total <- plus(p, q2)
                        inQMoved <- difference(total, p).flatMap(carried(inQ, _))
                        inXY <- intoSum(x, y, total, p, inP, inQMoved).flatMap(toSum(addMembers, x, y, total, _))
                        inZMoved <- difference(u, total).flatMap(carried(inZ, _))
                        inside <- intoSum(xy, z, u, total, inXY, inZMoved)
                        result <- toSum(addMembers, xy, z, u, inside)
                      } yield result
                    }
                  } yield result
                }
              } yield result
          ).flatMap(rules.gen(z, _)).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
        } yield result

      /** [[Cut.AddZero]]: `u - p < 0` is `u < p`, and a member of `x` has a larger one by `open`. */
      private def zeroFact(addMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          sum <- addition
          zero <- read(Fraction.Zero, Fraction.Classes)
          ofRational <- read(OfRational, Type.fun(Fraction.Classes, cutType))
          zeroCut <- app(ofRational, zero)
          left <- app(sum, x, zeroCut)
          clausesX <- clausesOf(x)
          result <- equalCuts(left, x)(
            held =>
              for {
                existential <- fromSum(addMembers, held)
                result <- choosing(existential, p) { pair =>
                  for {
                    parts <- halves(pair)
                    (inP, inZero) = parts
                    rest <- difference(u, p)
                    below <- memberOf(members, zero, rest).flatMap(eqMp(_, inZero))
                    less <- lessShifted(below, p).flatMap(rearranged(_, u, p))
                    result <- sets.downwards(clausesX, u, p, inP, less)
                  } yield result
                }
              } yield result,
            held =>
              for {
                higher <- rules.spec(u, clausesX.open).flatMap(rules.mp(_, held))
                result <- choosing(higher, s) { pairS =>
                  for {
                    parts <- halves(pairS)
                    (inS, below) = parts
                    negated <- minus(s)
                    rest <- difference(u, s)
                    less <- lessShifted(below, negated).flatMap(rearranged(_, rest, zero))
                    inZero <- memberOf(members, zero, rest).flatMap(Conv.sym).flatMap(eqMp(_, less))
                    inside <- intoSum(x, zeroCut, u, s, inS, inZero)
                    result <- toSum(addMembers, x, zeroCut, u, inside)
                  } yield result
                }
              } yield result
          ).flatMap(rules.gen(x, _))
        } yield result

      /** [[Cut.AtMostAdd]]: the witness in `x` is a witness in `y`. */
      private def orderFact(addMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          sum <- addition
          atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
          xy <- app(atMost, x, y).flatMap(assume)
          xz <- app(sum, x, z)
          yz <- app(sum, y, z)
          order <- included(xz, yz) { held =>
            for {
              existential <- fromSum(addMembers, held)
              result <- choosing(existential, p) { pair =>
                for {
                  parts <- halves(pair)
                  (inP, inRest) = parts
                  inY <- inside(xy, p, inP)
                  witnessed <- intoSum(y, z, u, p, inY, inRest)
                  result <- toSum(addMembers, y, z, u, witnessed)
                } yield result
              }
            } yield result
          }
          result <- rules.disch(xy.conclusion, order)
            .flatMap(rules.gen(z, _))
            .flatMap(rules.gen(y, _))
            .flatMap(rules.gen(x, _))
        } yield result

      /**
       * [[Cut.OfRationalAdd]]. Below `p + q` means `u - q < p`, so density puts some `a` between and
       * `u - a < q`; conversely `a < p` and `u - a < q` add up to `u < p + q`.
       */
      private def embeddedFact(addMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          sum <- addition
          ofRational <- read(OfRational, Type.fun(Fraction.Classes, cutType))
          total <- plus(p, q)
          ofTotal <- app(ofRational, total)
          ofP <- app(ofRational, p)
          ofQ <- app(ofRational, q)
          sumCut <- app(sum, ofP, ofQ)
          result <- equalCuts(ofTotal, sumCut)(
            held =>
              for {
                below <- memberOf(members, total, u).flatMap(eqMp(_, held))
                negated <- minus(q)
                restQ <- difference(u, q)
                lowered <- lessShifted(below, negated).flatMap(rearranged(_, restQ, p))
                between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(restQ, p))).flatMap(rules.mp(_, lowered))
                result <- choosing(between, a) { pair =>
                  for {
                    parts <- halves(pair)
                    (restBelowA, aBelowP) = parts
                    inP <- memberOf(members, p, a).flatMap(Conv.sym).flatMap(eqMp(_, aBelowP))
                    shift <- difference(q, a)
                    restA <- difference(u, a)
                    restBelowQ <- lessShifted(restBelowA, shift).flatMap(rearranged(_, restA, q))
                    inQ <- memberOf(members, q, restA).flatMap(Conv.sym).flatMap(eqMp(_, restBelowQ))
                    inside <- intoSum(ofP, ofQ, u, a, inP, inQ)
                    result <- toSum(addMembers, ofP, ofQ, u, inside)
                  } yield result
                }
              } yield result,
            held =>
              for {
                existential <- fromSum(addMembers, held)
                result <- choosing(existential, a) { pair =>
                  for {
                    parts <- halves(pair)
                    (inP, inQ) = parts
                    aBelowP <- memberOf(members, p, a).flatMap(eqMp(_, inP))
                    restA <- difference(u, a)
                    restBelowQ <- memberOf(members, q, restA).flatMap(eqMp(_, inQ))
                    middle <- plus(p, restA)
                    first <- lessShifted(aBelowP, restA).flatMap(rearranged(_, u, middle))
                    second <- lessShifted(restBelowQ, p).flatMap(rearranged(_, middle, total))
                    less <- lessTransitive(first, second)
                    result <- memberOf(members, total, u).flatMap(Conv.sym).flatMap(eqMp(_, less))
                  } yield result
                }
              } yield result
          ).flatMap(rules.gen(q, _)).flatMap(rules.gen(p, _))
        } yield result

      /** `\p. ?r. 0 < r /\ ~(dest_cut of (-p + -r))`. */
      private def negSet(of: Term): Either[LogicError, Term] = substituted(NegSetText, Some(setType), Map(x -> of))

      /** `?r. 0 < r /\ ~(dest_cut of (-at + -r))`. */
      private def inNegTerm(of: Term, at: Term): Either[LogicError, Term] =
        substituted(
          "?r:rat. RAT_LT RAT_ZERO r /\\ ~(dest_cut x (RAT_ADD (RAT_NEG p) (RAT_NEG r)))",
          None,
          Map(x -> of, p -> at)
        )

      private def intoNeg(of: Term, at: Term, witness: Term, positive: Kernel.Thm, outside: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          target <- inNegTerm(of, at)
          predicate <- logic.destExistsPredicate(target).toRight(NotOfForm("an existential", target))
          both <- rules.conjIntro(positive, outside)
          result <- rules.existsIntro(predicate, witness, both)
        } yield result

      /** `-at + -r`, the rational a witness `r` keeps outside the cut. */
      private def reflected(at: Term, witness: Term): Either[LogicError, Term] =
        minus(at).flatMap(negated => minus(witness).flatMap(plus(negated, _)))

      /** The rational a membership `dest_cut c t` is about. */
      private def pointOf(held: Kernel.Thm): Either[LogicError, Term] =
        held.conclusion match {
          case App(_, at) => Right(at)
          case other => Left(NotOfForm("a membership", other))
        }

      /** Every member of a cut is below every non-member. */
      private def belowOutside(clauses: Clauses, set: Term, inP: Kernel.Thm, outside: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          pAt <- pointOf(inP)
          aAt <- outside.conclusion match {
            case App(_, App(_, at)) => Right(at)
            case other => Left(NotOfForm("a negated membership", other))
          }
          result <- strict(pAt, aAt) { backwards =>
            sets.downwardsAtMost(clauses, set, aAt, pAt, inP, backwards).flatMap(rules.notElim(outside, _))
          }
        } yield result

      /**
       * [[Cut.NegIsCut]]. Inhabited by `-a - 1` for a non-member `a`; not everything, since `-e` for a
       * member `e` would need `e - r` outside `x`; closed downwards because a smaller point reflects
       * to a larger one; and without a greatest element because a witness `r` can be split at any
       * `s` between zero and it, moving the point up by `s` and keeping `r - s`.
       */
      private def negationIsCut: Either[LogicError, Kernel.Thm] =
        for {
          clausesX <- clausesOf(x)
          set <- negSet(x)
          body <- sets.unfolded(set).flatMap(rightOf)
          clauseTerms <- body match {
            case App(App(_, inhabited), App(App(_, proper), App(App(_, closed), open))) => Right((inhabited, proper, closed, open))
            case other => Left(NotOfForm("the four clauses of IS_CUT", other))
          }
          (inhabitedTerm, properTerm, _, _) = clauseTerms
          one <- read(Fraction.One, Fraction.Classes)
          zero <- read(Fraction.Zero, Fraction.Classes)
          positiveOne <- zeroBelowOne

          inhabited <- choosing(clausesX.proper, e) { notE =>
            for {
              point <- minus(e).flatMap(ne => minus(one).flatMap(plus(ne, _)))
              kept <- reflected(point, one).flatMap(carriedNot(notE, _))
              inside <- intoNeg(x, point, one, positiveOne, kept)
              predicate <- logic.destExistsPredicate(inhabitedTerm).toRight(NotOfForm("an existential", inhabitedTerm))
              result <- rules.existsIntro(predicate, point, inside)
            } yield result
          }

          proper <- choosing(clausesX.inhabited, e) { inE =>
            for {
              point <- minus(e)
              memberTerm <- inNegTerm(x, point)
              held <- assume(memberTerm)
              falsity <- choosing(held, r) { pair =>
                for {
                  parts <- halves(pair)
                  (positive, outside) = parts
                  kept <- reflected(point, r)
                  shift <- difference(e, r)
                  lowered <- lessShifted(positive, shift).flatMap(rearranged(_, kept, e))
                  inKept <- sets.downwards(clausesX, kept, e, inE, lowered)
                  result <- rules.notElim(outside, inKept)
                } yield result
              }
              notIn <- rules.notIntro(memberTerm, falsity)
              predicate <- logic.destExistsPredicate(properTerm).toRight(NotOfForm("an existential", properTerm))
              result <- rules.existsIntro(predicate, point, notIn)
            } yield result
          }

          closed <- for {
            inB <- inNegTerm(x, b)
            less <- lt(a, b)
            both <- logic.mkConj(inB, less).flatMap(assume)
            parts <- halves(both)
            (inBHeld, ab) = parts
            reached <- choosing(inBHeld, r) { pair =>
              for {
                inner <- halves(pair)
                (positive, outside) = inner
                keptB <- reflected(b, r)
                keptA <- reflected(a, r)
                shift <- minus(a).flatMap(na => minus(b).flatMap(plus(na, _))).flatMap(ab2 => minus(r).flatMap(plus(ab2, _)))
                ordered <- lessShifted(ab, shift).flatMap(rearranged(_, keptB, keptA))
                inATerm <- member(x, keptA)
                inA <- assume(inATerm)
                falsity <- sets.downwards(clausesX, keptB, keptA, inA, ordered).flatMap(rules.notElim(outside, _))
                outsideA <- rules.notIntro(inATerm, falsity)
                result <- intoNeg(x, a, r, positive, outsideA)
              } yield result
            }
            result <- rules.disch(both.conclusion, reached).flatMap(rules.gen(b, _)).flatMap(rules.gen(a, _))
          } yield result

          open <- for {
            inA <- inNegTerm(x, a).flatMap(assume)
            goal <- inNegTerm(x, b).flatMap(ib => lt(a, b).flatMap(ab => logic.mkConj(ib, ab))).flatMap(body => lift(Term.abs(b, body)))
            reached <- choosing(inA, r) { pair =>
              for {
                inner <- halves(pair)
                (positive, outside) = inner
                between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(zero, r))).flatMap(rules.mp(_, positive))
                result <- choosing(between, s) { pairS =>
                  for {
                    partsS <- halves(pairS)
                    (sPositive, sBelow) = partsS
                    higher <- plus(a, s)
                    rest <- difference(r, s)
                    negatedS <- minus(s)
                    restPositive <- lessShifted(sBelow, negatedS).flatMap(rearranged(_, zero, rest))
                    kept <- reflected(higher, rest).flatMap(carriedNot(outside, _))
                    inHigher <- intoNeg(x, higher, rest, restPositive, kept)
                    raised <- lessShifted(sPositive, a).flatMap(rearranged(_, a, higher))
                    both <- rules.conjIntro(inHigher, raised)
                    result <- rules.existsIntro(goal, higher, both)
                  } yield result
                }
              } yield result
            }
            result <- rules.disch(inA.conclusion, reached).flatMap(rules.gen(a, _))
          } yield result

          isCut <- sets.closedFrom(set, inhabited, proper, closed, open)
          result <- rules.gen(x, isCut)
        } yield result

      /** [[Cut.NegMembers]]: the definition, then the characterisation at a set that is a cut. */
      private def negationMembers(isCut: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          unfolded <- Conv.unfold(negationDefinition, List(x))
          carriedDest <- dest.flatMap(Conv.apTerm(_, unfolded))
          set <- negSet(x)
          atSet <- rules.spec(x, isCut)
          back <- rules.spec(set, rebuilds).flatMap(rules.mp(_, atSet))
          result <- Conv.trans(carriedDest, back).flatMap(rules.gen(x, _))
        } yield result

      /** `|- dest_cut (CUT_NEG of) at = ?r. 0 < r /\ ~(dest_cut of (-at + -r))`. */
      private def inNeg(negMembers: Kernel.Thm, of: Term, at: Term): Either[LogicError, Kernel.Thm] =
        for {
          atCut <- rules.spec(of, negMembers)
          applied <- Conv.apThm(atCut, at)
          reduced <- rightOf(applied).flatMap(Conv.betaRoot)
          result <- Conv.trans(applied, reduced)
        } yield result

      /**
       * [[Cut.AddNegation]]. A member of `x + -x` has a witness `p` in `x` and `r > 0` leaving
       * `p - u - r` outside `x`, so `p < p - u - r` and `u < -r < 0`. Conversely, for `u < 0` pick
       * `h` strictly between `0` and `-u`: it is enough that some member `p` has `p + h` outside,
       * with `r = -u - h`. If none had, induction would put `e + n * h` in `x` for every `n` from a
       * member `e`, and `RAT_ARCHIMEDES` at `(a - e) / h` for a non-member `a` would put `a` there too.
       */
      private def inverseFact(addMembers: Kernel.Thm, negMembers: Kernel.Thm, escape: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          sum <- addition
          negation <- read(Negation, Type.fun(cutType, cutType))
          ofRational <- read(OfRational, Type.fun(Fraction.Classes, cutType))
          zero <- read(Fraction.Zero, Fraction.Classes)
          number <- read(Fraction.OfNumber, Type.fun(TyApp(Natural.TypeName, Nil), Fraction.Classes))
          multiply <- binaryConstantRat(Fraction.Multiplication)
          inverseOf <- read(Fraction.Inverse, Type.fun(Fraction.Classes, Fraction.Classes))
          negX <- app(negation, x)
          left <- app(sum, x, negX)
          zeroCut <- app(ofRational, zero)
          clausesX <- clausesOf(x)
          destX <- dest.flatMap(app(_, x))
          ofNumberZero <- fact(Fraction.OfNumberZero)
          ofNumberSuccessor <- fact(Fraction.OfNumberSuccessor)
          n = Term.variable("n", TyApp(Natural.TypeName, Nil))

          result <- equalCuts(left, zeroCut)(
            held =>
              for {
                existential <- fromSum(addMembers, held)
                result <- choosing(existential, p) { pair =>
                  for {
                    parts <- halves(pair)
                    (inP, inNegRest) = parts
                    rest <- difference(u, p)
                    negExistential <- inNeg(negMembers, x, rest).flatMap(eqMp(_, inNegRest))
                    result <- choosing(negExistential, r) { pairR =>
                      for {
                        partsR <- halves(pairR)
                        (positive, outside) = partsR
                        above <- belowOutside(clausesX, destX, inP, outside)
                        kept <- reflected(rest, r)
                        shift <- plus(rest, r)
                        uPlusR <- plus(u, r)
                        sumBelow <- lessShifted(above, shift).flatMap(rearranged(_, uPlusR, zero))
                        uBelow <- lessShifted(positive, u).flatMap(rearranged(_, u, uPlusR))
                        less <- lessTransitive(uBelow, sumBelow)
                        result <- memberOf(members, zero, u).flatMap(Conv.sym).flatMap(eqMp(_, less))
                      } yield result
                    }
                  } yield result
                }
              } yield result,
            held =>
              for {
                negative <- memberOf(members, zero, u).flatMap(eqMp(_, held))
                negatedU <- minus(u)
                positiveU <- lessShifted(negative, negatedU).flatMap(rearranged(_, zero, negatedU))
                between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(zero, negatedU))).flatMap(rules.mp(_, positiveU))
                goalTerm <- dest.flatMap(app(_, left, u))
                result <- choosing(between, f) { pairH =>
                  for {
                    partsH <- halves(pairH)
                    (hPositive, hBelow) = partsH
                    // Some member `p` has `p + h` outside, and the witness `r = -u - h` works for it.
                    result <- choosing(clausesX.inhabited, e) { inE =>
                      for {
                        escaped <- rules.specAll(escape, List(x, e, f)).flatMap(rules.mp(_, inE)).flatMap(rules.mp(_, hPositive))
                        result <- choosing(escaped, p) { triple =>
                          for {
                            parts <- halves(triple)
                            (inP, farther) = parts
                            outside <- rules.conjElim2(farther)
                            rest <- difference(u, p)
                            radius <- difference(negatedU, f)
                            negatedH <- minus(f)
                            radiusPositive <- lessShifted(hBelow, negatedH).flatMap(rearranged(_, zero, radius))
                            kept <- reflected(rest, radius).flatMap(carriedNot(outside, _))
                            inNegRest <- intoNeg(x, rest, radius, radiusPositive, kept)
                              .flatMap(ex => inNeg(negMembers, x, rest).flatMap(Conv.sym).flatMap(eqMp(_, ex)))
                            inside <- intoSum(x, negX, u, p, inP, inNegRest)
                            result <- toSum(addMembers, x, negX, u, inside)
                          } yield result
                        }
                      } yield result
                    }
                  } yield result
                }
              } yield result
          ).flatMap(rules.gen(x, _))
        } yield result

      private def binaryConstantRat(name: String): Either[LogicError, Term] =
        read(name, Type.fun(Fraction.Classes, Type.fun(Fraction.Classes, Fraction.Classes)))

      /**
       * [[Cut.Escape]]. From a member `e` and a step `f > 0`, some member `p` at least `e` has `p + f`
       * outside the cut. Otherwise induction puts `e + n * f` in the cut for every `n`, since each of
       * those is at least `e`, and `RAT_ARCHIMEDES` at `(a - e) / f` for a non-member `a` puts `a`
       * there too. This is where the rationals being Archimedean reaches the cuts, once, for both
       * inverses.
       */
      private def escapeFact: Either[LogicError, Kernel.Thm] =
        for {
          clausesX <- clausesOf(x)
          destX <- dest.flatMap(app(_, x))
          zero <- read(Fraction.Zero, Fraction.Classes)
          number <- read(Fraction.OfNumber, Type.fun(TyApp(Natural.TypeName, Nil), Fraction.Classes))
          multiply <- binaryConstantRat(Fraction.Multiplication)
          inverseOf <- read(Fraction.Inverse, Type.fun(Fraction.Classes, Fraction.Classes))
          ofNumberZero <- fact(Fraction.OfNumberZero)
          ofNumberSuccessor <- fact(Fraction.OfNumberSuccessor)
          ofNumberNonNeg <- fact(Fraction.OfNumberNonNegative)
          n = Term.variable("n", TyApp(Natural.TypeName, Nil))

          inETerm <- member(x, e)
          inE <- assume(inETerm)
          positiveTerm <- lt(zero, f)
          positive <- assume(positiveTerm)
          stepped <- plus(p, f)
          body <- for {
            inP <- member(x, p)
            atLeast <- le(e, p)
            outside <- member(x, stepped).flatMap(logic.mkNot)
            rest <- logic.mkConj(atLeast, outside)
            result <- logic.mkConj(inP, rest)
          } yield result
          goal <- logic.mkExists(p, body)
          predicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
          viaGoal <- assume(goal)

          viaNone <- for {
            notGoal <- logic.mkNot(goal).flatMap(assume)
            steps <- for {
              inPTerm <- member(x, p)
              inP <- assume(inPTerm)
              atLeastTerm <- le(e, p)
              atLeast <- assume(atLeastTerm)
              inStepTerm <- member(x, stepped)
              positiveCase <- assume(inStepTerm)
              negativeCase <- for {
                outside <- logic.mkNot(inStepTerm).flatMap(assume)
                witnessed <- rules.conjIntro(atLeast, outside).flatMap(rules.conjIntro(inP, _)).flatMap(rules.existsIntro(predicate, p, _))
                result <- rules.notElim(notGoal, witnessed).flatMap(rules.falsityElim(inStepTerm, _))
              } yield result
              result <- classical.cases(inStepTerm, positiveCase, negativeCase)
                .flatMap(rules.disch(atLeastTerm, _))
                .flatMap(rules.disch(inPTerm, _))
                .flatMap(rules.gen(p, _))
            } yield result
            fNonNeg <- weakened(positive)
            /** `e <= e + OF k * f`, from `0 <= OF k` and `0 <= f`. */
            aboveE = (k: Term) =>
              for {
                numberK <- app(number, k)
                kf <- app(multiply, numberK, f)
                nonNeg <- rules.spec(k, ofNumberNonNeg)
                productNonNeg <- fact(Fraction.AtMostMul).flatMap(rules.specAll(_, List(numberK, f))).flatMap(rules.mp(_, nonNeg)).flatMap(rules.mp(_, fNonNeg))
                shifted <- fact(Fraction.AtMostAdd).flatMap(rules.specAll(_, List(zero, kf, e))).flatMap(rules.mp(_, productNonNeg))
                target <- plus(e, kf)
                result <- rearranged(shifted, e, target)
              } yield result
            falsity <- choosing(clausesX.proper, a) { notA =>
              for {
                walked <- proposition("!n:num. dest_cut x (RAT_ADD e (RAT_MUL (RAT_OF_NUM n) f))")
                driver = Induct.withCloser(logic, ring.prove, induction)
                minusF <- minus(f)
                everywhere <- driver.proveBy(
                  walked,
                  base =>
                    base match {
                      case App(_, target) => carriedUnder(inE, target, List(ofNumberZero -> minusF))
                      case other => Left(NotOfForm("a membership", other))
                    },
                  step =>
                    for {
                      reached <- pointOf(step.hypothesis)
                      bound <- aboveE(step.variable)
                      next <- rules.spec(reached, steps).flatMap(rules.mp(_, step.hypothesis)).flatMap(rules.mp(_, bound))
                      successor <- rules.spec(step.variable, ofNumberSuccessor)
                      target <- step.goal match {
                        case App(_, at) => Right(at)
                        case other => Left(NotOfForm("a membership", other))
                      }
                      result <- carriedUnder(next, target, List(successor -> minusF))
                    } yield result
                )
                gap <- difference(a, e)
                inverseF <- app(inverseOf, f)
                ratio <- app(multiply, gap, inverseF)
                bounded <- fact(Fraction.Archimedes).flatMap(rules.spec(ratio, _))
                result <- choosing(bounded, n) { atMost =>
                  for {
                    scaled <- fact(Fraction.MulLeftMonotone)
                      .flatMap(law => binary(atMost.conclusion).flatMap(sides => rules.specAll(law, List(f, sides._1, sides._2))))
                      .flatMap(rules.mp(_, fNonNeg))
                      .flatMap(rules.mp(_, atMost))
                    unit <- positiveNonZero(positive)
                      .flatMap(nonZero => fact(Fraction.MulInverse).flatMap(rules.spec(f, _)).flatMap(rules.mp(_, nonZero)))
                    sides <- binary(scaled.conclusion)
                    gapIs <- ring.consequence(sides._1, gap, List(unit -> gap))
                    gapBelow <- compared(scaled, gapIs, Conv.refl(sides._2))
                    moved <- fact(Fraction.AtMostAdd).flatMap(rules.specAll(_, List(gap, sides._2, e))).flatMap(rules.mp(_, gapBelow))
                    reachedN <- rules.spec(n, everywhere)
                    far <- pointOf(reachedN)
                    aBelow <- rearranged(moved, a, far)
                    inA <- sets.downwardsAtMost(clausesX, destX, a, far, reachedN, aBelow)
                    result <- rules.notElim(notA, inA)
                  } yield result
                }
              } yield result
            }
            result <- rules.falsityElim(goal, falsity)
          } yield result

          result <- classical.cases(goal, viaGoal, viaNone)
            .flatMap(rules.disch(positiveTerm, _))
            .flatMap(rules.disch(inETerm, _))
            .flatMap(rules.gen(f, _))
            .flatMap(rules.gen(e, _))
            .flatMap(rules.gen(x, _))
        } yield result

      /** [[Cut.AddNonNegative]]: a negative `u` splits as `a + (u - a)` with both halves negative. */
      private def addNonNegativeFact(addMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          zero <- read(Fraction.Zero, Fraction.Classes)
          zeroCut <- read(OfRational, Type.fun(Fraction.Classes, cutType)).flatMap(app(_, zero))
          atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
          hx <- app(atMost, zeroCut, x).flatMap(assume)
          hy <- app(atMost, zeroCut, y).flatMap(assume)
          sumCut <- addition.flatMap(app(_, x, y))
          order <- included(zeroCut, sumCut) { inZero =>
            for {
              negative <- memberOf(members, zero, u).flatMap(eqMp(_, inZero))
              between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(u, zero))).flatMap(rules.mp(_, negative))
              result <- choosing(between, a) { pair =>
                for {
                  parts <- halves(pair)
                  (uBelowA, aNegative) = parts
                  inX <- memberOf(members, zero, a).flatMap(Conv.sym).flatMap(eqMp(_, aNegative)).flatMap(inside(hx, a, _))
                  rest <- difference(u, a)
                  negatedA <- minus(a)
                  restNegative <- lessShifted(uBelowA, negatedA).flatMap(rearranged(_, rest, zero))
                  inY <- memberOf(members, zero, rest).flatMap(Conv.sym).flatMap(eqMp(_, restNegative)).flatMap(inside(hy, rest, _))
                  witnessed <- intoSum(x, y, u, a, inX, inY)
                  result <- toSum(addMembers, x, y, u, witnessed)
                } yield result
              }
            } yield result
          }
          result <- rules.disch(hy.conclusion, order)
            .flatMap(rules.disch(hx.conclusion, _))
            .flatMap(rules.gen(y, _))
            .flatMap(rules.gen(x, _))
        } yield result

      /**
       * The product on the non-negative cone. Every argument here is about a membership of the core,
       * `r < 0 \/ ?p q. p in x /\ q in y /\ 0 < p /\ 0 < q /\ r < p * q`, taken apart by [[fromCore]]
       * and put together by [[intoCore]], with the rationals' strict monotonicity doing the arithmetic.
       */
      private final case class Products(addMembers: Kernel.Thm, addNonNegative: Kernel.Thm, escape: Kernel.Thm) {
        private val c1 = Term.variable("c1", Fraction.Classes)
        private val c2 = Term.variable("c2", Fraction.Classes)
        private val c3 = Term.variable("c3", Fraction.Classes)
        private val c4 = Term.variable("c4", Fraction.Classes)
        private val c5 = Term.variable("c5", Fraction.Classes)
        /** The larger member [[inSumOf]] picks, apart from every witness a caller may hand it. */
        private val c6 = Term.variable("c6", Fraction.Classes)
        private val c7 = Term.variable("c7", Fraction.Classes)

        private def zero: Either[LogicError, Term] = read(Fraction.Zero, Fraction.Classes)
        private def one: Either[LogicError, Term] = read(Fraction.One, Fraction.Classes)
        private def ofRational(q: Term): Either[LogicError, Term] = read(OfRational, Type.fun(Fraction.Classes, cutType)).flatMap(app(_, q))
        private def product(left: Term, right: Term): Either[LogicError, Term] =
          read(PosMul, Type.fun(cutType, Type.fun(cutType, cutType))).flatMap(app(_, left, right))
        private def nonNegative(cut: Term): Either[LogicError, Term] =
          for {
            atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
            zeroCut <- zero.flatMap(ofRational)
            result <- app(atMost, zeroCut, cut)
          } yield result

        private def coreMemberTerm(left: Term, right: Term, at: Term): Either[LogicError, Term] =
          substituted(CoreMemberText, None, Map(x -> left, y -> right, r -> at))
        private def coreSet(left: Term, right: Term): Either[LogicError, Term] =
          substituted(CoreSetText, Some(setType), Map(x -> left, y -> right))

        /** `0 <= c` and `at < 0` give `dest_cut c at`. */
        private def holdsNegative(nonNeg: Kernel.Thm, less: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            at <- binary(less.conclusion).map(_._1)
            zeroTerm <- zero
            inZero <- memberOf(members, zeroTerm, at).flatMap(Conv.sym).flatMap(eqMp(_, less))
            result <- inside(nonNeg, at, inZero)
          } yield result

        /** `0 <= c` and `~(dest_cut c a)` give `0 <= a`. */
        private def outsideNonNegative(nonNeg: Kernel.Thm, outside: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          outside.conclusion match {
            case App(_, App(_, at)) =>
              for {
                zeroTerm <- zero
                lessTerm <- lt(at, zeroTerm)
                less <- assume(lessTerm)
                falsity <- holdsNegative(nonNeg, less).flatMap(rules.notElim(outside, _))
                notLessThm <- rules.notIntro(lessTerm, falsity)
                result <- notLess(notLessThm)
              } yield result
            case other => Left(NotOfForm("a negated membership", other))
          }

        private def intoCoreNegative(left: Term, right: Term, at: Term, less: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            target <- coreMemberTerm(left, right, at)
            disjuncts <- logic.destDisj(target).toRight(NotOfForm("a disjunction", target))
            result <- rules.disjIntro1(disjuncts._2, less)
          } yield result

        private def intoCore(
          left: Term, right: Term, at: Term, pv: Term, qv: Term,
          inP: Kernel.Thm, inQ: Kernel.Thm, pPositive: Kernel.Thm, qPositive: Kernel.Thm, less: Kernel.Thm
        ): Either[LogicError, Kernel.Thm] =
          for {
            target <- coreMemberTerm(left, right, at)
            disjuncts <- logic.destDisj(target).toRight(NotOfForm("a disjunction", target))
            predicateP <- logic.destExistsPredicate(disjuncts._2).toRight(NotOfForm("an existential", disjuncts._2))
            inner <- app(predicateP, pv).flatMap(Conv.betaRoot).flatMap(rightOf)
            predicateQ <- logic.destExistsPredicate(inner).toRight(NotOfForm("an existential", inner))
            tail <- rules.conjIntro(qPositive, less)
            third <- rules.conjIntro(pPositive, tail)
            second <- rules.conjIntro(inQ, third)
            all <- rules.conjIntro(inP, second)
            withQ <- rules.existsIntro(predicateQ, qv, all)
            withP <- rules.existsIntro(predicateP, pv, withQ)
            result <- rules.disjIntro2(disjuncts._1, withP)
          } yield result

        /** A membership of the core taken apart: the negative case, or witnesses `pv`, `qv` and five facts. */
        private def fromCore(held: Kernel.Thm, pv: FVar, qv: FVar)(
          negative: Kernel.Thm => Either[LogicError, Kernel.Thm],
          positive: (Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm, Kernel.Thm) => Either[LogicError, Kernel.Thm]
        ): Either[LogicError, Kernel.Thm] =
          for {
            parts <- logic.destDisj(held.conclusion).toRight(NotOfForm("a disjunction", held.conclusion))
            negativeCase <- assume(parts._1).flatMap(negative)
            positiveCase <- assume(parts._2).flatMap(existential =>
              choosing(existential, pv) { inner =>
                choosing(inner, qv) { all =>
                  for {
                    h1 <- halves(all)
                    (inP, rest1) = h1
                    h2 <- halves(rest1)
                    (inQ, rest2) = h2
                    h3 <- halves(rest2)
                    (pPositive, rest3) = h3
                    h4 <- halves(rest3)
                    (qPositive, less) = h4
                    result <- positive(inP, inQ, pPositive, qPositive, less)
                  } yield result
                }
              })
            result <- rules.disjElim(held, negativeCase, positiveCase)
          } yield result

        /** `|- dest_cut (CUT_PMUL left right) at = (the core's membership)`, from the members fact at the pair. */
        private def inCore(atPair: Kernel.Thm, at: Term): Either[LogicError, Kernel.Thm] =
          for {
            applied <- Conv.apThm(atPair, at)
            reduced <- rightOf(applied).flatMap(Conv.betaRoot)
            result <- Conv.trans(applied, reduced)
          } yield result
        private def outOfCore(atPair: Kernel.Thm, held: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          pointOf(held).flatMap(at => inCore(atPair, at)).flatMap(eqMp(_, held))
        private def backIntoCore(atPair: Kernel.Thm, at: Term, core: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          inCore(atPair, at).flatMap(Conv.sym).flatMap(eqMp(_, core))


        /**
         * A positive member of a cut known to be above zero: `~(c <= 0)` gives, by `NOT_FORALL`, a
         * member `t` outside zero's cut, so `0 <= t`, and the cut's lack of a greatest element gives a
         * larger member, which is positive. Handed to `body` as a witness under an elimination.
         */
        private def withPositiveMember(cut: Term, clauses: Clauses, positive: Kernel.Thm, first: FVar, second: FVar)(
          body: (FVar, Kernel.Thm, Kernel.Thm) => Either[LogicError, Kernel.Thm]
        ): Either[LogicError, Kernel.Thm] =
          for {
            zeroTerm <- zero
            zeroCut <- ofRational(zeroTerm)
            notAtMost <- Conv.unfold(lessThanDefinition, List(zeroCut, cut)).flatMap(eqMp(_, positive))
            opened <- atMostOpened(cut, zeroCut)
            notAll <- notAtMost.conclusion match {
              case App(not, _) => Conv.apTerm(not, opened).flatMap(eqMp(_, notAtMost))
              case other => Left(NotOfForm("a negation", other))
            }
            inclusion <- rightOf(opened)
            predicate <- logic.destForallPredicate(inclusion).toRight(NotOfForm("a universal", inclusion))
            notForall <- classical.fact(Classical.NotForall)
              .map(Kernel.instType(Map(Classical.TypeVariable -> Fraction.Classes), _))
              .flatMap(rules.spec(predicate, _))
            reduced <- Conv.betaNormalise(notForall.conclusion).flatMap(eqMp(_, notForall))
            witness <- rules.mp(reduced, notAll)
            result <- choosing(witness, first) { failure =>
              for {
                inCutTerm <- member(cut, first)
                inZeroTerm <- member(zeroCut, first)
                notInZero <- for {
                  inZero <- assume(inZeroTerm)
                  implication <- rules.disch(inCutTerm, inZero)
                  falsity <- rules.notElim(failure, implication)
                  result <- rules.notIntro(inZeroTerm, falsity)
                } yield result
                inCut <- for {
                  positiveCase <- assume(inCutTerm)
                  notIn <- logic.mkNot(inCutTerm).flatMap(assume)
                  implication <- assume(inCutTerm)
                    .flatMap(rules.notElim(notIn, _))
                    .flatMap(rules.falsityElim(inZeroTerm, _))
                    .flatMap(rules.disch(inCutTerm, _))
                  negativeCase <- rules.notElim(failure, implication).flatMap(rules.falsityElim(inCutTerm, _))
                  result <- classical.cases(inCutTerm, positiveCase, negativeCase)
                } yield result
                notNegative <- for {
                  lessTerm <- lt(first, zeroTerm)
                  less <- assume(lessTerm)
                  falsity <- memberOf(members, zeroTerm, first).flatMap(Conv.sym).flatMap(eqMp(_, less)).flatMap(rules.notElim(notInZero, _))
                  result <- rules.notIntro(lessTerm, falsity)
                } yield result
                nonNeg <- notLess(notNegative)
                higher <- rules.spec(first, clauses.open).flatMap(rules.mp(_, inCut))
                result <- choosing(higher, second) { pair =>
                  for {
                    parts <- halves(pair)
                    (inHigher, below) = parts
                    higherPositive <- atMostThenLess(nonNeg, below)
                    result <- body(second, inHigher, higherPositive)
                  } yield result
                }
              } yield result
            }
          } yield result

        /** [[Cut.PosMulPositive]]: zero is in the core, below the product of two positive members. */
        private def positiveFact(coreMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            zeroTerm <- zero
            zeroCut <- ofRational(zeroTerm)
            lessConst <- read(LessThan, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
            px <- app(lessConst, zeroCut, x).flatMap(assume)
            py <- app(lessConst, zeroCut, y).flatMap(assume)
            hx <- nonNegOfPositive(x, px)
            hy <- nonNegOfPositive(y, py)
            clausesX <- clausesOf(x)
            clausesY <- clausesOf(y)
            atPair <- membersAt(coreMembers, x, y, hx, hy)
            xy <- product(x, y)
            atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
            result <- withPositiveMember(x, clausesX, px, c1, c2) { (p, inP, pPositive) =>
              withPositiveMember(y, clausesY, py, c3, c4) { (q, inQ, qPositive) =>
                for {
                  productPositive <- timesPositive(pPositive, qPositive)
                  zeroIn <- intoCore(x, y, zeroTerm, p, q, inP, inQ, pPositive, qPositive, productPositive)
                    .flatMap(backIntoCore(atPair, zeroTerm, _))
                  belowTerm <- app(atMost, xy, zeroCut)
                  below <- assume(belowTerm)
                  inZero <- inside(below, zeroTerm, zeroIn)
                  loop <- memberOf(members, zeroTerm, zeroTerm).flatMap(eqMp(_, inZero))
                  falsity <- irreflexive(zeroTerm).flatMap(rules.notElim(_, loop))
                  notBelow <- rules.notIntro(belowTerm, falsity)
                  result <- Conv.unfold(lessThanDefinition, List(zeroCut, xy)).flatMap(Conv.sym).flatMap(eqMp(_, notBelow))
                } yield result
              }
            }
            discharged <- rules.disch(py.conclusion, result)
              .flatMap(rules.disch(px.conclusion, _))
              .flatMap(rules.gen(y, _))
              .flatMap(rules.gen(x, _))
          } yield discharged


        private def pinvMemberTerm(of: Term, at: Term): Either[LogicError, Term] =
          substituted(PinvMemberText, None, Map(x -> of, r -> at))
        private def pinvSet(of: Term): Either[LogicError, Term] = substituted(PinvSetText, Some(setType), Map(x -> of))
        private def inverseOf(t: Term): Either[LogicError, Term] =
          read(Fraction.Inverse, Type.fun(Fraction.Classes, Fraction.Classes)).flatMap(app(_, t))
        private def inversePositive(positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          binary(positive.conclusion).flatMap(ab => fact(Fraction.InversePositive).flatMap(rules.spec(ab._2, _)).flatMap(rules.mp(_, positive)))
        /** `|- t * RAT_INV t = 1` for `0 < t`. */
        private def unitAt(positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            t <- binary(positive.conclusion).map(_._2)
            nonZero <- positiveNonZero(positive)
            result <- fact(Fraction.MulInverse).flatMap(rules.spec(t, _)).flatMap(rules.mp(_, nonZero))
          } yield result

        private def intoPinvLow(of: Term, at: Term, atMost: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            target <- pinvMemberTerm(of, at)
            disjuncts <- logic.destDisj(target).toRight(NotOfForm("a disjunction", target))
            result <- rules.disjIntro1(disjuncts._2, atMost)
          } yield result

        private def intoPinv(of: Term, at: Term, sv: Term, outside: Kernel.Thm, sPositive: Kernel.Thm, below: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            target <- pinvMemberTerm(of, at)
            disjuncts <- logic.destDisj(target).toRight(NotOfForm("a disjunction", target))
            predicate <- logic.destExistsPredicate(disjuncts._2).toRight(NotOfForm("an existential", disjuncts._2))
            tail <- rules.conjIntro(sPositive, below)
            all <- rules.conjIntro(outside, tail)
            witnessed <- rules.existsIntro(predicate, sv, all)
            result <- rules.disjIntro2(disjuncts._1, witnessed)
          } yield result

        /** A membership of `CUT_PINV` taken apart: at most zero, or a witness `sv` and three facts. */
        private def fromPinv(held: Kernel.Thm, sv: FVar)(
          low: Kernel.Thm => Either[LogicError, Kernel.Thm],
          high: (Kernel.Thm, Kernel.Thm, Kernel.Thm) => Either[LogicError, Kernel.Thm]
        ): Either[LogicError, Kernel.Thm] =
          for {
            parts <- logic.destDisj(held.conclusion).toRight(NotOfForm("a disjunction", held.conclusion))
            lowCase <- assume(parts._1).flatMap(low)
            highCase <- assume(parts._2).flatMap(existential =>
              choosing(existential, sv) { all =>
                for {
                  h1 <- halves(all)
                  (outside, rest) = h1
                  h2 <- halves(rest)
                  (sPositive, below) = h2
                  result <- high(outside, sPositive, below)
                } yield result
              })
            result <- rules.disjElim(held, lowCase, highCase)
          } yield result

        private def positiveHypothesis(cut: Term): Either[LogicError, Kernel.Thm] =
          for {
            lessConst <- read(LessThan, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
            zeroCut <- zero.flatMap(ofRational)
            result <- app(lessConst, zeroCut, cut).flatMap(assume)
          } yield result

        /**
         * [[Cut.PosInverseIsCut]]. It holds zero; it does not hold `1 / p` for a positive member `p`,
         * since a positive non-member `s` is above `p`, so `s / p > 1`; it is closed downwards because
         * `s > 0`; and it has no greatest element, because `r * s < 1` leaves room below `1 / s`.
         */
        private def pinvIsCut: Either[LogicError, Kernel.Thm] =
          for {
            px <- positiveHypothesis(x)
            clausesX <- clausesOf(x)
            destX <- dest.flatMap(app(_, x))
            zeroTerm <- zero
            oneTerm <- one
            set <- pinvSet(x)
            body <- sets.unfolded(set).flatMap(rightOf)
            clauseTerms <- body match {
              case App(App(_, inhabited), App(App(_, proper), App(App(_, closed), open))) => Right((inhabited, proper, closed, open))
              case other => Left(NotOfForm("the four clauses of IS_CUT", other))
            }
            (inhabitedTerm, properTerm, _, _) = clauseTerms

            inhabited <- for {
              reflexive <- fact(Fraction.AtMostReflexive).flatMap(rules.spec(zeroTerm, _))
              member <- intoPinvLow(x, zeroTerm, reflexive)
              predicate <- logic.destExistsPredicate(inhabitedTerm).toRight(NotOfForm("an existential", inhabitedTerm))
              result <- rules.existsIntro(predicate, zeroTerm, member)
            } yield result

            proper <- withPositiveMember(x, clausesX, px, c1, c2) { (pv, inP, pPositive) =>
              for {
                t <- inverseOf(pv)
                tPositive <- inversePositive(pPositive)
                unit <- unitAt(pPositive)
                memberTerm <- pinvMemberTerm(x, t)
                held <- assume(memberTerm)
                falsity <- fromPinv(held, c3)(
                  atMostZero => contradicts(tPositive, atMostZero),
                  (outside, _, below) =>
                    for {
                      pBelowS <- belowOutside(clausesX, destX, inP, outside)
                      scaled <- timesLeft(tPositive, pBelowS)
                      sides <- binary(scaled.conclusion)
                      oneIs <- ring.consequence(sides._1, oneTerm, List(unit -> oneTerm))
                      oneBelow <- compared(scaled, oneIs, Conv.refl(sides._2))
                      loop <- lessTransitive(oneBelow, below)
                      result <- irreflexive(oneTerm).flatMap(rules.notElim(_, loop))
                    } yield result
                )
                notIn <- rules.notIntro(memberTerm, falsity)
                predicate <- logic.destExistsPredicate(properTerm).toRight(NotOfForm("an existential", properTerm))
                result <- rules.existsIntro(predicate, t, notIn)
              } yield result
            }

            closed <- for {
              inBTerm <- pinvMemberTerm(x, b)
              less <- lt(a, b)
              both <- logic.mkConj(inBTerm, less).flatMap(assume)
              parts <- halves(both)
              (inB, ab) = parts
              reached <- fromPinv(inB, c3)(
                atMostZero => weakened(ab).flatMap(sets.rationals.transitive(_, atMostZero)).flatMap(intoPinvLow(x, a, _)),
                (outside, sPositive, below) =>
                  for {
                    as <- times(a, c3)
                    bs <- times(b, c3)
                    scaled <- timesLeft(sPositive, ab).flatMap(rearranged(_, as, bs))
                    result <- lessTransitive(scaled, below).flatMap(intoPinv(x, a, c3, outside, sPositive, _))
                  } yield result
              )
              result <- rules.disch(both.conclusion, reached).flatMap(rules.gen(b, _)).flatMap(rules.gen(a, _))
            } yield result

            open <- for {
              inA <- pinvMemberTerm(x, a).flatMap(assume)
              goal <- pinvMemberTerm(x, b).flatMap(ib => lt(a, b).flatMap(ab => logic.mkConj(ib, ab))).flatMap(body => lift(Term.abs(b, body)))
              /** Room below `1 / s`: a `b` with `b * s < 1` strictly above `lower`, for `lower < 1 / s`. */
              above = (lower: Term, lowerBelow: Kernel.Thm, sv: Term, outside: Kernel.Thm, sPositive: Kernel.Thm, atLeast: Kernel.Thm => Either[LogicError, Kernel.Thm]) =>
                for {
                  is <- inverseOf(sv)
                  unit <- unitAt(sPositive)
                  between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(lower, is))).flatMap(rules.mp(_, lowerBelow))
                  result <- choosing(between, c7) { pair =>
                    for {
                      parts <- halves(pair)
                      (lowerBelowB, bBelow) = parts
                      scaled <- timesLeft(sPositive, bBelow)
                      sides <- binary(scaled.conclusion)
                      bs <- times(c7, sv)
                      bsIs <- same(sides._1, bs)
                      oneIs <- ring.consequence(sides._2, oneTerm, List(unit -> oneTerm))
                      bsBelow <- compared(scaled, bsIs, oneIs)
                      member <- intoPinv(x, c7, sv, outside, sPositive, bsBelow)
                      aBelowB <- atLeast(lowerBelowB)
                      both <- rules.conjIntro(member, aBelowB)
                      result <- rules.existsIntro(goal, c7, both)
                    } yield result
                  }
                } yield result
              reached <- fromPinv(inA, c3)(
                atMostZero =>
                  choosing(clausesX.proper, c4) { notS =>
                    withPositiveMember(x, clausesX, px, c5, c6) { (pv, inP, pPositive) =>
                      for {
                        sPositive <- belowOutside(clausesX, destX, inP, notS).flatMap(lessTransitive(pPositive, _))
                        isPositive <- inversePositive(sPositive)
                        result <- above(zeroTerm, isPositive, c4, notS, sPositive, bPositive => atMostThenLess(atMostZero, bPositive))
                      } yield result
                    }
                  },
                (outside, sPositive, below) =>
                  for {
                    is <- inverseOf(c3)
                    isPositive <- inversePositive(sPositive)
                    unit <- unitAt(sPositive)
                    scaled <- timesLeft(isPositive, below)
                    sides <- binary(scaled.conclusion)
                    aIs <- ring.consequence(sides._1, a, List(unit -> a))
                    isIs <- same(sides._2, is)
                    aBelow <- compared(scaled, aIs, isIs)
                    result <- above(a, aBelow, c3, outside, sPositive, Right(_))
                  } yield result
              )
              result <- rules.disch(inA.conclusion, reached).flatMap(rules.gen(a, _))
            } yield result

            isCut <- sets.closedFrom(set, inhabited, proper, closed, open)
            result <- rules.disch(px.conclusion, isCut).flatMap(rules.gen(x, _))
          } yield result

        /** [[Cut.PosInverseMembers]]: the definition, then the characterisation. */
        private def pinvMembersFact(isCut: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            px <- positiveHypothesis(x)
            unfolded <- Conv.unfold(posInverseDefinition, List(x))
            carriedDest <- dest.flatMap(Conv.apTerm(_, unfolded))
            set <- pinvSet(x)
            atSet <- rules.spec(x, isCut).flatMap(rules.mp(_, px))
            back <- rules.spec(set, rebuilds).flatMap(rules.mp(_, atSet))
            result <- Conv.trans(carriedDest, back).flatMap(rules.disch(px.conclusion, _)).flatMap(rules.gen(x, _))
          } yield result

        /** [[Cut.PosInverseNonNegative]]: every negative is at most zero, so in the set. */
        private def pinvNonNegFact(inverseMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            px <- positiveHypothesis(x)
            zeroTerm <- zero
            zeroCut <- ofRational(zeroTerm)
            pinv <- read(PosInverse, Type.fun(cutType, cutType)).flatMap(app(_, x))
            atX <- rules.spec(x, inverseMembers).flatMap(rules.mp(_, px))
            order <- included(zeroCut, pinv) { inZero =>
              for {
                negative <- memberOf(members, zeroTerm, u).flatMap(eqMp(_, inZero))
                member <- weakened(negative).flatMap(intoPinvLow(x, u, _))
                result <- backIntoCore(atX, u, member)
              } yield result
            }
            result <- rules.disch(px.conclusion, order).flatMap(rules.gen(x, _))
          } yield result

        /**
         * [[Cut.PosMulInverse]]. A witness `p * q` with `q * s < 1` for a non-member `s > p` is below
         * one. Conversely for `0 <= u < 1`: take `u < λ < 1`, a positive member `p0` and the step
         * `h = p0 (1 - λ) / λ`; `CUT_ESCAPE` gives a member `p >= p0` with `s = p + h` outside, and
         * then `λ s <= p`, so `u s < p`, and density puts a `q` with `u < p q` and `q s < 1`.
         */
        private def mulPinvFact(coreMembers: Kernel.Thm, inverseMembers: Kernel.Thm, inverseNonNeg: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            px <- positiveHypothesis(x)
            hx <- nonNegOfPositive(x, px)
            clausesX <- clausesOf(x)
            destX <- dest.flatMap(app(_, x))
            zeroTerm <- zero
            oneTerm <- one
            oneCut <- ofRational(oneTerm)
            pinv <- read(PosInverse, Type.fun(cutType, cutType)).flatMap(app(_, x))
            nnInv <- rules.spec(x, inverseNonNeg).flatMap(rules.mp(_, px))
            atPair <- membersAt(coreMembers, x, pinv, hx, nnInv)
            atInverse <- rules.spec(x, inverseMembers).flatMap(rules.mp(_, px))
            positiveOne <- zeroBelowOne
            productCut <- product(x, pinv)
            result <- equalCuts(productCut, oneCut)(
              held =>
                for {
                  core <- outOfCore(atPair, held)
                  goal <- dest.flatMap(app(_, oneCut, u))
                  result <- fromCore(core, c1, c2)(
                    negative => lessTransitive(negative, positiveOne).flatMap(less => memberOf(members, oneTerm, u).flatMap(Conv.sym).flatMap(eqMp(_, less))),
                    (inP, inQ, _, qPositive, less) =>
                      for {
                        inverseHeld <- outOfCore(atInverse, inQ)
                        result <- fromPinv(inverseHeld, c3)(
                          atMostZero => contradicts(qPositive, atMostZero).flatMap(rules.falsityElim(goal, _)),
                          (outside, _, qsBelow) =>
                            for {
                              pBelowS <- belowOutside(clausesX, destX, inP, outside)
                              pq <- times(c1, c2)
                              qs <- times(c2, c3)
                              scaled <- timesLeft(qPositive, pBelowS).flatMap(rearranged(_, pq, qs))
                              uBelow <- lessTransitive(less, scaled).flatMap(lessTransitive(_, qsBelow))
                              result <- memberOf(members, oneTerm, u).flatMap(Conv.sym).flatMap(eqMp(_, uBelow))
                            } yield result
                        )
                      } yield result
                  )
                } yield result,
              held =>
                for {
                  uBelowOne <- memberOf(members, oneTerm, u).flatMap(eqMp(_, held))
                  negativeTerm <- lt(u, zeroTerm)
                  viaNegative <- assume(negativeTerm)
                    .flatMap(intoCoreNegative(x, pinv, u, _))
                    .flatMap(backIntoCore(atPair, u, _))
                  notNegative <- logic.mkNot(negativeTerm).flatMap(assume)
                  uNonNeg <- notLess(notNegative)
                  between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(u, oneTerm))).flatMap(rules.mp(_, uBelowOne))
                  viaNonNegative <- choosing(between, c1) { pairL =>
                    for {
                      partsL <- halves(pairL)
                      (uBelowL, lBelowOne) = partsL
                      lPositive <- atMostThenLess(uNonNeg, uBelowL)
                      withPositiveResult <- withPositiveMember(x, clausesX, px, c2, c3) { (p0, inP0, p0Positive) =>
                        for {
                          negatedL <- minus(c1)
                          oneMinus <- plus(oneTerm, negatedL)
                          oneMinusPositive <- lessShifted(lBelowOne, negatedL).flatMap(rearranged(_, zeroTerm, oneMinus))
                          il <- inverseOf(c1)
                          ilPositive <- inversePositive(lPositive)
                          unitL <- unitAt(lPositive)
                          p0om <- times(p0, oneMinus)
                          h <- times(p0om, il)
                          hPositive <- timesPositive(p0Positive, oneMinusPositive).flatMap(timesPositive(_, ilPositive))
                          escaped <- rules.specAll(escape, List(x, p0, h)).flatMap(rules.mp(_, inP0)).flatMap(rules.mp(_, hPositive))
                          result <- choosing(escaped, c4) { triple =>
                            for {
                              parts <- halves(triple)
                              (inP, farther) = parts
                              p0AtMost <- rules.conjElim1(farther)
                              outside <- rules.conjElim2(farther)
                              pPositive <- lessThenAtMost(p0Positive, p0AtMost)
                              sTerm <- plus(c4, h)
                              sPositive <- lessShifted(hPositive, c4).flatMap(rearranged(_, c4, sTerm)).flatMap(lessTransitive(pPositive, _))
                              // λ s <= p
                              omNonNeg <- weakened(oneMinusPositive)
                              scaledOm <- fact(Fraction.MulLeftMonotone).flatMap(rules.specAll(_, List(oneMinus, p0, c4))).flatMap(rules.mp(_, omNonNeg)).flatMap(rules.mp(_, p0AtMost))
                              scaledSides <- binary(scaledOm.conclusion)
                              lp <- times(c1, c4)
                              added <- fact(Fraction.AtMostAdd).flatMap(rules.specAll(_, List(scaledSides._1, scaledSides._2, lp))).flatMap(rules.mp(_, scaledOm))
                              addedSides <- binary(added.conclusion)
                              ls <- times(c1, sTerm)
                              omp0 <- times(oneMinus, p0)
                              minusOmp0 <- minus(omp0)
                              leftIs <- ring.consequence(addedSides._1, ls, List(unitL -> minusOmp0))
                              rightIs <- same(addedSides._2, c4)
                              key <- compared(added, leftIs, rightIs)
                              us <- times(u, sTerm)
                              usBelow <- timesLeft(sPositive, uBelowL).flatMap(rearranged(_, us, ls)).flatMap(lessThenAtMost(_, key))
                              // u / p < q < 1 / s
                              ip <- inverseOf(c4)
                              is <- inverseOf(sTerm)
                              ipPositive <- inversePositive(pPositive)
                              isPositive <- inversePositive(sPositive)
                              unitP <- unitAt(pPositive)
                              unitS <- unitAt(sPositive)
                              factorPositive <- timesPositive(ipPositive, isPositive)
                              scaled <- timesLeft(factorPositive, usBelow)
                              ratioSides <- binary(scaled.conclusion)
                              uip <- times(u, ip)
                              uipIs <- ring.consequence(ratioSides._1, uip, List(unitS -> uip))
                              isIs <- ring.consequence(ratioSides._2, is, List(unitP -> is))
                              ratioBelow <- compared(scaled, uipIs, isIs)
                              uipNonNeg <- weakened(ipPositive).flatMap(ipNonNeg =>
                                fact(Fraction.AtMostMul).flatMap(rules.specAll(_, List(u, ip))).flatMap(rules.mp(_, uNonNeg)).flatMap(rules.mp(_, ipNonNeg)))
                              choice <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(uip, is))).flatMap(rules.mp(_, ratioBelow))
                              result <- choosing(choice, c5) { pairQ =>
                                for {
                                  partsQ <- halves(pairQ)
                                  (lowerBelowQ, qBelowIs) = partsQ
                                  qPositive <- atMostThenLess(uipNonNeg, lowerBelowQ)
                                  qsScaled <- timesLeft(sPositive, qBelowIs)
                                  qsSides <- binary(qsScaled.conclusion)
                                  qs <- times(c5, sTerm)
                                  qsIs <- same(qsSides._1, qs)
                                  oneIs <- ring.consequence(qsSides._2, oneTerm, List(unitS -> oneTerm))
                                  qsBelow <- compared(qsScaled, qsIs, oneIs)
                                  inQ <- intoPinv(x, c5, sTerm, outside, sPositive, qsBelow).flatMap(backIntoCore(atInverse, c5, _))
                                  raised <- timesLeft(pPositive, lowerBelowQ)
                                  raisedSides <- binary(raised.conclusion)
                                  uIs <- ring.consequence(raisedSides._1, u, List(unitP -> u))
                                  pq <- times(c4, c5)
                                  pqIs <- same(raisedSides._2, pq)
                                  uBelow <- compared(raised, uIs, pqIs)
                                  result <- intoCore(x, pinv, u, c4, c5, inP, inQ, pPositive, qPositive, uBelow)
                                    .flatMap(backIntoCore(atPair, u, _))
                                } yield result
                              }
                            } yield result
                          }
                        } yield result
                      }
                    } yield withPositiveResult
                  }
                  result <- classical.cases(negativeTerm, viaNegative, viaNonNegative)
                } yield result
            )
            discharged <- rules.disch(px.conclusion, result).flatMap(rules.gen(x, _))
          } yield discharged

        def facts: Either[LogicError, Vector[(String, Kernel.Thm)]] =
          for {
            isCut <- coreIsCut
            coreMembers <- membersFact(isCut)
            commutative <- commutativeFact
            atZero <- zeroFact
            nonNeg <- nonNegativeFact(coreMembers)
            unit <- oneFact(coreMembers)
            associative <- associativeFact(coreMembers, nonNeg)
            distributive <- distributiveFact(coreMembers)
            positive <- positiveFact(coreMembers)
            inverseIsCut <- pinvIsCut
            inverseMembers <- pinvMembersFact(inverseIsCut)
            inverseNonNeg <- pinvNonNegFact(inverseMembers)
            mulInverse <- mulPinvFact(coreMembers, inverseMembers, inverseNonNeg)
          } yield Vector(
            (PosMulIsCut, isCut),
            (PosMulMembers, coreMembers),
            (PosMulCommutative, commutative),
            (PosMulZero, atZero),
            (PosMulNonNegative, nonNeg),
            (PosMulOne, unit),
            (PosMulAssociative, associative),
            (PosMulDistributive, distributive),
            (PosMulPositive, positive),
            (PosInverseIsCut, inverseIsCut),
            (PosInverseMembers, inverseMembers),
            (PosInverseNonNegative, inverseNonNeg),
            (PosMulInverse, mulInverse)
          )

        /** The members fact at a pair, with its two hypotheses discharged. */
        private def membersAt(coreMembers: Kernel.Thm, left: Term, right: Term, nnLeft: Kernel.Thm, nnRight: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          rules.specAll(coreMembers, List(left, right)).flatMap(rules.mp(_, nnLeft)).flatMap(rules.mp(_, nnRight))

        /**
         * [[Cut.PosMulIsCut]]. Inhabited by `-1`; not everything, since for non-members `e` of `x` and
         * `f` of `y`, both at least zero because the cuts hold every negative, `e * f` is neither
         * negative nor below `p * q` for members `p < e` and `q < f`; closed downwards trivially; and
         * without a greatest element because a larger member `p'` of `x` gives `p * q < p' * q`.
         */
        private def coreIsCut: Either[LogicError, Kernel.Thm] =
          for {
            hx <- nonNegative(x).flatMap(assume)
            hy <- nonNegative(y).flatMap(assume)
            clausesX <- clausesOf(x)
            clausesY <- clausesOf(y)
            destX <- dest.flatMap(app(_, x))
            zeroTerm <- zero
            oneTerm <- one
            set <- coreSet(x, y)
            body <- sets.unfolded(set).flatMap(rightOf)
            clauseTerms <- body match {
              case App(App(_, inhabited), App(App(_, proper), App(App(_, closed), open))) => Right((inhabited, proper, closed, open))
              case other => Left(NotOfForm("the four clauses of IS_CUT", other))
            }
            (inhabitedTerm, properTerm, _, _) = clauseTerms

            inhabited <- for {
              minusOne <- minus(oneTerm)
              negative <- below(zeroTerm).flatMap(rearranged(_, minusOne, zeroTerm))
              member <- intoCoreNegative(x, y, minusOne, negative)
              predicate <- logic.destExistsPredicate(inhabitedTerm).toRight(NotOfForm("an existential", inhabitedTerm))
              result <- rules.existsIntro(predicate, minusOne, member)
            } yield result

            proper <- choosing(clausesX.proper, e) { notE =>
              choosing(clausesY.proper, f) { notF =>
                for {
                  eNonNeg <- outsideNonNegative(hx, notE)
                  fNonNeg <- outsideNonNegative(hy, notF)
                  ef <- times(e, f)
                  efNonNeg <- fact(Fraction.AtMostMul).flatMap(rules.specAll(_, List(e, f))).flatMap(rules.mp(_, eNonNeg)).flatMap(rules.mp(_, fNonNeg))
                  memberTerm <- coreMemberTerm(x, y, ef)
                  held <- assume(memberTerm)
                  falsity <- fromCore(held, c1, c2)(
                    negative => contradicts(negative, efNonNeg),
                    (inP, inQ, pPositive, qPositive, less) =>
                      for {
                        pBelow <- belowOutside(clausesX, destX, inP, notE)
                        destY <- dest.flatMap(app(_, y))
                        qBelow <- belowOutside(clausesY, destY, inQ, notF)
                        bound <- productBelow(pPositive, pBelow, qPositive, qBelow)
                        loop <- lessTransitive(less, bound)
                        result <- irreflexive(ef).flatMap(rules.notElim(_, loop))
                      } yield result
                  )
                  notIn <- rules.notIntro(memberTerm, falsity)
                  predicate <- logic.destExistsPredicate(properTerm).toRight(NotOfForm("an existential", properTerm))
                  result <- rules.existsIntro(predicate, ef, notIn)
                } yield result
              }
            }

            closed <- for {
              inBTerm <- coreMemberTerm(x, y, b)
              less <- lt(a, b)
              both <- logic.mkConj(inBTerm, less).flatMap(assume)
              parts <- halves(both)
              (inB, ab) = parts
              reached <- fromCore(inB, c1, c2)(
                negative => lessTransitive(ab, negative).flatMap(intoCoreNegative(x, y, a, _)),
                (inP, inQ, pPositive, qPositive, less2) =>
                  lessTransitive(ab, less2).flatMap(intoCore(x, y, a, c1, c2, inP, inQ, pPositive, qPositive, _))
              )
              result <- rules.disch(both.conclusion, reached).flatMap(rules.gen(b, _)).flatMap(rules.gen(a, _))
            } yield result

            open <- for {
              inA <- coreMemberTerm(x, y, a).flatMap(assume)
              goal <- coreMemberTerm(x, y, b).flatMap(ib => lt(a, b).flatMap(ab => logic.mkConj(ib, ab))).flatMap(body => lift(Term.abs(b, body)))
              reached <- fromCore(inA, c1, c2)(
                negative =>
                  for {
                    between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(a, zeroTerm))).flatMap(rules.mp(_, negative))
                    result <- choosing(between, c3) { pair =>
                      for {
                        parts <- halves(pair)
                        (aBelow, stillNegative) = parts
                        member <- intoCoreNegative(x, y, c3, stillNegative)
                        both <- rules.conjIntro(member, aBelow)
                        result <- rules.existsIntro(goal, c3, both)
                      } yield result
                    }
                  } yield result,
                (inP, inQ, pPositive, qPositive, less) =>
                  for {
                    higher <- rules.spec(c1, clausesX.open).flatMap(rules.mp(_, inP))
                    result <- choosing(higher, c3) { pair =>
                      for {
                        parts <- halves(pair)
                        (inHigher, pBelow) = parts
                        pq <- times(c1, c2)
                        higherQ <- times(c3, c2)
                        raised <- timesLeft(qPositive, pBelow).flatMap(rearranged(_, pq, higherQ))
                        higherPositive <- lessTransitive(pPositive, pBelow)
                        member <- intoCore(x, y, pq, c3, c2, inHigher, inQ, higherPositive, qPositive, raised)
                        both <- rules.conjIntro(member, less)
                        result <- rules.existsIntro(goal, pq, both)
                      } yield result
                    }
                  } yield result
              )
              result <- rules.disch(inA.conclusion, reached).flatMap(rules.gen(a, _))
            } yield result

            isCut <- sets.closedFrom(set, inhabited, proper, closed, open)
            result <- rules.disch(hy.conclusion, isCut)
              .flatMap(rules.disch(hx.conclusion, _))
              .flatMap(rules.gen(y, _))
              .flatMap(rules.gen(x, _))
          } yield result

        /** [[Cut.PosMulMembers]]: the definition, then the characterisation at a set that is a cut. */
        private def membersFact(isCut: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            hx <- nonNegative(x).flatMap(assume)
            hy <- nonNegative(y).flatMap(assume)
            unfolded <- Conv.unfold(posMulDefinition, List(x, y))
            carriedDest <- dest.flatMap(Conv.apTerm(_, unfolded))
            set <- coreSet(x, y)
            atSet <- rules.specAll(isCut, List(x, y)).flatMap(rules.mp(_, hx)).flatMap(rules.mp(_, hy))
            back <- rules.spec(set, rebuilds).flatMap(rules.mp(_, atSet))
            result <- Conv.trans(carriedDest, back)
              .flatMap(rules.disch(hy.conclusion, _))
              .flatMap(rules.disch(hx.conclusion, _))
              .flatMap(rules.gen(y, _))
              .flatMap(rules.gen(x, _))
          } yield result

        /** Two sets equal pointwise, as the sets: each side beta-expanded at `r`, then `ext`. */
        private def setsEqual(left: Term, right: Term, pointwise: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            atLeft <- app(left, r).flatMap(Conv.betaRoot)
            atRight <- app(right, r).flatMap(Conv.betaRoot).flatMap(Conv.sym)
            joined <- Conv.trans(atLeft, pointwise).flatMap(Conv.trans(_, atRight))
            result <- rules.gen(r, joined).flatMap(classical.ext(logic, _))
          } yield result

        /** [[Cut.PosMulCommutative]]: the core's two sets are one, by swapping the witnesses, with no hypothesis. */
        private def commutativeFact: Either[LogicError, Kernel.Thm] = {
          def swap(from: (Term, Term), to: (Term, Term))(held: Kernel.Thm): Either[LogicError, Kernel.Thm] =
            fromCore(held, c1, c2)(
              negative => intoCoreNegative(to._1, to._2, r, negative),
              (inP, inQ, pPositive, qPositive, less) =>
                times(c2, c1).flatMap(rearranged(less, r, _)).flatMap(intoCore(to._1, to._2, r, c2, c1, inQ, inP, qPositive, pPositive, _))
            )
          for {
            leftTerm <- coreMemberTerm(x, y, r)
            rightTerm <- coreMemberTerm(y, x, r)
            forwards <- assume(leftTerm).flatMap(swap((x, y), (y, x)))
            backwards <- assume(rightTerm).flatMap(swap((y, x), (x, y)))
            pointwise = Kernel.deductAntisym(backwards, forwards)
            leftSet <- coreSet(x, y)
            rightSet <- coreSet(y, x)
            sameSets <- setsEqual(leftSet, rightSet, pointwise)
            maker <- make
            carried <- Conv.apTerm(maker, sameSets)
            leftUnfolded <- Conv.unfold(posMulDefinition, List(x, y))
            rightUnfolded <- Conv.unfold(posMulDefinition, List(y, x)).flatMap(Conv.sym)
            result <- Conv.trans(leftUnfolded, carried).flatMap(Conv.trans(_, rightUnfolded))
              .flatMap(rules.gen(y, _))
              .flatMap(rules.gen(x, _))
          } yield result
        }

        /** [[Cut.PosMulZero]]: no positive rational is below zero, so the core is the negatives, with no hypothesis. */
        private def zeroFact: Either[LogicError, Kernel.Thm] =
          for {
            zeroTerm <- zero
            zeroCut <- ofRational(zeroTerm)
            memberTerm <- coreMemberTerm(x, zeroCut, r)
            negativeTerm <- lt(r, zeroTerm)
            forwards <- assume(memberTerm).flatMap(held =>
              fromCore(held, c1, c2)(
                negative => Right(negative),
                (_, inQ, _, qPositive, _) =>
                  for {
                    qNegative <- memberOf(members, zeroTerm, c2).flatMap(eqMp(_, inQ))
                    loop <- lessTransitive(qPositive, qNegative)
                    falsity <- irreflexive(zeroTerm).flatMap(rules.notElim(_, loop))
                    result <- rules.falsityElim(negativeTerm, falsity)
                  } yield result
              ))
            backwards <- assume(negativeTerm).flatMap(intoCoreNegative(x, zeroCut, r, _))
            pointwise = Kernel.deductAntisym(backwards, forwards)
            coreSetTerm <- coreSet(x, zeroCut)
            unfoldedZero <- Conv.unfold(ofRationalDefinition, List(zeroTerm))
            belowZero <- rightOf(unfoldedZero).flatMap {
              case App(_, set) => Right(set)
              case other => Left(NotOfForm("an application of mk_cut", other))
            }
            sameSets <- setsEqual(coreSetTerm, belowZero, pointwise)
            maker <- make
            carried <- Conv.apTerm(maker, sameSets)
            unfolded <- Conv.unfold(posMulDefinition, List(x, zeroCut))
            result <- Conv.sym(unfoldedZero).flatMap(back => Conv.trans(unfolded, carried).flatMap(Conv.trans(_, back)))
              .flatMap(rules.gen(x, _))
          } yield result

        /** [[Cut.PosMulNonNegative]]: every negative is in the core. */
        private def nonNegativeFact(coreMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            hx <- nonNegative(x).flatMap(assume)
            hy <- nonNegative(y).flatMap(assume)
            zeroTerm <- zero
            zeroCut <- ofRational(zeroTerm)
            xy <- product(x, y)
            atPair <- membersAt(coreMembers, x, y, hx, hy)
            order <- included(zeroCut, xy) { inZero =>
              for {
                negative <- memberOf(members, zeroTerm, u).flatMap(eqMp(_, inZero))
                core <- intoCoreNegative(x, y, u, negative)
                result <- backIntoCore(atPair, u, core)
              } yield result
            }
            result <- rules.disch(hy.conclusion, order)
              .flatMap(rules.disch(hx.conclusion, _))
              .flatMap(rules.gen(y, _))
              .flatMap(rules.gen(x, _))
          } yield result

        /**
         * [[Cut.PosMulOne]]. A witness `p * q` with `q < 1` is below `p`, so what the core holds is in
         * `x`. Conversely a member `u` of `x` at least zero has a larger member `p`, and density puts
         * some `q` strictly between `u / p` and `1`, which makes `u < p * q`.
         */
        private def oneFact(coreMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            hx <- nonNegative(x).flatMap(assume)
            clausesX <- clausesOf(x)
            zeroTerm <- zero
            oneTerm <- one
            oneCut <- ofRational(oneTerm)
            zeroCut <- ofRational(zeroTerm)
            positiveOne <- zeroBelowOne
            oneNonNeg <- included(zeroCut, oneCut) { inZero =>
              memberOf(members, zeroTerm, u).flatMap(eqMp(_, inZero))
                .flatMap(lessTransitive(_, positiveOne))
                .flatMap(less => memberOf(members, oneTerm, u).flatMap(Conv.sym).flatMap(eqMp(_, less)))
            }
            atPair <- membersAt(coreMembers, x, oneCut, hx, oneNonNeg)
            xOne <- product(x, oneCut)
            result <- equalCuts(xOne, x)(
              held =>
                for {
                  core <- outOfCore(atPair, held)
                  result <- fromCore(core, c1, c2)(
                    negative => holdsNegative(hx, negative),
                    (inP, inQ, pPositive, _, less) =>
                      for {
                        qBelowOne <- memberOf(members, oneTerm, c2).flatMap(eqMp(_, inQ))
                        pq <- times(c1, c2)
                        shrunk <- timesLeft(pPositive, qBelowOne).flatMap(rearranged(_, pq, c1))
                        uBelowP <- lessTransitive(less, shrunk)
                        result <- sets.downwards(clausesX, u, c1, inP, uBelowP)
                      } yield result
                  )
                } yield result,
              held =>
                for {
                  negativeTerm <- lt(u, zeroTerm)
                  viaNegative <- assume(negativeTerm)
                    .flatMap(intoCoreNegative(x, oneCut, u, _))
                    .flatMap(backIntoCore(atPair, u, _))
                  notNegativeTerm <- logic.mkNot(negativeTerm)
                  notNegative <- assume(notNegativeTerm)
                  uNonNeg <- notLess(notNegative)
                  higher <- rules.spec(u, clausesX.open).flatMap(rules.mp(_, held))
                  viaNonNegative <- choosing(higher, c1) { pair =>
                    for {
                      parts <- halves(pair)
                      (inP, uBelowP) = parts
                      pPositive <- atMostThenLess(uNonNeg, uBelowP)
                      inverse <- read(Fraction.Inverse, Type.fun(Fraction.Classes, Fraction.Classes)).flatMap(app(_, c1))
                      inversePositive <- fact(Fraction.InversePositive).flatMap(rules.spec(c1, _)).flatMap(rules.mp(_, pPositive))
                      unit <- positiveNonZero(pPositive)
                        .flatMap(nonZero => fact(Fraction.MulInverse).flatMap(rules.spec(c1, _)).flatMap(rules.mp(_, nonZero)))
                      ratio <- times(u, inverse)
                      scaled <- timesLeft(inversePositive, uBelowP)
                      sides <- binary(scaled.conclusion)
                      ratioIs <- same(sides._1, ratio)
                      oneIs <- ring.consequence(sides._2, oneTerm, List(unit -> oneTerm))
                      ratioBelowOne <- compared(scaled, ratioIs, oneIs)
                      ratioNonNeg <- weakened(inversePositive)
                        .flatMap(invNonNeg => fact(Fraction.AtMostMul).flatMap(rules.specAll(_, List(u, inverse))).flatMap(rules.mp(_, uNonNeg)).flatMap(rules.mp(_, invNonNeg)))
                      between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(ratio, oneTerm))).flatMap(rules.mp(_, ratioBelowOne))
                      result <- choosing(between, c2) { pairQ =>
                        for {
                          partsQ <- halves(pairQ)
                          (ratioBelowQ, qBelowOne) = partsQ
                          qPositive <- atMostThenLess(ratioNonNeg, ratioBelowQ)
                          inQ <- memberOf(members, oneTerm, c2).flatMap(Conv.sym).flatMap(eqMp(_, qBelowOne))
                          raised <- timesLeft(pPositive, ratioBelowQ)
                          raisedSides <- binary(raised.conclusion)
                          uIs <- ring.consequence(raisedSides._1, u, List(unit -> u))
                          less <- compared(raised, uIs, Conv.refl(raisedSides._2))
                          core <- intoCore(x, oneCut, u, c1, c2, inP, inQ, pPositive, qPositive, less)
                          result <- backIntoCore(atPair, u, core)
                        } yield result
                      }
                    } yield result
                  }
                  result <- classical.cases(negativeTerm, viaNegative, viaNonNegative)
                } yield result
            )
            discharged <- rules.disch(hx.conclusion, result).flatMap(rules.gen(x, _))
          } yield discharged

        /**
         * [[Cut.PosMulAssociative]]. A witness `w1 * w2` of `(x y) z` has `w1 < p * q` from `x y`, and
         * then `p * (q * w2)` bounds it, with `q * w2` in `y z` by a larger member of `z`; the other
         * direction is the same through a larger member of `x`.
         */
        private def associativeFact(coreMembers: Kernel.Thm, nonNeg: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            hx <- nonNegative(x).flatMap(assume)
            hy <- nonNegative(y).flatMap(assume)
            hz <- nonNegative(z).flatMap(assume)
            clausesX <- clausesOf(x)
            clausesZ <- clausesOf(z)
            zeroTerm <- zero
            xy <- product(x, y)
            yz <- product(y, z)
            left <- product(xy, z)
            right <- product(x, yz)
            nnXY <- rules.specAll(nonNeg, List(x, y)).flatMap(rules.mp(_, hx)).flatMap(rules.mp(_, hy))
            nnYZ <- rules.specAll(nonNeg, List(y, z)).flatMap(rules.mp(_, hy)).flatMap(rules.mp(_, hz))
            atXY <- membersAt(coreMembers, x, y, hx, hy)
            atYZ <- membersAt(coreMembers, y, z, hy, hz)
            atLeft <- membersAt(coreMembers, xy, z, nnXY, hz)
            atRight <- membersAt(coreMembers, x, yz, hx, nnYZ)
            result <- equalCuts(left, right)(
              held =>
                for {
                  core <- outOfCore(atLeft, held)
                  goal <- dest.flatMap(app(_, right, u))
                  result <- fromCore(core, c1, c2)(
                    negative => intoCoreNegative(x, yz, u, negative).flatMap(backIntoCore(atRight, u, _)),
                    (inW1, inW2, w1Positive, w2Positive, less) =>
                      for {
                        inner <- outOfCore(atXY, inW1)
                        result <- fromCore(inner, c3, c4)(
                          negative =>
                            lessTransitive(w1Positive, negative)
                              .flatMap(loop => irreflexive(zeroTerm).flatMap(rules.notElim(_, loop)))
                              .flatMap(rules.falsityElim(goal, _)),
                          (inP, inQ, pPositive, qPositive, w1Below) =>
                            for {
                              higher <- rules.spec(c2, clausesZ.open).flatMap(rules.mp(_, inW2))
                              result <- choosing(higher, c5) { pair =>
                                for {
                                  parts <- halves(pair)
                                  (inHigher, w2Below) = parts
                                  v <- times(c4, c2)
                                  vHigher <- times(c4, c5)
                                  vBelow <- timesLeft(qPositive, w2Below).flatMap(rearranged(_, v, vHigher))
                                  higherPositive <- lessTransitive(w2Positive, w2Below)
                                  inYZ <- intoCore(y, z, v, c4, c5, inQ, inHigher, qPositive, higherPositive, vBelow)
                                    .flatMap(backIntoCore(atYZ, v, _))
                                  vPositive <- timesPositive(qPositive, w2Positive)
                                  w1w2 <- times(c1, c2)
                                  pv <- times(c3, v)
                                  bounded <- timesLeft(w2Positive, w1Below).flatMap(rearranged(_, w1w2, pv))
                                  uBelow <- lessTransitive(less, bounded)
                                  result <- intoCore(x, yz, u, c3, v, inP, inYZ, pPositive, vPositive, uBelow)
                                    .flatMap(backIntoCore(atRight, u, _))
                                } yield result
                              }
                            } yield result
                        )
                      } yield result
                  )
                } yield result,
              held =>
                for {
                  core <- outOfCore(atRight, held)
                  goal <- dest.flatMap(app(_, left, u))
                  result <- fromCore(core, c1, c2)(
                    negative => intoCoreNegative(xy, z, u, negative).flatMap(backIntoCore(atLeft, u, _)),
                    (inP, inV, pPositive, vPositive, less) =>
                      for {
                        inner <- outOfCore(atYZ, inV)
                        result <- fromCore(inner, c3, c4)(
                          negative =>
                            lessTransitive(vPositive, negative)
                              .flatMap(loop => irreflexive(zeroTerm).flatMap(rules.notElim(_, loop)))
                              .flatMap(rules.falsityElim(goal, _)),
                          (inQ, inW, qPositive, wPositive, vBelow) =>
                            for {
                              higher <- rules.spec(c1, clausesX.open).flatMap(rules.mp(_, inP))
                              result <- choosing(higher, c5) { pair =>
                                for {
                                  parts <- halves(pair)
                                  (inHigher, pBelow) = parts
                                  t <- times(c1, c3)
                                  tHigher <- times(c5, c3)
                                  tBelow <- timesLeft(qPositive, pBelow).flatMap(rearranged(_, t, tHigher))
                                  higherPositive <- lessTransitive(pPositive, pBelow)
                                  inXY <- intoCore(x, y, t, c5, c3, inHigher, inQ, higherPositive, qPositive, tBelow)
                                    .flatMap(backIntoCore(atXY, t, _))
                                  tPositive <- timesPositive(pPositive, qPositive)
                                  pv <- times(c1, c2)
                                  tw <- times(t, c4)
                                  bounded <- timesLeft(pPositive, vBelow).flatMap(rearranged(_, pv, tw))
                                  uBelow <- lessTransitive(less, bounded)
                                  result <- intoCore(xy, z, u, t, c4, inXY, inW, tPositive, wPositive, uBelow)
                                    .flatMap(backIntoCore(atLeft, u, _))
                                } yield result
                              }
                            } yield result
                        )
                      } yield result
                  )
                } yield result
            )
            discharged <- rules.disch(hz.conclusion, result)
              .flatMap(rules.disch(hy.conclusion, _))
              .flatMap(rules.disch(hx.conclusion, _))
              .flatMap(rules.gen(z, _))
              .flatMap(rules.gen(y, _))
              .flatMap(rules.gen(x, _))
          } yield discharged

        /**
         * [[Cut.PosMulDistributive]]. A witness `p * s` of `x (y + z)` with `s = q + t` splits at any
         * rational `a` strictly between `u - p * t` and `p * q`, which density supplies, and each half
         * is in its product by the sign of `q` or `t`. The other direction adds two witnesses under the
         * larger of their two members of `x`.
         */
        private def distributiveFact(coreMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            hx <- nonNegative(x).flatMap(assume)
            hy <- nonNegative(y).flatMap(assume)
            hz <- nonNegative(z).flatMap(assume)
            clausesY <- clausesOf(y)
            clausesZ <- clausesOf(z)
            zeroTerm <- zero
            sum <- addition.flatMap(app(_, y, z))
            nnSum <- rules.specAll(addNonNegative, List(y, z)).flatMap(rules.mp(_, hy)).flatMap(rules.mp(_, hz))
            xy <- product(x, y)
            xz <- product(x, z)
            left <- product(x, sum)
            right <- addition.flatMap(app(_, xy, xz))
            atXY <- membersAt(coreMembers, x, y, hx, hy)
            atXZ <- membersAt(coreMembers, x, z, hx, hz)
            atLeft <- membersAt(coreMembers, x, sum, hx, nnSum)

            /** `a < p * v` gives `a` in the core of `x` and `other`, by the sign of `v`. */
            bySign = (other: Term, atPair: Kernel.Thm, at: Term, pv: Term, v: Term, inP: Kernel.Thm, inV: Kernel.Thm, pPositive: Kernel.Thm, less: Kernel.Thm) =>
              for {
                positiveTerm <- lt(zeroTerm, v)
                viaPositive <- assume(positiveTerm)
                  .flatMap(vPositive => intoCore(x, other, at, pv, v, inP, inV, pPositive, vPositive, less))
                  .flatMap(backIntoCore(atPair, at, _))
                notPositive <- logic.mkNot(positiveTerm).flatMap(assume)
                viaNotPositive <- notLess(notPositive)
                  .flatMap(productNonPositive(pPositive, _))
                  .flatMap(lessThenAtMost(less, _))
                  .flatMap(intoCoreNegative(x, other, at, _))
                  .flatMap(backIntoCore(atPair, at, _))
                result <- classical.cases(positiveTerm, viaPositive, viaNotPositive)
              } yield result

            /** `s` in `y + z` for a member `s` of `y` or of `z`, by a larger member of it and a negative in the other. */
            inSumOf = (s: Term, inS: Kernel.Thm, ofY: Boolean) =>
              for {
                clauses <- Right(if (ofY) clausesY else clausesZ)
                higher <- rules.spec(s, clauses.open).flatMap(rules.mp(_, inS))
                result <- choosing(higher, c6) { pair =>
                  for {
                    parts <- halves(pair)
                    (inHigher, sBelow) = parts
                    gap <- difference(s, c6)
                    negated <- minus(c6)
                    gapNegative <- lessShifted(sBelow, negated).flatMap(rearranged(_, gap, zeroTerm))
                    witnessed <-
                      if (ofY)
                        holdsNegative(hz, gapNegative).flatMap(intoSum(y, z, s, c6, inHigher, _))
                      else
                        for {
                          inY <- holdsNegative(hy, gapNegative)
                          back <- difference(s, gap).flatMap(carried(inHigher, _))
                          result <- intoSum(y, z, s, gap, inY, back)
                        } yield result
                    result <- toSum(addMembers, y, z, s, witnessed)
                  } yield result
                }
              } yield result

            result <- equalCuts(left, right)(
              held =>
                for {
                  core <- outOfCore(atLeft, held)
                  result <- fromCore(core, c1, c2)(
                    negative =>
                      for {
                        between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(u, zeroTerm))).flatMap(rules.mp(_, negative))
                        result <- choosing(between, c3) { pair =>
                          for {
                            parts <- halves(pair)
                            (uBelow, aNegative) = parts
                            inXY <- intoCoreNegative(x, y, c3, aNegative).flatMap(backIntoCore(atXY, c3, _))
                            rest <- difference(u, c3)
                            negatedA <- minus(c3)
                            restNegative <- lessShifted(uBelow, negatedA).flatMap(rearranged(_, rest, zeroTerm))
                            inXZ <- intoCoreNegative(x, z, rest, restNegative).flatMap(backIntoCore(atXZ, rest, _))
                            result <- intoSum(xy, xz, u, c3, inXY, inXZ).flatMap(toSum(addMembers, xy, xz, u, _))
                          } yield result
                        }
                      } yield result,
                    (inP, inS, pPositive, _, less) =>
                      for {
                        split <- fromSum(addMembers, inS)
                        result <- choosing(split, c3) { pairQ =>
                          for {
                            partsQ <- halves(pairQ)
                            (inQ, inT) = partsQ
                            tTerm <- difference(c2, c3)
                            pq <- times(c1, c3)
                            pt <- times(c1, tTerm)
                            lower <- difference(u, pt)
                            negatedPt <- minus(pt)
                            lowerBelow <- lessShifted(less, negatedPt).flatMap(rearranged(_, lower, pq))
                            between <- fact(Fraction.Dense).flatMap(rules.specAll(_, List(lower, pq))).flatMap(rules.mp(_, lowerBelow))
                            result <- choosing(between, c4) { pairA =>
                              for {
                                partsA <- halves(pairA)
                                (lowerBelowA, aBelow) = partsA
                                inXY <- bySign(y, atXY, c4, c1, c3, inP, inQ, pPositive, aBelow)
                                rest <- difference(u, c4)
                                shift <- difference(pt, c4)
                                restBelow <- lessShifted(lowerBelowA, shift).flatMap(rearranged(_, rest, pt))
                                inXZ <- bySign(z, atXZ, rest, c1, tTerm, inP, inT, pPositive, restBelow)
                                result <- intoSum(xy, xz, u, c4, inXY, inXZ).flatMap(toSum(addMembers, xy, xz, u, _))
                              } yield result
                            }
                          } yield result
                        }
                      } yield result
                  )
                } yield result,
              held =>
                for {
                  split <- fromSum(addMembers, held)
                  result <- choosing(split, c1) { pair =>
                    for {
                      parts <- halves(pair)
                      (inA, inRest) = parts
                      rest <- difference(u, c1)
                      coreA <- outOfCore(atXY, inA)
                      coreRest <- outOfCore(atXZ, inRest)
                      result <- fromCore(coreA, c2, c3)(
                        aNegative =>
                          fromCore(coreRest, c4, c5)(
                            restNegative =>
                              for {
                                uBelowA <- lessShifted(restNegative, c1).flatMap(rearranged(_, u, c1))
                                negative <- lessTransitive(uBelowA, aNegative)
                                result <- intoCoreNegative(x, sum, u, negative).flatMap(backIntoCore(atLeft, u, _))
                              } yield result,
                            (inP, inT, pPositive, tPositive, restBelow) =>
                              for {
                                pt <- times(c4, c5)
                                ptPlusA <- plus(pt, c1)
                                first <- lessShifted(restBelow, c1).flatMap(rearranged(_, u, ptPlusA))
                                second <- lessShifted(aNegative, pt).flatMap(rearranged(_, ptPlusA, pt))
                                uBelow <- lessTransitive(first, second)
                                inSum <- inSumOf(c5, inT, false)
                                result <- intoCore(x, sum, u, c4, c5, inP, inSum, pPositive, tPositive, uBelow)
                                  .flatMap(backIntoCore(atLeft, u, _))
                              } yield result
                          ),
                        (inP, inQ, pPositive, qPositive, aBelow) =>
                          fromCore(coreRest, c4, c5)(
                            restNegative =>
                              for {
                                uBelowA <- lessShifted(restNegative, c1).flatMap(rearranged(_, u, c1))
                                uBelow <- lessTransitive(uBelowA, aBelow)
                                inSum <- inSumOf(c3, inQ, true)
                                result <- intoCore(x, sum, u, c2, c3, inP, inSum, pPositive, qPositive, uBelow)
                                  .flatMap(backIntoCore(atLeft, u, _))
                              } yield result,
                            (inP2, inT, p2Positive, tPositive, restBelow) =>
                              for {
                                pq <- times(c2, c3)
                                pt <- times(c4, c5)
                                s <- plus(c3, c5)
                                both <- plus(pq, pt)
                                aPlusPt <- plus(c1, pt)
                                first <- lessShifted(restBelow, c1).flatMap(rearranged(_, u, aPlusPt))
                                second <- lessShifted(aBelow, pt).flatMap(rearranged(_, aPlusPt, both))
                                uBelowBoth <- lessTransitive(first, second)
                                inS <- difference(s, c3)
                                  .flatMap(carried(inT, _))
                                  .flatMap(intoSum(y, z, s, c3, inQ, _))
                                  .flatMap(toSum(addMembers, y, z, s, _))
                                sPositive <- lessShifted(qPositive, c5).flatMap(rearranged(_, c5, s)).flatMap(lessTransitive(tPositive, _))
                                qNonNeg <- weakened(qPositive)
                                tNonNeg <- weakened(tPositive)
                                total <- fact(Fraction.AtMostTotal).flatMap(rules.specAll(_, List(c2, c4)))
                                // the larger member of `x` carries both witnesses
                                viaSecond <- for {
                                  order <- le(c2, c4).flatMap(assume)
                                  scaled <- fact(Fraction.MulLeftMonotone)
                                    .flatMap(rules.specAll(_, List(c3, c2, c4)))
                                    .flatMap(rules.mp(_, qNonNeg))
                                    .flatMap(rules.mp(_, order))
                                  scaledSides <- binary(scaled.conclusion)
                                  added <- fact(Fraction.AtMostAdd).flatMap(rules.specAll(_, List(scaledSides._1, scaledSides._2, pt))).flatMap(rules.mp(_, scaled))
                                  larger <- times(c4, s)
                                  bound <- rearranged(added, both, larger)
                                  uBelow <- lessThenAtMost(uBelowBoth, bound)
                                  result <- intoCore(x, sum, u, c4, s, inP2, inS, p2Positive, sPositive, uBelow)
                                    .flatMap(backIntoCore(atLeft, u, _))
                                } yield result
                                viaFirst <- for {
                                  order <- le(c4, c2).flatMap(assume)
                                  scaled <- fact(Fraction.MulLeftMonotone)
                                    .flatMap(rules.specAll(_, List(c5, c4, c2)))
                                    .flatMap(rules.mp(_, tNonNeg))
                                    .flatMap(rules.mp(_, order))
                                  scaledSides <- binary(scaled.conclusion)
                                  added <- fact(Fraction.AtMostAdd).flatMap(rules.specAll(_, List(scaledSides._1, scaledSides._2, pq))).flatMap(rules.mp(_, scaled))
                                  larger <- times(c2, s)
                                  bound <- rearranged(added, both, larger)
                                  uBelow <- lessThenAtMost(uBelowBoth, bound)
                                  result <- intoCore(x, sum, u, c2, s, inP, inS, pPositive, sPositive, uBelow)
                                    .flatMap(backIntoCore(atLeft, u, _))
                                } yield result
                                result <- rules.disjElim(total, viaSecond, viaFirst)
                              } yield result
                          )
                      )
                    } yield result
                  }
                } yield result
            )
            discharged <- rules.disch(hz.conclusion, result)
              .flatMap(rules.disch(hy.conclusion, _))
              .flatMap(rules.disch(hx.conclusion, _))
              .flatMap(rules.gen(z, _))
              .flatMap(rules.gen(y, _))
              .flatMap(rules.gen(x, _))
          } yield discharged
      }

      /**
       * The additive group of cuts as a normaliser, which is what every sign argument below closes
       * with. Its rules are the four laws of addition and what they give: a left zero, the exchange,
       * the two cancellations, and through the uniqueness of an inverse `--x = x`, `-0 = 0` and
       * `-(x + y) = -x + -y`. `CommutativeRing.order` is the order because it compares under the
       * negations, which is what puts `x` beside `-x` for a cancellation to meet.
       */
      /** `CUT_LT 0 c` gives `0 <= c`: the other side of totality contradicts it. */
      private def nonNegOfPositive(cut: Term, positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          zeroCut <- read(Fraction.Zero, Fraction.Classes).flatMap(zr => read(OfRational, Type.fun(Fraction.Classes, cutType)).flatMap(app(_, zr)))
          notBelow <- Conv.unfold(lessThanDefinition, List(zeroCut, cut)).flatMap(eqMp(_, positive))
          cases <- rules.specAll(total, List(zeroCut, cut))
          parts <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
          first <- assume(parts._1)
          second <- assume(parts._2).flatMap(rules.notElim(notBelow, _)).flatMap(rules.falsityElim(parts._1, _))
          result <- rules.disjElim(cases, first, second)
        } yield result

      private final case class Group(unconditional: Vector[Rewrite.Rule], ordered: Vector[Rewrite.Rule], facts: Vector[(String, Kernel.Thm)]) {
        private val order = CommutativeRing.order(Some(Negation))

        /** `|- left = right` for an identity of the group, with the extra ordered rules given. */
        def equal(
          left: Term,
          right: Term,
          extra: Vector[Rewrite.Rule] = Vector.empty,
          extraUnconditional: Vector[Rewrite.Rule] = Vector.empty
        ): Either[LogicError, Kernel.Thm] =
          if (left == right) Right(Conv.refl(left))
          else
            lift(Term.eq(left, right)).flatMap(
              Rewrite.proveEquation(logic, Rewrite.normaliser(unconditional ++ extraUnconditional, ordered ++ extra, order), _)
            )
      }

      private def groupOf(associative: Kernel.Thm, commutative: Kernel.Thm, zero: Kernel.Thm, inverse: Kernel.Thm): Either[LogicError, Group] =
        for {
          sum <- addition
          negation <- read(Negation, Type.fun(cutType, cutType))
          zeroCut <- read(Fraction.Zero, Fraction.Classes).flatMap(zr => read(OfRational, Type.fun(Fraction.Classes, cutType)).flatMap(app(_, zr)))
          nx <- app(negation, x)

          zeroLeft <- rules.specAll(commutative, List(zeroCut, x))
            .flatMap(swapped => rules.spec(x, zero).flatMap(Conv.trans(swapped, _)))
            .flatMap(rules.gen(x, _))
          exchange <- for {
            s1 <- rules.specAll(associative, List(x, y, z)).flatMap(Conv.sym)
            swapped <- rules.specAll(commutative, List(x, y))
            s2 <- Conv.apTerm(sum, swapped).flatMap(Conv.apThm(_, z))
            s3 <- rules.specAll(associative, List(y, x, z))
            result <- Conv.trans(s1, s2).flatMap(Conv.trans(_, s3))
              .flatMap(rules.gen(z, _)).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
          } yield result
          negLeft <- rules.specAll(commutative, List(nx, x))
            .flatMap(swapped => rules.spec(x, inverse).flatMap(Conv.trans(swapped, _)))
            .flatMap(rules.gen(x, _))
          cancel <- for {
            s1 <- rules.specAll(associative, List(x, nx, y)).flatMap(Conv.sym)
            s2 <- rules.spec(x, inverse).flatMap(Conv.apTerm(sum, _)).flatMap(Conv.apThm(_, y))
            s3 <- rules.spec(y, zeroLeft)
            result <- Conv.trans(s1, s2).flatMap(Conv.trans(_, s3)).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
          } yield result
          cancelLeft <- for {
            s1 <- rules.specAll(associative, List(nx, x, y)).flatMap(Conv.sym)
            s2 <- rules.spec(x, negLeft).flatMap(Conv.apTerm(sum, _)).flatMap(Conv.apThm(_, y))
            s3 <- rules.spec(y, zeroLeft)
            result <- Conv.trans(s1, s2).flatMap(Conv.trans(_, s3)).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
          } yield result

          /** `a + b = 0` gives `b = -a`: `b = (-a + a) + b = -a + (a + b) = -a + 0`. */
          unique = (a: Term, b: Term, premise: Kernel.Thm) =>
            for {
              na <- app(negation, a)
              s1 <- rules.spec(b, zeroLeft).flatMap(Conv.sym)
              s2 <- rules.spec(a, negLeft).flatMap(Conv.sym).flatMap(Conv.apTerm(sum, _)).flatMap(Conv.apThm(_, b))
              s3 <- rules.specAll(associative, List(na, a, b))
              s4 <- app(sum, na).flatMap(Conv.apTerm(_, premise))
              s5 <- rules.spec(na, zero)
              result <- Conv.trans(s1, s2).flatMap(Conv.trans(_, s3)).flatMap(Conv.trans(_, s4)).flatMap(Conv.trans(_, s5))
            } yield result

          negNeg <- rules.spec(x, negLeft).flatMap(unique(nx, x, _)).flatMap(Conv.sym).flatMap(rules.gen(x, _))
          negZero <- rules.spec(zeroCut, zero).flatMap(unique(zeroCut, zeroCut, _)).flatMap(Conv.sym)
          baseUnconditional <- Rewrite.Rule.all(logic, Vector(associative, zero, zeroLeft, inverse, negLeft, cancel, cancelLeft))
          ordered <- Rewrite.Rule.all(logic, Vector(commutative, exchange))
          partial = Group(baseUnconditional, ordered, Vector.empty)
          negAdd <- for {
            xy <- app(sum, x, y)
            ny <- app(negation, y)
            both <- app(sum, nx, ny)
            total <- app(sum, xy, both)
            vanishes <- partial.equal(total, zeroCut)
            result <- unique(xy, both, vanishes).flatMap(Conv.sym).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
          } yield result
          extra <- Rewrite.Rule.all(logic, Vector(negNeg, negZero, negAdd))
        } yield Group(baseUnconditional ++ extra, ordered, Vector((NegNeg, negNeg), (NegZero, negZero), (NegAdd, negAdd)))

      /**
       * The product off the cone. `CUT_MUL` picks a branch by the signs of its arguments, and
       * [[evaluated]] reads the branch a pair of sign facts selects; every law is then an identity of
       * the group over the core, closed by [[Group.equal]] with the core's commutativity as an ordered
       * rule.
       */
      private final case class Signs(group: Group, atMostAdd: Kernel.Thm, addNonNegative: Kernel.Thm, products: Map[String, Kernel.Thm]) {
        private def product(name: String): Either[LogicError, Kernel.Thm] = products.get(name).toRight(MissingDefinition(name))
        private def zeroCut: Either[LogicError, Term] =
          read(Fraction.Zero, Fraction.Classes).flatMap(zr => read(OfRational, Type.fun(Fraction.Classes, cutType)).flatMap(app(_, zr)))
        private def oneCut: Either[LogicError, Term] =
          read(Fraction.One, Fraction.Classes).flatMap(o => read(OfRational, Type.fun(Fraction.Classes, cutType)).flatMap(app(_, o)))
        private def neg(t: Term): Either[LogicError, Term] = read(Negation, Type.fun(cutType, cutType)).flatMap(app(_, t))
        private def mul(a: Term, b: Term): Either[LogicError, Term] =
          read(Multiplication, Type.fun(cutType, Type.fun(cutType, cutType))).flatMap(app(_, a, b))
        private def nn(t: Term): Either[LogicError, Term] =
          for {
            atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
            zc <- zeroCut
            result <- app(atMost, zc, t)
          } yield result
        private def negation: Either[LogicError, Term] = read(Negation, Type.fun(cutType, cutType))
        private def groupFact(name: String): Either[LogicError, Kernel.Thm] =
          group.facts.collectFirst { case (`name`, theorem) => theorem }.toRight(MissingDefinition(name))

        /** The core's commutativity, as an ordered rule for [[Group.equal]]. */
        private def coreRules: Either[LogicError, Vector[Rewrite.Rule]] =
          product(PosMulCommutative).flatMap(c => Rewrite.Rule.all(logic, Vector(c)))
        private def equal(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
          coreRules.flatMap(group.equal(left, right, _))

        private def conditional(held: Boolean): Either[LogicError, Kernel.Thm] =
          classical.fact(if (held) Classical.CondTrue else Classical.CondFalse)
            .map(Kernel.instType(Map(Classical.TypeVariable -> cutType), _))

        /** `|- COND p a b = a` or `= b`, as the sign fact says `p` or `~p`. */
        private def branch(term: Term, sign: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          term match {
            case App(App(App(_, test), yes), no) =>
              val holds = sign.conclusion == test
              conditional(holds).flatMap(rules.specAll(_, List(test, yes, no))).flatMap(rules.mp(_, sign))
            case other => Left(NotOfForm("a conditional", other))
          }

        /** `|- CUT_MUL a b = (the branch the two sign facts select)`. */
        private def evaluated(a: Term, b: Term, signA: Kernel.Thm, signB: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            unfolded <- Conv.unfold(multiplicationDefinition, List(a, b))
            outer <- rightOf(unfolded).flatMap(branch(_, signA))
            stepped <- Conv.trans(unfolded, outer)
            inner <- rightOf(stepped).flatMap(branch(_, signB))
            result <- Conv.trans(stepped, inner)
          } yield result

        /** A case split on `0 <= t`, each branch handed the sign fact it assumed. */
        private def bySign(t: Term)(body: Kernel.Thm => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
          for {
            test <- nn(t)
            positive <- assume(test).flatMap(body)
            negative <- logic.mkNot(test).flatMap(assume).flatMap(body)
            result <- classical.cases(test, positive, negative)
          } yield result


        private def mulConstant: Either[LogicError, Term] = read(Multiplication, Type.fun(cutType, Type.fun(cutType, cutType)))
        private def posMulConstant: Either[LogicError, Term] = read(PosMul, Type.fun(cutType, Type.fun(cutType, cutType)))
        private def pmul(a: Term, b: Term): Either[LogicError, Term] = posMulConstant.flatMap(app(_, a, b))
        private def add(a: Term, b: Term): Either[LogicError, Term] = addition.flatMap(app(_, a, b))

        /** `|- a * b = CUT_PMUL a b` on the cone. */
        private def coneAt(cone: Kernel.Thm, a: Term, b: Term, ha: Kernel.Thm, hb: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          rules.specAll(cone, List(a, b)).flatMap(rules.mp(_, ha)).flatMap(rules.mp(_, hb))

        /** `|- a * (-b) = -(a * b)`, by commutativity on both sides of the left law. */
        private def negRightAt(negLeft: Kernel.Thm, commutative: Kernel.Thm, a: Term, b: Term): Either[LogicError, Kernel.Thm] =
          for {
            nb <- neg(b)
            s1 <- rules.specAll(commutative, List(a, nb))
            s2 <- rules.specAll(negLeft, List(b, a))
            s3 <- rules.specAll(commutative, List(b, a)).flatMap(eq => negation.flatMap(Conv.apTerm(_, eq)))
            result <- Conv.trans(s1, s2).flatMap(Conv.trans(_, s3))
          } yield result

        /** The two sign laws as unconditional rules: a negation is pulled out of either factor. */
        private def signRules(negLeft: Kernel.Thm, commutative: Kernel.Thm): Either[LogicError, Vector[Rewrite.Rule]] =
          for {
            negRight <- negRightAt(negLeft, commutative, x, y).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
            result <- Rewrite.Rule.all(logic, Vector(negLeft, negRight))
          } yield result

        /** From `|- A = B` about `-v`, the same law about `v`: negate both sides and pull the signs out. */
        private def transfer(law: Kernel.Thm, targetLeft: Term, targetRight: Term, pulled: Vector[Rewrite.Rule]): Either[LogicError, Kernel.Thm] =
          for {
            sides <- Term.destEq(law.conclusion).toRight(NotOfForm("an equation", law.conclusion))
            negatedLeft <- neg(sides._1)
            negatedRight <- neg(sides._2)
            t1 <- group.equal(targetLeft, negatedLeft, extraUnconditional = pulled)
            t2 <- negation.flatMap(Conv.apTerm(_, law))
            t3 <- group.equal(negatedRight, targetRight, extraUnconditional = pulled)
            result <- Conv.trans(t1, t2).flatMap(Conv.trans(_, t3))
          } yield result

        /** A case split on the sign of `t`: `0 <= t` or `0 <= -t`. */
        private def byCases(signs: Kernel.Thm, t: Term)(
          nonNeg: Kernel.Thm => Either[LogicError, Kernel.Thm],
          negNonNeg: Kernel.Thm => Either[LogicError, Kernel.Thm]
        ): Either[LogicError, Kernel.Thm] =
          for {
            cases <- rules.spec(t, signs)
            parts <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
            first <- assume(parts._1).flatMap(nonNeg)
            second <- assume(parts._2).flatMap(negNonNeg)
            result <- rules.disjElim(cases, first, second)
          } yield result

        /**
         * [[Cut.MulAssociative]]: the core's law on the cone, then each of the three variables in
         * turn is carried off it by [[transfer]], the law at `-v` giving the law at `v`.
         */
        private def associativeFact(signs: Kernel.Thm, negLeft: Kernel.Thm, commutative: Kernel.Thm, cone: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
          def lhs(a: Term, b: Term, c: Term) = mul(a, b).flatMap(mul(_, c))
          def rhs(a: Term, b: Term, c: Term) = mul(b, c).flatMap(mul(a, _))
          def onCone(a: Term, b: Term, c: Term, ha: Kernel.Thm, hb: Kernel.Thm, hc: Kernel.Thm) =
            for {
              m <- mulConstant
              ab <- coneAt(cone, a, b, ha, hb)
              p <- rightOf(ab)
              nnP <- product(PosMulNonNegative).flatMap(rules.specAll(_, List(a, b))).flatMap(rules.mp(_, ha)).flatMap(rules.mp(_, hb))
              left1 <- Conv.apTerm(m, ab).flatMap(Conv.apThm(_, c))
              left2 <- coneAt(cone, p, c, nnP, hc)
              core <- product(PosMulAssociative).flatMap(rules.specAll(_, List(a, b, c)))
                .flatMap(rules.mp(_, ha)).flatMap(rules.mp(_, hb)).flatMap(rules.mp(_, hc))
              bc <- coneAt(cone, b, c, hb, hc)
              q <- rightOf(bc)
              nnQ <- product(PosMulNonNegative).flatMap(rules.specAll(_, List(b, c))).flatMap(rules.mp(_, hb)).flatMap(rules.mp(_, hc))
              right1 <- app(m, a).flatMap(Conv.apTerm(_, bc))
              right2 <- coneAt(cone, a, q, ha, nnQ)
              back <- Conv.trans(right1, right2).flatMap(Conv.sym)
              result <- Conv.trans(left1, left2).flatMap(Conv.trans(_, core)).flatMap(Conv.trans(_, back))
            } yield result
          for {
            pulled <- signRules(negLeft, commutative)
            level1 = (a: Term, b: Term, c: Term, hb: Kernel.Thm, hc: Kernel.Thm) =>
              byCases(signs, a)(
                ha => onCone(a, b, c, ha, hb, hc),
                hna => for {
                  na <- neg(a)
                  law <- onCone(na, b, c, hna, hb, hc)
                  tl <- lhs(a, b, c)
                  tr <- rhs(a, b, c)
                  result <- transfer(law, tl, tr, pulled)
                } yield result
              )
            level2 = (a: Term, b: Term, c: Term, hc: Kernel.Thm) =>
              byCases(signs, b)(
                hb => level1(a, b, c, hb, hc),
                hnb => for {
                  nb <- neg(b)
                  law <- level1(a, nb, c, hnb, hc)
                  tl <- lhs(a, b, c)
                  tr <- rhs(a, b, c)
                  result <- transfer(law, tl, tr, pulled)
                } yield result
              )
            result <- byCases(signs, z)(
              hz => level2(x, y, z, hz),
              hnz => for {
                nz <- neg(z)
                law <- level2(x, y, nz, hnz)
                tl <- lhs(x, y, z)
                tr <- rhs(x, y, z)
                result <- transfer(law, tl, tr, pulled)
              } yield result
            )
            general <- rules.gen(z, result).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
          } yield general
        }

        /**
         * [[Cut.MulDistributive]]. On the cone it is the core's law. With `z` negative the sum is
         * split by its own sign and the core's law is read at `(y + z, -z)` or at `(-(y + z), y)`;
         * with both negative it is the cone at `(-y, -z)`; and a negative `x` is [[transfer]].
         */
        private def distributiveFact(signs: Kernel.Thm, negLeft: Kernel.Thm, commutative: Kernel.Thm, cone: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
          def lhs(a: Term, b: Term, c: Term) = add(b, c).flatMap(mul(a, _))
          def rhs(a: Term, b: Term, c: Term) = mul(a, b).flatMap(ab => mul(a, c).flatMap(add(ab, _)))
          def sumOf(left: Kernel.Thm, right: Kernel.Thm) = addition.flatMap(Conv.apTerm(_, left)).flatMap(p => lift(Kernel.mkComb(p, right)))
          def negNegAt(t: Term) = groupFact(NegNeg).flatMap(rules.spec(t, _))

          def onCone(a: Term, b: Term, c: Term, ha: Kernel.Thm, hb: Kernel.Thm, hc: Kernel.Thm) =
            for {
              s <- add(b, c)
              hs <- rules.specAll(addNonNegative, List(b, c)).flatMap(rules.mp(_, hb)).flatMap(rules.mp(_, hc))
              left <- coneAt(cone, a, s, ha, hs)
              core <- product(PosMulDistributive).flatMap(rules.specAll(_, List(a, b, c)))
                .flatMap(rules.mp(_, ha)).flatMap(rules.mp(_, hb)).flatMap(rules.mp(_, hc))
              r1 <- coneAt(cone, a, b, ha, hb)
              r2 <- coneAt(cone, a, c, ha, hc)
              back <- sumOf(r1, r2).flatMap(Conv.sym)
              result <- Conv.trans(left, core).flatMap(Conv.trans(_, back))
            } yield result

          /** `a * c = -(CUT_PMUL a (-c))` for `c` whose negation is on the cone. */
          def negativeFactor(a: Term, c: Term, ha: Kernel.Thm, hnc: Kernel.Thm) =
            for {
              m <- mulConstant
              w <- neg(c)
              cw <- negNegAt(c).flatMap(Conv.sym)
              s1 <- app(m, a).flatMap(Conv.apTerm(_, cw))
              s2 <- negRightAt(negLeft, commutative, a, w)
              s3 <- coneAt(cone, a, w, ha, hnc).flatMap(eq => negation.flatMap(Conv.apTerm(_, eq)))
              result <- Conv.trans(s1, s2).flatMap(Conv.trans(_, s3))
            } yield result

          def mixed(a: Term, b: Term, c: Term, ha: Kernel.Thm, hb: Kernel.Thm, hnc: Kernel.Thm) =
            for {
              s <- add(b, c)
              w <- neg(c)
              pm <- posMulConstant
              rab <- coneAt(cone, a, b, ha, hb)
              rac <- negativeFactor(a, c, ha, hnc)
              rhsEq <- sumOf(rab, rac)
              pab <- pmul(a, b)
              paw <- pmul(a, w)
              result <- bySign(s) { signS =>
                nn(s).flatMap { nonNegS =>
                  if (signS.conclusion == nonNegS)
                    for {
                      core <- product(PosMulDistributive).flatMap(rules.specAll(_, List(a, s, w)))
                        .flatMap(rules.mp(_, ha)).flatMap(rules.mp(_, signS)).flatMap(rules.mp(_, hnc))
                      sw <- add(s, w)
                      eqSW <- group.equal(sw, b)
                      eq <- app(pm, a).flatMap(Conv.apTerm(_, eqSW)).flatMap(Conv.sym).flatMap(Conv.trans(_, core))
                      lhsEq <- coneAt(cone, a, s, ha, signS)
                      npaw <- neg(paw)
                      substituted <- addition.flatMap(Conv.apTerm(_, eq)).flatMap(Conv.apThm(_, npaw))
                      pas <- pmul(a, s)
                      replaced <- rightOf(substituted)
                      close <- group.equal(pas, replaced)
                      result <- Conv.sym(substituted).flatMap(back => Conv.sym(rhsEq).flatMap(back2 =>
                        Conv.trans(lhsEq, close).flatMap(Conv.trans(_, back)).flatMap(Conv.trans(_, back2))))
                    } yield result
                  else
                    for {
                      ht <- negatedSign(signs, signS, s)
                      t <- neg(s)
                      core <- product(PosMulDistributive).flatMap(rules.specAll(_, List(a, t, b)))
                        .flatMap(rules.mp(_, ha)).flatMap(rules.mp(_, ht)).flatMap(rules.mp(_, hb))
                      tb <- add(t, b)
                      eqTB <- group.equal(tb, w)
                      eq <- app(pm, a).flatMap(Conv.apTerm(_, eqTB)).flatMap(Conv.sym).flatMap(Conv.trans(_, core))
                      lhsEq <- negativeFactor(a, s, ha, ht)
                      substituted <- negation.flatMap(Conv.apTerm(_, eq)).flatMap(inner => addition.flatMap(ad => app(ad, pab)).flatMap(Conv.apTerm(_, inner)))
                      pat <- pmul(a, t)
                      npat <- neg(pat)
                      replaced <- rightOf(substituted)
                      close <- group.equal(npat, replaced)
                      result <- Conv.sym(substituted).flatMap(back => Conv.sym(rhsEq).flatMap(back2 =>
                        Conv.trans(lhsEq, close).flatMap(Conv.trans(_, back)).flatMap(Conv.trans(_, back2))))
                    } yield result
                }
              }
            } yield result

          def bothNegative(a: Term, b: Term, c: Term, ha: Kernel.Thm, hnb: Kernel.Thm, hnc: Kernel.Thm) =
            for {
              m <- mulConstant
              nb <- neg(b)
              nc <- neg(c)
              law <- onCone(a, nb, nc, ha, hnb, hnc)
              bc <- add(b, c)
              k1 <- negRightAt(negLeft, commutative, a, bc)
              k2 <- groupFact(NegAdd).flatMap(rules.specAll(_, List(b, c))).flatMap(eq => app(m, a).flatMap(Conv.apTerm(_, eq)))
              f1 <- Conv.sym(k1).flatMap(Conv.trans(_, k2)).flatMap(Conv.trans(_, law))
              rb <- negRightAt(negLeft, commutative, a, b)
              rc <- negRightAt(negLeft, commutative, a, c)
              f2 <- sumOf(rb, rc).flatMap(Conv.trans(f1, _))
              g <- negation.flatMap(Conv.apTerm(_, f2))
              target <- lhs(a, b, c)
              goalRight <- rhs(a, b, c)
              gSides <- Term.destEq(g.conclusion).toRight(NotOfForm("an equation", g.conclusion))
              t1 <- group.equal(target, gSides._1)
              t3 <- group.equal(gSides._2, goalRight)
              result <- Conv.trans(t1, g).flatMap(Conv.trans(_, t3))
            } yield result

          def level1(a: Term, b: Term, c: Term, ha: Kernel.Thm) =
            byCases(signs, b)(
              hb => byCases(signs, c)(hc => onCone(a, b, c, ha, hb, hc), hnc => mixed(a, b, c, ha, hb, hnc)),
              hnb => byCases(signs, c)(
                hc => for {
                  m <- mulConstant
                  law <- mixed(a, c, b, ha, hc, hnb)
                  bc <- add(b, c)
                  cb <- add(c, b)
                  swapped <- group.equal(bc, cb).flatMap(eq => app(m, a).flatMap(Conv.apTerm(_, eq)))
                  lawRight <- rightOf(law)
                  goalRight <- rhs(a, b, c)
                  reordered <- group.equal(lawRight, goalRight)
                  result <- Conv.trans(swapped, law).flatMap(Conv.trans(_, reordered))
                } yield result,
                hnc => bothNegative(a, b, c, ha, hnb, hnc)
              )
            )

          for {
            pulled <- signRules(negLeft, commutative)
            result <- byCases(signs, x)(
              hx => level1(x, y, z, hx),
              hnx => for {
                nx <- neg(x)
                law <- level1(nx, y, z, hnx)
                tl <- lhs(x, y, z)
                tr <- rhs(x, y, z)
                result <- transfer(law, tl, tr, pulled)
              } yield result
            )
            general <- rules.gen(z, result).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
          } yield general
        }

        /** [[Cut.LessMul]]: two positive cuts are on the cone, where the product is the core. */
        private def lessMulFact(cone: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            zc <- zeroCut
            lessConst <- read(LessThan, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
            pxTerm <- app(lessConst, zc, x)
            pyTerm <- app(lessConst, zc, y)
            both <- logic.mkConj(pxTerm, pyTerm).flatMap(assume)
            px <- rules.conjElim1(both)
            py <- rules.conjElim2(both)
            hx <- nonNegOfPositive(x, px)
            hy <- nonNegOfPositive(y, py)
            onTheCone <- coneAt(cone, x, y, hx, hy)
            positive <- product(PosMulPositive).flatMap(rules.specAll(_, List(x, y))).flatMap(rules.mp(_, px)).flatMap(rules.mp(_, py))
            carried <- app(lessConst, zc).flatMap(Conv.apTerm(_, onTheCone)).flatMap(Conv.sym).flatMap(eqMp(_, positive))
            result <- rules.disch(both.conclusion, carried).flatMap(rules.gen(y, _)).flatMap(rules.gen(x, _))
          } yield result


        /**
         * [[Cut.InverseZero]] and [[Cut.MulInverse]]. `CUT_INV` reads `0 < x` and then `x < 0`, so at
         * zero both tests fail and the definition writes zero; above zero it is the positive inverse,
         * and below it the negated inverse of `-x`, where the sign laws carry the product across.
         */
        private def inverseFacts(cone: Kernel.Thm, negLeft: Kernel.Thm, commutative: Kernel.Thm, signs: Kernel.Thm): Either[LogicError, (Kernel.Thm, Kernel.Thm)] =
          for {
            zc <- zeroCut
            oc <- oneCut
            lessConst <- read(LessThan, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
            atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
            m <- mulConstant
            reflexiveZero <- zeroNonNeg
            notLessZero <- for {
              lessTerm <- app(lessConst, zc, zc)
              held <- assume(lessTerm)
              opened <- Conv.unfold(lessThanDefinition, List(zc, zc)).flatMap(eqMp(_, held))
              falsity <- rules.notElim(opened, reflexiveZero)
              result <- rules.notIntro(lessTerm, falsity)
            } yield result
            atZero <- for {
              unfolded <- Conv.unfold(inverseDefinition, List(zc))
              outer <- rightOf(unfolded).flatMap(branch(_, notLessZero))
              stepped <- Conv.trans(unfolded, outer)
              inner <- rightOf(stepped).flatMap(branch(_, notLessZero))
              result <- Conv.trans(stepped, inner)
            } yield result

            nonZeroTerm <- lift(Term.eq(x, zc)).flatMap(logic.mkNot)
            nonZero <- assume(nonZeroTerm)
            positiveTerm <- app(lessConst, zc, x)
            invX <- read(Inverse, Type.fun(cutType, cutType)).flatMap(app(_, x))
            pinvConst <- read(PosInverse, Type.fun(cutType, cutType))
            viaPositive <- for {
              positive <- assume(positiveTerm)
              hx <- nonNegOfPositive(x, positive)
              unfolded <- Conv.unfold(inverseDefinition, List(x))
              choice <- rightOf(unfolded).flatMap(branch(_, positive)).flatMap(Conv.trans(unfolded, _))
              carried <- app(m, x).flatMap(Conv.apTerm(_, choice))
              pinv <- app(pinvConst, x)
              nnInv <- product(PosInverseNonNegative).flatMap(rules.spec(x, _)).flatMap(rules.mp(_, positive))
              onTheCone <- coneAt(cone, x, pinv, hx, nnInv)
              unit <- product(PosMulInverse).flatMap(rules.spec(x, _)).flatMap(rules.mp(_, positive))
              result <- Conv.trans(carried, onTheCone).flatMap(Conv.trans(_, unit))
            } yield result
            viaNegative <- for {
              notPositive <- logic.mkNot(positiveTerm).flatMap(assume)
              atMostZeroTerm <- app(atMost, x, zc)
              doubled <- Conv.unfold(lessThanDefinition, List(zc, x))
                .flatMap(eq => notPositive.conclusion match {
                  case App(not, _) => Conv.apTerm(not, eq).flatMap(eqMp(_, notPositive))
                  case other => Left(NotOfForm("a negation", other))
                })
              atMostZero <- classical.fact(Classical.DoubleNegation).flatMap(rules.spec(atMostZeroTerm, _)).flatMap(rules.mp(_, doubled))
              negativeTerm <- app(lessConst, x, zc)
              negative <- for {
                aboveTerm <- app(atMost, zc, x)
                above <- assume(aboveTerm)
                isZero <- rules.specAll(antisymmetric, List(x, zc)).flatMap(rules.mp(_, atMostZero)).flatMap(rules.mp(_, above))
                falsity <- rules.notElim(nonZero, isZero)
                notAbove <- rules.notIntro(aboveTerm, falsity)
                result <- Conv.unfold(lessThanDefinition, List(x, zc)).flatMap(Conv.sym).flatMap(eqMp(_, notAbove))
              } yield result
              unfolded <- Conv.unfold(inverseDefinition, List(x))
              outer <- rightOf(unfolded).flatMap(branch(_, notPositive)).flatMap(Conv.trans(unfolded, _))
              choice <- rightOf(outer).flatMap(branch(_, negative)).flatMap(Conv.trans(outer, _))
              nx <- neg(x)
              pnx <- for {
                belowTerm <- app(atMost, nx, zc)
                below <- assume(belowTerm)
                flipped <- atMostNegFact.flatMap(rules.specAll(_, List(nx, zc))).flatMap(rules.mp(_, below))
                negZero <- groupFact(NegZero)
                negNeg <- groupFact(NegNeg).flatMap(rules.spec(x, _))
                above <- compared(flipped, negZero, negNeg)
                falsity <- Conv.unfold(lessThanDefinition, List(x, zc)).flatMap(eqMp(_, negative)).flatMap(rules.notElim(_, above))
                notBelow <- rules.notIntro(belowTerm, falsity)
                result <- Conv.unfold(lessThanDefinition, List(zc, nx)).flatMap(Conv.sym).flatMap(eqMp(_, notBelow))
              } yield result
              hnx <- nonNegOfPositive(nx, pnx)
              pinvNeg <- app(pinvConst, nx)
              nnInv <- product(PosInverseNonNegative).flatMap(rules.spec(nx, _)).flatMap(rules.mp(_, pnx))
              unitNeg <- coneAt(cone, nx, pinvNeg, hnx, nnInv)
                .flatMap(onTheCone => product(PosMulInverse).flatMap(rules.spec(nx, _)).flatMap(rules.mp(_, pnx)).flatMap(Conv.trans(onTheCone, _)))
              carried <- app(m, x).flatMap(Conv.apTerm(_, choice))
              pulledRight <- negRightAt(negLeft, commutative, x, pinvNeg)
              pulledLeft <- rules.specAll(negLeft, List(x, pinvNeg)).flatMap(Conv.sym)
              result <- Conv.trans(carried, pulledRight).flatMap(Conv.trans(_, pulledLeft)).flatMap(Conv.trans(_, unitNeg))
            } yield result
            mulInverse <- classical.cases(positiveTerm, viaPositive, viaNegative)
              .flatMap(rules.disch(nonZeroTerm, _))
              .flatMap(rules.gen(x, _))
          } yield (atZero, mulInverse)

        def facts: Either[LogicError, Vector[(String, Kernel.Thm)]] =
          for {
            flipped <- atMostNegFact
            signs <- signCasesFact(flipped)
            cone <- onConeFact
            zero <- mulZeroFact
            unit <- mulOneFact(signs)
            commutative <- commutativeFact
            negLeft <- negLeftFact(signs, commutative, zero)
            associative <- associativeFact(signs, negLeft, commutative, cone)
            distributive <- distributiveFact(signs, negLeft, commutative, cone)
            lessMul <- lessMulFact(cone)
            inverses <- inverseFacts(cone, negLeft, commutative, signs)
          } yield Vector(
            (AtMostNeg, flipped),
            (SignCases, signs),
            (MulOnCone, cone),
            (MulZero, zero),
            (MulOne, unit),
            (MulCommutative, commutative),
            (MulNegLeft, negLeft),
            (MulAssociative, associative),
            (MulDistributive, distributive),
            (LessMul, lessMul),
            (InverseZero, inverses._1),
            (MulInverse, inverses._2)
          )

        /** [[Cut.AtMostNeg]]: add `-x + -y` to both sides. */
        private def atMostNegFact: Either[LogicError, Kernel.Thm] =
          for {
            atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
            held <- app(atMost, x, y).flatMap(assume)
            nx <- neg(x)
            ny <- neg(y)
            shift <- addition.flatMap(app(_, nx, ny))
            shifted <- rules.specAll(atMostAdd, List(x, y, shift)).flatMap(rules.mp(_, held))
            sides <- binary(shifted.conclusion)
            leftIs <- equal(sides._1, ny)
            rightIs <- equal(sides._2, nx)
            result <- compared(shifted, leftIs, rightIs)
              .flatMap(rules.disch(held.conclusion, _))
              .flatMap(rules.gen(y, _))
              .flatMap(rules.gen(x, _))
          } yield result

        /** [[Cut.SignCases]]: totality at zero, and `x <= 0` flipped. */
        private def signCasesFact(flipped: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            zc <- zeroCut
            nx <- neg(x)
            nonNegTerm <- nn(x)
            negNonNegTerm <- nn(nx)
            cases <- rules.specAll(total, List(zc, x))
            viaFirst <- assume(nonNegTerm).flatMap(rules.disjIntro1(negNonNegTerm, _))
            belowTerm <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool))).flatMap(app(_, x, zc))
            viaSecond <- for {
              below <- assume(belowTerm)
              turned <- rules.specAll(flipped, List(x, zc)).flatMap(rules.mp(_, below))
              negZero <- groupFact(NegZero)
              result <- compared(turned, negZero, Conv.refl(nx)).flatMap(rules.disjIntro2(nonNegTerm, _))
            } yield result
            result <- rules.disjElim(cases, viaFirst, viaSecond).flatMap(rules.gen(x, _))
          } yield result

        /** `~(0 <= t)` gives `0 <= -t`. */
        private def negatedSign(signs: Kernel.Thm, notNonNeg: Kernel.Thm, t: Term): Either[LogicError, Kernel.Thm] =
          for {
            cases <- rules.spec(t, signs)
            nt <- neg(t)
            target <- nn(nt)
            first <- nn(t).flatMap(assume).flatMap(held => rules.notElim(notNonNeg, held)).flatMap(rules.falsityElim(target, _))
            second <- assume(target)
            result <- rules.disjElim(cases, first, second)
          } yield result

        /** [[Cut.MulOnCone]]: both tests hold, so both conditionals take their first branch. */
        private def onConeFact: Either[LogicError, Kernel.Thm] =
          for {
            hx <- nn(x).flatMap(assume)
            hy <- nn(y).flatMap(assume)
            result <- evaluated(x, y, hx, hy)
              .flatMap(rules.disch(hy.conclusion, _))
              .flatMap(rules.disch(hx.conclusion, _))
              .flatMap(rules.gen(y, _))
              .flatMap(rules.gen(x, _))
          } yield result

        private def zeroNonNeg: Either[LogicError, Kernel.Thm] = zeroCut.flatMap(rules.spec(_, reflexive))

        /** [[Cut.MulZero]]: the core at zero is zero, and so is its negation. */
        private def mulZeroFact: Either[LogicError, Kernel.Thm] =
          for {
            zc <- zeroCut
            nonNegZero <- zeroNonNeg
            coreZero <- product(PosMulZero)
            result <- bySign(x) { sign =>
              for {
                evaluatedAt <- evaluated(x, zc, sign, nonNegZero)
                nonNegX <- nn(x)
                closing <-
                  if (sign.conclusion == nonNegX) rules.spec(x, coreZero)
                  else
                    for {
                      nx <- neg(x)
                      atNegX <- rules.spec(nx, coreZero)
                      carried <- negation.flatMap(Conv.apTerm(_, atNegX))
                      negZero <- groupFact(NegZero)
                      result <- Conv.trans(carried, negZero)
                    } yield result
                result <- Conv.trans(evaluatedAt, closing)
              } yield result
            }
            general <- rules.gen(x, result)
          } yield general

        /** [[Cut.MulOne]]: the core's unit on the cone, and `--x = x` off it. */
        private def mulOneFact(signs: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            zc <- zeroCut
            oc <- oneCut
            zeroTerm <- read(Fraction.Zero, Fraction.Classes)
            oneTerm <- read(Fraction.One, Fraction.Classes)
            positiveOne <- zeroBelowOne
            oneNonNeg <- included(zc, oc) { inZero =>
              memberOf(members, zeroTerm, u).flatMap(eqMp(_, inZero))
                .flatMap(lessTransitive(_, positiveOne))
                .flatMap(less => memberOf(members, oneTerm, u).flatMap(Conv.sym).flatMap(eqMp(_, less)))
            }
            coreOne <- product(PosMulOne)
            result <- bySign(x) { sign =>
              for {
                evaluatedAt <- evaluated(x, oc, sign, oneNonNeg)
                nonNegX <- nn(x)
                closing <-
                  if (sign.conclusion == nonNegX) rules.spec(x, coreOne).flatMap(rules.mp(_, sign))
                  else
                    for {
                      nx <- neg(x)
                      negNonNeg <- negatedSign(signs, sign, x)
                      unit <- rules.spec(nx, coreOne).flatMap(rules.mp(_, negNonNeg))
                      carried <- negation.flatMap(Conv.apTerm(_, unit))
                      negNeg <- groupFact(NegNeg).flatMap(rules.spec(x, _))
                      result <- Conv.trans(carried, negNeg)
                    } yield result
                result <- Conv.trans(evaluatedAt, closing)
              } yield result
            }
            general <- rules.gen(x, result)
          } yield general

        /** [[Cut.MulCommutative]]: in each of the four sign cases the branches differ by the core's order. */
        private def commutativeFact: Either[LogicError, Kernel.Thm] =
          for {
            result <- bySign(x) { signX =>
              bySign(y) { signY =>
                for {
                  forwards <- evaluated(x, y, signX, signY)
                  backwards <- evaluated(y, x, signY, signX)
                  left <- rightOf(forwards)
                  right <- rightOf(backwards)
                  bridge <- equal(left, right)
                  result <- Conv.sym(backwards).flatMap(back => Conv.trans(forwards, bridge).flatMap(Conv.trans(_, back)))
                } yield result
              }
            }
            general <- rules.gen(y, result).flatMap(rules.gen(x, _))
          } yield general

        /**
         * [[Cut.MulNegLeft]]. Where exactly one of `x` and `-x` is at least zero the two sides are
         * branches that the group identifies; where both are, `x` is zero and both sides are zero.
         */
        private def negLeftFact(signs: Kernel.Thm, commutative: Kernel.Thm, mulZero: Kernel.Thm): Either[LogicError, Kernel.Thm] =
          for {
            nx <- neg(x)
            zc <- zeroCut
            nonNegX <- nn(x)
            nonNegNegX <- nn(nx)
            result <- bySign(x) { signX =>
              bySign(nx) { signNegX =>
                val bothNonNeg = signX.conclusion == nonNegX && signNegX.conclusion == nonNegNegX
                val neither = signX.conclusion != nonNegX && signNegX.conclusion != nonNegNegX
                if (neither)
                  for {
                    cases <- rules.spec(x, signs)
                    target <- mul(nx, y).flatMap(l => mul(x, y).flatMap(neg).flatMap(r => lift(Term.eq(l, r))))
                    first <- assume(nonNegX).flatMap(rules.notElim(signX, _)).flatMap(rules.falsityElim(target, _))
                    second <- assume(nonNegNegX).flatMap(rules.notElim(signNegX, _)).flatMap(rules.falsityElim(target, _))
                    result <- rules.disjElim(cases, first, second)
                  } yield result
                else if (bothNonNeg)
                  for {
                    // `0 <= -x` flipped is `x <= 0`, so `x = 0`
                    flipped <- atMostNegFact
                    turned <- rules.specAll(flipped, List(zc, nx)).flatMap(rules.mp(_, signNegX))
                    negZero <- groupFact(NegZero)
                    negNeg <- groupFact(NegNeg).flatMap(rules.spec(x, _))
                    below <- compared(turned, negNeg, negZero)
                    isZero <- rules.specAll(antisymmetric, List(x, zc)).flatMap(rules.mp(_, below)).flatMap(rules.mp(_, signX))
                    // both sides at zero
                    zeroLeft <- rules.specAll(commutative, List(zc, y)).flatMap(swap => rules.spec(y, mulZero).flatMap(Conv.trans(swap, _)))
                    negIsZero <- negation.flatMap(Conv.apTerm(_, isZero)).flatMap(Conv.trans(_, negZero))
                    leftAtZero <- read(Multiplication, Type.fun(cutType, Type.fun(cutType, cutType)))
                      .flatMap(m => Conv.apTerm(m, negIsZero)).flatMap(Conv.apThm(_, y)).flatMap(Conv.trans(_, zeroLeft))
                    rightAtZero <- read(Multiplication, Type.fun(cutType, Type.fun(cutType, cutType)))
                      .flatMap(m => Conv.apTerm(m, isZero)).flatMap(Conv.apThm(_, y)).flatMap(Conv.trans(_, zeroLeft))
                      .flatMap(inner => negation.flatMap(Conv.apTerm(_, inner))).flatMap(Conv.trans(_, negZero))
                    result <- Conv.sym(rightAtZero).flatMap(Conv.trans(leftAtZero, _))
                  } yield result
                else
                  bySign(y) { signY =>
                    for {
                      left <- evaluated(nx, y, signNegX, signY)
                      right <- evaluated(x, y, signX, signY)
                      leftBranch <- rightOf(left)
                      rightBranch <- rightOf(right).flatMap(neg)
                      bridge <- equal(leftBranch, rightBranch)
                      back <- negation.flatMap(Conv.apTerm(_, right)).flatMap(Conv.sym)
                      result <- Conv.trans(left, bridge).flatMap(Conv.trans(_, back))
                    } yield result
                  }
              }
            }
            general <- rules.gen(y, result).flatMap(rules.gen(x, _))
          } yield general
      }
    }

    /** [[Cut.Represents]]: the characterisation at `dest_cut x`, whose right side is `abs (rep x) = x` carried. */
    private def representsFact: Either[LogicError, Kernel.Thm] =
      for {
        destX <- dest.flatMap(app(_, x))
        atRep <- characterised(destX)
        back <- rebuilt(x)
        carried <- dest.flatMap(Conv.apTerm(_, back))
        result <- Conv.sym(atRep).flatMap(eqMp(_, carried)).flatMap(rules.gen(x, _))
      } yield result

    /** [[Cut.Rebuilds]]: the characterisation read left to right. */
    private def rebuildsFact: Either[LogicError, Kernel.Thm] =
      for {
        isCut <- read(IsCut, Type.fun(setType, Type.Bool)).flatMap(app(_, set))
        held <- assume(isCut)
        result <- characterised(set).flatMap(eqMp(_, held))
          .flatMap(rules.disch(isCut, _))
          .flatMap(rules.gen(set, _))
      } yield result

    private def transitiveFact: Either[LogicError, Kernel.Thm] =
      for {
        xy <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool))).flatMap(app(_, x, y)).flatMap(assume)
        yz <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool))).flatMap(app(_, y, z)).flatMap(assume)
        xz <- included(x, z)(inX => inside(xy, u, inX).flatMap(inside(yz, u, _)))
        result <- rules.disch(yz.conclusion, xz)
          .flatMap(rules.disch(xy.conclusion, _))
          .flatMap(rules.gen(z, _))
          .flatMap(rules.gen(y, _))
          .flatMap(rules.gen(x, _))
      } yield result

    /** Two cuts with the same members are one cut: `ext` on the members, then the bijection. */
    private def antisymmetricFact: Either[LogicError, Kernel.Thm] =
      for {
        atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
        xy <- app(atMost, x, y).flatMap(assume)
        yx <- app(atMost, y, x).flatMap(assume)
        inX <- member(x, q).flatMap(assume)
        inY <- member(y, q).flatMap(assume)
        fromY <- inside(yx, q, inY)
        fromX <- inside(xy, q, inX)
        pointwise <- rules.gen(q, Kernel.deductAntisym(fromY, fromX))
        sameMembers <- classical.ext(logic, pointwise)
        maker <- make
        carried <- Conv.apTerm(maker, sameMembers)
        backX <- rebuilt(x).flatMap(Conv.sym)
        backY <- rebuilt(y)
        equal <- Conv.trans(backX, carried).flatMap(Conv.trans(_, backY))
        result <- rules.disch(yx.conclusion, equal)
          .flatMap(rules.disch(xy.conclusion, _))
          .flatMap(rules.gen(y, _))
          .flatMap(rules.gen(x, _))
      } yield result

    /**
     * [[Cut.AtMostTotal]]. If `x` is not inside `y`, `NOT_FORALL` gives a `t` with
     * `~(dest_cut x t ==> dest_cut y t)`, so `t` is in `x` and not in `y`. A member `q` of `y` is then
     * below `t`, since `t <= q` would put `t` in `y` by the closure, and so `q` is in `x`.
     */
    private def totalFact(represents: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
        xyTerm <- app(atMost, x, y)
        yxTerm <- app(atMost, y, x)
        forwards <- assume(xyTerm).flatMap(rules.disjIntro1(yxTerm, _))

        notXY <- logic.mkNot(xyTerm)
        missing <- assume(notXY)
        destY <- dest.flatMap(app(_, y))
        clausesX <- rules.spec(x, represents).flatMap(sets.clauses)
        clausesY <- rules.spec(y, represents).flatMap(sets.clauses)

        // `~(!q. dest_cut x q ==> dest_cut y q)`, then a witness of the failure
        notAll <- atMostOpened(x, y).flatMap(opened =>
          missing.conclusion match {
            case App(not, _) => Conv.apTerm(not, opened).flatMap(eqMp(_, missing))
            case other => Left(NotOfForm("a negation", other))
          })
        inclusion <- atMostOpened(x, y).flatMap(rightOf)
        predicate <- logic.destForallPredicate(inclusion).toRight(NotOfForm("a universal", inclusion))
        notForall <- classical.fact(Classical.NotForall)
          .map(Kernel.instType(Map(Classical.TypeVariable -> Fraction.Classes), _))
          .flatMap(rules.spec(predicate, _))
        reduced <- Conv.betaNormalise(notForall.conclusion).flatMap(eqMp(_, notForall))
        witness <- rules.mp(reduced, notAll)
        failureTerm <- member(x, t).flatMap(inX => member(y, t).flatMap(inY => logic.mkImp(inX, inY))).flatMap(logic.mkNot)
        failure <- assume(failureTerm)

        inXTerm <- member(x, t)
        inYTerm <- member(y, t)
        notInY <- for {
          inY <- assume(inYTerm)
          implication <- rules.disch(inXTerm, inY)
          falsity <- rules.notElim(failure, implication)
          result <- rules.notIntro(inYTerm, falsity)
        } yield result
        inX <- for {
          positive <- assume(inXTerm)
          notInX <- logic.mkNot(inXTerm).flatMap(assume)
          implication <- assume(inXTerm)
            .flatMap(rules.notElim(notInX, _))
            .flatMap(rules.falsityElim(inYTerm, _))
            .flatMap(rules.disch(inXTerm, _))
          negative <- rules.notElim(failure, implication).flatMap(rules.falsityElim(inXTerm, _))
          result <- classical.cases(inXTerm, positive, negative)
        } yield result

        backwards <- included(y, x) { inYq =>
          for {
            lessTerm <- lt(u, t)
            less <- assume(lessTerm)
            viaLess <- sets.downwards(clausesX, u, t, inX, less)
            notLessTerm <- logic.mkNot(lessTerm)
            notLessHeld <- assume(notLessTerm)
            order <- notLess(notLessHeld)
            reached <- sets.downwardsAtMost(clausesY, destY, t, u, inYq, order)
            viaNot <- rules.notElim(notInY, reached).flatMap(inXq => member(x, u).flatMap(rules.falsityElim(_, inXq)))
            result <- classical.cases(lessTerm, viaLess, viaNot)
          } yield result
        }
        fromWitness <- rules.existsElim(witness, t, backwards)
        backward <- rules.disjIntro2(xyTerm, fromWitness)
        result <- classical.cases(xyTerm, forwards, backward)
          .flatMap(rules.gen(y, _))
          .flatMap(rules.gen(x, _))
      } yield result

    /** [[Cut.OfRationalMembers]]: the definition, then the characterisation at a set that is a cut. */
    private def membersFact(belowIsCut: Kernel.Thm, rebuilds: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        unfolded <- Conv.unfold(ofRationalDefinition, List(q))
        carried <- dest.flatMap(Conv.apTerm(_, unfolded))
        below <- rightOf(unfolded).flatMap {
          case App(_, argument) => Right(argument)
          case other => Left(NotOfForm("an application of mk_cut", other))
        }
        isCut <- rules.spec(q, belowIsCut)
        back <- rules.spec(below, rebuilds).flatMap(rules.mp(_, isCut))
        result <- Conv.trans(carried, back).flatMap(rules.gen(q, _))
      } yield result

    /** `|- dest_cut (CUT_OF_RAT bound) rational = RAT_LT rational bound`. */
    private def memberOf(members: Kernel.Thm, bound: Term, rational: Term): Either[LogicError, Kernel.Thm] =
      for {
        atBound <- rules.spec(bound, members)
        applied <- Conv.apThm(atBound, rational)
        reduced <- rightOf(applied).flatMap(Conv.betaRoot)
        result <- Conv.trans(applied, reduced)
      } yield result

    /** [[Cut.OfRationalOrder]]: inclusion of the two sets below is the order between their bounds. */
    private def orderFact(members: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ofRational <- read(OfRational, Type.fun(Fraction.Classes, cutType))
        ofP <- app(ofRational, p)
        ofQ <- app(ofRational, q)
        atMost <- read(AtMost, Type.fun(cutType, Type.fun(cutType, Type.Bool)))
        cutsTerm <- app(atMost, ofP, ofQ)
        ratsTerm <- le(p, q)

        forwards <- for {
          cuts <- assume(cutsTerm)
          reversedTerm <- lt(q, p)
          reversed <- assume(reversedTerm)
          inP <- memberOf(members, p, q).flatMap(Conv.sym).flatMap(eqMp(_, reversed))
          inQ <- inside(cuts, q, inP)
          self <- memberOf(members, q, q).flatMap(eqMp(_, inQ))
          falsity <- irreflexive(q).flatMap(rules.notElim(_, self))
          notReversed <- rules.notIntro(reversedTerm, falsity)
          result <- notLess(notReversed)
        } yield result

        backwards <- for {
          rats <- assume(ratsTerm)
          result <- {
            val below = (inP: Kernel.Thm) =>
              for {
                atR <- inP.conclusion match {
                  case App(_, rational) => Right(rational)
                  case other => Left(NotOfForm("a membership", other))
                }
                rp <- memberOf(members, p, atR).flatMap(eqMp(_, inP))
                rq <- lessThenAtMost(rp, rats)
                result <- memberOf(members, q, atR).flatMap(Conv.sym).flatMap(eqMp(_, rq))
              } yield result
            included(ofP, ofQ)(below)
          }
        } yield result

        result <- Right(Kernel.deductAntisym(backwards, forwards))
          .flatMap(rules.gen(q, _))
          .flatMap(rules.gen(p, _))
      } yield result

    /** [[Cut.OfRationalInjective]]: reflexivity carried across the equation, both ways, and antisymmetry of `rat`. */
    private def injectiveFact(reflexive: Kernel.Thm, order: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        ofRational <- read(OfRational, Type.fun(Fraction.Classes, cutType))
        ofP <- app(ofRational, p)
        ofQ <- app(ofRational, q)
        equalTerm <- lift(Term.eq(ofP, ofQ))
        equal <- assume(equalTerm)
        forwardsCuts <- rules.spec(ofP, reflexive).flatMap(compared(_, Conv.refl(ofP), equal))
        forwards <- rules.specAll(order, List(p, q)).flatMap(eqMp(_, forwardsCuts))
        backwardsCuts <- rules.spec(ofP, reflexive).flatMap(compared(_, equal, Conv.refl(ofP)))
        backwards <- rules.specAll(order, List(q, p)).flatMap(eqMp(_, backwardsCuts))
        same <- fact(Fraction.AtMostAntisymmetric)
          .flatMap(rules.specAll(_, List(p, q)))
          .flatMap(rules.mp(_, forwards))
          .flatMap(rules.mp(_, backwards))
        result <- rules.disch(equalTerm, same).flatMap(rules.gen(q, _)).flatMap(rules.gen(p, _))
      } yield result

    /**
     * [[Cut.Complete]]. The union `U = \q. ?x. P x /\ dest_cut x q` is a cut: inhabited by a member
     * of some `x` in the family, not everything because a bound `b` misses something and every `x`
     * sits inside `b`, closed downwards and without a greatest element because each `x` is. Its cut
     * holds every `x`, and sits inside every bound.
     */
    private def completeFact(represents: Kernel.Thm, rebuilds: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val family = Term.variable("P", Type.fun(cutType, Type.Bool))
      val a = Term.variable("a", Fraction.Classes)
      val b = Term.variable("b", Fraction.Classes)
      val bound = Term.variable("b", cutType)
      for {
        hypothesisTerm <- proposition("(?x:real. P x) /\\ (?b:real. !x:real. P x ==> CUT_LE x b)")
        hypothesis <- assume(hypothesisTerm)
        nonEmpty <- rules.conjElim1(hypothesis)
        bounded <- rules.conjElim2(hypothesis)
        union <- read("\\q:rat. ?x:real. P x /\\ dest_cut x q", setType)
        unionBody <- sets.unfolded(union).flatMap(rightOf)
        clauseTerms <- unionBody match {
          case App(App(_, inhabited), App(App(_, proper), App(App(_, closed), open))) => Right((inhabited, proper, closed, open))
          case other => Left(NotOfForm("the four clauses of IS_CUT", other))
        }
        (inhabitedTerm, properTerm, _, _) = clauseTerms
        inUnion = (rational: Term) => proposition("?x:real. P x /\\ dest_cut x q").flatMap(text => lift(Term.substitute(Map(q -> rational), text)))
        intoUnion = (cut: Term, rational: Term, inFamily: Kernel.Thm, isMember: Kernel.Thm) =>
          for {
            target <- inUnion(rational)
            predicate <- logic.destExistsPredicate(target).toRight(NotOfForm("an existential", target))
            both <- rules.conjIntro(inFamily, isMember)
            result <- rules.existsIntro(predicate, cut, both)
          } yield result
        inFamilyTerm = (cut: Term) => lift(Term.app(family, cut))

        inhabited <- for {
          inFamily <- inFamilyTerm(x).flatMap(assume)
          clauses <- rules.spec(x, represents).flatMap(sets.clauses)
          predicate <- logic.destExistsPredicate(inhabitedTerm).toRight(NotOfForm("an existential", inhabitedTerm))
          isMember <- member(x, a).flatMap(assume)
          inU <- intoUnion(x, a, inFamily, isMember)
          introduced <- rules.existsIntro(predicate, a, inU)
          fromMember <- rules.existsElim(clauses.inhabited, a, introduced)
          result <- rules.existsElim(nonEmpty, x, fromMember)
        } yield result

        proper <- for {
          boundedBy <- proposition("!x:real. P x ==> CUT_LE x b").flatMap(assume)
          clauses <- rules.spec(bound, represents).flatMap(sets.clauses)
          missing <- member(bound, b).flatMap(logic.mkNot).flatMap(assume)
          inUTerm <- inUnion(b)
          inU <- assume(inUTerm)
          someX <- for {
            pair <- inFamilyTerm(x).flatMap(px => member(x, b).flatMap(xb => logic.mkConj(px, xb))).flatMap(assume)
            inFamily <- rules.conjElim1(pair)
            isMember <- rules.conjElim2(pair)
            order <- rules.spec(x, boundedBy).flatMap(rules.mp(_, inFamily))
            inBound <- inside(order, b, isMember)
            falsity <- rules.notElim(missing, inBound)
          } yield falsity
          falsity <- rules.existsElim(inU, x, someX)
          notInU <- rules.notIntro(inUTerm, falsity)
          predicate <- logic.destExistsPredicate(properTerm).toRight(NotOfForm("an existential", properTerm))
          introduced <- rules.existsIntro(predicate, b, notInU)
          fromMissing <- rules.existsElim(clauses.proper, b, introduced)
          result <- rules.existsElim(bounded, bound, fromMissing)
        } yield result

        closed <- for {
          inUTerm <- inUnion(b)
          less <- lt(a, b)
          both <- logic.mkConj(inUTerm, less).flatMap(assume)
          inU <- rules.conjElim1(both)
          ab <- rules.conjElim2(both)
          someX <- for {
            pair <- inFamilyTerm(x).flatMap(px => member(x, b).flatMap(xb => logic.mkConj(px, xb))).flatMap(assume)
            inFamily <- rules.conjElim1(pair)
            isMember <- rules.conjElim2(pair)
            clauses <- rules.spec(x, represents).flatMap(sets.clauses)
            lower <- sets.downwards(clauses, a, b, isMember, ab)
            result <- intoUnion(x, a, inFamily, lower)
          } yield result
          result <- rules.existsElim(inU, x, someX)
            .flatMap(rules.disch(both.conclusion, _))
            .flatMap(rules.gen(b, _))
            .flatMap(rules.gen(a, _))
        } yield result

        open <- for {
          inU <- inUnion(a).flatMap(assume)
          goal <- inUnion(b).flatMap(ub => lt(a, b).flatMap(ab => logic.mkConj(ub, ab)))
            .flatMap(body => lift(Term.abs(b, body)))
          someX <- for {
            pair <- inFamilyTerm(x).flatMap(px => member(x, a).flatMap(xa => logic.mkConj(px, xa))).flatMap(assume)
            inFamily <- rules.conjElim1(pair)
            isMember <- rules.conjElim2(pair)
            clauses <- rules.spec(x, represents).flatMap(sets.clauses)
            higher <- rules.spec(a, clauses.open).flatMap(rules.mp(_, isMember))
            atB <- for {
              pairB <- member(x, b).flatMap(xb => lt(a, b).flatMap(ab => logic.mkConj(xb, ab))).flatMap(assume)
              xb <- rules.conjElim1(pairB)
              ab <- rules.conjElim2(pairB)
              inUB <- intoUnion(x, b, inFamily, xb)
              both <- rules.conjIntro(inUB, ab)
              result <- rules.existsIntro(goal, b, both)
            } yield result
            result <- rules.existsElim(higher, b, atB)
          } yield result
          result <- rules.existsElim(inU, x, someX)
            .flatMap(rules.disch(inU.conclusion, _))
            .flatMap(rules.gen(a, _))
        } yield result

        isCut <- sets.closedFrom(union, inhabited, proper, closed, open)
        maker <- make
        supremum <- app(maker, union)
        unionMembers <- rules.spec(union, rebuilds).flatMap(rules.mp(_, isCut))
        /** `|- dest_cut supremum r = ?x. P x /\ dest_cut x r`. */
        inSupremum = (rational: Term) =>
          for {
            applied <- Conv.apThm(unionMembers, rational)
            reduced <- rightOf(applied).flatMap(Conv.betaRoot)
            result <- Conv.trans(applied, reduced)
          } yield result

        upper <- for {
          inFamily <- inFamilyTerm(x).flatMap(assume)
          order <- included(x, supremum) { inX =>
            intoUnion(x, u, inFamily, inX).flatMap(inU => inSupremum(u).flatMap(Conv.sym).flatMap(eqMp(_, inU)))
          }
          result <- rules.disch(inFamily.conclusion, order).flatMap(rules.gen(x, _))
        } yield result

        least <- for {
          boundedBy <- proposition("!x:real. P x ==> CUT_LE x b").flatMap(assume)
          order <- included(supremum, bound) { inS =>
            for {
              inU <- inSupremum(u).flatMap(eqMp(_, inS))
              someX <- for {
                pair <- inFamilyTerm(x).flatMap(px => member(x, u).flatMap(xu => logic.mkConj(px, xu))).flatMap(assume)
                inFamily <- rules.conjElim1(pair)
                isMember <- rules.conjElim2(pair)
                below <- rules.spec(x, boundedBy).flatMap(rules.mp(_, inFamily))
                result <- inside(below, u, isMember)
              } yield result
              result <- rules.existsElim(inU, x, someX)
            } yield result
          }
          result <- rules.disch(boundedBy.conclusion, order).flatMap(rules.gen(bound, _))
        } yield result

        both <- rules.conjIntro(upper, least)
        goal <- proposition(
          "?s:real. (!x:real. P x ==> CUT_LE x s) /\\ (!b:real. (!x:real. P x ==> CUT_LE x b) ==> CUT_LE s b)"
        )
        predicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
        introduced <- rules.existsIntro(predicate, supremum, both)
        result <- rules.disch(hypothesisTerm, introduced).flatMap(rules.gen(family, _))
      } yield result
    }
  }
}
