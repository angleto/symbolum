package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The reals as Dedekind cuts on the rationals, first stage: the type, its order, the rationals inside
 * it, and least upper bounds as a theorem.
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
 * downwards and has no greatest element. `IS_CUT` says those four things and `cut` is carved out of
 * `rat -> bool` by it; the witness is the cut of zero, and the fourth clause of it is `RAT_DENSE`,
 * which is what that fact was built for.
 *
 * The order is inclusion, which is why three of its four laws are one line each and the fourth is
 * the one argument in the file: two cuts are comparable because if `x` is not inside `y` then some
 * `t` is in `x` and not in `y`, and every member of `y` is then below `t`, since otherwise the
 * closure of `y` would put `t` in it. That needs the excluded middle twice, and the laws of `rat`
 * need none, so `CUT_LE_TOTAL` is where this development's classical cost is spent.
 *
 * == The one fact worth the file ==
 *
 * `CUT_COMPLETE` is `COMPLETENESS`, the sixteenth axiom of `Real.scala`, stated word for word over
 * `cut` and `CUT_LE`, and **proved**: the least upper bound of a non-empty bounded family of cuts is
 * the union of their members. It is the axiom that separates an ordered field from the reals, and
 * on this type it is not assumed. What is not here is the arithmetic: addition and negation are the
 * next card, multiplication the one after, and the sixteen become theorems under their own names only
 * when all of it is in place.
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
  val TypeName: String = "cut"
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

  /** `COMPLETENESS` over `cut`: a non-empty family with an upper bound has a least one. */
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

  private val IsCutBody: String =
    "\\S:rat->bool. (?a:rat. S a) /\\ (?b:rat. ~(S b)) /\\ " +
      "(!a:rat. !b:rat. S b /\\ RAT_LT a b ==> S a) /\\ (!a:rat. S a ==> (?b:rat. S b /\\ RAT_LT a b))"
  private val AtMostBody: String = "\\x:cut. \\y:cut. !q:rat. dest_cut x q ==> dest_cut y q"
  private val OfRationalBody: String = "\\q:rat. mk_cut (\\p:rat. RAT_LT p q)"
  private val SumSetText: String = "\\r:rat. ?p:rat. dest_cut x p /\\ dest_cut y (RAT_ADD r (RAT_NEG p))"
  private val AdditionBody: String = "\\x:cut. \\y:cut. mk_cut (" + SumSetText + ")"
  private val NegSetText: String =
    "\\p:rat. ?r:rat. RAT_LT RAT_ZERO r /\\ ~(dest_cut x (RAT_ADD (RAT_NEG p) (RAT_NEG r)))"
  private val NegationBody: String = "\\x:cut. mk_cut (" + NegSetText + ")"

  /** Each fact with the text it is published as, which the construction compares against. */
  val Statements: Vector[(String, String)] = Vector(
    BelowIsCut -> "!q:rat. IS_CUT (\\p:rat. RAT_LT p q)",
    Represents -> "!x:cut. IS_CUT (dest_cut x)",
    Rebuilds -> "!S:rat->bool. IS_CUT S ==> dest_cut (mk_cut S) = S",
    AtMostReflexive -> "!x:cut. CUT_LE x x",
    AtMostTransitive -> "!x:cut. !y:cut. !z:cut. CUT_LE x y ==> CUT_LE y z ==> CUT_LE x z",
    AtMostAntisymmetric -> "!x:cut. !y:cut. CUT_LE x y ==> CUT_LE y x ==> x = y",
    AtMostTotal -> "!x:cut. !y:cut. CUT_LE x y \\/ CUT_LE y x",
    OfRationalMembers -> "!q:rat. dest_cut (CUT_OF_RAT q) = (\\p:rat. RAT_LT p q)",
    OfRationalOrder -> "!p:rat. !q:rat. CUT_LE (CUT_OF_RAT p) (CUT_OF_RAT q) = RAT_LE p q",
    OfRationalInjective -> "!p:rat. !q:rat. CUT_OF_RAT p = CUT_OF_RAT q ==> p = q",
    Complete ->
      ("!P:cut->bool. (?x:cut. P x) /\\ (?b:cut. !x:cut. P x ==> CUT_LE x b) ==> " +
        "(?s:cut. (!x:cut. P x ==> CUT_LE x s) /\\ (!b:cut. (!x:cut. P x ==> CUT_LE x b) ==> CUT_LE s b))"),
    AddIsCut -> ("!x:cut. !y:cut. IS_CUT (" + SumSetText + ")"),
    AddMembers -> ("!x:cut. !y:cut. dest_cut (CUT_ADD x y) = (" + SumSetText + ")"),
    AddCommutative -> "!x:cut. !y:cut. CUT_ADD x y = CUT_ADD y x",
    AddAssociative -> "!x:cut. !y:cut. !z:cut. CUT_ADD (CUT_ADD x y) z = CUT_ADD x (CUT_ADD y z)",
    AddZero -> "!x:cut. CUT_ADD x (CUT_OF_RAT RAT_ZERO) = x",
    AtMostAdd -> "!x:cut. !y:cut. !z:cut. CUT_LE x y ==> CUT_LE (CUT_ADD x z) (CUT_ADD y z)",
    OfRationalAdd -> "!p:rat. !q:rat. CUT_OF_RAT (RAT_ADD p q) = CUT_ADD (CUT_OF_RAT p) (CUT_OF_RAT q)",
    NegIsCut -> ("!x:cut. IS_CUT (" + NegSetText + ")"),
    NegMembers -> ("!x:cut. dest_cut (CUT_NEG x) = (" + NegSetText + ")"),
    AddNegation -> "!x:cut. CUT_ADD x (CUT_NEG x) = CUT_OF_RAT RAT_ZERO"
  )

  private def statementOf(name: String): String =
    Statements.collectFirst { case (`name`, text) => text }.getOrElse(name)

  val Classes: Type = TyApp(TypeName, Nil)

  /* ------------------------------------------------------------------ the construction */

  def construct(fractions: Fraction, peano: Peano): Either[LogicError, Cut] = {
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
      addition <- define(withOfRational, Addition, AdditionBody)
      (withAddition, additionDefinition) = addition
      negation <- define(withAddition, Negation, NegationBody)
      (complete, negationDefinition) = negation
      induction <- peano.naturals.fact(Natural.Induction)

      wider <- classical.logic.over(complete)
      widerRationals = Rationals(wider, complete, notation, classical, fractions, ring)
      sets = Sets(widerRationals, isCutDefinition)
      proved <- Cuts(sets, bijection, atMostDefinition, ofRationalDefinition, additionDefinition, negationDefinition, induction)
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
        Negation -> negationDefinition
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
        sums <- Sums(represents, rebuilds, antisymmetric, members).facts
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
      members: Kernel.Thm
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
          inverse <- inverseFact(addMembers, negMembers)
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
          (AddNegation, inverse)
        )

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
      private def inverseFact(addMembers: Kernel.Thm, negMembers: Kernel.Thm): Either[LogicError, Kernel.Thm] =
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
                    stepped <- plus(p, f)
                    escapeBody <- member(x, p).flatMap(inP => member(x, stepped).flatMap(logic.mkNot).flatMap(logic.mkConj(inP, _)))
                    escapeTerm <- logic.mkExists(p, escapeBody)
                    escapes <- assume(escapeTerm)

                    // There is a member `p` with `p + h` outside: the witness `r = -u - h` works.
                    viaEscape <- choosing(escapes, p) { pair =>
                      for {
                        parts <- halves(pair)
                        (inP, outside) = parts
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

                    // There is none: every member steps to a member, which Archimedes refutes.
                    viaNone <- for {
                      notEscapeTerm <- logic.mkNot(escapeTerm)
                      notEscape <- assume(notEscapeTerm)
                      steps <- for {
                        inPTerm <- member(x, p)
                        inP <- assume(inPTerm)
                        inStepTerm <- member(x, stepped)
                        positive <- assume(inStepTerm)
                        negativeCase <- for {
                          outside <- logic.mkNot(inStepTerm).flatMap(assume)
                          both <- rules.conjIntro(inP, outside)
                          predicate <- logic.destExistsPredicate(escapeTerm).toRight(NotOfForm("an existential", escapeTerm))
                          witnessed <- rules.existsIntro(predicate, p, both)
                          result <- rules.notElim(notEscape, witnessed).flatMap(rules.falsityElim(inStepTerm, _))
                        } yield result
                        result <- classical.cases(inStepTerm, positive, negativeCase)
                          .flatMap(rules.disch(inPTerm, _))
                          .flatMap(rules.gen(p, _))
                      } yield result
                      falsity <- choosing(clausesX.inhabited, e) { inE =>
                        choosing(clausesX.proper, a) { notA =>
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
                                  next <- rules.spec(reached, steps).flatMap(rules.mp(_, step.hypothesis))
                                  successor <- rules.spec(step.variable, ofNumberSuccessor)
                                  target <- step.goal match {
                                    case App(_, at) => Right(at)
                                    case other => Left(NotOfForm("a membership", other))
                                  }
                                  result <- carriedUnder(next, target, List(successor -> minusF))
                                } yield result
                            )
                            gap <- difference(a, e)
                            inverseH <- app(inverseOf, f)
                            ratio <- app(multiply, gap, inverseH)
                            bounded <- fact(Fraction.Archimedes).flatMap(rules.spec(ratio, _))
                            result <- choosing(bounded, n) { atMost =>
                              for {
                                hNonNegative <- weakened(hPositive)
                                scaled <- fact(Fraction.MulLeftMonotone)
                                  .flatMap(law => binary(atMost.conclusion).flatMap(sides => rules.specAll(law, List(f, sides._1, sides._2))))
                                  .flatMap(rules.mp(_, hNonNegative))
                                  .flatMap(rules.mp(_, atMost))
                                unit <- positiveNonZero(hPositive)
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
                      }
                      result <- rules.falsityElim(goalTerm, falsity)
                    } yield result

                    result <- classical.cases(escapeTerm, viaEscape, viaNone)
                  } yield result
                }
              } yield result
          ).flatMap(rules.gen(x, _))
        } yield result

      private def binaryConstantRat(name: String): Either[LogicError, Term] =
        read(name, Type.fun(Fraction.Classes, Type.fun(Fraction.Classes, Fraction.Classes)))
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
        hypothesisTerm <- proposition("(?x:cut. P x) /\\ (?b:cut. !x:cut. P x ==> CUT_LE x b)")
        hypothesis <- assume(hypothesisTerm)
        nonEmpty <- rules.conjElim1(hypothesis)
        bounded <- rules.conjElim2(hypothesis)
        union <- read("\\q:rat. ?x:cut. P x /\\ dest_cut x q", setType)
        unionBody <- sets.unfolded(union).flatMap(rightOf)
        clauseTerms <- unionBody match {
          case App(App(_, inhabited), App(App(_, proper), App(App(_, closed), open))) => Right((inhabited, proper, closed, open))
          case other => Left(NotOfForm("the four clauses of IS_CUT", other))
        }
        (inhabitedTerm, properTerm, _, _) = clauseTerms
        inUnion = (rational: Term) => proposition("?x:cut. P x /\\ dest_cut x q").flatMap(text => lift(Term.substitute(Map(q -> rational), text)))
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
          boundedBy <- proposition("!x:cut. P x ==> CUT_LE x b").flatMap(assume)
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
          boundedBy <- proposition("!x:cut. P x ==> CUT_LE x b").flatMap(assume)
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
          "?s:cut. (!x:cut. P x ==> CUT_LE x s) /\\ (!b:cut. (!x:cut. P x ==> CUT_LE x b) ==> CUT_LE s b)"
        )
        predicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
        introduced <- rules.existsIntro(predicate, supremum, both)
        result <- rules.disch(hypothesisTerm, introduced).flatMap(rules.gen(family, _))
      } yield result
    }
  }
}
