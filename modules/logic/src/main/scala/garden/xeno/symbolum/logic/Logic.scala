package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * The propositional and quantifier connectives, as definitions over the kernel's theory.
 *
 * None of them is primitive and none of them is an axiom. Each is an abbreviation introduced by
 * [[garden.xeno.symbolum.kernel.Kernel.defineConstant]], which means this whole layer is a conservative
 * extension: it proves nothing that could not already be proved about the terms the definitions
 * expand to, and [[garden.xeno.symbolum.kernel.Theory.axioms]] is still empty after it.
 *
 * The definitions are the standard ones of the HOL tradition, and each is chosen so that its
 * introduction and elimination rules come out of the kernel's ten rules rather than needing new
 * ones. Conjunction is the clearest case: `p /\ q` is defined as the statement that the two
 * functions `\f. f p q` and `\f. f T T` are equal, and the two projections fall out by applying
 * both sides to a selector.
 *
 * == What is here and what is not ==
 *
 * All eight constants are defined, and [[Rules]] derives introduction and elimination for every
 * one of them. Falsity is the exception: it has its definition and no rule, because nothing in the
 * development has yet had a contradiction to discharge that `notIntro` did not already cover.
 *
 * The definitions of disjunction and the existential are the second-order ones, `!r. (p ==> r) ==>
 * ((q ==> r) ==> r)` and `!q. (!x. P x ==> q) ==> q`, which say what each connective is good for
 * rather than what it is. That is what lets their rules come out of the kernel's ten like the
 * others: eliminating a disjunction is a specialisation and two detachments, and no case-splitting
 * principle is needed. It is also why the connectives **of this class** are intuitionistic: nothing
 * here proves `p \/ ~p`, and that is a property of what this file asserts, which is nothing.
 *
 * **It is not a property of the system, and it stopped being one on 2026-09-10.** `p \/ ~p` is a
 * theorem of [[Classical]], derived from the choice operator in 841 steps and reaching no other
 * axiom; `docs/adr/0009` is the record and it also records that three places here said the excluded
 * middle would need an axiom of its own, which was false. What is true of this file is the weaker
 * and more useful statement: a development that takes `Logic.standard` and declines the classical
 * extension has no case split on a proposition, and every result it proves is free of both of the
 * logic's axioms. That is the whole reason the extension sits beside this class rather than in it.
 */
final class Logic private (
  val theory: Theory,
  private val definitions: Map[String, Kernel.Thm],
  val truth: Term,
  val falsity: Term,
  val conjunction: Term,
  val disjunction: Term,
  val implication: Term,
  val negation: Term
) {

  import Logic.*

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definitionOf(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** The derived rules over this theory. */
  lazy val rules: Rules = new Rules(this)

  /**
   * The same logic, reading and building against a theory that extends this one.
   *
   * The connectives are polymorphic and their definitions say nothing about any particular type,
   * but building one at a type means asking a theory for the constant at that type, and a theory
   * refuses a type operator it has never heard of. So a development that defines a type of its own
   * could quantify over it only where a term already did: `Rules.gen` worked over the naturals
   * because the goal it was closing already carried the quantifier, and `Rules.existsIntro` did not,
   * because it has to build one. That is a limit of the plumbing rather than of the logic, and it
   * would have bitten everything above a new type.
   *
   * **The extension is checked rather than trusted.** Every constant this logic knows has to be in
   * the wider theory at the same type, or the result would be a logic whose connectives mean
   * something else, which is the shape `docs/adr/0008` is about one level down.
   */
  def over(wider: Theory): Either[LogicError, Logic] = {
    val missing = theory.constants.filterNot { case (name, ty) => wider.constants.get(name).contains(ty) }

    if (missing.nonEmpty)
      Left(NotOfForm(s"a theory extending this one; it does not declare ${missing.keys.mkString(", ")}", truth))
    else
      Right(
        new Logic(wider, definitions, truth, falsity, conjunction, disjunction, implication, negation)
      )
  }

  /* ------------------------------------------------------------------ syntax */

  def mkConj(left: Term, right: Term): Either[LogicError, Term] =
    LogicError.lift(Term.appAll(conjunction, List(left, right)))

  def destConj(term: Term): Option[(Term, Term)] = term match {
    case App(App(Const(Conjunction, _), left), right) => Some((left, right))
    case _ => None
  }

  def mkDisj(left: Term, right: Term): Either[LogicError, Term] =
    LogicError.lift(Term.appAll(disjunction, List(left, right)))

  def destDisj(term: Term): Option[(Term, Term)] = term match {
    case App(App(Const(Disjunction, _), left), right) => Some((left, right))
    case _ => None
  }

  def mkImp(antecedent: Term, consequent: Term): Either[LogicError, Term] =
    LogicError.lift(Term.appAll(implication, List(antecedent, consequent)))

  def destImp(term: Term): Option[(Term, Term)] = term match {
    case App(App(Const(Implication, _), antecedent), consequent) => Some((antecedent, consequent))
    case _ => None
  }

  def mkNot(proposition: Term): Either[LogicError, Term] =
    LogicError.lift(Term.app(negation, proposition))

  def destNot(term: Term): Option[Term] = term match {
    case App(Const(Negation, _), proposition) => Some(proposition)
    case _ => None
  }

  /** The universal quantifier at the type it ranges over. */
  def universalAt(ty: Type): Either[LogicError, Term] =
    LogicError.lift(theory.constant(Universal, quantifierType(ty)))

  /** The existential quantifier at the type it ranges over. */
  def existentialAt(ty: Type): Either[LogicError, Term] =
    LogicError.lift(theory.constant(Existential, quantifierType(ty)))

  def mkForall(variable: FVar, body: Term): Either[LogicError, Term] =
    for {
      quantifier <- universalAt(variable.ty)
      predicate <- LogicError.lift(Term.abs(variable, body))
      result <- LogicError.lift(Term.app(quantifier, predicate))
    } yield result

  def mkExists(variable: FVar, body: Term): Either[LogicError, Term] =
    for {
      quantifier <- existentialAt(variable.ty)
      predicate <- LogicError.lift(Term.abs(variable, body))
      result <- LogicError.lift(Term.app(quantifier, predicate))
    } yield result

  /**
   * The predicate a universal quantification is applied to.
   *
   * The predicate rather than the body, because the body alone would need the bound variable to
   * be given a name, and the rules that use this apply the predicate to something instead.
   */
  def destForallPredicate(term: Term): Option[Term] = term match {
    case App(Const(Universal, _), predicate) => Some(predicate)
    case _ => None
  }

  /** The predicate an existential quantification is applied to. */
  def destExistsPredicate(term: Term): Option[Term] = term match {
    case App(Const(Existential, _), predicate) => Some(predicate)
    case _ => None
  }
}

object Logic {

  /**
   * Take the leading universal quantifiers off, replacing each bound variable with a fresh free one.
   *
   * A quantified statement is a constant applied to a lambda, and there is nothing in that to
   * distribute, evaluate or add up, so every procedure that works on the body of a goal starts
   * here: the ring and linear arithmetic tactics before they normalise, and the refutation
   * search before it evaluates. It was written three times before it was written once.
   *
   * On the object rather than on an instance, because it needs no theory: the universal is one
   * constant and the move is the same wherever it is applied.
   *
   * The names are freshened against what is already free, so a bound `x` under a free `x` cannot
   * capture it, and the variables come back in the order they were written so that a caller can
   * quantify them again afterwards.
   */
  def stripForall(term: Term): Either[LogicError, (Vector[FVar], Term)] = {
    def go(current: Term, variables: Vector[FVar]): Either[LogicError, (Vector[FVar], Term)] =
      universalPredicate(current) match {
        case None => Right((variables, current))

        case Some(predicate) =>
          Type.destFun(Term.typeOf(predicate)) match {
            case None => Right((variables, current))

            case Some((domain, _)) =>
              // Named the way the printer names a binder, and not `a`, `a1`, `a2`. Most of the
              // time the variable is quantified again before anyone sees it and the name is
              // invisible; `Field` is where it is not, because a variable a side condition
              // mentions cannot be quantified again and stays free in what comes back. A theorem
              // about `a1` where the goal said `y` is a theorem about a different statement, so
              // the two namings are held together rather than left to coincide.
              val taken = (Term.freeVariables(current) ++ variables).map(_.name)
              val variable = Term.variable(Show.binderName(domain, taken.contains), domain)

              for {
                applied <- LogicError.lift(Term.app(predicate, variable))
                opened <- Term.betaReduce(applied).toRight(NotOfForm("a redex", applied))
                result <- go(opened, variables :+ variable)
              } yield result
          }
      }

    go(term, Vector.empty)
  }

  private def universalPredicate(term: Term): Option[Term] = term match {
    case App(Const(Universal, _), predicate) => Some(predicate)
    case _ => None
  }


  val Truth: String = "T"
  val Falsity: String = "F"
  val Conjunction: String = "/\\"
  val Disjunction: String = "\\/"
  val Implication: String = "==>"
  val Negation: String = "~"
  val Universal: String = "!"
  val Existential: String = "?"

  /** The type of a quantifier over `ty`: it takes a predicate and gives a proposition. */
  def quantifierType(ty: Type): Type = Type.fun(Type.fun(ty, Type.Bool), Type.Bool)

  /**
   * The standard theory.
   *
   * Built once. A failure here is a defect in the definitions rather than a condition a caller
   * could handle, so it is raised rather than returned; [[construct]] is public so that a test can
   * assert it succeeds without provoking an initialisation error to find out.
   */
  lazy val standard: Logic =
    construct().fold(
      error => throw new IllegalStateException(s"the standard theory does not build: ${error.message}"),
      identity
    )

  /** Build the standard theory from the primitive one, definition by definition. */
  def construct(): Either[LogicError, Logic] = {
    val bool = Type.Bool
    val alpha = TyVar("A")
    val binary = Type.fun(bool, Type.fun(bool, bool))

    val p = Term.variable("p", bool)
    val q = Term.variable("q", bool)
    val r = Term.variable("r", bool)
    val selector = Term.variable("f", binary)
    val boolVariable = Term.variable("x", bool)
    val alphaVariable = Term.variable("x", alpha)
    val predicate = Term.variable("P", Type.fun(alpha, bool))

    def define(stage: Stage, name: String, body: Term): Either[LogicError, Stage] =
      LogicError.lift(Kernel.defineConstant(stage.theory, name, body)).map { case (theory, theorem) =>
        Stage(theory, stage.definitions.updated(name, theorem))
      }

    def constant(stage: Stage, name: String, ty: Type): Either[LogicError, Term] =
      LogicError.lift(stage.theory.constant(name, ty))

    def apply2(fn: Term, left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(fn, List(left, right)))

    // Abstraction refuses a body that is not locally closed, since 2026-09-10, so it returns a
    // refusal like every other builder here. None of the bodies below can be open: each is built a
    // line or two above out of variables and constants. They are threaded rather than forced for
    // the reason the kernel threads its own: a forced refusal is a theorem nobody checked.
    def lam(variable: FVar, body: Term): Either[LogicError, Term] =
      LogicError.lift(Term.abs(variable, body))

    def lamAll(variables: List[FVar], body: Term): Either[LogicError, Term] =
      LogicError.lift(Term.absAll(variables, body))

    val start = Stage(Theory.primitive, Map.empty)

    for {
      // T = ((\p. p) = (\p. p))
      identity <- lam(p, p)
      truthBody <- LogicError.lift(Term.eq(identity, identity))
      afterTruth <- define(start, Truth, truthBody)
      truth <- constant(afterTruth, Truth, bool)

      // /\ = \p q. ((\f. f p q) = (\f. f T T))
      appliedToPair <- LogicError.lift(Term.appAll(selector, List(p, q)))
      appliedToTruths <- LogicError.lift(Term.appAll(selector, List(truth, truth)))
      pairSide <- lam(selector, appliedToPair)
      truthSide <- lam(selector, appliedToTruths)
      conjBody <- LogicError.lift(Term.eq(pairSide, truthSide))
      conjunctionBody <- lamAll(List(p, q), conjBody)
      afterConj <- define(afterTruth, Conjunction, conjunctionBody)
      conjunction <- constant(afterConj, Conjunction, binary)

      // ==> = \p q. ((p /\ q) = p)
      conjOfPair <- apply2(conjunction, p, q)
      impBody <- LogicError.lift(Term.eq(conjOfPair, p))
      implicationBody <- lamAll(List(p, q), impBody)
      afterImp <- define(afterConj, Implication, implicationBody)
      implication <- constant(afterImp, Implication, binary)

      // ! = \P. (P = (\x. T))
      constantlyTrue <- lam(alphaVariable, truth)
      forallBody <- LogicError.lift(Term.eq(predicate, constantlyTrue))
      universalBody <- lam(predicate, forallBody)
      afterForall <- define(afterImp, Universal, universalBody)
      forallAtBool <- constant(afterForall, Universal, quantifierType(bool))

      // F = !x:bool. x
      boolIdentity <- lam(boolVariable, boolVariable)
      falsityBody <- LogicError.lift(Term.app(forallAtBool, boolIdentity))
      afterFalsity <- define(afterForall, Falsity, falsityBody)
      falsity <- constant(afterFalsity, Falsity, bool)

      // ~ = \p. (p ==> F)
      negBody <- apply2(implication, p, falsity)
      negationBody <- lam(p, negBody)
      afterNegation <- define(afterFalsity, Negation, negationBody)
      negation <- constant(afterNegation, Negation, Type.fun(bool, bool))

      // \/ = \p q. !r. ((p ==> r) ==> ((q ==> r) ==> r))
      pImpliesR <- apply2(implication, p, r)
      qImpliesR <- apply2(implication, q, r)
      inner <- apply2(implication, qImpliesR, r)
      outer <- apply2(implication, pImpliesR, inner)
      overR <- lam(r, outer)
      quantified <- LogicError.lift(Term.app(forallAtBool, overR))
      disjunctionBody <- lamAll(List(p, q), quantified)
      afterDisj <- define(afterNegation, Disjunction, disjunctionBody)
      disjunction <- constant(afterDisj, Disjunction, binary)

      // ? = \P. !q. ((!x. (P x ==> q)) ==> q)
      forallAtAlpha <- constant(afterDisj, Universal, quantifierType(alpha))
      predicateAt <- LogicError.lift(Term.app(predicate, alphaVariable))
      predicateImplies <- apply2(implication, predicateAt, q)
      impliesOverAlpha <- lam(alphaVariable, predicateImplies)
      overAlpha <- LogicError.lift(Term.app(forallAtAlpha, impliesOverAlpha))
      existsInner <- apply2(implication, overAlpha, q)
      overQ <- lam(q, existsInner)
      existsQuantified <- LogicError.lift(Term.app(forallAtBool, overQ))
      existentialBody <- lam(predicate, existsQuantified)
      afterExists <- define(afterDisj, Existential, existentialBody)
    } yield new Logic(
      afterExists.theory,
      afterExists.definitions,
      truth,
      falsity,
      conjunction,
      disjunction,
      implication,
      negation
    )
  }

  private final case class Stage(theory: Theory, definitions: Map[String, Kernel.Thm])
}
