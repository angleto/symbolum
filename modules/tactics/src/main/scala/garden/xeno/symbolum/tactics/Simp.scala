package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What `simp` rewrites with, and how a theorem becomes rewrite rules: `docs/adr/0080`.
 *
 * `simp` is rewriting to a normal form with a set of equations nobody has to name at the step. The
 * set is the connectives' clauses, the equations that define `+` and `*` over `num` with the
 * freeness of its constructors, and what a document puts in it: the constructors of each datatype it
 * declares, the equations of each function it defines by recursion, and each theorem it marks
 * `[simp]`, its own and those of the documents it imports. A step adds facts for itself with
 * `simp [F, G]`. Nothing here constructs a theorem: every rule is a theorem the kernel holds, turned
 * into an equation by inferences of `Rules`, and the rewriting is `Rewrite`'s.
 *
 * == A theorem as rules ==
 *
 * A rewriter rewrites with equations, and most facts a reader would want simplified with are not
 * written as one. So a theorem is taken apart under its quantifiers: an equation is itself; a
 * conjunction is each of its conjuncts; a negation `~P` is `P = F`, and when `P` is `a = b` also
 * `(b = a) = F`, since which way round a goal writes a disequality is not the fact's business; a
 * constructor's injectivity, `C xs = C ys ==> x1 = y1 /\ ...`, is the equation between its two
 * sides, which is how `Datatype` states it and how a reader uses it; anything else that is a
 * proposition `P` is `P = T`. An implication of any other shape is a conditional equation, which
 * `Rewrite` does not apply, and it is refused naming that rather than read as something it is not.
 *
 * `rewrite` takes the first two of those readings and no others: `rewrite F` rewrites with the
 * equations `F` states, and a conjunction of them is several equations. Turning a fact into
 * `P = T` is a choice of `simp`, which owns a set; a `rewrite` that silently did it would rewrite
 * a hypothesis `P` into the goal where its writer meant an equation and named the wrong fact.
 */
object Simp {

  /**
   * The library's facts every `simp` rewrites with: the freeness of `num`'s constructors and the
   * equations by which `+` and `*` are defined. They are the facts a datatype declared in a document
   * contributes for its own type, written out for the one type the chain defines with its own
   * construction rather than through `Datatype`.
   */
  val Base: Vector[String] =
    Vector("NUM_SUC_INJECTIVE", "NUM_SUC_NOT_ZERO", "NUM_ADD_ZERO", "NUM_ADD_SUC", "NUM_MUL_ZERO", "NUM_MUL_SUC")

  /**
   * The clauses of the connectives, as a reader checks them: [[clauses]] derives each and compares
   * what it derived with this text, so the list a reader reads is the list `simp` holds.
   */
  val Clauses: Vector[String] = Vector(
    "!x:'a. (x = x) = T",
    "(!x:'a. T) = T",
    "!p:bool. (T /\\ p) = p",
    "!p:bool. (p /\\ T) = p",
    "!p:bool. (F /\\ p) = F",
    "!p:bool. (p /\\ F) = F",
    "!p:bool. (T \\/ p) = T",
    "!p:bool. (p \\/ T) = T",
    "!p:bool. (F \\/ p) = p",
    "!p:bool. (p \\/ F) = p",
    "!p:bool. (T ==> p) = p",
    "!p:bool. (p ==> T) = T",
    "!p:bool. (F ==> p) = T",
    "!p:bool. (p ==> p) = T",
    "(~T) = F",
    "(~F) = T"
  )

  /**
   * The clauses, derived: each by `Kernel.deductAntisym` from a proof in each direction, and
   * checked against [[Clauses]] read in `theory`. They are not asked of the tactic surface, which
   * reads `=` between two propositions as an equation of some domain and does not prove
   * `(x = x) = T` at a type variable.
   */
  def clauses(logic: Logic, theory: Theory, notation: Notation): Either[LogicError, Vector[Kernel.Thm]] = {
    val rules = logic.rules
    val p = Term.variable("p", Type.Bool)
    val x = Term.variable("x", TyVar("a"))
    val (truth, falsity) = (logic.truth, logic.falsity)
    def assume(term: Term) = LogicError.lift(Kernel.assume(term))
    /** `left` proves the clause's left side, `right` its right side, each from the other. */
    def both(left: Either[LogicError, Kernel.Thm], right: Either[LogicError, Kernel.Thm]) =
      for { l <- left; r <- right } yield Kernel.deductAntisym(l, r)
    def over(variable: FVar)(clause: Either[LogicError, Kernel.Thm]) = clause.flatMap(rules.gen(variable, _))
    val derived: Vector[Either[LogicError, Kernel.Thm]] = Vector(
      over(x)(rules.eqTruthIntro(Kernel.refl(x))),
      // (!x. T) = T, which is what a universal goal is once its body has gone to T
      both(rules.truth.flatMap(rules.gen(x, _)), rules.truth),
      // (T /\ p) = p and (p /\ T) = p
      over(p)(both(for { t <- rules.truth; h <- assume(p); c <- rules.conjIntro(t, h) } yield c,
        logic.mkConj(truth, p).flatMap(assume).flatMap(rules.conjElim2))),
      over(p)(both(for { t <- rules.truth; h <- assume(p); c <- rules.conjIntro(h, t) } yield c,
        logic.mkConj(p, truth).flatMap(assume).flatMap(rules.conjElim1))),
      // (F /\ p) = F and (p /\ F) = F
      over(p)(both(for { c <- logic.mkConj(falsity, p); f <- assume(falsity); e <- rules.falsityElim(c, f) } yield e,
        logic.mkConj(falsity, p).flatMap(assume).flatMap(rules.conjElim1))),
      over(p)(both(for { c <- logic.mkConj(p, falsity); f <- assume(falsity); e <- rules.falsityElim(c, f) } yield e,
        logic.mkConj(p, falsity).flatMap(assume).flatMap(rules.conjElim2))),
      // (T \/ p) = T and (p \/ T) = T
      over(p)(both(rules.truth.flatMap(rules.disjIntro1(p, _)), rules.truth)),
      over(p)(both(rules.truth.flatMap(rules.disjIntro2(p, _)), rules.truth)),
      // (F \/ p) = p and (p \/ F) = p
      over(p)(both(assume(p).flatMap(rules.disjIntro2(falsity, _)),
        for { d <- logic.mkDisj(falsity, p).flatMap(assume); f <- assume(falsity); l <- rules.falsityElim(p, f); r <- assume(p); e <- rules.disjElim(d, l, r) } yield e)),
      over(p)(both(assume(p).flatMap(rules.disjIntro1(falsity, _)),
        for { d <- logic.mkDisj(p, falsity).flatMap(assume); l <- assume(p); f <- assume(falsity); r <- rules.falsityElim(p, f); e <- rules.disjElim(d, l, r) } yield e)),
      // (T ==> p) = p, (p ==> T) = T, (F ==> p) = T, (p ==> p) = T
      over(p)(both(assume(p).flatMap(rules.disch(truth, _)),
        for { i <- logic.mkImp(truth, p).flatMap(assume); t <- rules.truth; e <- rules.mp(i, t) } yield e)),
      over(p)(both(rules.truth.flatMap(rules.disch(p, _)), rules.truth)),
      over(p)(both(for { f <- assume(falsity); e <- rules.falsityElim(p, f); d <- rules.disch(falsity, e) } yield d, rules.truth)),
      over(p)(both(assume(p).flatMap(rules.disch(p, _)), rules.truth)),
      // (~T) = F and (~F) = T
      both(for { n <- logic.mkNot(truth); f <- assume(falsity); e <- rules.falsityElim(n, f) } yield e,
        for { n <- logic.mkNot(truth).flatMap(assume); t <- rules.truth; e <- rules.notElim(n, t) } yield e),
      both(assume(falsity).flatMap(rules.notIntro(falsity, _)), rules.truth)
    )
    Clauses.zip(derived).foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { case (acc, (text, clause)) =>
      for {
        done <- acc
        theorem <- clause
        stated <- Parser.proposition(theory, notation, text)
        checked <-
          if (theorem.hypotheses.isEmpty && theorem.conclusion == stated) Right(theorem)
          else Left(NotOfForm("the clause as it is stated, with no hypothesis", theorem.conclusion))
      } yield done :+ checked
    }
  }

  /** The equations a theorem gives `rewrite`: each equation it states, a conjunction of them being several. */
  def equations(logic: Logic, theorem: Kernel.Thm): Either[LogicError, Vector[Kernel.Thm]] =
    apart(logic, theorem, equationsOnly = true)

  /** The rules a theorem gives `simp`, which is every reading the description of this object lists. */
  def rules(logic: Logic, theorem: Kernel.Thm): Either[LogicError, Vector[Kernel.Thm]] =
    apart(logic, theorem, equationsOnly = false)

  private def apart(logic: Logic, theorem: Kernel.Thm, equationsOnly: Boolean): Either[LogicError, Vector[Kernel.Thm]] = {
    val rules = logic.rules
    def general(variables: Vector[FVar])(found: Vector[Kernel.Thm]): Either[LogicError, Vector[Kernel.Thm]] =
      found.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, one) =>
        acc.flatMap(done => rules.genAll(one, variables.toList).map(done :+ _))
      }
    Rewrite.specialiseAll(logic, theorem).flatMap { case (variables, open) =>
      val conclusion = open.conclusion
      logic.destConj(conclusion) match {
        case Some(_) =>
          for {
            left <- rules.conjElim1(open)
            right <- rules.conjElim2(open)
            leftRules <- apart(logic, left, equationsOnly)
            rightRules <- apart(logic, right, equationsOnly)
            closed <- general(variables)(leftRules ++ rightRules)
          } yield closed
        case None if Term.destEq(conclusion).isDefined => Right(Vector(theorem))
        case None if equationsOnly => Left(NotOfForm("an equation, or a conjunction of equations", conclusion))
        case None =>
          (logic.destNot(conclusion), logic.destImp(conclusion)) match {
            case (Some(negated), _) => negation(logic, open, negated).flatMap(general(variables))
            case (None, Some((antecedent, consequent))) =>
              injectivity(logic, open, antecedent, consequent) match {
                case Some(equation) => equation.flatMap(e => general(variables)(Vector(e)))
                case None =>
                  Left(NotOfForm("a fact `simp` can rewrite with: a conditional equation is not one, so a fact of the shape A ==> B is refused", conclusion))
              }
            case (None, None) => rules.eqTruthIntro(open).flatMap(e => general(variables)(Vector(e)))
          }
      }
    }
  }

  /** `|- ~P` as `|- P = F`, and when `P` is `a = b` also as `|- (b = a) = F`. */
  private def negation(logic: Logic, theorem: Kernel.Thm, negated: Term): Either[LogicError, Vector[Kernel.Thm]] = {
    val rules = logic.rules
    def falsified(denial: Kernel.Thm, claim: Term): Either[LogicError, Kernel.Thm] =
      for {
        assumed <- LogicError.lift(Kernel.assume(claim))
        absurd <- rules.notElim(denial, assumed)
        bottom <- LogicError.lift(Kernel.assume(logic.falsity))
        anything <- rules.falsityElim(claim, bottom)
      } yield Kernel.deductAntisym(anything, absurd)
    for {
      forward <- falsified(theorem, negated)
      reversed <- Term.destEq(negated) match {
        case None => Right(Vector.empty)
        case Some((left, right)) =>
          for {
            flipped <- LogicError.lift(Term.eq(right, left))
            assumed <- LogicError.lift(Kernel.assume(flipped))
            back <- Conv.sym(assumed)
            absurd <- rules.notElim(theorem, back)
            denial <- rules.notIntro(flipped, absurd)
            equation <- falsified(denial, flipped)
          } yield Vector(equation)
      }
    } yield forward +: reversed
  }

  /**
   * `|- C xs = C ys ==> x1 = y1 /\ ...` as `|- (C xs = C ys) = (x1 = y1 /\ ...)`, when it is that
   * shape: the two sides of the antecedent are one constant applied to as many arguments, and the
   * consequent is the equations between the arguments that differ, in order. Nothing when it is
   * not that shape, for the caller to refuse.
   */
  private def injectivity(logic: Logic, theorem: Kernel.Thm, antecedent: Term, consequent: Term): Option[Either[LogicError, Kernel.Thm]] = {
    def spine(term: Term): (Term, List[Term]) = term match {
      case App(function, argument) =>
        val (head, arguments) = spine(function)
        (head, arguments :+ argument)
      case other => (other, Nil)
    }
    def isConstant(term: Term): Boolean = term match {
      case Const(_, _) => true
      case _ => false
    }
    def conjuncts(term: Term): List[Term] = logic.destConj(term) match {
      case Some((left, right)) => left :: conjuncts(right)
      case None => List(term)
    }
    for {
      sides <- Term.destEq(antecedent)
      (left, right) = sides
      (head, leftArguments) = spine(left)
      (other, rightArguments) = spine(right)
      if isConstant(head) && head == other && leftArguments.size == rightArguments.size && leftArguments.nonEmpty
      differing = leftArguments.zip(rightArguments).filter { case (a, b) => a != b }
      if conjuncts(consequent).flatMap(Term.destEq) == differing
    } yield {
      val rules = logic.rules
      for {
        assumedEquations <- LogicError.lift(Kernel.assume(consequent))
        pieces <- (1 until differing.size).foldLeft[Either[LogicError, (List[Kernel.Thm], Kernel.Thm)]](Right((Nil, assumedEquations))) {
          case (acc, _) =>
            acc.flatMap { case (done, rest) =>
              for { first <- rules.conjElim1(rest); remaining <- rules.conjElim2(rest) } yield (done :+ first, remaining)
            }
        }
        equations = pieces._1 :+ pieces._2
        byPair = differing.zip(equations).toMap
        backward <- leftArguments.zip(rightArguments).foldLeft[Either[LogicError, Kernel.Thm]](Right(Conv.refl(head))) {
          case (acc, (a, b)) =>
            acc.flatMap(function => LogicError.lift(Kernel.mkComb(function, byPair.getOrElse((a, b), Conv.refl(a)))))
        }
        assumedEquality <- LogicError.lift(Kernel.assume(antecedent))
        forward <- rules.mp(theorem, assumedEquality)
      } yield Kernel.deductAntisym(backward, forward)
    }
  }
}
