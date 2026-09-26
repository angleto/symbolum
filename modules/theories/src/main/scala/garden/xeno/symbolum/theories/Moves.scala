package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The moves a hand derivation over `num` is written in, in direct style: each returns a theorem or
 * throws [[Moves.RefusedHere]], which the development catches once at its door and hands back as the
 * refusal it carries. Nothing here constructs a theorem the kernel would not; every move is a derived
 * rule or a sequence of them.
 *
 * `Pigeonhole` wrote these first, inside its builder over a whole `Chain`. They moved here on
 * 2026-09-26 because `Wilson` needed them at a place a chain does not exist yet: `Primes` is built
 * while the chain is being assembled, and publishes what `Wilson` derives. So what the moves need is
 * a [[Moves.Ground]], the theory and notation texts are read in, the logic, the classical extension,
 * and a lookup for facts and definitions by name, and a chain is one way of supplying it.
 * `Steps` is the other set of moves in this package, over the same `Freshman.Kit` in the monadic
 * style `Euler` is written in; the two are the two styles, and neither is a copy of the other.
 *
 * Texts are annotated by [[Moves.annotatedWith]] from a table of the caller's variables, so a name
 * elaborated at a type the table does not declare is refused where it is written rather than forty
 * lines later as a refused `mp`.
 */
private[theories] class Moves(val ground: Moves.Ground, types: Map[String, Type], written: Map[Type, String]) {
  import Moves.{Num, RefusedHere}

  private def annotated(text: String): String = Moves.annotatedWith(types, written)(text)

  val theory: Theory = ground.theory
  val notation: Notation = ground.notation
  val logic: Logic = ground.logic
  val rules: Rules = logic.rules
  val classical: Classical = ground.classical
  val propositional = Propositional.over(classical, logic)
  val intuitionistic = Intuitionistic(logic)

  /* --------------------------------------------------------------- the moves */

  def force[T](result: Either[LogicError, T]): T =
    result.fold(error => throw new RefusedHere(error), identity)

  def refuse(what: String, term: Term): Nothing = throw new RefusedHere(NotOfForm(what, term))

  def typed(term: Term, holes: Set[String]): Term = {
    Term.freeVariables(term).foreach { variable =>
      if (!holes.contains(variable.name) && !types.get(variable.name).contains(variable.ty))
        refuse(s"the variable ${variable.name} at the type the derivation declares for it", variable)
    }
    term
  }

  def prop(text: String): Term = typed(force(Parser.proposition(theory, notation, annotated(text))), Set.empty)
  def term(text: String, ty: Type): Term = typed(force(Parser.term(theory, notation, annotated(text), ty)), Set.empty)
  def variable(name: String): FVar =
    Term.variable(name, types.getOrElse(name, refuse("a declared variable", Term.variable(name, Type.Bool))))

  def assumeT(statement: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(statement)))
  def assume(text: String): Kernel.Thm = assumeT(prop(text))

  def pf(name: String): Kernel.Thm = force(ground.fact(name))
  def nf(name: String): Kernel.Thm = force(ground.fact(name))
  def cf(name: String): Kernel.Thm = force(classical.fact(name))
  def rf(name: String): Kernel.Thm = force(ground.fact(name))

  def freeIn(theorem: Kernel.Thm): Set[FVar] =
    theorem.hypotheses.flatMap(Term.freeVariables).toSet ++ Term.freeVariables(theorem.conclusion)

  def reduced(theorem: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(theorem.conclusion).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))

  /** Specialise the leading quantifiers at texts, each read at its binder's type, and reduce. */
  def spec(theorem: Kernel.Thm, arguments: String*): Kernel.Thm =
    reduced(arguments.foldLeft(theorem) { (current, text) =>
      val predicate = logic.destForallPredicate(current.conclusion).getOrElse(refuse("a universal", current.conclusion))
      val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(refuse("a predicate", predicate))
      force(rules.spec(term(text, domain), current))
    })

  /** Replace free variables by texts, each read at the variable's type, and reduce. */
  def inst(theorem: Kernel.Thm, pairs: (String, String)*): Kernel.Thm = {
    val free = freeIn(theorem)
    val substitution: Map[FVar, Term] = pairs.map { case (name, text) =>
      val target = free.find(_.name == name).getOrElse(refuse(s"a theorem with $name free in it", theorem.conclusion))
      target -> term(text, target.ty)
    }.toMap
    reduced(force(LogicError.lift(Kernel.inst(substitution, theorem))))
  }

  def mp(implication: Kernel.Thm, premises: Kernel.Thm*): Kernel.Thm =
    premises.foldLeft(implication)((current, premise) => force(rules.mp(current, premise)))

  def conj(left: Kernel.Thm, right: Kernel.Thm): Kernel.Thm = force(rules.conjIntro(left, right))
  def left(theorem: Kernel.Thm): Kernel.Thm = force(rules.conjElim1(theorem))
  def right(theorem: Kernel.Thm): Kernel.Thm = force(rules.conjElim2(theorem))

  /** `t1 ==> ... ==> tn ==> <conclusion>`, discharging the texts in the order written. */
  def discharged(theorem: Kernel.Thm, texts: String*): Kernel.Thm =
    texts.reverse.foldLeft(theorem)((current, text) => force(rules.disch(prop(text), current)))

  def generalised(theorem: Kernel.Thm, names: String*): Kernel.Thm =
    force(rules.genAll(theorem, names.toList.map(variable)))

  def sym(equation: Kernel.Thm): Kernel.Thm = force(Conv.sym(equation))
  def trans(first: Kernel.Thm, second: Kernel.Thm): Kernel.Thm = force(Conv.trans(first, second))
  def congruent(fn: String, equation: Kernel.Thm): Kernel.Thm = {
    val (lhs, _) = Term.destEq(equation.conclusion).getOrElse(refuse("an equation", equation.conclusion))
    force(Conv.apTerm(term(fn, Type.fun(Term.typeOf(lhs), Num)), equation))
  }

  /**
   * `|- T[b]` from `|- a = b` and `|- T[a]`, where `T` is `template` with its hole written `zz`.
   *
   * Through the abstraction `\zz. T` and two root contractions, so nothing else in `T` moves.
   */
  def transport(equation: Kernel.Thm, template: String, theorem: Kernel.Thm): Kernel.Thm = {
    val (lhs, _) = Term.destEq(equation.conclusion).getOrElse(refuse("an equation", equation.conclusion))
    val zz = Term.variable("zz", Term.typeOf(lhs))
    // Every hole in this file is a number; a hole of another type is refused rather than guessed.
    if (Term.typeOf(lhs) != Num) refuse("an equation between numbers", equation.conclusion)
    val body = typed(force(Parser.proposition(theory, notation, annotated(template).replace("zz", "(zz:num)"))), Set("zz"))
    val lambda = force(LogicError.lift(Term.abs(zz, body)))
    val across = force(Conv.apTerm(lambda, equation))
    val (from, to) = Term.destEq(across.conclusion).getOrElse(refuse("an equation", across.conclusion))
    val opened = force(Conv.betaRoot(from))
    val closed = force(Conv.betaRoot(to))
    val joined = trans(trans(sym(opened), across), closed)
    val (start, _) = Term.destEq(joined.conclusion).getOrElse(refuse("an equation", joined.conclusion))
    if (start != theorem.conclusion) refuse("a proof of the template at the left side", theorem.conclusion)
    force(LogicError.lift(Kernel.eqMp(joined, theorem)))
  }

  /** Every free occurrence of the variable `x` replaced by `t`, from `|- x = t`. */
  def substituted(equation: Kernel.Thm, theorem: Kernel.Thm): Kernel.Thm = {
    val (lhs, _) = Term.destEq(equation.conclusion).getOrElse(refuse("an equation", equation.conclusion))
    val x = lhs match {
      case variable: FVar => variable
      case other => refuse("an equation whose left side is a variable", other)
    }
    val zz = Term.variable("zz", x.ty)
    val body = force(LogicError.lift(Term.substitute(Map(x -> zz), theorem.conclusion)))
    val lambda = force(LogicError.lift(Term.abs(zz, body)))
    val across = force(Conv.apTerm(lambda, equation))
    val (from, to) = Term.destEq(across.conclusion).getOrElse(refuse("an equation", across.conclusion))
    val joined = trans(trans(sym(force(Conv.betaRoot(from))), across), force(Conv.betaRoot(to)))
    force(LogicError.lift(Kernel.eqMp(joined, theorem)))
  }

  def absurd(negation: Kernel.Thm, positive: Kernel.Thm): Kernel.Thm = force(rules.notElim(negation, positive))
  def exFalso(statement: Term, falsity: Kernel.Thm): Kernel.Thm = force(rules.falsityElim(statement, falsity))

  /** `|- ~(b = a)` from `|- ~(a = b)`. */
  def unequalSym(theorem: Kernel.Thm): Kernel.Thm = {
    val equation = logic.destNot(theorem.conclusion).getOrElse(refuse("a negation", theorem.conclusion))
    val (a, b) = Term.destEq(equation).getOrElse(refuse("an equation", equation))
    val flipped = force(LogicError.lift(Term.eq(b, a)))
    force(rules.notIntro(flipped, absurd(theorem, sym(assumeT(flipped)))))
  }

  /** `|- A = F` from `|- ~A`. */
  def falseEquation(theorem: Kernel.Thm): Kernel.Thm = {
    val statement = logic.destNot(theorem.conclusion).getOrElse(refuse("a negation", theorem.conclusion))
    val fromFalsity = exFalso(statement, assumeT(logic.falsity))
    val toFalsity = absurd(theorem, assumeT(statement))
    Kernel.deductAntisym(fromFalsity, toFalsity)
  }

  def truthEquation(theorem: Kernel.Thm): Kernel.Thm = force(rules.eqTruthIntro(theorem))

  /** A propositional consequence of the premises, the subterms read as atoms. */
  def taut(goal: Term, premises: Kernel.Thm*): Kernel.Thm = {
    val implication = premises.foldRight(goal)((premise, acc) => force(logic.mkImp(premise.conclusion, acc)))
    val proved = intuitionistic.prove(implication).orElse(propositional.prove(implication))
    mp(force(proved), premises*)
  }

  /** By the excluded middle on `statement`: each branch receives its assumption. */
  def cases(statement: Term)(positive: Kernel.Thm => Kernel.Thm, negative: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
    val denial = force(logic.mkNot(statement))
    force(classical.cases(statement, positive(assumeT(statement)), negative(assumeT(denial))))
  }

  /** `|- statement`, from falsity under its denial. */
  def byContradiction(statement: Term)(reach: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
    val denial = force(logic.mkNot(statement))
    force(classical.contradiction(statement, reach(assumeT(denial))))
  }

  /** `|- ~statement`, from falsity under the statement. */
  def refuted(statement: Term)(reach: Kernel.Thm => Kernel.Thm): Kernel.Thm =
    force(rules.notIntro(statement, reach(assumeT(statement))))

  def byDisjunction(disjunction: Kernel.Thm)(first: Kernel.Thm => Kernel.Thm, second: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
    val (a, b) = logic.destDisj(disjunction.conclusion).getOrElse(refuse("a disjunction", disjunction.conclusion))
    force(rules.disjElim(disjunction, first(assumeT(a)), second(assumeT(b))))
  }

  def disjoined(target: Term, proof: Kernel.Thm): Kernel.Thm = {
    val (a, b) = logic.destDisj(target).getOrElse(refuse("a disjunction", target))
    if (proof.conclusion == a) force(rules.disjIntro1(b, proof))
    else if (proof.conclusion == b) force(rules.disjIntro2(a, proof))
    else refuse("a proof of one of the two disjuncts", proof.conclusion)
  }

  /** Eliminates an existential into `reach`'s theorem, the witness being the variable `name`. */
  def opened(existential: Kernel.Thm, name: String)(reach: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
    val predicate = logic.destExistsPredicate(existential.conclusion).getOrElse(refuse("an existential", existential.conclusion))
    val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(refuse("a predicate", predicate))
    val witness = Term.variable(name, domain)
    if (freeIn(existential).contains(witness)) refuse(s"an existential in which $name is not already free", existential.conclusion)
    val applied = force(LogicError.lift(Term.app(predicate, witness)))
    val body = Term.destEq(force(Conv.betaRoot(applied)).conclusion).map(_._2).getOrElse(refuse("an equation", applied))
    force(rules.existsElim(existential, witness, reach(assumeT(body))))
  }

  /** `|- ?x1 ... xn. body` from a proof of the body at the witnesses, each read at its type. */
  def witnessed(target: Term, witnesses: List[String], proof: Kernel.Thm): Kernel.Thm =
    witnessedBy(target, witnesses.map(text => (domain: Type) => term(text, domain)), proof)

  /** The same, with each witness built from the type its binder has. */
  def witnessedBy(target: Term, witnesses: List[Type => Term], proof: Kernel.Thm): Kernel.Thm =
    witnesses match {
      case Nil =>
        if (target == proof.conclusion) proof
        else {
          val normal = force(Conv.betaNormalise(target))
          val (_, reducedTarget) = Term.destEq(normal.conclusion).getOrElse(refuse("an equation", target))
          if (reducedTarget == proof.conclusion) force(LogicError.lift(Kernel.eqMp(sym(normal), proof)))
          else refuse("a proof of the body the existential opens to", proof.conclusion)
        }
      case first :: rest =>
        val predicate = logic.destExistsPredicate(target).getOrElse(refuse("an existential", target))
        val domain = Type.destFun(Term.typeOf(predicate)).map(_._1).getOrElse(refuse("a predicate", predicate))
        val witness = first(domain)
        val applied = force(LogicError.lift(Term.app(predicate, witness)))
        val inner = Term.destEq(force(Conv.betaRoot(applied)).conclusion).map(_._2).getOrElse(refuse("an equation", applied))
        force(rules.existsIntro(predicate, witness, witnessedBy(inner, rest, proof)))
    }

  /** `COND c y z = y` from `|- c`, at `num`. */
  def whenHolds(guard: Kernel.Thm, y: String, z: String): Kernel.Thm =
    mp(force(rules.specAll(Kernel.instType(Map(Classical.TypeVariable -> Num), cf(Classical.CondTrue)),
      List(guard.conclusion, term(y, Num), term(z, Num)))), guard)

  /** `COND c y z = z` from `|- ~c`, at `num`. */
  def whenFails(guard: Kernel.Thm, y: String, z: String): Kernel.Thm = {
    val statement = logic.destNot(guard.conclusion).getOrElse(refuse("a negation", guard.conclusion))
    mp(force(rules.specAll(Kernel.instType(Map(Classical.TypeVariable -> Num), cf(Classical.CondFalse)),
      List(statement, term(y, Num), term(z, Num)))), guard)
  }

  /** `|- C a1 ... an = <its body>`, reduced, for a definition the ground can find. */
  def unfolded(name: String, arguments: String*): Kernel.Thm = {
    val definition = force(ground.definition(name))
    val names = arguments.toList.map(variable)
    val equation = force(Conv.unfold(definition, names))
    val body = Term.destEq(equation.conclusion).map(_._2).getOrElse(refuse("an equation", equation.conclusion))
    trans(equation, force(Conv.betaNormalise(body)))
  }

  def openDefinition(name: String, theorem: Kernel.Thm, arguments: String*): Kernel.Thm =
    force(LogicError.lift(Kernel.eqMp(unfolded(name, arguments*), theorem)))

}

private[theories] object Moves {

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Fun: Type = Type.fun(Num, Num)

  /**
   * What the moves read: the theory and notation a text is parsed in, the logic, the classical
   * extension, and a lookup of facts and of definitions by name.
   */
  final case class Ground(
    theory: Theory,
    notation: Notation,
    logic: Logic,
    classical: Classical,
    fact: String => Either[LogicError, Kernel.Thm],
    definition: String => Either[LogicError, Kernel.Thm]
  )

  object Ground {

    /** The ground at a chain's widest signature, finding a fact in any development `Pigeonhole` read one from. */
    def of(chain: Chain): Ground = {
      val signature = chain.widest
      def fact(name: String): Either[LogicError, Kernel.Thm] =
        chain.peano.fact(name)
          .orElse(chain.naturals.fact(name))
          .orElse(chain.classical.fact(name))
          .orElse(chain.resolving.fact(name))
          .left.map(_ => MissingDefinition(name))
      Ground(signature.theory, signature.notation, chain.logic, chain.classical, fact, chain.resolving.definition)
    }
  }

  /** Carry a refusal out of a derivation written in direct style. */
  final class RefusedHere(val error: LogicError) extends RuntimeException(error.message)

  val Written: Map[Type, String] = Map(
    Num -> "num",
    Fun -> "num->num",
    Type.fun(Num, Fun) -> "num->num->num",
    Type.fun(Num, Type.fun(Num, Type.Bool)) -> "num->num->bool",
    Type.fun(Num, Type.Bool) -> "num->bool"
  )

  private val Identifier = "(?<![A-Za-z0-9_])([A-Za-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_])".r

  /**
   * Every occurrence of a name in `Types` written with its type, except where it is being bound.
   *
   * The texts here are short and many of their variables occur where nothing fixes a type, `g x =
   * g y` being the plain case, and a name elaborated at an open type is refused. Annotating each by
   * hand was the first version, and it failed at the first run in eleven places.
   */

  /**
   * [[annotated]] over a table of the caller's, which is what lets a development with variables of
   * its own reuse [[Builder]] rather than copy it.
   */
  def annotatedWith(types: Map[String, Type], written: Map[Type, String])(text: String): String =
    Identifier.replaceAllIn(text, found => {
      val name = found.group(1)
      val rest = text.substring(found.end).dropWhile(_ == ' ')
      types.get(name).flatMap(written.get) match {
        case Some(written) if !rest.startsWith(":") =>
          scala.util.matching.Regex.quoteReplacement(s"($name:$written)")
        case _ => scala.util.matching.Regex.quoteReplacement(name)
      }
    })
}
