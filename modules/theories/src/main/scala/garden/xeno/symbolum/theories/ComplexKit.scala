package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The steps the derivations beside `Complex` are written in: `Fundamental`, `FiniteFourier`,
 * `CollatzFourier`, `RuleThirty` and `Decision`.
 *
 * Each is a line or two of `Rules`, `Conv` or `Linarith` under a name that says what the step is,
 * and none decides anything a reader has to trust: what comes out is a theorem the kernel built or a
 * refusal. They are one class rather than a copy in each file because the derivations open
 * existentials, split conjunctions, induct and rewrite under binders in the same way, and a copy is
 * where the two would start to disagree.
 *
 * `lookup` answers the complex numbers' own facts first and those of every link below after.
 */
private[theories] final case class ComplexKit(
  logic: Logic,
  classical: Classical,
  theory: Theory,
  notation: Notation,
  ring: Ring,
  linarith: Linarith,
  driver: Complex.Driver,
  induction: Kernel.Thm,
  lookup: String => Either[LogicError, Kernel.Thm],
  within: Kernel.Thm,
  reals: RealTheory,
  definitions: Map[String, Kernel.Thm]
) {
  val rules: Rules = logic.rules

  private val Reals: Type = TyApp(Real.TypeName, Nil)
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Complexes: Type = Complex.Complexes

  def fact(name: String): Either[LogicError, Kernel.Thm] = lookup(name)

  /** A proposition, beta-normal: a coefficient written as a lambda is applied where it is used. */
  def prop(text: String): Either[LogicError, Term] =
    for {
      t <- Parser.proposition(theory, notation, text)
      n <- normal(t)
    } yield n

  def normal(t: Term): Either[LogicError, Term] =
    Conv.betaNormalise(t).flatMap(eq => Term.destEq(eq.conclusion).map(_._2).toRight(NotOfForm("an equation", eq.conclusion)))

  def term(text: String, ty: Type): Either[LogicError, Term] = Parser.term(theory, notation, text, ty).flatMap(normal)
  def cx(text: String): Either[LogicError, Term] = term(text, Complexes)
  def re(text: String): Either[LogicError, Term] = term(text, Reals)
  def nm(text: String): Either[LogicError, Term] = term(text, Numbers)

  /** `thm` with its conclusion beta-normalised. */
  def beta(thm: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      eq <- Conv.betaNormalise(thm.conclusion)
      out <- LogicError.lift(Kernel.eqMp(eq, thm))
    } yield out

  def assume(text: String): Either[LogicError, Kernel.Thm] = prop(text).flatMap(t => LogicError.lift(Kernel.assume(t)))

  /** Specialise at the terms given, in order, and beta-normalise. */
  def spec(thm: Kernel.Thm, args: Term*): Either[LogicError, Kernel.Thm] = rules.specAll(thm, args.toList).flatMap(beta)
  def specR(thm: Either[LogicError, Kernel.Thm], args: Either[LogicError, Term]*): Either[LogicError, Kernel.Thm] =
    for {
      t <- thm
      as <- args.foldLeft[Either[LogicError, List[Term]]](Right(Nil))((acc, a) => for { l <- acc; x <- a } yield l :+ x)
      out <- spec(t, as*)
    } yield out

  def mp(imp: Kernel.Thm, premises: Kernel.Thm*): Either[LogicError, Kernel.Thm] =
    premises.foldLeft[Either[LogicError, Kernel.Thm]](Right(imp))((acc, p) => acc.flatMap(rules.mp(_, p)))

  def disch(text: String, thm: Kernel.Thm): Either[LogicError, Kernel.Thm] = prop(text).flatMap(rules.disch(_, thm))
  def gen(thm: Kernel.Thm, vars: FVar*): Either[LogicError, Kernel.Thm] = rules.genAll(thm, vars.toList)
  def conj(a: Kernel.Thm, b: Kernel.Thm): Either[LogicError, Kernel.Thm] = rules.conjIntro(a, b)
  def conjs(ts: Kernel.Thm*): Either[LogicError, Kernel.Thm] =
    ts.init.foldRight[Either[LogicError, Kernel.Thm]](Right(ts.last))((t, acc) => acc.flatMap(rules.conjIntro(t, _)))

  /** Every conjunct of a conjunction, nested to the right. */
  def split(thm: Kernel.Thm): Either[LogicError, Vector[Kernel.Thm]] =
    logic.destConj(thm.conclusion) match {
      case Some(_) =>
        for {
          l <- rules.conjElim1(thm)
          r <- rules.conjElim2(thm)
          rest <- split(r)
        } yield l +: rest
      case None => Right(Vector(thm))
    }

  /** `goal` by `Linarith` from `facts`, quotients abstracted. */
  def lin(facts: Seq[Kernel.Thm], goal: String): Either[LogicError, Kernel.Thm] = prop(goal).flatMap(linT(facts, _))
  def linT(facts: Seq[Kernel.Thm], goal: Term): Either[LogicError, Kernel.Thm] = Complex.conclude(logic, linarith, facts, goal)

  /** A closed schematic arithmetic fact over real variables. */
  def lemma(text: String): Either[LogicError, Kernel.Thm] = prop(text).flatMap(linarith.prove)

  /** An identity, at complex or real type, by the parts and `Ring`. */
  def identity(text: String, extra: Kernel.Thm*): Either[LogicError, Kernel.Thm] = prop(text).flatMap(driver.using(extra*).identity)

  /** `goal` rewritten with `equations` and closed by `close`. */
  def rewriting(equations: Seq[Kernel.Thm], goal: Term)(close: Term => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    Rewrite.Rule.all(logic, equations.toVector).flatMap(set => Induct.afterRewriting(set, goal)(close))

  def existsIntro(predicateText: String, witness: Term, holds: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      statement <- Parser.proposition(theory, notation, predicateText)
      predicate <- logic.destExistsPredicate(statement).toRight(NotOfForm("an existential", statement))
      out <- rules.existsIntro(predicate, witness, holds)
    } yield out

  /** The instance of an existential at a fresh variable named `name`, assumed: the case to prove. */
  def instance(existential: Kernel.Thm, name: String): Either[LogicError, (FVar, Kernel.Thm)] =
    for {
      predicate <- logic.destExistsPredicate(existential.conclusion).toRight(NotOfForm("an existential", existential.conclusion))
      ty <- Type.destFun(Term.typeOf(predicate)).map(_._1).toRight(NotOfForm("a predicate", predicate))
      v = Term.variable(name, ty)
      applied <- LogicError.lift(Term.app(predicate, v))
      reduced <- Conv.betaRoot(applied)
      body <- Term.destEq(reduced.conclusion).map(_._2).toRight(NotOfForm("an equation", reduced.conclusion))
      assumed <- LogicError.lift(Kernel.assume(body))
    } yield (v, assumed)

  /** `existential` eliminated: `use` proves the conclusion from the instance at a fresh `name`. */
  def choose(existential: Kernel.Thm, name: String)(use: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    for {
      opened <- instance(existential, name)
      (v, assumed) = opened
      proved <- use(v, assumed)
      out <- rules.existsElim(existential, v, proved)
    } yield out

  /** A proof by cases on `text`. */
  def cases(text: String)(yes: Kernel.Thm => Either[LogicError, Kernel.Thm], no: Kernel.Thm => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    for {
      p <- prop(text)
      np <- logic.mkNot(p)
      a <- LogicError.lift(Kernel.assume(p)).flatMap(yes)
      b <- LogicError.lift(Kernel.assume(np)).flatMap(no)
      out <- classical.cases(p, a, b)
    } yield out

  /** A statement by induction on `variable`, with everything else in `predicate` quantified inside. */
  def induct(variable: FVar, body: Term)(
    base: Term => Either[LogicError, Kernel.Thm],
    step: (FVar, Kernel.Thm, Term) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      predicate <- LogicError.lift(Term.abs(variable, body))
      inst <- rules.spec(predicate, induction)
      opened <- beta(inst)
      premises <- logic.destImp(opened.conclusion).toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(premises._1).toRight(NotOfForm("a conjunction", premises._1))
      provedBase <- base(halves._1)
      stepStripped <- Logic.stripForall(halves._2)
      k <- stepStripped._1.headOption.toRight(NotOfForm("a claim about every number", halves._2))
      parts <- logic.destImp(stepStripped._2).toRight(NotOfForm("an implication", stepStripped._2))
      assumed <- LogicError.lift(Kernel.assume(parts._1))
      reached <- step(k, assumed, parts._2)
      provedStep <- rules.disch(parts._1, reached).flatMap(rules.gen(k, _))
      both <- rules.conjIntro(provedBase, provedStep)
      out <- rules.mp(opened, both)
    } yield out

  /** `complex_sum F n = complex_sum G n` from `F k = G k` at a variable `k` nothing assumes. */
  def sumCong(k: FVar, pointwise: Kernel.Thm, n: Term): Either[LogicError, Kernel.Thm] =
    for {
      lambdas <- LogicError.lift(Kernel.abs(k, pointwise))
      summation <- LogicError.lift(theory.constant(Complex.Summation, Type.fun(Type.fun(Numbers, Complexes), Type.fun(Numbers, Complexes))))
      out <- Conv.apTerm(summation, lambdas).flatMap(Conv.apThm(_, n))
    } yield out

  /** Assume every antecedent of an implication, prove its conclusion with them, discharge them again. */
  def underHyps(goal: Term)(body: (Vector[Kernel.Thm], Term) => Either[LogicError, Kernel.Thm]): Either[LogicError, Kernel.Thm] = {
    def antecedents(t: Term, acc: Vector[Term]): (Vector[Term], Term) =
      logic.destImp(t) match {
        case Some((a, rest)) => antecedents(rest, acc :+ a)
        case None => (acc, t)
      }
    val (as, conclusion) = antecedents(goal, Vector.empty)
    for {
      assumed <- as.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty))((acc, a) =>
        for { v <- acc; h <- LogicError.lift(Kernel.assume(a)) } yield v :+ h)
      proved <- body(assumed, conclusion)
      out <- as.foldRight[Either[LogicError, Kernel.Thm]](Right(proved))((a, acc) => acc.flatMap(rules.disch(a, _)))
    } yield out
  }

  /** `goal` rewritten with `equations`, then closed by `Linarith` from `facts`. */
  def linAfter(equations: Seq[Kernel.Thm], facts: Seq[Kernel.Thm], goal: Term): Either[LogicError, Kernel.Thm] =
    rewriting(equations, goal)(linT(facts, _))

  /** `thm` specialised to the instance written in `text`, redexes contracted: by matching, never by position. */
  def at(thm: Kernel.Thm, text: String): Either[LogicError, Kernel.Thm] = prop(text).flatMap(rules.specToReduced(thm, _))
  def at(thm: Either[LogicError, Kernel.Thm], text: String): Either[LogicError, Kernel.Thm] = thm.flatMap(at(_, text))

  /** `term` with free variables replaced, through the kernel's own substitution. */
  def substitute(map: Map[FVar, Term], term: Term): Either[LogicError, Term] =
    LogicError.lift(Kernel.inst(map, Conv.refl(term))).flatMap(th =>
      Term.destEq(th.conclusion).map(_._1).toRight(NotOfForm("an equation", th.conclusion)))

  /** The predicate of the existential written in `text`. */
  def predicateOf(text: String): Either[LogicError, Term] =
    prop(text).flatMap(e => logic.destExistsPredicate(e).toRight(NotOfForm("an existential", e)))

  /** `?x. P x` from `holds`, which proves `P witness` up to beta. */
  def introduce(predicate: Term, witness: Term, holds: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      applied <- LogicError.lift(Term.app(predicate, witness))
      root <- Conv.betaRoot(applied)
      wanted <- Term.destEq(root.conclusion).map(_._2).toRight(NotOfForm("an equation", root.conclusion))
      toNormal <- Conv.betaNormalise(wanted)
      fromHolds <- Conv.betaNormalise(holds.conclusion)
      back <- Conv.sym(toNormal)
      bridge <- Conv.trans(fromHolds, back)
      moved <- LogicError.lift(Kernel.eqMp(bridge, holds))
      out <- rules.existsIntro(predicate, witness, moved)
    } yield out

  /** `Sum F n = Sum G n` over the reals, from `F k = G k` at a variable `k` nothing assumes. */
  def sumCongReal(k: FVar, pointwise: Kernel.Thm, n: Term): Either[LogicError, Kernel.Thm] =
    for {
      lambdas <- LogicError.lift(Kernel.abs(k, pointwise))
      summation <- LogicError.lift(theory.constant(Series.SumName, Type.fun(Type.fun(Numbers, Reals), Type.fun(Numbers, Reals))))
      out <- Conv.apTerm(summation, lambdas).flatMap(Conv.apThm(_, n))
    } yield out

  /** Equations chained left to right. */
  def trans(first: Kernel.Thm, rest: Kernel.Thm*): Either[LogicError, Kernel.Thm] =
    rest.foldLeft[Either[LogicError, Kernel.Thm]](Right(first))((acc, e) => acc.flatMap(Conv.trans(_, e)))

  /** `thm` with `equation` rewritten in it everywhere, under binders too. */
  def rw(equation: Kernel.Thm, thm: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    Rewrite.Rule.all(logic, Vector(equation)).flatMap(Rewrite.inTheorem(_, thm))
}

private[theories] object ComplexKit {

  /**
   * Each step of `order` run in turn over what the ones before it proved, and the facts
   * `statements` names read off the end: a lemma proved on the way and not named there stays here.
   */
  def derive[P](
    order: Vector[(String, P => Either[LogicError, Kernel.Thm])],
    statements: Vector[(String, String)],
    held: Map[String, Kernel.Thm]
  )(proofs: Map[String, Kernel.Thm] => P): Either[LogicError, Map[String, Kernel.Thm]] =
    for {
      proved <- order.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(held)) { case (acc, (name, step)) =>
        for {
          known <- acc
          made <- step(proofs(known))
        } yield known + (name -> made)
      }
      published <- statements.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) { case (acc, (name, _)) =>
        for {
          made <- acc
          fact <- proved.get(name).toRight(MissingDefinition(name))
        } yield made + (name -> fact)
      }
    } yield published
}
