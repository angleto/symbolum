package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What the embedded theory can prove, as a predicate on codes.
 *
 * `NUM_PROV n` says the formula coded by `n` is derivable in Peano arithmetic. It is the last thing
 * Goedel's argument needs before the diagonal, and the reason it is a development of its own rather
 * than more of [[Language]] is that it is about that language rather than part of it: nothing here
 * declares a constructor or a predicate of the object syntax.
 *
 * **Not one of the three definitions is a recursion**, and that is the whole return on
 * `docs/adr/0013`. A derivation is a finite sequence of formulas, and a definition that had to walk
 * one would be a recursion over the length. The beta function is what removes that: a sequence is
 * two numbers, `NUM_BETA a b j` is its `j`th entry, and quantifying over the entries is quantifying
 * over an index. So `NUM_STEP`, `NUM_PROOF` and `NUM_PROV` are formulas with their subjects free,
 * exactly as `NUM_PA` and `NUM_LOGIC` are, and all three cost no axiom.
 *
 * **A proof carries the index of its last step, not its length.** `NUM_PROOF d n` holds when `d` is
 * `NUM_PAIR k (NUM_PAIR a b)`, every step from `0` to `k` is justified, and step `k` is `n`. Writing
 * the length instead would put `0 < k` and a `k - 1` into every statement about a proof, and the
 * subtraction on `num` is truncated, so that is a guard and an asymmetry bought for nothing.
 *
 * **Two rules of inference and not three.** Modus ponens and generalisation, which with the eight
 * schemes of [[Language]] are a complete Hilbert system. A step is an axiom of PA, a logical axiom,
 * a modus ponens from two **earlier** steps, or a generalisation of one earlier step; the bounds on
 * `x` and `y` are what make a derivation well founded without anything here being a recursion.
 *
 * What is here and what is not, dated rather than left to be found. The predicate is **inhabited**:
 * every axiom is provable, which is the one-step derivation and this file's first consumer of
 * `NUM_BETA_SEQUENCE`. What is not here is closure under the rules, `NUM_PROV (p ==> q)` and
 * `NUM_PROV p` giving `NUM_PROV q`, which is the second of Goedel's derivability conditions and
 * needs two derivations concatenated into one sequence.
 */
final class Provability private (
  val language: Language,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  val numbering: Numbering = language.numbering

  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Provability {

  /** `NUM_STEP a b j` says the `j`th entry of the sequence `a`, `b` is a justified step. */
  val StepName: String = "NUM_STEP"

  /** `|- !a b j. NUM_STEP a b j = (<an axiom> \/ <modus ponens> \/ <a generalisation>)`. */
  val StepCases: String = "NUM_STEP_CASES"

  /** `NUM_PROOF d n` says `d` codes a derivation whose last line is the formula `n`. */
  val ProofName: String = "NUM_PROOF"

  /** `|- !d n. NUM_PROOF d n = (?k a b. ...)`. */
  val ProofCases: String = "NUM_PROOF_CASES"

  /** `NUM_PROV n` says the formula `n` is derivable. */
  val ProvableName: String = "NUM_PROV"

  /** `|- !n. NUM_PROV n = (?d. NUM_PROOF d n)`. */
  val ProvableCases: String = "NUM_PROV_CASES"

  /** `|- !n. NUM_PA n ==> NUM_PROV n`. */
  val ProvablePeano: String = "NUM_PROV_PA"

  /** `|- !n. NUM_LOGIC n ==> NUM_PROV n`. */
  val ProvableLogic: String = "NUM_PROV_LOGIC"

  /**
   * A justified step stays justified when the sequence it lives in is moved along.
   *
   * `|- !a b c u v m j. (!i. i <= m ==> NUM_BETA a b (c + i) = NUM_BETA u v i) ==> j <= m ==>
   * NUM_STEP u v j ==> NUM_STEP a b (c + j)`
   *
   * The lemma the second derivability condition is built from, and the only hard thing in it. To
   * put two derivations end to end their steps have to be renumbered, and a step's justification
   * names **earlier steps by index**, so every one of those indices moves too. What makes it work
   * is that the bounds move with them: `x < j` gives `c + x < c + j`, which is why
   * `Peano.NUM_ADD_LT_MONOTONE` had to be proved before this.
   *
   * It is stated with a shift rather than as two lemmas because the shift at zero **is** the other
   * one: the first block of a concatenation keeps its numbering, the second does not, and a lemma
   * for each would be this proof written twice with `c + j` replaced by `j`.
   *
   * The agreement is only asked for up to `m`, which is the whole point. A concatenated sequence
   * does not agree with either half beyond that half's own last step, and a lemma that asked for
   * agreement everywhere would be true and useless.
   */
  val StepShift: String = "NUM_STEP_SHIFT"

  /**
   * A step's four ways of being justified, with the three subjects free.
   *
   * Written once and read twice, as the body of the definition and as the right-hand side of the
   * published equation. The two used to be separate strings in the development below this one and
   * the second went stale; here there is one.
   */
  private def stepBody(a: String, b: String, at: String): String = {
    val here = s"NUM_BETA $a $b $at"
    s"NUM_PA ($here) " +
      s"\\/ NUM_LOGIC ($here) " +
      s"\\/ (?x:num. ?y:num. NUM_LT x $at /\\ NUM_LT y $at /\\ " +
      s"NUM_BETA $a $b x = NUM_CODE 7 (NUM_PAIR (NUM_BETA $a $b y) ($here))) " +
      s"\\/ (?x:num. ?i:num. NUM_LT x $at /\\ " +
      s"$here = NUM_CODE 8 (NUM_PAIR i (NUM_BETA $a $b x)))"
  }

  /** A proof's three parts: the shape of the code, its last line, and every step justified. */
  private def proofBody(proof: String, claim: String): String =
    s"?k:num. ?a:num. ?b:num. $proof = NUM_PAIR k (NUM_PAIR a b) /\\ " +
      s"NUM_BETA a b k = $claim /\\ (!j:num. NUM_LE j k ==> NUM_STEP a b j)"

  val Statements: Vector[(String, String)] = Vector(
    StepCases -> s"!a:num b:num j:num. NUM_STEP a b j = (${stepBody("a", "b", "j")})",
    ProofCases -> s"!d:num n:num. NUM_PROOF d n = (${proofBody("d", "n")})",
    ProvableCases -> "!n:num. NUM_PROV n = (?d:num. NUM_PROOF d n)",
    ProvablePeano -> "!n:num. NUM_PA n ==> NUM_PROV n",
    ProvableLogic -> "!n:num. NUM_LOGIC n ==> NUM_PROV n",
    StepShift ->
      ("!a:num b:num c:num u:num v:num m:num j:num. " +
        "(!i:num. NUM_LE i m ==> NUM_BETA a b (NUM_ADD c i) = NUM_BETA u v i) ==> " +
        "NUM_LE j m ==> NUM_STEP u v j ==> NUM_STEP a b (NUM_ADD c j)")
  )

  /** Build it over the language, in that development's own notation. */
  def construct(language: Language): Either[LogicError, Provability] =
    construct(language, language.theory, language.notation)

  /** The same, extending a theory that already holds something else. */
  def construct(
    language: Language,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Provability] =
    for {
      withStep <- Language.defineByCases(
        base,
        notation,
        language.logic,
        StepName,
        s"\\a:num. \\b:num. \\j:num. ${stepBody("a", "b", "j")}",
        List("a", "b", "j")
      )
      (stepTheory, stepDefinition, stepCases) = withStep
      stepLogic <- language.logic.over(stepTheory)

      withProof <- Language.defineByCases(
        stepTheory,
        notation,
        stepLogic,
        ProofName,
        s"\\d:num. \\n:num. ${proofBody("d", "n")}",
        List("d", "n")
      )
      (proofTheory, proofDefinition, proofCases) = withProof
      proofLogic <- language.logic.over(proofTheory)

      withProvable <- Language.defineByCases(
        proofTheory,
        notation,
        proofLogic,
        ProvableName,
        "\\n:num. ?d:num. NUM_PROOF d n",
        List("n")
      )
      (theory, provableDefinition, provableCases) = withProvable
      logic <- language.logic.over(theory)

      facts = Map(
        StepCases -> stepCases,
        ProofCases -> proofCases,
        ProvableCases -> provableCases
      )
      fromPeano <- inhabited(language, theory, notation, logic, facts, Language.AxiomName, 0,
        ProvablePeano)
      fromLogic <- inhabited(language, theory, notation, logic, facts, Language.LogicName, 1,
        ProvableLogic)
      shifted <- stepsShift(language, theory, notation, logic, facts)
    } yield new Provability(
      language,
      theory,
      notation,
      logic,
      Map(
        StepName -> stepDefinition,
        ProofName -> proofDefinition,
        ProvableName -> provableDefinition
      ),
      facts
        .updated(ProvablePeano, fromPeano)
        .updated(ProvableLogic, fromLogic)
        .updated(StepShift, shifted)
    )

  /**
   * [[StepShift]], by the four-way case analysis the step relation asks for.
   *
   * Each case is the same shape: the justification names some indices, each of those is at most
   * `m` because it is below `j` and `j` is, so the agreement applies to it, and the shifted index
   * keeps its bound by strict monotonicity. The axiom cases name no index at all and are two lines.
   *
   * **Written in direct style with the refusal carried out by an exception**, which the rest of
   * this module does not do. The reason is the shape rather than the length: a `for` comprehension
   * over `Either` makes four independent cases into one sequence of bindings, and the case that
   * fails is then found by reading which binding came first. The exception is caught here and
   * nowhere else, and what leaves this method is an `Either` like everything else.
   */
  private def stepsShift(
    language: Language,
    theory: Theory,
    notation: Notation,
    logic: Logic,
    facts: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val chain = language.numbering

    def force[T](result: Either[LogicError, T]): T =
      result.fold(error => throw new RefusedHere(error), identity)

    try {
    def variable(name: String): FVar = Term.variable(name, numbers)

    val a = variable("a"); val b = variable("b"); val c = variable("c")
    val u = variable("u"); val v = variable("v")
    val m = variable("m"); val j = variable("j")

    def app(head: Term, args: List[Term]): Term = force(LogicError.lift(Term.appAll(head, args)))

    val beta = force(LogicError.lift(theory.constant(Coding.BetaName,
      Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, numbers))))))
    val plus = force(LogicError.lift(theory.constant(Peano.Addition,
      Type.fun(numbers, Type.fun(numbers, numbers)))))
    val atMost = force(LogicError.lift(theory.constant(Peano.NonStrictOrder,
      Type.fun(numbers, Type.fun(numbers, Type.Bool)))))
    val pair = force(LogicError.lift(theory.constant(Numbering.PairName,
      Type.fun(numbers, Type.fun(numbers, numbers)))))
    val codeConst = force(LogicError.lift(theory.constant(Numbering.CodeName,
      Type.fun(numbers, Type.fun(numbers, numbers)))))
    def tagged(tag: String): Term =
      app(codeConst, List(force(Parser.term(theory, notation, tag, numbers))))

    val peanoSet = force(LogicError.lift(theory.constant(Language.AxiomName,
      Type.fun(numbers, Type.Bool))))
    val logicSet = force(LogicError.lift(theory.constant(Language.LogicName,
      Type.fun(numbers, Type.Bool))))

    def shifted(i: Term): Term = app(plus, List(c, i))
    def wide(i: Term): Term = app(beta, List(a, b, i))
    def narrow(i: Term): Term = app(beta, List(u, v, i))

    val agreement = force(Parser.proposition(theory, notation,
      "!i:num. NUM_LE i m ==> NUM_BETA a b (NUM_ADD c i) = NUM_BETA u v i"))
    val agree = force(LogicError.lift(Kernel.assume(agreement)))
    val boundTerm = app(atMost, List(j, m))
    val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))
    val sourceTerm = force(Parser.proposition(theory, notation, "NUM_STEP u v j"))
    val source = force(LogicError.lift(Kernel.assume(sourceTerm)))

    val stepCases = force(facts.get(StepCases).toRight(MissingDefinition(StepCases)))
    val target = force(rules.specAll(stepCases, List(a, b, shifted(j))))
    val at = force(rules.specAll(stepCases, List(u, v, j)))
    val opened = force(LogicError.lift(Kernel.eqMp(at, source)))

    def disjunctsOf(t: Term, count: Int): Vector[Term] =
      if (count == 1) Vector(t)
      else {
        val (first, rest) = logic.destDisj(t).getOrElse(sys.error(s"a disjunction: $t"))
        first +: disjunctsOf(rest, count - 1)
      }

    def nestOf(run: Vector[Term]): Term =
      run.toList.reverse match {
        case Nil => sys.error("a disjunct")
        case last :: rest => rest.foldLeft(last)((carried, one) => force(logic.mkDisj(one, carried)))
      }

    val targetParts = disjunctsOf(Term.destEq(target.conclusion).map(_._2).get, 4)
    val sourceParts = disjunctsOf(Term.destEq(at.conclusion).map(_._2).get, 4)

    def injected(which: Int, proof: Kernel.Thm): Kernel.Thm = {
      val entered =
        if (which == 3) proof
        else force(rules.disjIntro1(nestOf(targetParts.drop(which + 1)), proof))
      (0 until which).reverse.foldLeft(entered)((carried, before) =>
        force(rules.disjIntro2(targetParts(before), carried)))
    }

    /** `NUM_BETA a b (c + i) = NUM_BETA u v i`, for an `i` shown to be at most `m`. */
    def agreesAt(i: Term, small: Kernel.Thm): Kernel.Thm =
      force(rules.spec(i, agree).flatMap(rules.mp(_, small)))

    val here = agreesAt(j, bounded)

    /** From `i < j` and `j <= m`, that `i <= m`. */
    def atMostM(below: Kernel.Thm, witness: Term): Kernel.Thm = {
      val chained = force(rules.conjIntro(below, bounded))
      val strict = force(rules.specAll(force(chain.peano.fact(Peano.BelowThenAtMost)),
        List(witness, j, m)).flatMap(rules.mp(_, chained)))
      force(rules.specAll(force(chain.peano.fact(Peano.AtMostFromBelow)), List(witness, m))
        .flatMap(rules.mp(_, strict)))
    }

    def strictShift(below: Kernel.Thm, witness: Term): Kernel.Thm =
      force(rules.specAll(force(chain.peano.fact(Peano.AddStrictlyMonotone)), List(c, witness, j))
        .flatMap(rules.mp(_, below)))

    def open(existential: Kernel.Thm, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val predicate = logic.destExistsPredicate(existential.conclusion).get
      val fresh = Conv.freshVariable(name, numbers, taken)
      val applied = app(predicate, List(fresh))
      val contraction = force(Conv.betaRoot(applied))
      val body = Term.destEq(contraction.conclusion).map(_._2).get
      val instance = force(LogicError.lift(Kernel.assume(body)))
      force(rules.existsElim(existential, fresh, reach(fresh, instance)))
    }

    def instantiate(existential: Term, argument: Term): Term = {
      val inner = logic.destExistsPredicate(existential).get
      val applied = app(inner, List(argument))
      Term.destEq(force(Conv.betaRoot(applied)).conclusion).map(_._2).get
    }

    /** Case 0 and 1: the step is an axiom, and the two codes are equal. */
    def axiomCase(which: Int, head: Term): Kernel.Thm = {
      val assumed = force(LogicError.lift(Kernel.assume(sourceParts(which))))
      val moved = force(Conv.apTerm(head, here).flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed))))
      injected(which, moved)
    }

    val taken = Set(a, b, c, u, v, m, j)

    val modusPonens = {
      val assumed = force(LogicError.lift(Kernel.assume(sourceParts(2))))
      open(assumed, "x", taken) { (left, atLeft) =>
        open(atLeft, "y", taken + left) { (right, atRight) =>
          val leftBelow = force(rules.conjElim1(atRight))
          val restOne = force(rules.conjElim2(atRight))
          val rightBelow = force(rules.conjElim1(restOne))
          val equation = force(rules.conjElim2(restOne))

          val leftAgrees = agreesAt(left, atMostM(leftBelow, left))
          val rightAgrees = agreesAt(right, atMostM(rightBelow, right))

          val code = tagged("7")
          val inner = force(LogicError.lift(Kernel.mkComb(
            force(Conv.apTerm(pair, force(Conv.sym(rightAgrees)))),
            force(Conv.sym(here)))))
          val outer = force(Conv.apTerm(code, inner))
          val rebuilt = force(Conv.trans(leftAgrees, equation).flatMap(Conv.trans(_, outer)))

          val body = instantiate(instantiate(targetParts(2), shifted(left)), shifted(right))
          val conjoined = force(rules.conjIntro(strictShift(leftBelow, left),
            force(rules.conjIntro(strictShift(rightBelow, right), rebuilt))))
          val level1 = instantiate(targetParts(2), shifted(left))
          val underRight = force(rules.existsIntro(
            logic.destExistsPredicate(level1).get, shifted(right), conjoined))
          val underLeft = force(rules.existsIntro(
            logic.destExistsPredicate(targetParts(2)).get, shifted(left), underRight))
          injected(2, underLeft)
        }
      }
    }

    val generalisation = {
      val assumed = force(LogicError.lift(Kernel.assume(sourceParts(3))))
      open(assumed, "x", taken) { (step, atStep) =>
        open(atStep, "i", taken + step) { (index, atIndex) =>
          val below = force(rules.conjElim1(atIndex))
          val equation = force(rules.conjElim2(atIndex))
          val agrees = agreesAt(step, atMostM(below, step))

          val code = tagged("8")
          val partial = app(pair, List(index))
          val inner = force(Conv.apTerm(partial, force(Conv.sym(agrees))))
          val outer = force(Conv.apTerm(code, inner))
          val rebuilt = force(Conv.trans(here, equation).flatMap(Conv.trans(_, outer)))

          val conjoined = force(rules.conjIntro(strictShift(below, step), rebuilt))
          val level1 = instantiate(targetParts(3), shifted(step))
          val underIndex = force(rules.existsIntro(
            logic.destExistsPredicate(level1).get, index, conjoined))
          val underStep = force(rules.existsIntro(
            logic.destExistsPredicate(targetParts(3)).get, shifted(step), underIndex))
          injected(3, underStep)
        }
      }
    }

    val cases = Vector(
      axiomCase(0, peanoSet),
      axiomCase(1, logicSet),
      modusPonens,
      generalisation
    )

    val tail = force(LogicError.lift(Kernel.assume(force(logic.mkDisj(sourceParts(2), sourceParts(3))))))
    val rest = force(LogicError.lift(Kernel.assume(
      force(logic.mkDisj(sourceParts(1), force(logic.mkDisj(sourceParts(2), sourceParts(3))))))))
    val insideTail = force(rules.disjElim(tail, cases(2), cases(3)))
    val insideRest = force(rules.disjElim(rest, cases(1), insideTail))
    val settled = force(rules.disjElim(opened, cases(0), insideRest))

    val placed = force(Conv.sym(target)
      .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, settled))))
    val closed = force(
      rules.disch(sourceTerm, placed)
        .flatMap(rules.disch(boundTerm, _))
        .flatMap(rules.disch(agreement, _))
        .flatMap(rules.genAll(_, List(a, b, c, u, v, m, j)))
    )



    val wanted = force(
      Statements
        .collectFirst { case (name, text) if name == StepShift => text }
        .toRight(MissingDefinition(StepShift))
        .flatMap(Parser.proposition(theory, notation, _))
    )

      if (closed.conclusion == wanted) Right(closed)
      else Left(NotOfForm(s"the statement published for $StepShift", closed.conclusion))
    } catch {
      case refused: RefusedHere => Left(refused.error)
    }
  }

  /** Carry a refusal out of the derivation above, which is written in direct style. */
  private final class RefusedHere(val error: LogicError) extends RuntimeException

  /**
   * Every member of a set of axioms is provable, by the derivation that is one line long.
   *
   * The assertion with teeth about this whole file, because a predicate nothing satisfies would
   * satisfy every equation above it. It is also the first thing anywhere to spend
   * `NUM_BETA_SEQUENCE`: the one-line derivation is the constant sequence at `n`, taken up to
   * `SUC ZERO`, and getting two numbers that code it is exactly what the beta function is for.
   * `docs/adr/0013` chose that coding over iterated pairing and over prime powers, and this is
   * where the choice starts paying.
   *
   * Written once for both axiom sets, since the two derivations differ in one place: which
   * disjunct of `NUM_STEP` the single line is justified by. Passing that position is cheaper than
   * a second copy and says what the difference is.
   */
  private def inhabited(
    language: Language,
    theory: Theory,
    notation: Notation,
    logic: Logic,
    facts: Map[String, Kernel.Thm],
    setName: String,
    which: Int,
    statementName: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val subject = Term.variable("n", numbers)
    val chain = language.numbering

    def term(text: String): Either[LogicError, Term] = Parser.term(theory, notation, text, numbers)

    def fact(name: String): Either[LogicError, Kernel.Thm] =
      facts.get(name).toRight(MissingDefinition(name))

    /** Open `?x. p x` with a fresh name, leaving the existential itself assumed. */
    def withWitness(existential: Kernel.Thm, name: String, avoid: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        predicate <- logic
          .destExistsPredicate(existential.conclusion)
          .toRight(NotOfForm("an existential", existential.conclusion))
        variable = Conv.freshVariable(
          name, numbers, avoid ++ Term.freeVariables(existential.conclusion))
        applied <- LogicError.lift(Term.app(predicate, variable))
        contraction <- Conv.betaRoot(applied)
        instance <- Term
          .destEq(contraction.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", contraction.conclusion))
        assumed <- LogicError.lift(Kernel.assume(instance))
        reached <- reach(variable, assumed)
        result <- rules.existsElim(existential, variable, reached)
      } yield result

    /** `?x. body` at an argument, beta-reduced. */
    def instantiate(existential: Term, argument: Term): Either[LogicError, Term] =
      for {
        inner <- logic
          .destExistsPredicate(existential)
          .toRight(NotOfForm("an existential", existential))
        applied <- LogicError.lift(Term.app(inner, argument))
        contraction <- Conv.betaRoot(applied)
        body <- Term
          .destEq(contraction.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", contraction.conclusion))
      } yield body

    def disjunctsOf(subject: Term, count: Int): Either[LogicError, Vector[Term]] =
      if (count == 1) Right(Vector(subject))
      else
        logic
          .destDisj(subject)
          .toRight(NotOfForm("a disjunction", subject))
          .flatMap(split => disjunctsOf(split._2, count - 1).map(split._1 +: _))

    def nestOf(run: Vector[Term]): Either[LogicError, Term] =
      run.toList.reverse match {
        case Nil => Left(MissingDefinition("at least one disjunct"))
        case last :: rest =>
          rest.foldLeft[Either[LogicError, Term]](Right(last))((carried, one) =>
            carried.flatMap(logic.mkDisj(one, _))
          )
      }

    def injectedAt(parts: Vector[Term], proof: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        entered <-
          if (which == parts.size - 1) Right(proof)
          else nestOf(parts.drop(which + 1)).flatMap(rules.disjIntro1(_, proof))
        result <- (0 until which).reverse.foldLeft[Either[LogicError, Kernel.Thm]](Right(entered)) {
          (carried, before) => carried.flatMap(rules.disjIntro2(parts(before), _))
        }
      } yield result

    for {
      head <- LogicError.lift(theory.constant(setName, Type.fun(numbers, Type.Bool)))
      pairing <- LogicError.lift(
        theory.constant(
          Numbering.PairName, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      stepHead <- LogicError.lift(
        theory.constant(
          StepName, Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, Type.Bool))))
      )
      claim <- LogicError.lift(Term.app(head, subject))
      assumed <- LogicError.lift(Kernel.assume(claim))
      zero <- term("ZERO")
      one <- term("SUC ZERO")

      // The sequence whose only entry is the formula itself, taken up to one.
      constant <- LogicError.lift(Term.abs(Term.variable("j", numbers), subject))
      sequence <- chain.coding.fact(Coding.BetaSequence)
      taken <- rules.specAll(sequence, List(constant, one))
      opened <- Conv
        .betaNormalise(taken.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, taken)))

      result <- withWitness(opened, "a", Set(subject)) { (left, atLeft) =>
        withWitness(atLeft, "b", Set(subject, left)) { (right, atRight) =>
          for {
            positive <- chain.peano.fact(Peano.SuccessorPositive)
            belowOne <- rules.spec(zero, positive)
            here <- rules.spec(zero, atRight).flatMap(rules.mp(_, belowOne))

            stepCases <- fact(StepCases)
            stepAt <- rules.specAll(stepCases, List(left, right, zero))
            cases <- Term
              .destEq(stepAt.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", stepAt.conclusion))
            parts <- disjunctsOf(cases, 4)
            inSet <- Conv
              .apTerm(head, here)
              .flatMap(Conv.sym)
              .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed)))
            placed <- injectedAt(parts, inSet)
            atZero <- Conv
              .sym(stepAt)
              .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, placed)))

            // Every step at most `ZERO`, of which there is one.
            index = Term.variable("j", numbers)
            atMost <- Parser.proposition(theory, notation, "NUM_LE j ZERO")
            bounded <- LogicError.lift(Kernel.assume(atMost))
            isZero <- chain.peano
              .fact(Peano.AtMostZero)
              .flatMap(rules.spec(index, _))
              .flatMap(rules.mp(_, bounded))
            partial <- LogicError.lift(Term.appAll(stepHead, List(left, right)))
            atIndex <- Conv
              .apTerm(partial, isZero)
              .flatMap(Conv.sym)
              .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atZero)))
            every <- rules.disch(atMost, atIndex).flatMap(rules.gen(index, _))

            inner <- LogicError.lift(Term.appAll(pairing, List(left, right)))
            code <- LogicError.lift(Term.appAll(pairing, List(zero, inner)))
            proofCases <- fact(ProofCases)
            proofAt <- rules.specAll(proofCases, List(code, subject))
            body <- Term
              .destEq(proofAt.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", proofAt.conclusion))
            atLength <- instantiate(body, zero)
            atFirst <- instantiate(atLength, left)
            conjoined <- rules
              .conjIntro(here, every)
              .flatMap(rules.conjIntro(Conv.refl(code), _))
            underSecond <- logic
              .destExistsPredicate(atFirst)
              .toRight(NotOfForm("an existential", atFirst))
              .flatMap(rules.existsIntro(_, right, conjoined))
            underFirst <- logic
              .destExistsPredicate(atLength)
              .toRight(NotOfForm("an existential", atLength))
              .flatMap(rules.existsIntro(_, left, underSecond))
            underLength <- logic
              .destExistsPredicate(body)
              .toRight(NotOfForm("an existential", body))
              .flatMap(rules.existsIntro(_, zero, underFirst))
            isProof <- Conv
              .sym(proofAt)
              .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, underLength)))

            provableCases <- fact(ProvableCases)
            provableAt <- rules.spec(subject, provableCases)
            existential <- Term
              .destEq(provableAt.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", provableAt.conclusion))
            underProof <- logic
              .destExistsPredicate(existential)
              .toRight(NotOfForm("an existential", existential))
              .flatMap(rules.existsIntro(_, code, isProof))
            settled <- Conv
              .sym(provableAt)
              .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, underProof)))
          } yield settled
        }
      }
      closed <- rules.disch(claim, result).flatMap(rules.gen(subject, _))
      wanted <- Statements
        .collectFirst { case (name, text) if name == statementName => text }
        .toRight(MissingDefinition(statementName))
        .flatMap(Parser.proposition(theory, notation, _))
      checked <-
        if (closed.conclusion == wanted) Right(closed)
        else Left(NotOfForm(s"the statement published for $statementName", closed.conclusion))
    } yield checked
  }
}
