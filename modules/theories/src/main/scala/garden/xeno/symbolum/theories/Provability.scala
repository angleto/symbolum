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
 * `NUM_BETA_SEQUENCE`. Since 2026-09-14 it is **closed under both rules of inference**: under
 * modus ponens, which is the first thing here that puts two derivations into one sequence, and
 * under generalisation, which is the same construction with one block instead of two. With the
 * eight schemes of [[Language]] those two rules are the whole Hilbert system, so what this
 * predicate holds of is closed under everything the embedded theory can do.
 *
 * What is not here is anything at the object level: D1, D2 and D3 are theorems **of PA**, written
 * in the object language and derived inside it, and `docs/adr/0013` records that as a piece of
 * work of its own. The two closures here are the meta-level counterparts those will formalise.
 */
final class Provability private (
  val language: Language,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

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
   * The embedded theory is closed under modus ponens.
   *
   * `|- !p q. NUM_PROV (NUM_CODE 7 (NUM_PAIR p q)) ==> NUM_PROV p ==> NUM_PROV q`
   *
   * The first thing here that puts two derivations together rather than exhibiting one.
   *
   * **It is not D2 and the difference matters.** Goedel's second derivability condition is a
   * theorem **of PA**, `Prov(p ==> q) ==> Prov p ==> Prov q` written in the object language and
   * derived inside it, which `docs/adr/0013` records as its own piece of work. This is the same
   * shape one level up: an implication of the ambient logic about the `NUM_PROV` predicate, which
   * says the coded predicate behaves like a theory rather than like a set of axioms. It is what
   * that object-level derivation will have to formalise, and it is what every meta-level argument
   * about the embedded theory chains with, but a reader who takes it for D2 will think the hard
   * part is done.
   *
   * Given a derivation of `p ==> q` ending at
   * index `k1` and one of `p` ending at `k2`, the sequence it builds is the first block unchanged,
   * the second block shifted by `SUC k1`, and `q` appended at `SUC (SUC k1 + k2)`, justified by
   * modus ponens from index `k1` and index `SUC k1 + k2`.
   *
   * **The sequence is a conditional on the index and not a concatenation of anything**, because a
   * sequence here is a function `num -> num` reached through [[Coding.BetaSequence]], and there is
   * nothing to append to. So the whole derivation is three evaluations of `COND` and the arithmetic
   * that decides which branch each index takes, which is where its length goes.
   *
   * [[Generalisation]] is its sibling and the shorter half: one derivation keeps its numbering, so
   * none of the arithmetic of where the join falls appears there. The two are written over one
   * toolkit, which [[closures]] explains.
   */
  val ModusPonens: String = "NUM_PROV_MP"

  /** `NUM_STEP_FROM h a b j` says the `j`th entry is a justified step, or is `h` itself. */
  val StepFromName: String = "NUM_STEP_FROM"

  /**
   * `|- !h a b j. NUM_STEP_FROM h a b j = (NUM_FORM (NUM_BETA a b j) /\ (NUM_STEP a b j \/ ...))`
   *
   * Derivability from one extra assumption, which is what the deduction theorem is about. A step is
   * justified as before, or it **is** the assumption, and that is the whole difference.
   *
   * **It carries `NUM_FORM` where [[StepCases]] does not, and that is a decision rather than an
   * oversight.** The three rules `Deduction` assembles the deduction theorem from each need their
   * formulas to be formulas, because every scheme of `NUM_LOGIC` carries that side condition. Two
   * ways to supply it: invert `NUM_FORM_CASES` at tags seven and eight, which is two lemmas of
   * seventy lines and is the general fix; or ask it of the derivation, which is one conjunct here.
   * This takes the second, so the theorem's hypothesis is stronger than the textbook's by exactly
   * "and every line is a formula", which a caller building a derivation can always supply and
   * usually has in hand.
   *
   * What it leaves behind is worth writing down: **`NUM_STEP` does not require a step to be a
   * formula**, so `NUM_PROV` could in principle hold of a code that is not one. Nothing here shows
   * it does, and the pairing's bound makes the obvious route impossible, but it has not been ruled
   * out and the inversion lemmas are what would settle it.
   */
  val StepFromCases: String = "NUM_STEP_FROM_CASES"

  /** `NUM_PROV_FROM h n` says `n` is derivable from the axioms together with `h`. */
  val ProvableFromName: String = "NUM_PROV_FROM"

  /**
   * `|- !h n. NUM_PROV_FROM h n = (?k a b. NUM_BETA a b k = n /\ (!j. j <= k ==> ...))`
   *
   * **Two definitions here and three for [[ProvableName]]**, and the missing one is [[ProofName]].
   * That exists because `NUM_PROV n` quantifies over a derivation as a single number, which the
   * pairing supplies; nothing will ever quantify over a derivation-from-a-hypothesis that way,
   * because this predicate is a convenience of the ambient logic and is not the thing Goedel's
   * argument arithmetises. So the three numbers are quantified directly and there is no code for
   * them.
   */
  val ProvableFromCases: String = "NUM_PROV_FROM_CASES"

  /**
   * The embedded theory is closed under generalisation.
   *
   * `|- !i p. NUM_PROV p ==> NUM_PROV (NUM_CODE 8 (NUM_PAIR i p))`
   *
   * The other rule of the Hilbert system, and the short half of [[ModusPonens]]: one derivation,
   * which keeps its numbering, so [[StepShift]] is used only at a shift of zero and none of the
   * arithmetic of where a join falls is needed.
   *
   * The index it generalises is **free** in the statement and universally quantified outside the
   * implication, which is what makes this closure under the rule rather than under one instance
   * of it. Nothing is asked of the index: the object language's quantifier binds an index whether
   * or not that index occurs in the formula, and the vacuous case is a theorem there too.
   */
  val Generalisation: String = "NUM_PROV_GEN"

  /**
   * A justified step stays justified when the sequence it lives in is moved along.
   *
   * `|- !a b c u v m j. (!i. i <= m ==> NUM_BETA a b (c + i) = NUM_BETA u v i) ==> j <= m ==>
   * NUM_STEP u v j ==> NUM_STEP a b (c + j)`
   *
   * The lemma [[ModusPonens]] is built from, and the only hard thing in it. To
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
  /** A step of a derivation that may also use `h`, with the four subjects free. */
  private def stepFromBody(h: String, a: String, b: String, at: String): String = {
    val here = s"NUM_BETA $a $b $at"
    s"NUM_FORM ($here) /\\ (NUM_STEP $a $b $at \\/ $here = $h)"
  }

  private def proofBody(proof: String, claim: String): String =
    s"?k:num. ?a:num. ?b:num. $proof = NUM_PAIR k (NUM_PAIR a b) /\\ " +
      s"NUM_BETA a b k = $claim /\\ (!j:num. NUM_LE j k ==> NUM_STEP a b j)"

  val Statements: Vector[(String, String)] = Vector(
    StepCases -> s"!a:num b:num j:num. NUM_STEP a b j = (${stepBody("a", "b", "j")})",
    ProofCases -> s"!d:num n:num. NUM_PROOF d n = (${proofBody("d", "n")})",
    ProvableCases -> "!n:num. NUM_PROV n = (?d:num. NUM_PROOF d n)",
    ProvablePeano -> "!n:num. NUM_PA n ==> NUM_PROV n",
    ProvableLogic -> "!n:num. NUM_LOGIC n ==> NUM_PROV n",
    ModusPonens ->
      ("!p:num q:num. NUM_PROV (NUM_CODE 7 (NUM_PAIR p q)) ==> " +
        "NUM_PROV p ==> NUM_PROV q"),
    Generalisation ->
      "!i:num p:num. NUM_PROV p ==> NUM_PROV (NUM_CODE 8 (NUM_PAIR i p))",
    StepFromCases ->
      s"!h:num a:num b:num j:num. NUM_STEP_FROM h a b j = (${stepFromBody("h", "a", "b", "j")})",
    ProvableFromCases ->
      ("!h:num n:num. NUM_PROV_FROM h n = (?k:num. ?a:num. ?b:num. NUM_BETA a b k = n /\\ " +
        "(!j:num. NUM_LE j k ==> NUM_STEP_FROM h a b j))"),
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
      (provableTheory, provableDefinition, provableCases) = withProvable
      provableLogic <- language.logic.over(provableTheory)

      withStepFrom <- Language.defineByCases(
        provableTheory,
        notation,
        provableLogic,
        StepFromName,
        s"\\h:num. \\a:num. \\b:num. \\j:num. ${stepFromBody("h", "a", "b", "j")}",
        List("h", "a", "b", "j")
      )
      (stepFromTheory, stepFromDefinition, stepFromCases) = withStepFrom
      stepFromLogic <- language.logic.over(stepFromTheory)

      withProvableFrom <- Language.defineByCases(
        stepFromTheory,
        notation,
        stepFromLogic,
        ProvableFromName,
        ("\\h:num. \\n:num. ?k:num. ?a:num. ?b:num. NUM_BETA a b k = n /\\ " +
          "(!j:num. NUM_LE j k ==> NUM_STEP_FROM h a b j)"),
        List("h", "n")
      )
      (theory, provableFromDefinition, provableFromCases) = withProvableFrom
      logic <- language.logic.over(theory)

      facts = Map(
        StepCases -> stepCases,
        ProofCases -> proofCases,
        ProvableCases -> provableCases,
        StepFromCases -> stepFromCases,
        ProvableFromCases -> provableFromCases
      )
      fromPeano <- inhabited(language, theory, notation, logic, facts, Language.AxiomName, 0,
        ProvablePeano)
      fromLogic <- inhabited(language, theory, notation, logic, facts, Language.LogicName, 1,
        ProvableLogic)
      shifted <- stepsShift(language, theory, notation, logic, facts)
      both <- closures(language, theory, notation, logic, facts, shifted)
      (joined, generalised) = both
    } yield new Provability(
      language,
      theory,
      notation,
      logic,
      Map(
        StepName -> stepDefinition,
        ProofName -> proofDefinition,
        ProvableName -> provableDefinition,
        StepFromName -> stepFromDefinition,
        ProvableFromName -> provableFromDefinition
      ),
      facts
        .updated(ProvablePeano, fromPeano)
        .updated(ProvableLogic, fromLogic)
        .updated(StepShift, shifted)
        .updated(ModusPonens, joined)
        .updated(Generalisation, generalised)
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

  /**
   * The two closures, over one toolkit, because they are one construction with two ends.
   *
   * A derivation here is a function from an index to a formula, reached through
   * [[Coding.BetaSequence]], so closing under a rule means writing a **new** function that agrees
   * with the old one below some index and answers the conclusion at that index. Both closures do
   * exactly that and differ in three places: how many blocks the function is built from, which
   * disjunct of [[StepCases]] justifies the appended line, and what that line is.
   *
   * Written as one class with two methods rather than two methods with a shared prelude, because
   * the prelude is most of it: the constants, the order facts, the opening of an existential, the
   * injection into the four-way disjunction, the transfer of a block at a shift of zero, and the
   * assembly of a sequence into a `NUM_PROV`. The second closure landed after the first and was
   * this toolkit plus forty lines.
   *
   * **Direct style, with the refusal carried out by an exception**, for the reason [[stepsShift]]
   * gives: a derivation is a tree of independent obligations, and a `for` comprehension over
   * `Either` turns "which obligation failed" into "which binding came first". The exception is
   * caught here and nowhere else.
   */
  private def closures(
    language: Language,
    theory: Theory,
    notation: Notation,
    logic: Logic,
    facts: Map[String, Kernel.Thm],
    stepShift: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] =
    try {
      val joining = new Joining(language, theory, notation, logic, facts, stepShift)
      Right(
        (
          joining.checked(ModusPonens, joining.modusPonens),
          joining.checked(Generalisation, joining.generalisation)
        )
      )
    } catch {
      case refused: RefusedHere => Left(refused.error)
    }

  /** What both closures are written over. See [[closures]] for why it is a class. */
  private final class Joining(
    language: Language,
    theory: Theory,
    notation: Notation,
    logic: Logic,
    facts: Map[String, Kernel.Thm],
    stepShift: Kernel.Thm
  ) {
    private val rules = logic.rules
    private val numbers = TyApp(Natural.TypeName, Nil)
    private val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    private val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))
    private val chain = language.numbering
    private val classical = chain.peano.naturals.classical

    private def force[T](result: Either[LogicError, T]): T =
      result.fold(error => throw new RefusedHere(error), identity)

    private def app(head: Term, args: List[Term]): Term =
      force(LogicError.lift(Term.appAll(head, args)))
    private def text(source: String): Term =
      force(Parser.term(theory, notation, source, numbers))
    private def fact(name: String): Kernel.Thm = force(chain.peano.fact(name))
    private def published(name: String): Kernel.Thm =
      force(facts.get(name).toRight(MissingDefinition(name)))

    /* --------------------------------------------------------------- constants */

    private val betaConstant = force(LogicError.lift(theory.constant(Coding.BetaName,
      Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, numbers))))))
    private val plus = force(LogicError.lift(theory.constant(Peano.Addition, arithmetic)))
    private val minus = force(LogicError.lift(theory.constant(Peano.Subtraction, arithmetic)))
    private val atMostConstant =
      force(LogicError.lift(theory.constant(Peano.NonStrictOrder, relation)))
    private val successorConstant = force(LogicError.lift(
      theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))))
    private val conditional = force(LogicError.lift(theory.constant(Classical.Conditional,
      Type.fun(Type.Bool, Type.fun(numbers, Type.fun(numbers, numbers))))))
    private val pairConstant =
      force(LogicError.lift(theory.constant(Numbering.PairName, arithmetic)))
    private val codeConstant =
      force(LogicError.lift(theory.constant(Numbering.CodeName, arithmetic)))
    private val stepConstant = force(LogicError.lift(theory.constant(StepName,
      Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, Type.Bool))))))
    private val provableConstant = force(LogicError.lift(
      theory.constant(ProvableName, Type.fun(numbers, Type.Bool))))

    private def beta(a: Term, b: Term, i: Term): Term = app(betaConstant, List(a, b, i))
    private def add(x: Term, y: Term): Term = app(plus, List(x, y))
    private def subtract(x: Term, y: Term): Term = app(minus, List(x, y))
    private def atMost(x: Term, y: Term): Term = app(atMostConstant, List(x, y))
    private def successor(x: Term): Term = app(successorConstant, List(x))
    private def cond(guard: Term, yes: Term, no: Term): Term =
      app(conditional, List(guard, yes, no))
    private def pair(x: Term, y: Term): Term = app(pairConstant, List(x, y))

    /** The object language's implication and universal quantifier, as partial applications. */
    private val implies = app(codeConstant, List(text("7")))
    private val forall = app(codeConstant, List(text("8")))
    private val zero = text("ZERO")

    private def destCond(subject: Term): (Term, Term, Term) = subject match {
      case App(App(App(head, guard), yes), no) if head == conditional => (guard, yes, no)
      case other => throw new RefusedHere(NotOfForm("a conditional", other))
    }

    /* ------------------------------------------------------- order, assembled */

    private def transitive(
      first: Kernel.Thm, second: Kernel.Thm, x: Term, y: Term, z: Term): Kernel.Thm =
      force(rules.conjIntro(first, second).flatMap(both =>
        rules.specAll(fact(Peano.Transitive), List(x, y, z)).flatMap(rules.mp(_, both))))

    /** `x <= y` and `y < z` give `x < z`. */
    private def thenBelow(
      first: Kernel.Thm, second: Kernel.Thm, x: Term, y: Term, z: Term): Kernel.Thm =
      force(rules.conjIntro(first, second).flatMap(both =>
        rules.specAll(fact(Peano.AtMostThenBelow), List(x, y, z)).flatMap(rules.mp(_, both))))

    /** `x < y` and `y <= z` give `x < z`. */
    private def belowThen(
      first: Kernel.Thm, second: Kernel.Thm, x: Term, y: Term, z: Term): Kernel.Thm =
      force(rules.conjIntro(first, second).flatMap(both =>
        rules.specAll(fact(Peano.BelowThenAtMost), List(x, y, z)).flatMap(rules.mp(_, both))))

    private def reflexive(x: Term): Kernel.Thm = force(rules.spec(x, fact(Peano.Reflexive)))
    private def belowSuccessor(x: Term): Kernel.Thm =
      force(rules.spec(x, fact(Peano.BelowSuccessor)))
    private def atMostSuccessor(x: Term): Kernel.Thm =
      force(rules.spec(x, fact(Peano.AtMostSuccessor)))
    private def atMostSum(x: Term, y: Term): Kernel.Thm =
      force(rules.specAll(fact(Peano.AtMostSum), List(x, y)))
    private def fromBelow(held: Kernel.Thm, x: Term, y: Term): Kernel.Thm =
      force(rules.specAll(fact(Peano.AtMostFromBelow), List(x, y)).flatMap(rules.mp(_, held)))
    private def notAtMost(held: Kernel.Thm, x: Term, y: Term): Kernel.Thm =
      force(rules.specAll(fact(Peano.BelowExcludesAtMost), List(x, y)).flatMap(rules.mp(_, held)))
    private def addMonotone(held: Kernel.Thm, p: Term, x: Term, y: Term): Kernel.Thm =
      force(rules.specAll(fact(Peano.AddMonotone), List(p, x, y)).flatMap(rules.mp(_, held)))
    private def cancel(held: Kernel.Thm, p: Term, x: Term, y: Term): Kernel.Thm =
      force(rules.specAll(fact(Peano.AddCancelsOrder), List(p, x, y)).flatMap(rules.mp(_, held)))

    /** From `x = y`, that `x <= y`, through the order being reflexive. */
    private def atMostByEquation(equation: Kernel.Thm, x: Term): Kernel.Thm =
      force(Conv.apTerm(app(atMostConstant, List(x)), equation)
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, reflexive(x)))))

    /* ------------------------------------------------ opening and injecting */

    /** `?x. body` at an argument, beta-reduced. */
    private def instantiate(existential: Term, argument: Term): Term = {
      val inner = logic.destExistsPredicate(existential)
        .getOrElse(throw new RefusedHere(NotOfForm("an existential", existential)))
      force(rightOf(force(Conv.betaRoot(app(inner, List(argument))))))
    }

    private def open(existential: Kernel.Thm, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val predicate = logic.destExistsPredicate(existential.conclusion)
        .getOrElse(throw new RefusedHere(NotOfForm("an existential", existential.conclusion)))
      val fresh = Conv.freshVariable(
        name, numbers, taken ++ Term.freeVariables(existential.conclusion))
      val body = force(rightOf(force(Conv.betaRoot(app(predicate, List(fresh))))))
      val instance = force(LogicError.lift(Kernel.assume(body)))
      force(rules.existsElim(existential, fresh, reach(fresh, instance)))
    }

    /** `?x. body` at a witness, where the proof is of the body already reduced. */
    private def under(existential: Term, witness: Term, proof: Kernel.Thm): Kernel.Thm =
      force(rules.existsIntro(
        logic.destExistsPredicate(existential)
          .getOrElse(throw new RefusedHere(NotOfForm("an existential", existential))),
        witness, proof))

    private def disjunctsOf(subject: Term, count: Int): Vector[Term] =
      if (count == 1) Vector(subject)
      else {
        val (first, rest) = logic.destDisj(subject)
          .getOrElse(throw new RefusedHere(NotOfForm("a disjunction", subject)))
        first +: disjunctsOf(rest, count - 1)
      }

    private def nestOf(run: Vector[Term]): Term =
      run.toList.reverse match {
        case Nil => throw new RefusedHere(MissingDefinition("at least one disjunct"))
        case last :: rest =>
          rest.foldLeft(last)((carried, one) => force(logic.mkDisj(one, carried)))
      }

    private def injected(parts: Vector[Term], which: Int, proof: Kernel.Thm): Kernel.Thm = {
      val entered =
        if (which == parts.size - 1) proof
        else force(rules.disjIntro1(nestOf(parts.drop(which + 1)), proof))
      (0 until which).reverse.foldLeft(entered)((carried, before) =>
        force(rules.disjIntro2(parts(before), carried)))
    }

    /* ------------------------------------------------------ what is read off */

    private val provableCases = published(ProvableCases)
    private val proofCases = published(ProofCases)
    private val stepCases = published(StepCases)
    private val betaSequence = force(chain.coding.fact(Coding.BetaSequence))
    private val condTrue = Kernel.instType(Map(Classical.TypeVariable -> numbers),
      force(classical.fact(Classical.CondTrue)))
    private val condFalse = Kernel.instType(Map(Classical.TypeVariable -> numbers),
      force(classical.fact(Classical.CondFalse)))

    /* ------------------------------------------------- the shared four steps */

    /** `NUM_PROV n` assumed and opened into the derivation it claims exists. */
    private def opened(subject: Term): (Term, Kernel.Thm) = {
      val premise = app(provableConstant, List(subject))
      val assumed = force(LogicError.lift(Kernel.assume(premise)))
      (premise, force(rules.spec(subject, provableCases)
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, assumed)))))
    }

    /** A derivation's last line and the justification of every step in it. */
    private def parts(held: Kernel.Thm): (Kernel.Thm, Kernel.Thm) = {
      val rest = force(rules.conjElim2(held))
      (force(rules.conjElim1(rest)), force(rules.conjElim2(rest)))
    }

    /** Two numbers coding a function, over a range the beta function answers for. */
    private def sequenceOver(sequence: Term, bound: Term): Kernel.Thm = {
      val taking = force(rules.specAll(betaSequence, List(sequence, bound)))
      force(Conv.betaNormalise(taking.conclusion)
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, taking))))
    }

    /**
     * Reading the joined sequence at an index, given what the beta function agreed to.
     *
     * `agreement` quantifies an index below `SUC after`, and every caller holds instead a bound of
     * the form `at <= after`, which is the shape the blocks and the appended line come in.
     */
    private final class Values(agreement: Kernel.Thm, after: Term) {
      private val afterAfter = successor(after)

      def valueAt(at: Term, small: Kernel.Thm): Kernel.Thm = {
        val strict = thenBelow(small, belowSuccessor(after), at, after, afterAfter)
        force(rules.spec(at, agreement).flatMap(rules.mp(_, strict)))
      }

      /** One `COND` evaluated, by whichever of the two rules the guard supports. */
      def branch(value: Kernel.Thm, guard: Kernel.Thm, holds: Boolean): Kernel.Thm = {
        val (asked, yes, no) = destCond(force(rightOf(value)))
        val rule = if (holds) condTrue else condFalse
        val evaluated =
          force(rules.specAll(rule, List(asked, yes, no)).flatMap(rules.mp(_, guard)))
        force(Conv.trans(value, evaluated))
      }
    }

    /**
     * The block that keeps its numbering, carried across by [[StepShift]] at a shift of zero.
     *
     * Both closures have one of these and it is the same in both: the first derivation of a
     * concatenation and the only derivation of a generalisation are the same thing. The shift is
     * `ZERO` and `NUM_ZERO_ADD` rewrites it away on both sides, once inside the agreement the
     * lemma asks for and once in the conclusion it gives back.
     */
    private def unshifted(
      wideA: Term, wideB: Term, sourceA: Term, sourceB: Term,
      bound: Term, steps: Kernel.Thm, agreement: Kernel.Thm, taken: Set[FVar]
    ): Kernel.Thm = {
      val j = Conv.freshVariable("j", numbers, taken)
      val boundTerm = atMost(j, bound)
      val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))
      val shiftedAgreement = {
        val i = Conv.freshVariable("i", numbers, taken)
        val innerBound = atMost(i, bound)
        val innerHeld = force(LogicError.lift(Kernel.assume(innerBound)))
        val value = force(rules.spec(i, agreement).flatMap(rules.mp(_, innerHeld)))
        val identity = force(rules.spec(i, fact(Peano.ZeroPlus)))
        val moved = force(Conv.apTerm(app(betaConstant, List(wideA, wideB)), identity))
        force(rules.disch(innerBound, force(Conv.trans(moved, value))).flatMap(rules.gen(i, _)))
      }
      val source = force(rules.spec(j, steps).flatMap(rules.mp(_, bounded)))
      val moved = force(rules
        .specAll(stepShift, List(wideA, wideB, zero, sourceA, sourceB, bound, j))
        .flatMap(rules.mp(_, shiftedAgreement))
        .flatMap(rules.mp(_, bounded))
        .flatMap(rules.mp(_, source)))
      val identity = force(rules.spec(j, fact(Peano.ZeroPlus)))
      val placed = force(Conv.apTerm(app(stepConstant, List(wideA, wideB)), identity)
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, moved))))
      force(rules.disch(boundTerm, placed).flatMap(rules.gen(j, _)))
    }

    /** From `j = t` and the step at `t`, the step at `j`. */
    private def stepAt(
      wideA: Term, wideB: Term, equation: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
      force(Conv.apTerm(app(stepConstant, List(wideA, wideB)), equation)
        .flatMap(Conv.sym)
        .flatMap(step => LogicError.lift(Kernel.eqMp(step, held))))

    /**
     * A sequence whose every step up to `after` is justified and whose value there is the claim,
     * read as a proof and then as the claim being provable.
     *
     * The last twenty lines of both closures, and the only part of either that mentions
     * [[ProofName]]. A proof's code carries the index of its last step, so `after` appears twice:
     * once as that index and once as the place the claim sits.
     */
    private def provable(
      wideA: Term, wideB: Term, after: Term,
      valueLast: Kernel.Thm, everyStep: Kernel.Thm, claim: Term
    ): Kernel.Thm = {
      val code = pair(after, pair(wideA, wideB))
      val proofAt = force(rules.specAll(proofCases, List(code, claim)))
      val body = force(rightOf(proofAt))
      val atLength = instantiate(body, after)
      val atFirst = instantiate(atLength, wideA)
      val conjoined = force(rules.conjIntro(valueLast, everyStep)
        .flatMap(rules.conjIntro(Conv.refl(code), _)))
      val isProof = force(Conv.sym(proofAt).flatMap(step => LogicError.lift(Kernel.eqMp(
        step,
        under(body, after, under(atLength, wideA, under(atFirst, wideB, conjoined)))))))

      val provableAt = force(rules.spec(claim, provableCases))
      force(Conv.sym(provableAt).flatMap(step => LogicError.lift(Kernel.eqMp(
        step, under(force(rightOf(provableAt)), code, isProof)))))
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
      else throw new RefusedHere(
        NotOfForm(s"the statement published for $name", theorem.conclusion))
    }

    /* ------------------------------------------------------------ the closures */

    /**
     * [[ModusPonens]], by building the sequence that holds both derivations and one step more.
     *
     * Write `c` for `SUC k1` and `L` for `c + k2`, where `k1` and `k2` are the last indices of the
     * derivation of `p ==> q` and of the derivation of `p`. The sequence is
     *
     * {{{
     * \i. COND (i <= k1) (NUM_BETA a1 b1 i)
     *          (COND (i <= L) (NUM_BETA a2 b2 (i - c)) q)
     * }}}
     *
     * taken up to `SUC (SUC L)` so that the index `SUC L`, where `q` sits, is inside the range
     * [[Coding.BetaSequence]] answers for. Three evaluations of `COND` come out of that, one per
     * block and one for the appended line, and each is an arithmetic fact about where an index
     * sits rather than anything about derivations. That arithmetic is most of the method.
     *
     * The two blocks transfer through [[StepShift]], at a shift of zero and at a shift of `c`,
     * which is the one lemma this needs and the reason it is stated with a shift.
     *
     * **The last case of the assembly is where the shift is undone.** An index `j` above `k1` and
     * at most `L` is the second block's index `j - c`, and saying so needs `c + (j - c) = j`,
     * which is `Peano.NUM_SUB_ADD` against `c <= j`, and `j - c <= k2`, which is
     * `Peano.NUM_ADD_LE_CANCEL` against `j <= L`. The second of those did not exist before this:
     * nothing cancelled a summand out of a comparison, only out of an equation.
     */
    def modusPonens: Kernel.Thm = {
      val p = Term.variable("p", numbers)
      val q = Term.variable("q", numbers)
      val implication = app(implies, List(pair(p, q)))
      val (premiseOne, outerOne) = opened(implication)
      val (premiseTwo, outerTwo) = opened(p)

      val settled = open(outerOne, "d1", Set(p, q)) { (d1, holdsOne) =>
        val casesOne = force(rules.specAll(proofCases, List(d1, implication))
          .flatMap(step => LogicError.lift(Kernel.eqMp(step, holdsOne))))
        open(casesOne, "k1", Set(p, q, d1)) { (k1, atK1) =>
          open(atK1, "a1", Set(p, q, d1, k1)) { (a1, atA1) =>
            open(atA1, "b1", Set(p, q, d1, k1, a1)) { (b1, atB1) =>
              val (lastOne, stepsOne) = parts(atB1)
              open(outerTwo, "d2", Set(p, q, d1, k1, a1, b1)) { (d2, holdsTwo) =>
                val casesTwo = force(rules.specAll(proofCases, List(d2, p))
                  .flatMap(step => LogicError.lift(Kernel.eqMp(step, holdsTwo))))
                open(casesTwo, "k2", Set(p, q, d1, k1, a1, b1, d2)) { (k2, atK2) =>
                  open(atK2, "a2", Set(p, q, d1, k1, a1, b1, d2, k2)) { (a2, atA2) =>
                    open(atA2, "b2", Set(p, q, d1, k1, a1, b1, d2, k2, a2)) { (b2, atB2) =>
                      val (lastTwo, stepsTwo) = parts(atB2)
                      join(q, k1, a1, b1, lastOne, stepsOne, k2, a2, b2, lastTwo, stepsTwo,
                        Set(p, q, d1, k1, a1, b1, d2, k2, a2, b2))
                    }
                  }
                }
              }
            }
          }
        }
      }

      force(rules.disch(premiseTwo, settled)
        .flatMap(rules.disch(premiseOne, _))
        .flatMap(rules.genAll(_, List(p, q))))
    }

    /** The inside of [[modusPonens]], once both derivations have been taken apart. */
    private def join(
      q: Term,
      k1: Term, a1: Term, b1: Term, lastOne: Kernel.Thm, stepsOne: Kernel.Thm,
      k2: Term, a2: Term, b2: Term, lastTwo: Kernel.Thm, stepsTwo: Kernel.Thm,
      taken: Set[FVar]
    ): Kernel.Thm = {
      val c = successor(k1)
      val last = add(c, k2)
      val after = successor(last)

      // k1 < c <= L <= SUC L, assembled once and used throughout.
      val k1BelowShift = belowSuccessor(k1)
      val lastAtMostAfter = atMostSuccessor(last)
      val lastBelowAfter = belowSuccessor(last)
      val k1AtMostLast = transitive(atMostSuccessor(k1), atMostSum(c, k2), k1, c, last)
      val k1AtMostAfter = transitive(k1AtMostLast, lastAtMostAfter, k1, last, after)
      val k1BelowAfter = thenBelow(k1AtMostLast, lastBelowAfter, k1, last, after)

      val index = Conv.freshVariable("i", numbers, taken)
      val sequence = force(LogicError.lift(Term.abs(index,
        cond(atMost(index, k1), beta(a1, b1, index),
          cond(atMost(index, last), beta(a2, b2, subtract(index, c)), q)))))

      open(sequenceOver(sequence, successor(after)), "a", taken) { (wideA, atA) =>
        open(atA, "b", taken + wideA) { (wideB, agreement) =>
          val here = taken + wideA + wideB
          val values = new Values(agreement, after)

          /* Below the join the first block is read off unchanged. */
          val agreeFirst = {
            val i = Conv.freshVariable("i", numbers, here)
            val boundTerm = atMost(i, k1)
            val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))
            val small = transitive(bounded, k1AtMostAfter, i, k1, after)
            val value = values.branch(values.valueAt(i, small), bounded, holds = true)
            force(rules.disch(boundTerm, value).flatMap(rules.gen(i, _)))
          }

          /* Above it the second block is, at an index shifted by `c`. */
          val agreeSecond = {
            val i = Conv.freshVariable("i", numbers, here)
            val boundTerm = atMost(i, k2)
            val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))
            val at = add(c, i)
            val inRange = addMonotone(bounded, c, i, k2)
            val small = transitive(inRange, lastAtMostAfter, at, last, after)
            val notFirst =
              notAtMost(belowThen(k1BelowShift, atMostSum(c, i), k1, c, at), k1, at)
            val inner = values.branch(
              values.branch(values.valueAt(at, small), notFirst, holds = false),
              inRange, holds = true)
            // `(c + i) - c = i`, by commuting the sum the subtraction undoes.
            val commuted = force(rules.specAll(fact(Peano.AddCommutative), List(c, i)))
            val reduced = force(Conv.apThm(force(Conv.apTerm(minus, commuted)), c)
              .flatMap(Conv.trans(_, force(rules.specAll(fact(Peano.SumMinus), List(i, c))))))
            val moved = force(Conv.apTerm(app(betaConstant, List(a2, b2)), reduced))
            force(rules.disch(boundTerm, force(Conv.trans(inner, moved)))
              .flatMap(rules.gen(i, _)))
          }

          /* At the appended index both guards fail and the value is the conclusion. */
          val valueLast = values.branch(
            values.branch(values.valueAt(after, reflexive(after)),
              notAtMost(k1BelowAfter, k1, after), holds = false),
            notAtMost(lastBelowAfter, last, after), holds = false)

          val blockFirst = unshifted(wideA, wideB, a1, b1, k1, stepsOne, agreeFirst, here)

          val blockSecond = {
            val i = Conv.freshVariable("i", numbers, here)
            val boundTerm = atMost(i, k2)
            val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))
            val source = force(rules.spec(i, stepsTwo).flatMap(rules.mp(_, bounded)))
            val moved = force(rules
              .specAll(stepShift, List(wideA, wideB, c, a2, b2, k2, i))
              .flatMap(rules.mp(_, agreeSecond))
              .flatMap(rules.mp(_, bounded))
              .flatMap(rules.mp(_, source)))
            force(rules.disch(boundTerm, moved).flatMap(rules.gen(i, _)))
          }

          /* The appended step, justified by modus ponens from `k1` and from `L`. */
          val blockLast = {
            val atFirstEnd = force(Conv.trans(
              values.branch(values.valueAt(k1, k1AtMostAfter), reflexive(k1), holds = true),
              lastOne))
            val atSecondEnd = force(Conv.trans(
              force(rules.spec(k2, agreeSecond).flatMap(rules.mp(_, reflexive(k2)))), lastTwo))
            val rebuilt = force(LogicError.lift(Kernel.mkComb(
              force(Conv.apTerm(pairConstant, force(Conv.sym(atSecondEnd)))),
              force(Conv.sym(valueLast)))))
            val justified =
              force(Conv.trans(atFirstEnd, force(Conv.apTerm(implies, rebuilt))))

            val target = force(rules.specAll(stepCases, List(wideA, wideB, after)))
            val disjuncts = disjunctsOf(force(rightOf(target)), 4)
            val conjoined = force(rules.conjIntro(k1BelowAfter,
              force(rules.conjIntro(lastBelowAfter, justified))))
            val placed = under(disjuncts(2), k1,
              under(instantiate(disjuncts(2), k1), last, conjoined))
            force(Conv.sym(target).flatMap(step =>
              LogicError.lift(Kernel.eqMp(step, injected(disjuncts, 2, placed)))))
          }

          /* Every index at most `SUC L` falls to one of the three. */
          val everyStep = {
            val j = Conv.freshVariable("j", numbers, here)
            val boundTerm = atMost(j, after)
            val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))

            /** From `j <= L`, by where `j` sits relative to `k1`. */
            def withinBlocks(atMostLast: Kernel.Thm): Kernel.Thm = {
              val trichotomy = force(rules.specAll(fact(Peano.Trichotomy), List(j, k1)))
              val cases = disjunctsOf(trichotomy.conclusion, 3)

              val fromBelowFirst = {
                val held = force(LogicError.lift(Kernel.assume(cases(0))))
                force(rules.spec(j, blockFirst).flatMap(rules.mp(_, fromBelow(held, j, k1))))
              }
              val fromEqual = {
                val held = force(LogicError.lift(Kernel.assume(cases(1))))
                force(rules.spec(j, blockFirst).flatMap(rules.mp(_, atMostByEquation(held, j))))
              }
              val fromAbove = {
                val held = force(LogicError.lift(Kernel.assume(cases(2))))
                // `k1 < j` IS `SUC k1 <= j` by definition, which is `c <= j`.
                val reached = force(Conv
                  .unfold(force(chain.peano.definition(Peano.StrictOrder)), List(k1, j))
                  .flatMap(step => LogicError.lift(Kernel.eqMp(step, held))))
                val difference = subtract(j, c)
                val rebuilt = force(rules.specAll(fact(Peano.MinusThenPlus), List(j, c))
                  .flatMap(rules.mp(_, reached)))
                val placed = force(Conv.trans(
                  force(rules.specAll(fact(Peano.AddCommutative), List(c, difference))), rebuilt))
                val shiftedBound = force(
                  Conv.apThm(force(Conv.apTerm(atMostConstant, placed)), last)
                    .flatMap(Conv.sym)
                    .flatMap(step => LogicError.lift(Kernel.eqMp(step, atMostLast))))
                val within = cancel(shiftedBound, c, difference, k2)
                val moved = force(
                  rules.spec(difference, blockSecond).flatMap(rules.mp(_, within)))
                stepAt(wideA, wideB, force(Conv.sym(placed)), moved)
              }

              val tail = force(LogicError.lift(Kernel.assume(
                force(logic.mkDisj(cases(1), cases(2))))))
              force(rules.disjElim(trichotomy, fromBelowFirst,
                force(rules.disjElim(tail, fromEqual, fromAbove))))
            }

            val split = force(rules.specAll(fact(Peano.BelowOrEqual), List(j, after))
              .flatMap(rules.mp(_, bounded)))
            val splitParts = disjunctsOf(split.conclusion, 2)

            val strictCase = {
              val held = force(LogicError.lift(Kernel.assume(splitParts(0))))
              val peeled = force(rules.specAll(fact(Peano.BelowSuccessorCases), List(last, j))
                .flatMap(rules.mp(_, held)))
              val peeledParts = disjunctsOf(peeled.conclusion, 2)
              val fromStrict = withinBlocks(
                fromBelow(force(LogicError.lift(Kernel.assume(peeledParts(0)))), j, last))
              val fromEqual = withinBlocks(atMostByEquation(
                force(LogicError.lift(Kernel.assume(peeledParts(1)))), j))
              force(rules.disjElim(peeled, fromStrict, fromEqual))
            }
            val equalCase = stepAt(
              wideA, wideB, force(LogicError.lift(Kernel.assume(splitParts(1)))), blockLast)

            val reached = force(rules.disjElim(split, strictCase, equalCase))
            force(rules.disch(boundTerm, reached).flatMap(rules.gen(j, _)))
          }

          provable(wideA, wideB, after, valueLast, everyStep, q)
        }
      }
    }

    /**
     * [[Generalisation]], which is the same construction with one block instead of two.
     *
     * The derivation of `p` keeps its numbering, so there is nothing to shift and no arithmetic of
     * where a join falls: the sequence is
     *
     * {{{
     * \j. COND (j <= k) (NUM_BETA a1 b1 j) (NUM_CODE 8 (NUM_PAIR i p))
     * }}}
     *
     * one `COND` per end rather than three, and the appended line at `SUC k` is justified by the
     * fourth disjunct of [[StepCases]] naming `k`, which is below it. What makes that disjunct
     * apply is that `p` is the value of the joined sequence at `k`, which is the first block's
     * agreement read at its own last index.
     *
     * The index `i` it quantifies over is **free** in the appended code and is bound only at the
     * end, which is what makes this a closure under the rule rather than under one instance of it.
     */
    def generalisation: Kernel.Thm = {
      val index = Term.variable("i", numbers)
      val p = Term.variable("p", numbers)
      val claim = app(forall, List(pair(index, p)))
      val (premise, outer) = opened(p)

      val settled = open(outer, "d", Set(index, p)) { (d, holds) =>
        val cases = force(rules.specAll(proofCases, List(d, p))
          .flatMap(step => LogicError.lift(Kernel.eqMp(step, holds))))
        open(cases, "k", Set(index, p, d)) { (k, atK) =>
          open(atK, "a1", Set(index, p, d, k)) { (a1, atA1) =>
            open(atA1, "b1", Set(index, p, d, k, a1)) { (b1, atB1) =>
              val (lastLine, steps) = parts(atB1)
              val taken = Set(index, p, d, k, a1, b1)
              val after = successor(k)
              val kBelowAfter = belowSuccessor(k)
              val kAtMostAfter = atMostSuccessor(k)

              val at = Conv.freshVariable("j", numbers, taken)
              val sequence = force(LogicError.lift(Term.abs(at,
                cond(atMost(at, k), beta(a1, b1, at), claim))))

              open(sequenceOver(sequence, successor(after)), "a", taken) { (wideA, atA) =>
                open(atA, "b", taken + wideA) { (wideB, agreement) =>
                  val here = taken + wideA + wideB
                  val values = new Values(agreement, after)

                  val agreeBlock = {
                    val j = Conv.freshVariable("j", numbers, here)
                    val boundTerm = atMost(j, k)
                    val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))
                    val small = transitive(bounded, kAtMostAfter, j, k, after)
                    val value = values.branch(values.valueAt(j, small), bounded, holds = true)
                    force(rules.disch(boundTerm, value).flatMap(rules.gen(j, _)))
                  }

                  val valueLast = values.branch(
                    values.valueAt(after, reflexive(after)),
                    notAtMost(kBelowAfter, k, after), holds = false)

                  val block = unshifted(wideA, wideB, a1, b1, k, steps, agreeBlock, here)

                  /* The appended step, justified by generalising the step at `k`. */
                  val blockLast = {
                    val atEnd = force(Conv.trans(
                      values.branch(values.valueAt(k, kAtMostAfter), reflexive(k), holds = true),
                      lastLine))
                    val rebuilt =
                      force(Conv.apTerm(app(pairConstant, List(index)), force(Conv.sym(atEnd))))
                    val justified =
                      force(Conv.trans(valueLast, force(Conv.apTerm(forall, rebuilt))))

                    val target = force(rules.specAll(stepCases, List(wideA, wideB, after)))
                    val disjuncts = disjunctsOf(force(rightOf(target)), 4)
                    val conjoined = force(rules.conjIntro(kBelowAfter, justified))
                    val placed = under(disjuncts(3), k,
                      under(instantiate(disjuncts(3), k), index, conjoined))
                    force(Conv.sym(target).flatMap(step =>
                      LogicError.lift(Kernel.eqMp(step, injected(disjuncts, 3, placed)))))
                  }

                  /* Every index at most `SUC k` is either in the block or is the new line. */
                  val everyStep = {
                    val j = Conv.freshVariable("j", numbers, here)
                    val boundTerm = atMost(j, after)
                    val bounded = force(LogicError.lift(Kernel.assume(boundTerm)))
                    val split = force(rules.specAll(fact(Peano.BelowOrEqual), List(j, after))
                      .flatMap(rules.mp(_, bounded)))
                    val splitParts = disjunctsOf(split.conclusion, 2)

                    val strictCase = {
                      val held = force(LogicError.lift(Kernel.assume(splitParts(0))))
                      val peeled = force(rules.specAll(fact(Peano.BelowSuccessorCases), List(k, j))
                        .flatMap(rules.mp(_, held)))
                      val peeledParts = disjunctsOf(peeled.conclusion, 2)
                      val fromStrict = force(rules.spec(j, block).flatMap(rules.mp(_,
                        fromBelow(force(LogicError.lift(Kernel.assume(peeledParts(0)))), j, k))))
                      val fromEqual = force(rules.spec(j, block).flatMap(rules.mp(_,
                        atMostByEquation(
                          force(LogicError.lift(Kernel.assume(peeledParts(1)))), j))))
                      force(rules.disjElim(peeled, fromStrict, fromEqual))
                    }
                    val equalCase = stepAt(
                      wideA, wideB,
                      force(LogicError.lift(Kernel.assume(splitParts(1)))), blockLast)

                    val reached = force(rules.disjElim(split, strictCase, equalCase))
                    force(rules.disch(boundTerm, reached).flatMap(rules.gen(j, _)))
                  }

                  provable(wideA, wideB, after, valueLast, everyStep, claim)
                }
              }
            }
          }
        }
      }

      force(rules.disch(premise, settled).flatMap(rules.genAll(_, List(index, p))))
    }
  }

  /** An equation's right-hand side, which this file reads off a dozen theorems. */
  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

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
