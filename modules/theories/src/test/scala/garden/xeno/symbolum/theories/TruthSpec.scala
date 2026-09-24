package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The truth of a formula of the embedded theory, and whether it says anything.
 *
 * **What it says.** Every clause is compared against the text `Truth.Statements` holds, as a term,
 * and the list of statements against the map of facts in both directions.
 *
 * **What it cost.** Three definitions and no axiom, asserted as a difference against the theory it
 * extends, and what the facts spend asserted as an equality per fact.
 *
 * **Whether it discriminates**, which is the part a list of equations cannot show. A truth
 * predicate that answered `T` everywhere, or one whose quantifier forgot to update the environment,
 * would satisfy every clause read as a rewrite in the wrong hands, so three formulas are evaluated
 * to an answer: `0 = S 0` is refuted at every environment; `~ !v0. v0 = 0` is proved at the
 * environment sending everything to zero, which is exactly where a quantifier that ignored its
 * update would read `0 = 0` and answer the other way; and the graph of the triangle is proved at
 * one environment and refuted at another, which spends both directions of its representation.
 */
class TruthSpec extends AnyFlatSpec with Matchers {

  private lazy val chain: Chain = Chain.standard
  private lazy val truth: Truth =
    Truth.construct(chain).fold(error => fail(s"the development does not build: $error"), identity)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private def fact(name: String): Kernel.Thm = force(truth.fact(name))
  private def term(text: String): Term = force(truth.term(text))
  private def proposition(text: String): Term = force(truth.proposition(text))
  private lazy val rules = truth.logic.rules
  private val numbers: Type = TyApp(Natural.TypeName, Nil)

  /** Rewrite to a fixed point, reducing every redex a substituted environment leaves behind. */
  private def evaluate(subject: Term, equations: Vector[Kernel.Thm]): Kernel.Thm = {
    val conditionals = force(Language.conditionalRules(truth.logic, chain.classical, numbers))
    val ruleSet = force(Rewrite.Rule.all(truth.logic, equations ++ conditionals))
    def round(current: Kernel.Thm, left: Int): Kernel.Thm = {
      val right = force(Term.destEq(current.conclusion).map(_._2).toRight("an equation"))
      val reduced = force(Conv.betaNormalise(right))
      val rewritten = force(Rewrite.rewrite(ruleSet, force(Term.destEq(reduced.conclusion)
        .map(_._2).toRight("an equation"))))
      val next = force(Conv.trans(current, reduced).flatMap(Conv.trans(_, rewritten)))
      if (next.conclusion == current.conclusion || left == 0) next else round(next, left - 1)
    }
    round(Conv.refl(subject), 6)
  }

  private def rightOf(theorem: Kernel.Thm): Term =
    force(Term.destEq(theorem.conclusion).map(_._2).toRight("an equation"))

  /* ------------------------------------------------------------------------ what it says */

  "The truth of the object language" should "prove every statement it publishes, owing nothing" in {
    Truth.Statements.foreach { case (name, text) =>
      val proved = fact(name)
      withClue(s"$name: ") {
        proved.hypotheses shouldBe empty
        proved.conclusion shouldBe proposition(text)
      }
    }
  }

  it should "publish a fact for every name in its statement list, and nothing else" in {
    Truth.Statements.map(_._1).distinct.size shouldBe Truth.Statements.size
    Truth.Statements.map(_._1).toSet shouldBe truth.facts.keySet
  }

  /* ------------------------------------------------------------------------ what it cost */

  it should "define three constants and assert no axiom" in {
    val below = chain.provability.theory
    truth.theory.axioms shouldBe below.axioms
    (truth.theory.constants.keySet -- below.constants.keySet) shouldBe
      Set(Truth.ValueName, Truth.TrueName, Truth.TriangleGraphName)
    truth.theory.typeOperators.keySet shouldBe below.typeOperators.keySet
  }

  it should "spend what the naturals cost, fact by fact" in {
    // Measured at the commit that landed this and asserted as an equality for each fact, so a
    // derivation that starts or stops spending an axiom goes red naming itself. The clauses spend
    // choice through the witness the recursion is named by and infinity through `num`.
    val choice = chain.classical.axioms(Classical.Choice).conclusion
    val infinity = chain.naturals.axioms(Natural.Infinity).conclusion
    val eta = chain.classical.axioms(Classical.Eta).conclusion
    val named = Map(choice -> "SELECT", infinity -> "INFINITY", eta -> "ETA")
    val perFact = Truth.Statements.map { case (name, _) =>
      name -> Derivation.axiomsOf(fact(name))
    }
    val report = perFact
      .map { case (name, axioms) =>
        val names = axioms.toVector.map(a => named.getOrElse(a, truth.show(a))).sorted
        s"$name: " + names.mkString(", ")
      }
      .mkString("; ")
    info(report)
    val expected: Map[String, Set[Term]] =
      Truth.Statements.map { case (name, _) => name -> Set(choice, infinity) }.toMap
    withClue(s"per fact: $report\n") {
      perFact.toMap shouldBe expected
    }
  }

  /* -------------------------------------------------------------- whether it discriminates */

  "An equation between zero and a successor" should "be false at every environment" in {
    val code = "NUM_CODE 5 (NUM_PAIR (NUM_CODE 1 0) (NUM_CODE 2 (NUM_CODE 1 0)))"
    val environment = Term.variable("e", Type.fun(numbers, numbers))
    val claim = force(LogicError.lift(Term.appAll(term(s"NUM_TRUE ($code)"), List(environment))))
    val evaluated = evaluate(claim, Vector(
      fact(Truth.TrueEquality), fact(Truth.ValueZero), fact(Truth.ValueSuccessor)))
    rightOf(evaluated) shouldBe proposition("ZERO = SUC ZERO")

    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val equated = force(LogicError.lift(Kernel.eqMp(evaluated, assumed)))
    val never = force(
      chain.naturals.fact(Natural.SuccessorNotZero).flatMap(rules.spec(term("ZERO"), _)))
    val refuted = force(
      Conv.sym(equated).flatMap(rules.notElim(never, _)).flatMap(rules.notIntro(claim, _)))
    val general = force(rules.gen(environment, refuted))
    general.hypotheses shouldBe empty
    general.conclusion shouldBe proposition(s"!e:num -> num. ~(NUM_TRUE ($code) e)")
  }

  "A quantifier" should "read its body at the updated environment, which the update settles" in {
    // `~ !v0. v0 = 0` at the environment sending every variable to zero. With the update, the body
    // is read at `n` and the claim is that not every `n` is zero, which is true. A quantifier that
    // read its body at `e` unchanged would ask whether `e 0 = 0` for every `n`, which is `0 = 0`
    // here, and the negation would be false.
    val code =
      "NUM_CODE 6 (NUM_CODE 8 (NUM_PAIR 0 (NUM_CODE 5 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 1 0)))))"
    val claim = proposition(s"NUM_TRUE ($code) (\\k:num. ZERO)")
    val zeroIsZero = force(rules.eqTruthIntro(Kernel.refl(term("0:num"))))
    val evaluated = evaluate(claim, Vector(
      fact(Truth.TrueNegation), fact(Truth.TrueUniversal), fact(Truth.TrueEquality),
      fact(Truth.ValueVariable), fact(Truth.ValueZero), zeroIsZero))
    rightOf(evaluated) shouldBe proposition("~(!n:num. n = ZERO)")

    val everything = proposition("!n:num. n = ZERO")
    val assumed = force(LogicError.lift(Kernel.assume(everything)))
    val one = force(rules.spec(term("SUC ZERO"), assumed))
    val never = force(
      chain.naturals.fact(Natural.SuccessorNotZero).flatMap(rules.spec(term("ZERO"), _)))
    val denied = force(rules.notElim(never, one).flatMap(rules.notIntro(everything, _)))
    val proved = force(Conv.sym(evaluated).flatMap(e => LogicError.lift(Kernel.eqMp(e, denied))))
    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe claim
  }

  "The graph of the triangle" should "hold where the value is the triangle, fail elsewhere" in {
    val graph = fact(Truth.TriangleGraphTrue)
    val arithmetic = Vector(
      force(chain.numbering.fact(Numbering.TriangleAtZero)),
      force(chain.numbering.fact(Numbering.TriangleAtSuccessor)),
      force(chain.peano.fact(Peano.ZeroPlus)),
      force(chain.peano.fact(Peano.AddAtSuccessor)),
      force(chain.peano.fact(Peano.AddAtZero)))

    // At zero everywhere: `0 = NUM_TRI 0`, which is the triangle's first equation.
    val atZero = force(rules.spec(term("\\k:num. ZERO"), graph))
    val zeroReading = evaluate(rightOf(atZero), arithmetic)
    rightOf(zeroReading) shouldBe proposition("ZERO = ZERO")
    val holds = force(Conv.trans(atZero, zeroReading).flatMap(Conv.sym)
      .flatMap(e => LogicError.lift(Kernel.eqMp(e, Kernel.refl(term("ZERO"))))))
    holds.hypotheses shouldBe empty
    holds.conclusion shouldBe proposition("NUM_TRUE NUM_TRI_GRAPH (\\k:num. ZERO)")

    // At two everywhere: `2 = NUM_TRI 2`, and the triangle of two is three. This is the direction
    // that spends the uniqueness half of the representation: the graph is refuted, not merely
    // left unproved.
    val two = "SUC (SUC ZERO)"
    val atTwo = force(rules.spec(term(s"\\k:num. $two"), graph))
    val twoReading = evaluate(rightOf(atTwo), arithmetic)
    rightOf(twoReading) shouldBe proposition(s"$two = SUC ($two)")
    val claim = proposition(s"NUM_TRUE NUM_TRI_GRAPH (\\k:num. $two)")
    val assumed = force(LogicError.lift(Kernel.assume(claim)))
    val reached = force(Conv.trans(atTwo, twoReading)
      .flatMap(e => LogicError.lift(Kernel.eqMp(e, assumed))))
    // Two successors taken off both sides leave `0 = SUC 0`. `Successor.distinct` would say it in
    // one line, and it reads numerals rather than the successor form the triangle unfolds into.
    val injective = force(chain.naturals.fact(Natural.SuccessorInjective))
    def peel(equation: Kernel.Thm): Kernel.Thm = equation.conclusion match {
      case App(App(_, App(_, left)), App(_, right)) =>
        force(rules.specAll(injective, List(left, right)).flatMap(rules.mp(_, equation)))
      case other => fail(s"not an equation between successors: $other")
    }
    val bottom = peel(peel(reached))
    val never = force(
      chain.naturals.fact(Natural.SuccessorNotZero).flatMap(rules.spec(term("ZERO"), _)))
    val refuted = force(
      Conv.sym(bottom).flatMap(rules.notElim(never, _)).flatMap(rules.notIntro(claim, _)))
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe proposition(s"~(NUM_TRUE NUM_TRI_GRAPH (\\k:num. $two))")
  }

  "The value of a numeral" should "be its number at an environment that says nothing about it" in {
    // `NUM_VALUE_NUMERAL` is general, so it is true of an empty case; this reads it at a number
    // and an environment chosen so that the answer could only come from the numeral.
    val read = force(rules.specAll(fact(Truth.ValueNumeral),
      List(term("\\k:num. SUC k"), term("SUC (SUC ZERO)"))))
    read.conclusion shouldBe
      proposition("NUM_VALUE (NUM_NUMERAL (SUC (SUC ZERO))) (\\k:num. SUC k) = SUC (SUC ZERO)")
  }
}
