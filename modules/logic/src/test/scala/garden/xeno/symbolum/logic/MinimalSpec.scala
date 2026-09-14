package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * The negation-free propositional fragment, and the two boundaries either side of it.
 *
 * The assertion that carries the file is not that these are provable. It is that they are provable
 * **on no axioms**: the excluded middle is derived here rather than assumed, what it is derived
 * from is the choice operator, and a truth-table procedure would put that under every propositional
 * theorem this system ever produced. The `axiomsOf` line in each test is the point.
 */
class MinimalSpec extends AnyFlatSpec with Matchers {

  private val logic = Logic.standard
  private val minimal = Minimal.standard

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private val p = Term.variable("p", Type.Bool)
  private val q = Term.variable("q", Type.Bool)
  private val r = Term.variable("r", Type.Bool)

  private def conj(left: Term, right: Term): Term = force(logic.mkConj(left, right))
  private def disj(left: Term, right: Term): Term = force(logic.mkDisj(left, right))
  private def imp(left: Term, right: Term): Term = force(logic.mkImp(left, right))
  private def all(variables: List[FVar], body: Term): Term =
    variables.foldRight(body)((variable, inner) => force(logic.mkForall(variable, inner)))

  private def proved(goal: Term): Kernel.Thm = {
    val theorem = force(minimal.prove(goal))
    theorem.conclusion shouldBe goal
    theorem.hypotheses shouldBe empty
    withClue(s"this fragment must cost nothing, and ${Derivation.size(theorem)} steps reached: ") {
      Derivation.axiomsOf(theorem) shouldBe empty
    }
    theorem
  }

  "Conjunction elimination as a goal" should "be proved on no axioms" in {
    proved(all(List(p, q), imp(conj(p, q), p)))
  }

  "Disjunction introduction as a goal" should "be proved on no axioms" in {
    proved(all(List(p, q), imp(p, disj(p, q))))
  }

  "A case analysis" should "be proved on no axioms" in {
    // `(p \/ q) /\ (p ==> r) /\ (q ==> r) ==> r`. The disjunction on the left branches and both
    // branches have to be proved whatever else is tried, which is why it is an invertible rule
    // here and not a guess.
    val premises = conj(disj(p, q), conj(imp(p, r), imp(q, r)))
    proved(all(List(p, q, r), imp(premises, r)))
  }

  "The monotonicity of a negation-free selector" should "be proved on no axioms" in {
    // The obligation the engineering handbook's rule selector generates, at one concrete
    // expression, `surface & (pii | authz)`. Declaring more facets must never load fewer rules,
    // so over-declaring is always safe and under-declaring is the only way to lose an obligation.
    //
    // Why it is true is the whole reason the grammar forbids negation: conjunction and disjunction
    // are monotone in their arguments and negation is the one construct that would break it. That
    // was an argument in prose until this test ran.
    val s = Term.variable("s", Type.Bool)
    val a = Term.variable("a", Type.Bool)
    val s2 = Term.variable("s2", Type.Bool)
    val p2 = Term.variable("p2", Type.Bool)
    val a2 = Term.variable("a2", Type.Bool)

    val binds = conj(s, disj(p, a))
    val grows = conj(imp(s, s2), conj(imp(p, p2), imp(a, a2)))
    val bindsWider = conj(s2, disj(p2, a2))

    val theorem = proved(all(List(s, p, a, s2, p2, a2), imp(conj(binds, grows), bindsWider)))
    info(s"${Derivation.size(theorem)} inferences, ${Derivation.axiomsOf(theorem).size} axioms")
  }

  /* ------------------------------------------------------------------ the boundaries */

  "A formula with a negation in it" should "be refused by naming the negation" in {
    // Out, not hard. A caller told only "cannot prove this" reformulates for ever.
    val excluded = disj(p, force(logic.mkNot(p)))

    minimal.prove(all(List(p), excluded)) match {
      case Right(theorem) => fail(s"this fragment must not reach $theorem")
      case Left(refusal) => refusal.message should include("negation")
    }

    minimal.reads(all(List(p), excluded)) shouldBe false
  }

  "Peirce's law" should "be refused, and it is the boundary rather than a defect" in {
    // `((p ==> q) ==> p) ==> p` has no negation in it and is not intuitionistically provable, so
    // "negation-free" and "reachable here" are not the same set. The card that asked for this file
    // said they were; they are not, and the honest place to put that is a test rather than a
    // sentence.
    //
    // A classical procedure would settle it, and would put the choice operator under it. That is
    // the trade this file exists to make explicit.
    val peirce = imp(imp(imp(p, q), p), p)

    minimal.reads(all(List(p, q), peirce)) shouldBe true
    minimal.prove(all(List(p, q), peirce)).isLeft shouldBe true
  }

  "A goal that is not a proposition" should "be refused before anything is spent" in {
    minimal.reads(Term.variable("x", TyVar("A"))) shouldBe false
  }
}
