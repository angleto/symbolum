package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.Chain

/**
 * What the propositional address costs, over the population the question is actually about.
 *
 * `docs/adr/0023` moved `Prove`'s propositional address from `Minimal` to the calculus under it,
 * and the figures that decided it are here rather than in a probe somebody ran once. The card
 * asking for the work named the corpus and the library as the population to measure, and that
 * measurement is in `Prove`'s own docstring: of the library's 503 statements two carry a negation at
 * this address and both are `Classical`'s own, and of the Mathlib ring corpus and the statable slice
 * of miniF2F **none** reaches the address at all. Read as "the change buys nothing" that zero is an
 * absence reported by an instrument pointed at a subject that cannot contain the thing: those three
 * populations are arithmetic, and a goal reaches this address carrying a negation only where every
 * atom is a bare proposition.
 *
 * So the population here is the propositional formulas themselves, enumerated rather than sampled:
 * every formula over two atoms with at most [[Nodes]] nodes, which is [[Formulas]] of them. A bound
 * and not a sample, so there is no sample count to justify; what the bound is chosen for is that it
 * is the smallest one containing all four of the shapes the argument turns on — an intuitionistic
 * theorem with a negation, a classical-only one, a goal `Minimal` takes, and a goal nothing proves.
 *
 * == What it is guarding ==
 *
 * The figures the front page carries. They are counts the code knows, so they are asserted here and
 * not written by hand anywhere a test cannot reach; the row names 58 and 98 and this is what makes
 * those two numbers fail rather than drift.
 *
 * And the fact the routing rests on, which is the one worth more than any of the counts:
 * **everything `Minimal` proves, the calculus under it proves**. `Minimal.prove` is
 * `Intuitionistic.prove` behind a test for a negation, so asking the gate first can add no theorem
 * and can only turn one away. Stated as a count that must be zero rather than as a sentence.
 *
 * == What makes it non-vacuous ==
 *
 * Both directions are asserted non-empty. A change that made the calculus prove nothing would leave
 * "nothing `Minimal` proves is missed" true, and a change that made it prove everything would leave
 * "the classical procedure still has a job" true; the two counts in the middle are what refuse both.
 */
class PropositionalRouteSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val chain: Chain = Chain.standard
  private val logic: Logic = chain.widest.logic
  private val prover: Prove = force(Prove.construct(chain))
  private val gate: Minimal = Minimal(logic)
  private val calculus: Intuitionistic = Intuitionistic(logic)
  private val classical: Propositional = Propositional(chain.classical)

  /** The node bound, with `~` and each binary connective costing one. */
  private val Nodes: Int = 6

  /** How many formulas that is, asserted below rather than trusted here. */
  private val Formulas: Int = 1116

  private val formulas: Vector[Term] = {
    val atoms = Vector(Term.variable("p", Type.Bool), Term.variable("q", Type.Bool))
    val bySize = scala.collection.mutable.Map[Int, Vector[Term]](1 -> atoms)

    (2 to Nodes).foreach { size =>
      val unary = bySize.getOrElse(size - 1, Vector.empty).map(inner => force(logic.mkNot(inner)))
      val binary = for {
        left <- (1 until size).toVector
        a <- bySize.getOrElse(left, Vector.empty)
        b <- bySize.getOrElse(size - 1 - left, Vector.empty)
        built <- Vector(logic.mkConj(a, b), logic.mkDisj(a, b), logic.mkImp(a, b))
      } yield force(built)
      bySize(size) = unary ++ binary
    }

    (1 to Nodes).toVector.flatMap(bySize.getOrElse(_, Vector.empty))
  }

  private def carriesANegation(term: Term): Boolean = term match {
    case Const(name, _) => name == Logic.Negation || name == Logic.Falsity
    case App(fn, argument) => carriesANegation(fn) || carriesANegation(argument)
    case Abs(_, body) => carriesANegation(body)
    case _ => false
  }

  private final case class Reading(
    goal: Term,
    negated: Boolean,
    byGate: Boolean,
    byCalculus: Boolean,
    byClassical: Boolean
  )

  private lazy val addressed: Vector[Reading] =
    formulas
      .filter(goal => Prove.addressOf(chain.widest, goal) == Prove.Address.Propositional)
      .map(goal =>
        Reading(
          goal,
          carriesANegation(goal),
          gate.prove(goal).isRight,
          calculus.prove(goal).isRight,
          classical.prove(goal).isRight
        )
      )

  /** The goals the routing moved: the gate turns them away and the calculus settles them. */
  private lazy val gained: Vector[Reading] = addressed.filter(r => !r.byGate && r.byCalculus)

  "The formulas over two atoms" should "be the population the front page counts over" in {
    formulas.size shouldBe Formulas
    addressed.size shouldBe 1114

    // The two that are not at this address are the bare atoms: `Minimal.reads` wants a connective,
    // because a goal with none is a single atom and belongs to whatever procedure can read it.
    (formulas.size - addressed.size) shouldBe 2

    info(s"$Formulas formulas of at most $Nodes nodes, ${addressed.size} at the propositional address")
  }

  "The gate in front of the calculus" should "add no theorem to it, which is why it is not asked" in {
    // The measurement `docs/adr/0023` turns on, as a count that must be zero. `Minimal.prove` is
    // `Intuitionistic.prove` behind a test for a negation, so a goal the gate proves and the
    // calculus does not would be a contradiction in the file rather than a preference about order.
    addressed.count(r => r.byGate && !r.byCalculus) shouldBe 0

    // And what the gate does take, so the zero above is not the zero of a gate that proves nothing.
    addressed.count(_.byGate) shouldBe 32
    addressed.filter(_.byGate).foreach(r => withClue(s"${chain.widest.show(r.goal)}: ") {
      r.negated shouldBe false
    })
  }

  "The goals the routing moved" should "be the number the front page names" in {
    addressed.count(_.negated) shouldBe 958
    addressed.count(_.byClassical) shouldBe 188
    addressed.count(r => r.negated && r.byClassical) shouldBe 152
    gained.size shouldBe 58

    info(s"${gained.size} goals move from one axiom to none; " +
      s"${addressed.count(r => r.byClassical && !r.byCalculus)} stay classical-only")
  }

  it should "still leave the classical procedure a job, or the order would decide nothing" in {
    // The other direction, and the guard against the guard. If the calculus reached everything the
    // classical one does, "ask the cheap one first" would be a rule about an empty difference and
    // every assertion above would still pass.
    val classicalOnly = addressed.filter(r => r.byClassical && !r.byCalculus)

    classicalOnly.size shouldBe 98
    classicalOnly.map(goal => chain.widest.show(goal.goal)) should contain("p \\/ ~p")
  }

  "Each goal the routing moved" should "come out of the prover resting on nothing" in {
    // The end-to-end claim, and the card's own criterion of completion: not that the calculus can
    // do it, but that asking the system gets it, at no axiom. Run over all 58 rather than over a
    // witness, because a witness is the shape of evidence that survives a routing that works for
    // one goal.
    gained.foreach { reading =>
      withClue(s"${chain.widest.show(reading.goal)}: ") {
        val theorem = force(prover(reading.goal))

        theorem.conclusion shouldBe reading.goal
        theorem.hypotheses shouldBe empty
        Derivation.axiomsOf(theorem) shouldBe empty
      }
    }
  }

  it should "have cost one axiom on the route it used to take" in {
    // The price the zero above is read against. Every one of them is classically provable, and the
    // classical procedure closes with `DOUBLE_NEGATION`, so every one of them used to arrive
    // resting on the choice operator: same theorem, different accounting, which is the currency
    // this repository exists to report.
    gained.foreach { reading =>
      withClue(s"${chain.widest.show(reading.goal)}: ") {
        reading.byClassical shouldBe true
        Derivation.axiomsOf(force(classical.prove(reading.goal))).size shouldBe 1
      }
    }
  }
}
