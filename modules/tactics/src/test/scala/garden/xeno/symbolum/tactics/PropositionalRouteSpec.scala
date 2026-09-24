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
 * measurement is in `Prove`'s own docstring: of the library's statements two carry a negation at
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

  /** Every formula with its own size, which is what the net's criterion is stated against. */
  private val sized: Vector[(Int, Term)] = {
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

    (1 to Nodes).toVector.flatMap(size => bySize.getOrElse(size, Vector.empty).map(size -> _))
  }

  private val formulas: Vector[Term] = sized.map(_._2)

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

  "The net under the calculus" should "not be reached by any goal of this population" in {
    // `2e85b5d4`, which is the consequence `docs/adr/0023` wrote down and did not repair: a goal
    // that exhausts `Intuitionistic.Fuel` comes back `BoundReached`, the propositional address
    // hands it to the classical procedure anyway, and the theorem that comes back costs an axiom
    // with nothing saying the free route was cut short rather than decided against.
    //
    // The card's own first step is to find out whether anything reaches the net at all, because if
    // nothing does then a report distinguishing the two refusals is machinery bought for a case
    // that does not occur. This is that count, and the criterion it counts by is written here
    // rather than left to the reader: a goal REACHES the net when `prove` refuses it with
    // `BoundReached` naming this search, which is the one refusal that means "I stopped" rather
    // than "it is not so".
    val exhausted = addressed.filter { reading =>
      calculus.prove(reading.goal) match {
        case Left(BoundReached(name, _, _, _)) => name == Intuitionistic.SearchName
        case _ => false
      }
    }

    exhausted shouldBe empty
  }

  it should "have most of itself unused, measured rather than assumed" in {
    // Zero above says nothing about how close anything came, and "nobody hit 256" is a weak
    // sentence if the deepest goal used 255. So the net is lowered until the population's answers
    // change, and the depth at which they first do is how much of it is actually in use.
    //
    // The whole answer vector is compared rather than a count, because two goals swapping which of
    // them is proved would leave a count alone. And the search at a lower depth is the same search:
    // `Intuitionistic.prove` takes the depth for this measurement and nothing else passes it.
    val atFull: Vector[Boolean] = addressed.map(r => calculus.prove(r.goal).isRight)

    def answersAt(fuel: Int): Vector[Boolean] =
      addressed.map(r => calculus.prove(r.goal, fuel).isRight)

    // The least depth that still answers exactly as the full net does. Binary search, and the pair
    // of assertions under it is what says the search landed on a real edge rather than anywhere:
    // it agrees at `needed` and disagrees at `needed - 1`.
    val needed: Int = {
      var low = 1
      var high = Intuitionistic.Fuel
      while (low < high) {
        val mid = low + (high - low) / 2
        if (answersAt(mid) == atFull) high = mid else low = mid + 1
      }
      low
    }

    answersAt(needed) shouldBe atFull
    answersAt(needed - 1) should not be atFull

    // And the assumption the binary search rests on, measured instead of assumed: that agreement
    // once reached is not lost again higher up. If it could be, `needed` would be an edge rather
    // than THE edge and the margin below would be a statement about nothing. More depth can only
    // let the search go further, so this should hold by construction — which is exactly the kind
    // of "should" this repository asks to be counted.
    Iterator.iterate(needed)(_ * 2).takeWhile(_ <= Intuitionistic.Fuel).foreach { depth =>
      withClue(s"the answers changed again at depth $depth: ") {
        answersAt(depth) shouldBe atFull
      }
    }

    // The figure this card is closed with, and it is written as an inequality rather than as the
    // number: the number is a property of these rules and would move for a reason that is not a
    // defect, where the margin is the claim. A change that made the search deep enough to matter
    // fails here and gets to argue for a larger net instead of discovering it in production.
    needed should be <= (Intuitionistic.Fuel / 4)

    info(s"the deepest of ${addressed.size} goals needs $needed of ${Intuitionistic.Fuel}")
  }

  it should "be a net whose size is a statement about the goal, which is what chose the number" in {
    // The criterion `87e74c7f` asked for, and the reason 256 is a decision rather than a rounding:
    // **the fuel a goal needs never exceeds the goal's own size**, counting one for each connective
    // and one for each atom occurrence. Read forwards, `Intuitionistic.Fuel` at 256 is the promise
    // that any goal of at most 256 nodes is answered rather than stopped, which is a sentence a
    // reader can check a written claim against. The two tests above give the edge on one family;
    // this gives the relation the number can be chosen by.
    //
    // It is also the assertion the net exists to be: the net is there against a mistake in the
    // RULES, which the class comment says in as many words, and a rule that stopped decreasing the
    // measure would show up here as a goal needing more than its size. Before this, that mistake
    // was caught by an out-of-memory or by nothing.
    //
    // Measured beyond this population on 2026-09-22, exhaustively over every formula on two atoms
    // of at most **seven** nodes, 5618 of them: no goal needs more than its size. Eight nodes is
    // 26032 formulas and did not finish inside the time it was given, which is why the figure
    // quoted is seven. What that probe reports per size band is the worst NEED, which is 4 at five
    // and six nodes and 6 at seven; it is not a ratio, and reading it as one is the defect the
    // comment beside the second assertion records.
    def needOf(goal: Term): Int = {
      def stopped(fuel: Int): Boolean = calculus.prove(goal, fuel) match {
        case Left(BoundReached(name, _, _, _)) => name == Intuitionistic.SearchName
        case _ => false
      }

      var low = 1
      var high = Intuitionistic.Fuel
      while (low < high) {
        val mid = low + (high - low) / 2
        if (stopped(mid)) low = mid + 1 else high = mid
      }
      low
    }

    val over = sized.filter { case (size, goal) =>
      Prove.addressOf(chain.widest, goal) == Prove.Address.Propositional && needOf(goal) > size
    }

    withClue(s"goals needing more fuel than their own size: ${over.map(_._2).map(chain.widest.show).mkString(", ")}\n") {
      over shouldBe empty
    }

    // And the bound is approached, which is what keeps the assertion above from being a claim
    // about a number nothing comes near: without this it would pass just as well on a search that
    // spent one unit on everything.
    //
    // **The bound is in fact ATTAINED, and where it is attained is why this assertion asks for
    // four nodes rather than for equality.** `~p` and `~q` need 2 of 2, which is the ratio the
    // `info` below prints and which perturbation 1 of `tools/verify/perturb-the-nets-criterion.sh`
    // names when it fires. Equality at two nodes is trivial: a negation opens and the search is
    // done, so any calculus at all attains it, and an assertion on the ratio would be satisfied by
    // one that spent nothing anywhere else. The witness worth asking for is a goal with structure
    // in it, so what is asserted is that some formula of at least four nodes needs all but one of
    // them.
    //
    // **The sentence that stood here said "the worst ratio is 6 of 7" and it was three copies of
    // a wrong reading, found by the verification of card 87e74c7f on 2026-09-22.** Six is the
    // worst NEED among the seven-node formulas of the out-of-tree probe, a statistic per size
    // band; the worst ratio is 1, and the instrument three statements down was printing `2 of 2`
    // in the same run that the comment claimed 6 of 7. The two cannot be the same number, and the
    // one that is recomputed on every run is the one that was right.
    //
    // **This half has been seen failing exactly once and by one perturbation**, number 4 in that
    // harness, which charges nothing at the NEGATION rule. Three earlier attempts could not: each
    // made a rule free that the edge's chain of implications is built from, so the edge moved and
    // the two tests below went red before this one could. The negation is the one rule that chain
    // never reaches, which is what made it the perturbation that isolates this assertion.
    val approached = sized.filter { case (size, goal) =>
      size >= 4 &&
      Prove.addressOf(chain.widest, goal) == Prove.Address.Propositional &&
      needOf(goal) >= size - 1
    }
    approached should not be empty

    val worst = sized
      .filter { case (_, goal) => Prove.addressOf(chain.widest, goal) == Prove.Address.Propositional }
      .map { case (size, goal) => (needOf(goal), size) }
      .maxBy { case (need, size) => need.toDouble / size }

    info(
      s"${sized.size} formulas, none needing more than its size; " +
        s"the closest is ${worst._1} of ${worst._2}, and ${approached.size} come within one")
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
        val theorem = force(prover(reading.goal)).theorem

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

  /* ------------------------------------------------ what the documents say about all of this */

  /**
   * The documents read with the line breaks taken out, because a sentence is wrapped where the
   * column ran out and a figure lands on either side of that break with no warning.
   *
   * The idiom is `ClassicalSpec`'s, which pins the excluded middle's step count in the four places
   * that spell it; this is the same instrument pointed at the two counts this file computes.
   */
  private def read(relative: String): String =
    java.nio.file.Files
      .readString(java.nio.file.Paths.get(relative))
      .replaceAll("\\s+", " ")

  "The counts this file computes" should "be the counts the documents spell, wherever they spell them" in {
    // Added 2026-09-18, by the verification of the card this work came from, and the defect is one
    // the assertions above cannot see: 58 and 98 are written by hand in `README.md`,
    // `docs/evaluation.md` and `Prove`'s docstring, and nothing read any of them. A change to the
    // routing turns the counts above red, which is the half that was covered; a hand edit to a
    // document, or a repair that fixes this file and not the prose, was the half that was not.
    //
    // The sentence in `README.md` even said the figures "are asserted by `PropositionalRouteSpec`",
    // which a reader takes for a document being pinned and which was true only of the code's own
    // count. `CLAUDE.md` cites the excluded middle's step count as the opposite precedent, "written
    // by hand in four documents **and asserted in all four** by `ClassicalSpec`", and that half of
    // it is true: `ClassicalSpec` spells the figure into three sentences from `Derivation.size`
    // and has since 2026-09-11, which is the arrangement this test copies. What card `ad47e293`
    // found on 2026-09-22 is what the sentence left out rather than what it claimed: a list of
    // guarded sentences covers the list, and six copies were not on it. Both files now carry the
    // other half, a walk that refuses the figure everywhere the list does not reach.
    //
    // `docs/adr/0023` spells both figures four times and is deliberately NOT read here: an ADR is a
    // dated record of a decision, superseded rather than maintained, so a test that forced it to
    // track a moving count would be asking it to stop being one.
    val gainedCount = gained.size
    val classicalOnly = addressed.count(r => r.byClassical && !r.byCalculus)

    val readme = read("README.md")
    withClue(s"README.md does not say $gainedCount goals move from one axiom to none: ") {
      readme should include(s"on two atoms, **$gainedCount** are exactly that")
    }
    withClue(s"README.md does not say $classicalOnly stay classical-only: ") {
      readme should include(s"$classicalOnly of the formulas in that same measurement stay classical-only")
    }

    withClue(s"docs/evaluation.md does not spell ${addressed.size}, $gainedCount and $classicalOnly: ") {
      read("docs/evaluation.md") should include(
        s"of the ${addressed.size} formulas of at most six nodes on two atoms that take this " +
          s"address, $gainedCount move from one axiom to none and $classicalOnly stay classical-only"
      )
    }

    val prove = read("modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Prove.scala")
    withClue(s"Prove.scala's docstring does not say $gainedCount are provable here: ") {
      prove should include(s"**$gainedCount of those are provable here**")
    }
    withClue(s"Prove.scala's docstring does not say the other $classicalOnly stay classical-only: ") {
      prove should include(s"The other $classicalOnly stay classical-only")
    }
  }

  it should "be produced by the procedure the front instructions name at this address" in {
    // The other half of the same repair, and the one with no figure in it. `CLAUDE.md` went on
    // saying that the propositional address runs `Minimal` before `Propositional` for the whole of
    // the day the routing moved, in the document every session reads before it does anything, and
    // nothing anywhere read that sentence. It is read here rather than in `DocumentationSpec`
    // because it is a claim about this address and this file is what measures this address.
    //
    // Spelled from `Prove.Search` rather than written out, so a third procedure at this address
    // fails this line instead of leaving the sentence quietly wrong again.
    val instructions = read("CLAUDE.md")
    val free = Prove.Search.Intuitionistic.spelling

    withClue(s"CLAUDE.md does not say the propositional address runs `$free` first: ") {
      instructions should include(s"the propositional address, where `$free`")
    }
    instructions should include(s"`$free` runs before `Propositional`")

    // And the sentence it replaced, so that rewriting the paragraph from memory cannot bring it
    // back: the gate is spent on the address now and answers no goal there.
    instructions should not include "where `Minimal` runs"
  }

  /* ------------------------------------------- what a bound rather than the claim paid for */

  /**
   * A chain of implications of `links` links, which is the family the net is measured on.
   *
   *   ((p1 ==> p2) /\ (p2 ==> p3) /\ ... ) ==> (p1 ==> p(links+1))
   *
   * Intuitionistically valid at every length, every atom a bare proposition so that it takes this
   * address at all, and the only thing that changes with the length is the size. It is the shape
   * `docs/adr/0026` used at the twin site in `Domain.close`, so the two measurements are read
   * against each other rather than each against itself.
   */
  private def chainOf(links: Int): Term = {
    def atom(i: Int): Term = Term.variable(s"p$i", Type.Bool)
    val steps = (1 to links).map(i => force(logic.mkImp(atom(i), atom(i + 1))))
    force(
      logic.mkImp(
        steps.reduceLeft((a, b) => force(logic.mkConj(a, b))),
        force(logic.mkImp(atom(1), atom(links + 1)))
      )
    )
  }

  "A goal the free route reaches" should "come back settled, at no axiom" in {
    // The half that makes the assertion below a difference rather than a fact about one goal. At
    // this length the calculus uses the whole net and finishes inside it: 127 links needs 256 of
    // 256, measured on 2026-09-18, and the consumption grows as `2n + 2`.
    prover(chainOf(127)) match {
      case Right(Prove.Outcome.Settled(theorem)) =>
        Derivation.axiomsOf(theorem) shouldBe empty
      case other => fail(s"a chain of 127 links is settled for nothing: $other")
    }
  }

  it should "be the size `Intuitionistic`'s docstring gives it" in {
    // The docstring argues from the chain's size in nodes, one for each connective and one for each
    // atom occurrence, which is the unit its criterion counts in, and that figure was a digit
    // compared with nothing until 2026-09-24. A node is a leaf of the term: a connective's constant
    // or an atom, since a connective is a constant applied to its arguments.
    def nodes(term: Term): Int = term match {
      case App(function, argument) => nodes(function) + nodes(argument)
      case _ => 1
    }
    val size = nodes(chainOf(127))
    size shouldBe 4 * 127 + 3

    val docstring = read("modules/logic/src/main/scala/garden/xeno/symbolum/logic/Intuitionistic.scala")
    withClue(s"a 127-link chain is $size nodes: ") {
      docstring should include(s"A 127-link chain is $size nodes")
    }
  }

  it should "come back cut short, naming the bound and its depth, one link further on" in {
    // The defect `docs/adr/0023` recorded and left, and `docs/adr/0031` repairs: the same theorem,
    // one link longer, at one axiom, and until 2026-09-18 nothing in the answer said why. The pair
    // is what makes it a measurement instead of an anecdote — the two goals differ by one link and
    // the price differs by the choice axiom.
    prover(chainOf(128)) match {
      case Right(Prove.Outcome.CutShort(theorem, search, depth)) =>
        search shouldBe Intuitionistic.SearchName
        depth shouldBe Intuitionistic.Fuel
        Derivation.axiomsOf(theorem) should have size 1

        // And it is the same theorem the settled one would have been, so what the case reports is
        // the price and not a different answer.
        theorem.conclusion shouldBe chainOf(128)
        theorem.hypotheses shouldBe empty

      case other => fail(s"a chain of 128 links is cut short by the net: $other")
    }
  }

  it should "say nothing of the sort about the goals this repository actually holds" in {
    // The guard against the guard, and the measurement that says the case above is a real edge and
    // not the ordinary answer: over the whole enumerated population nothing is cut short. The
    // library reads the same way — 184 of its statements take this address and the deepest uses 9
    // of 256 — and that measurement is on the card rather than here, because it is about the
    // library and this file is about the address.
    addressed.foreach { reading =>
      prover(reading.goal) match {
        case Right(Prove.Outcome.CutShort(_, _, _)) =>
          fail(s"${chain.widest.show(reading.goal)} is cut short, and nothing of this size should be")
        case _ => ()
      }
    }
  }
}
