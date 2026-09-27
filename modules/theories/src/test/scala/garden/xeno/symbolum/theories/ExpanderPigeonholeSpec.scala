package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The width bound for the pigeonhole principle on an expanding graph, and what keeps it from being
 * about nothing.
 *
 * **That its hypotheses are met together, and the width conjunct is not free there.** The complete
 * bipartite graph from three pigeons to two holes, at `r = 1` and `w = 2`: every single pigeon is
 * matched, and a single pigeon has both holes as unique neighbours. The refutation is the one of
 * nineteen steps in `ResolutionFixture`. Every hypothesis is derived with nothing assumed and the
 * theorem is detached, and the conclusion it gives there is not true of every step: three steps of
 * that refutation have one literal and one has none.
 *
 * **That `EXPANDING` is load-bearing.** Everything else the theorem asks is independent of `w`, so at
 * `w = 20` the other four hypotheses still hold at the same refutation, and the conclusion is
 * refuted there: no step has twenty literals. With `EXPANDING` dropped the statement is false.
 *
 * **That `0 < r` is load-bearing too.** At `r = 0` no size `t` has `t <= r < 2t`, so `EXPANDING`
 * asks nothing and holds at every `w`, and `MATCHABLE` asks about the empty set only. Both are
 * derived there at `w = 20`, with the inputs and the refutation, and the conclusion is refuted: with
 * the positivity hypothesis dropped the statement is false for the same reason as above.
 *
 * What this does not show is a graph where `w` exceeds the degree, which is where the theorem says
 * something about proof complexity; the smallest expanders with that property are far past what a
 * refutation written out by hand can reach.
 */
class ExpanderPigeonholeSpec extends AnyFlatSpec with Matchers {

  private def ok[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private lazy val chain: Chain = Chain.standard
  private lazy val expander: ExpanderPigeonhole = ok(ExpanderPigeonhole.construct(chain))
  private lazy val moves: Pigeonhole.Builder = new ExpanderPigeonhole.Proof(chain).b
  private lazy val fixture: ResolutionFixture.Fixture = ResolutionFixture(moves, chain, term => expander.show(term))
  import fixture.{numeral, antecedents, implication, opened, conjuncts, split, belowBound, below}

  private def fact(name: String): Kernel.Thm = ok(expander.fact(name))

  "Every fact of the development" should "prove the statement it is published as" in {
    ExpanderPigeonhole.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe ok(expander.proposition(text))
        fact(name).hypotheses shouldBe empty
      }
    }
    expander.facts.keySet shouldBe ExpanderPigeonhole.Statements.map(_._1).toSet
  }

  it should "cost choice and infinity and none of the reals' axioms" in {
    val expected = Set(
      ok(chain.classical.axiom(Classical.Choice)).conclusion,
      ok(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    Derivation.axiomsOf(fact(ExpanderPigeonhole.ExpanderWidth)) shouldBe expected
  }

  it should "read the resolvents through the soundness of a resolution step and count with the injection bound" in {
    // Steps 3 and 5 of the argument. A proof reaching the statement some other way would state the
    // same thing and would not be this argument.
    val wanted = Set(
      ok(chain.resolving.fact(Resolving.StepSound)).conclusion,
      moves.injection.conclusion
    )
    Derivation.restingOn(fact(ExpanderPigeonhole.ExpanderWidth), wanted) shouldBe wanted
  }

  /* --------------------------------------------------- the complete graph K(3, 2) */

  private val Pigeons = 3
  private val Holes = 2
  private val Complete = "\\p:num. \\h:num. T"
  private lazy val refutation = fixture.threeIntoTwo
  private lazy val truth = ok(moves.rules.truth)

  private def general(width: Int): Kernel.Thm =
    moves.spec(fact(ExpanderPigeonhole.ExpanderWidth), numeral(Pigeons), numeral(Holes), Complete, numeral(1), numeral(width),
      "k", "v", "s", numeral(refutation.inputs), numeral(refutation.size))

  /** `|- NUM_LT x (SUC ZERO) ==> x = ZERO`, as a function of a proof of the premise. */
  private def onlyZero(x: String, below: Kernel.Thm): Kernel.Thm =
    moves.byDisjunction(moves.mp(moves.spec(moves.pf(Peano.BelowSuccessorCases), "ZERO", x), below))(
      under => moves.exFalso(moves.prop(s"$x = ZERO"), moves.absurd(moves.spec(moves.pf(Peano.NotBelowZero), x), under)),
      identity
    )

  /** The antecedent `atMost(sx, t)` opened: two members of the set are one, when `t <= 1`. */
  private def atMostOne(sized: Kernel.Thm, tAtMostOne: Option[Kernel.Thm], a: String, b: String,
      aBelow: Kernel.Thm, bBelow: Kernel.Thm, aIn: Kernel.Thm, bIn: Kernel.Thm, goal: Term): Kernel.Thm =
    moves.opened(sized, "g1") { g =>
      def zero(x: String, xBelow: Kernel.Thm, xIn: Kernel.Thm): Kernel.Thm = {
        val underT = moves.mp(moves.spec(moves.left(g), x), xBelow, xIn)
        val underOne = tAtMostOne.fold(underT)(atMostT =>
          moves.mp(moves.spec(moves.pf(Peano.BelowThenAtMost), s"g1 $x", "t", numeral(1)), moves.conj(underT, atMostT)))
        onlyZero(s"g1 $x", underOne)
      }
      val same = moves.mp(moves.spec(moves.right(g), a, b), aBelow, bBelow, aIn, bIn,
        moves.trans(zero(a, aBelow, aIn), moves.sym(zero(b, bBelow, bIn))))
      if (same.conclusion == goal) same else fail(s"the pair ${expander.show(same.conclusion)}")
    }

  private def matchable(goal: Term): Kernel.Thm = {
    val (guard, body) = implication(opened(goal, "sx"))
    val sized = moves.assumeT(guard)
    val range = {
      val proof = moves.conj(below(0, Holes), truth)
      moves.generalised(moves.discharged(proof, s"NUM_LT p0 ${numeral(Pigeons)}", "sx p0"), "p0")
    }
    val injective = {
      val p0Below = moves.assume(s"NUM_LT p0 ${numeral(Pigeons)}")
      val q0Below = moves.assume(s"NUM_LT q0 ${numeral(Pigeons)}")
      val same = atMostOne(sized, None, "p0", "q0", p0Below, q0Below, moves.assume("sx p0"), moves.assume("sx q0"), moves.prop("p0 = q0"))
      moves.generalised(moves.discharged(same, s"NUM_LT p0 ${numeral(Pigeons)}", s"NUM_LT q0 ${numeral(Pigeons)}",
        "sx p0", "sx q0", "ZERO = ZERO"), "p0", "q0")
    }
    val matched = moves.witnessed(body, List("\\y:num. ZERO"), moves.conj(range, injective))
    moves.generalised(ok(moves.rules.disch(guard, matched)), "sx")
  }

  private def expanding(goal: Term): Kernel.Thm = {
    val (hypotheses, body) = antecedents(opened(goal, "sx", "t"), 4)
    val tAtMostOne = moves.assumeT(hypotheses(0))
    val sized = moves.assumeT(hypotheses(2))
    val notSmaller = moves.assumeT(hypotheses(3))
    val (_, smaller) = (hypotheses(3), moves.logic.destNot(hypotheses(3)).getOrElse(fail("a negation")))
    val someMember = moves.prop(s"?p0:num. NUM_LT p0 ${numeral(Pigeons)} /\\ sx p0")
    // The set has a member below the pigeons, else it would inject into [0, PRE t) vacuously.
    val member = moves.byContradiction(someMember) { none =>
      def vacuous(statement: String): Kernel.Thm = {
        val found = moves.witnessed(someMember, List("p0"), moves.conj(moves.assume(s"NUM_LT p0 ${numeral(Pigeons)}"), moves.assume("sx p0")))
        moves.exFalso(moves.prop(statement), moves.absurd(none, found))
      }
      val range = moves.generalised(moves.discharged(vacuous("NUM_LT ZERO (PRE t)"),
        s"NUM_LT p0 ${numeral(Pigeons)}", "sx p0"), "p0")
      val injective = moves.generalised(moves.discharged(vacuous("p0 = q0"),
        s"NUM_LT p0 ${numeral(Pigeons)}", s"NUM_LT q0 ${numeral(Pigeons)}", "sx p0", "sx q0", "ZERO = ZERO"), "p0", "q0")
      moves.absurd(notSmaller, moves.witnessed(smaller, List("\\y:num. ZERO"), moves.conj(range, injective)))
    }
    val chosen = moves.opened(member, "p") { own =>
      val onBoundary = {
        val iBelow = moves.assume(s"NUM_LT i1 ${numeral(Holes)}")
        val unique = {
          val qBelow = moves.assume(s"NUM_LT q0 ${numeral(Pigeons)}")
          val same = atMostOne(sized, Some(tAtMostOne), "q0", "p", qBelow, moves.left(own), moves.assume("sx q0"), moves.right(own), moves.prop("q0 = p"))
          moves.generalised(moves.discharged(same, s"NUM_LT q0 ${numeral(Pigeons)}", "sx q0", "T"), "q0")
        }
        val there = moves.witnessed(moves.prop(s"?p0:num. NUM_LT p0 ${numeral(Pigeons)} /\\ sx p0 /\\ T /\\ " +
          s"(!q0:num. NUM_LT q0 ${numeral(Pigeons)} ==> sx q0 ==> T ==> q0 = p0)"), List("p"),
          moves.conj(moves.left(own), moves.conj(moves.right(own), moves.conj(truth, unique))))
        moves.generalised(moves.discharged(moves.conj(iBelow, there), s"NUM_LT i1 ${numeral(Holes)}"), "i1")
      }
      val injective = {
        val same = moves.assume("i1 = i2")
        moves.generalised(moves.discharged(same, s"NUM_LT i1 ${numeral(Holes)}", s"NUM_LT i2 ${numeral(Holes)}", "i1 = i2"), "i1", "i2")
      }
      moves.witnessed(body, List("\\i:num. i"), moves.conj(onBoundary, injective))
    }
    val closed = hypotheses.reverse.foldLeft(chosen)((current, hypothesis) => ok(moves.rules.disch(hypothesis, current)))
    moves.generalised(closed, "sx", "t")
  }

  /** Every input is a clause of the principle on the complete graph, from the refutation's values. */
  private def inputsAreClauses(goal: Term): Kernel.Thm =
    belowBound(goal, refutation.inputs) { (c, body) =>
      val (pigeonPart, holePart) = moves.logic.destDisj(body).getOrElse(fail("a disjunction"))
      val clause = refutation.clauses(c)
      def literal(i: Int): Kernel.Thm = moves.conj(refutation.variableOf(c, i), refutation.polarityOf(c, i))
      def present(i: Int, part: Term): Kernel.Thm =
        moves.witnessed(part, List(numeral(i)), moves.conj(refutation.indexBelow(c, i), literal(i)))
      if (clause.forall(_.positive)) {
        val pigeon = clause.head.pigeon
        val parts = conjuncts(opened(pigeonPart, numeral(pigeon)))
        val every = refutation.forEachLiteral(parts(1), c) { (i, atI) =>
          moves.witnessed(atI, List(numeral(clause(i).hole)), moves.conj(below(clause(i).hole, Holes), moves.conj(truth, literal(i))))
        }
        val neighbours = belowBound(parts(2), Holes, "t") { (h, atH) =>
          val (adjacent, found) = implication(atH)
          ok(moves.rules.disch(adjacent, present(clause.indexWhere(_.hole == h), found)))
        }
        moves.disjoined(body, moves.witnessed(pigeonPart, List(numeral(pigeon)), moves.conj(below(pigeon, Pigeons), moves.conj(every, neighbours))))
      } else {
        val (first, second) = (clause(0), clause(1))
        val at = List(numeral(first.pigeon), numeral(second.pigeon), numeral(first.hole))
        val parts = conjuncts(opened(holePart, at*))
        val every = refutation.forEachLiteral(parts(5), c) { (i, atI) =>
          val (either, _) = split(atI)
          moves.conj(moves.disjoined(either, refutation.variableOf(c, i)), refutation.polarityOf(c, i))
        }
        val proof = moves.conj(below(first.pigeon, second.pigeon), moves.conj(below(second.pigeon, Pigeons),
          moves.conj(below(first.hole, Holes), moves.conj(truth, moves.conj(truth,
            moves.conj(every, moves.conj(present(0, parts(6)), present(1, parts(7)))))))))
        moves.disjoined(body, moves.witnessed(holePart, at, proof))
      }
    }

  /** The four hypotheses that do not mention `w`, and the refutation, at the given width. */
  private def detachedBut(width: Int)(expansion: Term => Kernel.Thm): Kernel.Thm = {
    val stated = general(width)
    val (hypotheses, _) = antecedents(stated.conclusion, 5)
    moves.mp(stated, below(0, 1), matchable(hypotheses(1)), expansion(hypotheses(2)), inputsAreClauses(hypotheses(3)),
      refutation.refutes(hypotheses(4)))
  }

  "The theorem" should "have hypotheses the complete graph K(3, 2) and a refutation meet, and detach there" in {
    val result = refutation.close(detachedBut(2)(expanding))
    result.hypotheses shouldBe empty
    val expected = moves.prop(s"?j:num. NUM_LT j ${numeral(refutation.size)} /\\ NUM_LE ${numeral(2)} ((${refutation.lengths}) j)")
    result.conclusion shouldBe fixture.rightOf(ok(Conv.betaNormalise(expected)))
  }

  it should "say something at that refutation: steps of fewer than two literals exist there" in {
    // The detached conclusion is not true of every step, so the width conjunct is exercised.
    val narrow = refutation.clauses.indices.filter(j => refutation.clauses(j).size < 2)
    narrow should not be empty
    narrow.foreach { j =>
      val length = fixture.decided(fixture.rightOf(ok(Conv.betaNormalise(moves.term(s"(${refutation.lengths}) ${numeral(j)}", TyApp(Natural.TypeName, Nil))))))
      val size = refutation.clauses(j).size
      fixture.rightOf(length) shouldBe moves.term(numeral(size), TyApp(Natural.TypeName, Nil))
      moves.mp(moves.spec(moves.pf(Peano.BelowExcludesAtMost), numeral(size), numeral(2)), below(size, 2)).conclusion shouldBe
        moves.prop(s"~(NUM_LE ${numeral(2)} ${numeral(size)})")
    }
  }

  it should "be false without EXPANDING: at w = 20 the rest still holds and no step is that wide" in {
    val Wide = 20
    val stated = general(Wide)
    val (hypotheses, conclusion) = antecedents(stated.conclusion, 5)
    val rest = moves.mp(moves.spec(fact(ExpanderPigeonhole.ExpanderWidth), numeral(Pigeons), numeral(Holes), Complete, numeral(1), numeral(Wide),
      "k", "v", "s", numeral(refutation.inputs), numeral(refutation.size)), below(0, 1), matchable(hypotheses(1)))
    rest.conclusion shouldBe ok(moves.logic.mkImp(hypotheses(2), ok(moves.logic.mkImp(hypotheses(3), ok(moves.logic.mkImp(hypotheses(4), conclusion))))))
    val inputs = inputsAreClauses(hypotheses(3))
    val refuting = refutation.refutes(hypotheses(4))
    inputs.conclusion shouldBe hypotheses(3)
    refuting.conclusion shouldBe hypotheses(4)

    // No step has twenty literals: each length is at most two.
    val everyNarrow = belowBound(moves.prop(s"!w:num. NUM_LT w ${numeral(refutation.size)} ==> ~(NUM_LE ${numeral(Wide)} (k w))"),
      refutation.size) { (j, _) =>
      val size = refutation.clauses(j).size
      val excluded = moves.mp(moves.spec(moves.pf(Peano.BelowExcludesAtMost), numeral(size), numeral(Wide)), below(size, Wide))
      moves.transport(moves.sym(refutation.lengthOf(j)), s"~(NUM_LE ${numeral(Wide)} zz)", excluded)
    }
    val denial = ok(moves.rules.notIntro(conclusion, moves.opened(moves.assumeT(conclusion), "j") { body =>
      moves.absurd(moves.mp(moves.spec(everyNarrow, "j"), moves.left(body)), moves.right(body))
    }))
    val closed = refutation.close(moves.conj(moves.conj(inputs, refuting), denial))
    closed.hypotheses shouldBe empty
  }

  /* ------------------------------------------ what r = 0 makes of the two graph hypotheses */

  /** `MATCHABLE` at `r = 0`: a set injecting into `[0, 0)` has no member, so any map matches it. */
  private def matchableAtZero(goal: Term): Kernel.Thm = {
    val (guard, body) = implication(opened(goal, "sx"))
    val sized = moves.assumeT(guard)
    val range = moves.generalised(moves.discharged(moves.conj(below(0, Holes), truth),
      s"NUM_LT p0 ${numeral(Pigeons)}", "sx p0"), "p0")
    val injective = moves.opened(sized, "g1") { g =>
      val underZero = moves.mp(moves.spec(moves.left(g), "p0"), moves.assume(s"NUM_LT p0 ${numeral(Pigeons)}"), moves.assume("sx p0"))
      val none = moves.absurd(moves.spec(moves.pf(Peano.NotBelowZero), "g1 p0"), underZero)
      moves.generalised(moves.discharged(moves.exFalso(moves.prop("p0 = q0"), none), s"NUM_LT p0 ${numeral(Pigeons)}",
        s"NUM_LT q0 ${numeral(Pigeons)}", "sx p0", "sx q0", "ZERO = ZERO"), "p0", "q0")
    }
    val matched = moves.witnessed(body, List("\\y:num. ZERO"), moves.conj(range, injective))
    moves.generalised(ok(moves.rules.disch(guard, matched)), "sx")
  }

  /** `EXPANDING` at `r = 0`, for every `w`: `t <= 0` and `0 < t + t` never hold together. */
  private def expandingAtZero(goal: Term): Kernel.Thm = {
    val (hypotheses, body) = antecedents(opened(goal, "sx", "t"), 4)
    val tZero = moves.mp(moves.spec(moves.pf(Peano.AtMostZero), "t"), moves.assumeT(hypotheses(0)))
    val doubled = moves.substituted(tZero, moves.assumeT(hypotheses(1)))
    val atZero = moves.transport(moves.spec(moves.pf(Peano.AddAtZero), "ZERO"), "NUM_LT ZERO zz", doubled)
    val none = moves.absurd(moves.spec(moves.pf(Peano.StrictIrreflexive), "ZERO"), atZero)
    val closed = hypotheses.reverse.foldLeft(moves.exFalso(body, none))((current, hypothesis) => ok(moves.rules.disch(hypothesis, current)))
    moves.generalised(closed, "sx", "t")
  }

  it should "be false without 0 < r: at r = 0 both graph hypotheses hold for every w, and no step is twenty wide" in {
    // What makes the statement trivially true is an empty range of set sizes: at r = 0 no t has
    // t <= r < 2t, so EXPANDING asks nothing and holds at any w. The positivity hypothesis is the
    // only thing standing between that and a false theorem, and this shows it: every other
    // hypothesis is derived here at w = 20, and the conclusion is refuted at the same refutation.
    val Wide = 20
    val stated = moves.spec(fact(ExpanderPigeonhole.ExpanderWidth), numeral(Pigeons), numeral(Holes), Complete, numeral(0),
      numeral(Wide), "k", "v", "s", numeral(refutation.inputs), numeral(refutation.size))
    val (hypotheses, conclusion) = antecedents(stated.conclusion, 5)
    moves.spec(moves.pf(Peano.StrictIrreflexive), "ZERO").conclusion shouldBe ok(moves.logic.mkNot(hypotheses(0)))
    val matched = matchableAtZero(hypotheses(1))
    val expanded = expandingAtZero(hypotheses(2))
    val inputs = inputsAreClauses(hypotheses(3))
    val refuting = refutation.refutes(hypotheses(4))
    List(matched, expanded, inputs, refuting).map(_.conclusion) shouldBe hypotheses.drop(1)
    List(matched, expanded).foreach(_.hypotheses shouldBe empty)

    val everyNarrow = belowBound(moves.prop(s"!w:num. NUM_LT w ${numeral(refutation.size)} ==> ~(NUM_LE ${numeral(Wide)} (k w))"),
      refutation.size) { (j, _) =>
      val size = refutation.clauses(j).size
      val excluded = moves.mp(moves.spec(moves.pf(Peano.BelowExcludesAtMost), numeral(size), numeral(Wide)), below(size, Wide))
      moves.transport(moves.sym(refutation.lengthOf(j)), s"~(NUM_LE ${numeral(Wide)} zz)", excluded)
    }
    val denial = ok(moves.rules.notIntro(conclusion, moves.opened(moves.assumeT(conclusion), "j") { body =>
      moves.absurd(moves.mp(moves.spec(everyNarrow, "j"), moves.left(body)), moves.right(body))
    }))
    val closed = refutation.close(moves.conj(moves.conj(moves.conj(matched, expanded), moves.conj(inputs, refuting)), denial))
    closed.hypotheses shouldBe empty
  }
}
