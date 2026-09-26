package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The width of a resolution refutation of the pigeonhole principle, and what keeps the theorem from
 * being about nothing.
 *
 * **That its hypotheses are met, where the width conjunct is not free.** A lower bound whose
 * hypotheses nothing satisfies is true and empty, and it would pass every other test here. The
 * instance is three pigeons in two holes and the refutation of nineteen steps in
 * `ResolutionFixture`; every hypothesis is derived for it with nothing assumed and the theorem is
 * detached there. This read `n = 1` until 2026-09-26, and the verification of 2026-09-25 is why it
 * does not: at `n = 1` the conjunct `1 <= SUC (k j)` holds of every step, so a theorem proving only
 * `?j. inputs <= j /\ j < m` would have passed the same detachment. At `n = 2` the empty clause
 * fails the conjunct, which is asserted beside it.
 *
 * **That `0 < n` is load-bearing.** At `n = 0` the one pigeon's clause is empty, so the refutation of
 * one step meets the other two hypotheses and has no derived step at all: the conclusion is refuted
 * at it. The theorem with that hypothesis dropped is false, and that is derived rather than argued.
 *
 * **That the injection bound needs its injectivity.** A constant function from two numbers into one
 * meets the range hypothesis, and `2 <= 1` is refuted.
 *
 * The goals are read off the published theorem, specialised, rather than written out a second time
 * here: what is shown to be met is exactly what the theorem asks.
 */
class PigeonholeSpec extends AnyFlatSpec with Matchers {

  private def ok[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private lazy val chain = Chain.standard
  private lazy val pigeonhole = ok(Pigeonhole.construct(chain))
  private lazy val moves = new Pigeonhole.Builder(chain)
  private val Num = TyApp(Natural.TypeName, Nil)

  private def fact(name: String): Kernel.Thm = ok(pigeonhole.fact(name))

  "Every fact of the development" should "prove the statement it is published as" in {
    Pigeonhole.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe ok(pigeonhole.proposition(text))
        fact(name).hypotheses shouldBe empty
      }
    }
    pigeonhole.facts.keySet shouldBe Pigeonhole.Statements.map(_._1).toSet
  }

  it should "cost choice and infinity and none of the reals' axioms" in {
    // Built over the chain's end, where the reals live; nothing about a field is reached.
    val expected = Set(
      ok(chain.classical.axiom(Classical.Choice)).conclusion,
      ok(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    Pigeonhole.Statements.foreach { case (name, _) =>
      withClue(s"$name: ")(Derivation.axiomsOf(fact(name)) shouldBe expected)
    }
  }

  it should "read the bad pigeons through the soundness of a resolution step" in {
    // Step 3 of the argument: a resolvent's bad pigeons are its parents'. A proof that reached the
    // conclusion some other way would state the same thing and would not be this argument.
    val wanted = Set(ok(chain.resolving.fact(Resolving.StepSound)).conclusion)
    Derivation.restingOn(fact(Pigeonhole.DerivedWidth), wanted) shouldBe wanted
  }

  /* ------------------------------------------------------------------ the moves */

  private lazy val fixture = new ResolutionFixture(moves, chain, term => pigeonhole.show(term))
  import fixture.{numeral, antecedents, implication, opened, conjuncts, split, rightOf, argumentsOf, unfold, belowBound, below, noMoreThan}

  private lazy val One = numeral(1)
  private lazy val Two = numeral(2)

  /* ------------------------------------------- the refutation of three pigeons in two holes */

  private val Holes = 2
  private lazy val refutation = fixture.threeIntoTwo

  /** Every input is a clause of the principle for three pigeons, from the refutation's values. */
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
          moves.witnessed(atI, List(numeral(clause(i).hole)), moves.conj(below(clause(i).hole, Holes), literal(i)))
        }
        val holes = belowBound(parts(2), Holes, "t") { (h, atH) => present(clause.indexWhere(_.hole == h), atH) }
        moves.disjoined(body, moves.witnessed(pigeonPart, List(numeral(pigeon)), moves.conj(noMoreThan(pigeon, Holes), moves.conj(every, holes))))
      } else {
        val (first, second) = (clause(0), clause(1))
        val at = List(numeral(first.pigeon), numeral(second.pigeon), numeral(first.hole))
        val parts = conjuncts(opened(holePart, at*))
        val every = refutation.forEachLiteral(parts(3), c) { (i, atI) =>
          val (either, _) = split(atI)
          moves.conj(moves.disjoined(either, refutation.variableOf(c, i)), refutation.polarityOf(c, i))
        }
        val proof = moves.conj(below(first.pigeon, second.pigeon), moves.conj(noMoreThan(second.pigeon, Holes),
          moves.conj(below(first.hole, Holes), moves.conj(every, moves.conj(present(0, parts(4)), present(1, parts(5)))))))
        moves.disjoined(body, moves.witnessed(holePart, at, proof))
      }
    }

  "The theorem" should "have hypotheses a refutation of three pigeons in two holes meets, and detach at it" in {
    val general = moves.spec(fact(Pigeonhole.DerivedWidth), Two, "k", "v", "s", numeral(refutation.inputs), numeral(refutation.size))
    val (hypotheses, _) = antecedents(general.conclusion, 3)
    val detached = moves.mp(general, below(0, 2), inputsAreClauses(hypotheses(1)), refutation.refutes(hypotheses(2)))
    val result = refutation.close(detached)
    result.hypotheses shouldBe empty
    val expected = moves.prop(s"?j:num. NUM_LE ${numeral(refutation.inputs)} j /\\ NUM_LT j ${numeral(refutation.size)} /\\ " +
      s"NUM_LE $Two (SUC ((${refutation.lengths}) j))")
    result.conclusion shouldBe rightOf(ok(Conv.betaNormalise(expected)))
  }

  it should "say something at that refutation: its last step is too narrow for the width conjunct" in {
    // At `n = 1` the conjunct `1 <= SUC (k j)` held of every step, so a detachment there never read
    // it. At `n = 2` the empty clause has `SUC 0 = 1 < 2`, so the witness has to be a step with a
    // literal in it, and the conjunct is exercised.
    val last = refutation.size - 1
    refutation.clauses(last) shouldBe empty
    val length = fixture.decided(rightOf(ok(Conv.betaNormalise(moves.term(s"(${refutation.lengths}) ${numeral(last)}", Num)))))
    rightOf(length) shouldBe moves.term("ZERO", Num)
    moves.mp(moves.spec(moves.pf(Peano.BelowExcludesAtMost), One, Two), below(1, 2)).conclusion shouldBe
      moves.prop(s"~(NUM_LE $Two (SUC ZERO))")
  }

  it should "be false without 0 < n, at the one-step refutation of the empty pigeon clause" in {
    // At `n = 0` the pigeon clause is empty, so a refutation can stop at its input.
    val general = moves.spec(fact(Pigeonhole.DerivedWidth), "ZERO", "k", "v", "s", One, One)
    val (hypotheses, conclusion) = antecedents(general.conclusion, 3)
    val positive = hypotheses(0)
    val inputs = hypotheses(1)
    val refutation = hypotheses(2)
    val emptyLength = moves.assume("k ZERO = ZERO")

    val clause = belowBound(inputs, 1) { (_, body) =>
      val (pigeonPart, _) = moves.logic.destDisj(body).getOrElse(fail("a disjunction"))
      val parts = conjuncts(opened(pigeonPart, "ZERO"))
      def vacuous(goal: Term, bound: Kernel.Thm => Kernel.Thm): Kernel.Thm = {
        val (guard, rest) = implication(opened(goal, "i"))
        val underZero = bound(moves.assumeT(guard))
        val absurd = moves.absurd(moves.spec(moves.pf(Peano.NotBelowZero), "i"), underZero)
        moves.generalised(ok(moves.rules.disch(guard, moves.exFalso(rest, absurd))), "i")
      }
      val literals = vacuous(parts(1), below => moves.transport(emptyLength, "NUM_LT i zz", below))
      val holes = vacuous(parts(2), identity)
      moves.disjoined(body, moves.witnessed(pigeonPart, List("ZERO"),
        moves.conj(moves.spec(moves.pf(Peano.ZeroIsLeast), "ZERO"), moves.conj(literals, holes))))
    }
    val refuting = {
      val opening = unfold(Resolving.Refutation, argumentsOf(refutation))
      val (everyStep, reachesEmpty) = split(rightOf(opening))
      val steps = belowBound(everyStep, 1) { (_, justifiedAt) =>
        val justifying = unfold(Resolving.JustifiedName, argumentsOf(justifiedAt))
        ok(LogicError.lift(Kernel.eqMp(moves.sym(justifying), moves.disjoined(rightOf(justifying), below(0, 1)))))
      }
      val empty = moves.witnessed(reachesEmpty, List("ZERO"), moves.conj(below(0, 1), emptyLength))
      ok(LogicError.lift(Kernel.eqMp(moves.sym(opening), moves.conj(steps, empty))))
    }
    refuting.conclusion shouldBe refutation
    clause.conclusion shouldBe inputs

    // And nothing it asks for exists: a derived step is at least one and below one.
    val refuted = ok(moves.rules.notIntro(conclusion, {
      val assumed = moves.assumeT(conclusion)
      val predicate = moves.logic.destExistsPredicate(conclusion).get
      val j = Term.variable("j", Num)
      val body = Term.destEq(ok(Conv.betaRoot(ok(LogicError.lift(Term.app(predicate, j))))).conclusion).map(_._2).get
      val parts = moves.assumeT(body)
      val atLeast = moves.left(parts)
      val underOne = moves.left(moves.right(parts))
      val excluded = moves.mp(moves.spec(moves.pf(Peano.BelowExcludesAtMost), "j", One), underOne)
      ok(moves.rules.existsElim(assumed, j, moves.absurd(excluded, atLeast)))
    }))
    // The two hypotheses rest on the one-step refutation's length alone, the conclusion's denial on
    // nothing; what stands between them and a falsity is `0 < 0`, which is itself refuted.
    refuted.hypotheses shouldBe empty
    clause.hypotheses.toSet shouldBe Set(moves.prop("k ZERO = ZERO"))
    refuting.hypotheses.toSet shouldBe Set(moves.prop("k ZERO = ZERO"))
    positive shouldBe moves.prop("NUM_LT ZERO ZERO")
    moves.spec(moves.pf(Peano.StrictIrreflexive), "ZERO").conclusion shouldBe ok(moves.logic.mkNot(positive))
  }

  "The injection bound" should "need its injectivity: a constant function puts two into one" in {
    val general = moves.spec(fact(Pigeonhole.Injection), Two, One, "\\x:num. ZERO")
    val (hypotheses, conclusion) = antecedents(general.conclusion, 2)
    val range = hypotheses(0)
    val rangeHolds = {
      val (guard, body) = implication(opened(range, "x"))
      moves.generalised(ok(moves.rules.disch(guard, below(0, 1).ensuring(_.conclusion == body))), "x")
    }
    rangeHolds.conclusion shouldBe range
    val notInjective = moves.spec(moves.nf(Natural.SuccessorNotZero), "ZERO")
    notInjective.conclusion shouldBe moves.prop(s"~($One = ZERO)")
    moves.mp(moves.spec(moves.pf(Peano.BelowExcludesAtMost), One, Two), below(1, 2)).conclusion shouldBe
      ok(moves.logic.mkNot(conclusion))
  }
}
