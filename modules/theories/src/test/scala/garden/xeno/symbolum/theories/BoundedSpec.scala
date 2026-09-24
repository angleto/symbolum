package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A bounded universal discharged by enumeration, which nothing here could do.
 *
 * The audit wrote the gap as *"a bounded universal is not discharged by computation. There is no
 * reflection: a consumer checks twelve forms by enumeration and that fact has no route into the
 * kernel"*. The instances were never the missing half: a caller could prove each of the twelve and
 * had nothing to join them with, `Peano` holding no fact that takes `i < SUC n` apart.
 *
 * What is asserted here, in order: the two lemmas are what they say they are; the consumers are
 * proved end to end, which is this repository's bar for a tactic being built; the refusals are told
 * apart from each other; and the cost is measured as a function of the bound, because that number
 * is what tells a future reader what this is for and what it is not for.
 */
class BoundedSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val peano = chain.peano
  private val logic = peano.logic
  private val rules = logic.rules
  private val bounded = Bounded.standard
  private val linarith = force(Linarith.construct(chain.order))

  private val numbers = TyApp(Natural.TypeName, Nil)
  private val index = Term.variable("i", numbers)

  private val zero = force(LogicError.lift(peano.theory.constant(Natural.NumberZero, numbers)))
  private val successor = force(
    LogicError.lift(peano.theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers)))
  )
  private val lessThan = force(
    LogicError.lift(
      peano.theory.constant(Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
    )
  )

  /** `!i:num. NUM_LT i <bound> ==> consequent`, built rather than parsed: this driver walks successors. */
  private def claim(bound: Int, consequent: Term): Term = {
    val limit = force(Bounded.numeral(zero, successor, bound))
    val guard = force(LogicError.lift(Term.appAll(lessThan, List(index, limit))))
    force(logic.mkForall(index, force(logic.mkImp(guard, consequent))))
  }

  /** The two equations that carry an index of `num` into the reals, as rewrite rules. */
  private val embedding = force(
    Rewrite.Rule.all(
      logic,
      Vector(force(peano.fact(Peano.EmbedsZero)), force(peano.fact(Peano.EmbedsSuccessor)))
    )
  )

  /* ----------------------------------------------------------------- the lemmas */

  "The case split the driver rests on" should "be `Peano`'s, and say what it is recorded as saying" in {
    // Stated rather than described, for the reason `Peano.Statements` gives: a statement is checked
    // by reading it, and builder calls are not read. Both lemmas were derived in `Bounded` until
    // 2026-09-11 and are `Peano`'s now: nothing about either is about enumeration, and a driver
    // holding its own copy of a fact the chain already proves is a second place for it to drift.
    val split = force(peano.fact(Peano.BelowSuccessorCases))

    split.conclusion shouldBe force(
      peano.proposition("!n:num i:num. NUM_LT i (SUC n) ==> NUM_LT i n \\/ i = n")
    )
    split.hypotheses shouldBe empty

    val none = force(peano.fact(Peano.NotBelowZero))

    none.conclusion shouldBe force(peano.proposition("!i:num. ~(NUM_LT i ZERO)"))
    none.hypotheses shouldBe empty

    info(
      s"${Derivation.size(split)} inferences for the case split, ${Derivation.size(none)} for the " +
        s"empty range, over ${Derivation.axiomsOf(split).size} axioms"
    )
  }

  it should "cost no axiom the chain did not already carry" in {
    // The trusted base must not move, and this is the check rather than the claim. Both lemmas are
    // derived from `Peano` and `Natural`, so what they reach is what those reach.
    val assumed = chain.series.theory.axioms.toSet

    Derivation.axiomsOf(force(peano.fact(Peano.BelowSuccessorCases))).diff(assumed) shouldBe empty
    Derivation.axiomsOf(force(peano.fact(Peano.NotBelowZero))).diff(assumed) shouldBe empty
  }

  /* --------------------------------------------------------- the worked consumers */

  "A polynomial that vanishes on three residues" should "be proved for every index below three" in {
    // The shape the audit described: a claim true of each of a handful of cases and of nothing else,
    // checked by enumeration, with each case closed by a procedure that knows nothing about the
    // bound. `x (x - 1) (x - 2) = 0` is false for a real `x` and true for each of `0`, `1` and `2`,
    // so nothing but the enumeration can be what proves it.
    val statement = force(
      peano.proposition(
        "!i:num. NUM_LT i (SUC (SUC (SUC ZERO))) ==> " +
          "real_of_num i * (real_of_num i - 1) * (real_of_num i - 2) = 0"
      )
    )

    val theorem = force(
      bounded.prove(statement)(instance =>
        Induct.afterRewriting(embedding, instance.goal)(chain.ring.prove)
      )
    )

    theorem.conclusion shouldBe statement
    theorem.hypotheses shouldBe empty
    Derivation.axiomsOf(theorem).diff(chain.series.theory.axioms.toSet) shouldBe empty

    info(s"${Derivation.size(theorem)} inferences over ${Derivation.axiomsOf(theorem).size} axioms")
  }

  "Every index below four" should "be below four in the reals, by LINARITH at each of them" in {
    // The other half of what a consumer wants: the instances closed by a decision procedure over the
    // reals, reached through `real_of_num`. Note what is NOT used: `NUM_REAL_LT`, which would carry
    // the bound across in one step and prove the claim for a variable bound as well. This is the
    // case where there is no such lemma, and the four instances are the proof.
    val statement = force(
      peano.proposition("!i:num. NUM_LT i (SUC (SUC (SUC (SUC ZERO)))) ==> real_of_num i < 4")
    )

    val theorem = force(
      bounded.prove(statement)(instance =>
        Induct.afterRewriting(embedding, instance.goal)(linarith.prove)
      )
    )

    theorem.conclusion shouldBe statement
    theorem.hypotheses shouldBe empty

    info(s"${Derivation.size(theorem)} inferences over ${Derivation.axiomsOf(theorem).size} axioms")
  }

  "The driver" should "hand the caller each index in turn, instantiated" in {
    // The record `Induct.Step` exists for, one driver over: a caller cannot see inside, so what it
    // is given has to be what it needs. The order is part of the contract because a caller building
    // on its own earlier answers depends on it.
    val seen = scala.collection.mutable.ArrayBuffer.empty[(Int, Term, Term)]
    val truth = force(rules.truth)
    val statement = claim(3, truth.conclusion)

    force(bounded.prove(statement) { instance =>
      seen += ((instance.position, instance.index, instance.goal))
      Right(truth)
    })

    seen.map(_._1).toVector shouldBe Vector(0, 1, 2)
    seen.map(_._2).toVector shouldBe Vector(0, 1, 2).map(k =>
      force(Bounded.numeral(zero, successor, k))
    )
    seen.map(_._3).toVector.distinct shouldBe Vector(truth.conclusion)
  }

  /* ------------------------------------------------------------------- the refusals */

  "A bound that is not a numeral" should "be refused by shape, and not by a limit" in {
    // `!i. i < n ==> P i` over a variable `n` is not false and is not provable this way. The refusal
    // has to send the reader to `Induct` rather than to a number, which is what separating it from
    // `BoundReached` buys.
    val variable = Term.variable("n", numbers)
    val guard = force(LogicError.lift(Term.appAll(lessThan, List(index, variable))))
    val truth = force(rules.truth)
    val statement = force(logic.mkForall(index, force(logic.mkImp(guard, truth.conclusion))))

    bounded.prove(statement)(_ => Right(truth)) match {
      case Left(NotOfForm(expected, found)) =>
        expected should include("numeral")
        found shouldBe variable
      case other => fail(s"expected a refusal about the shape of the bound, got $other")
    }
  }

  "A bound past the budget" should "name the limit and the bound rather than run" in {
    // Ten thousand, which is a term a translator produces without anybody intending it. The
    // assertion worth having is not that it is quick: it is that nothing was decided, which is what
    // `BoundReached` says and `NotOfForm` would not.
    val truth = force(rules.truth)
    val statement = claim(10000, truth.conclusion)

    bounded.prove(statement)(_ => Right(truth)) match {
      case Left(BoundReached(limit, reached, allowed, _)) =>
        limit shouldBe Bounded.LimitName
        reached shouldBe 10000
        allowed shouldBe Bounded.Instances
      case other => fail(s"expected the budget to stop it, got $other")
    }
  }

  "An index the caller cannot settle" should "name that index and carry its reason" in {
    // A false claim: `real_of_num i < 2` holds at `0` and `1` and fails at `2`. What the refusal has
    // to say is WHICH one, because a walk that stopped at the third instance and a walk that stopped
    // at the first mean different things, and only the second suggests the method is wrong.
    val statement = force(
      peano.proposition("!i:num. NUM_LT i (SUC (SUC (SUC ZERO))) ==> real_of_num i < 2")
    )

    bounded.prove(statement)(instance =>
      Induct.afterRewriting(embedding, instance.goal)(linarith.prove)
    ) match {
      case Left(InstanceRefused(at, goal, reason)) =>
        at shouldBe 2
        // The goal named is the instance, not the claim: the index has been substituted, so there
        // is nothing left in it that a reader has to instantiate for themselves.
        Term.freeVariables(goal) shouldBe empty
        reason.message should not be empty
      case other => fail(s"expected the refusal to name the index, got $other")
    }
  }

  it should "be told apart from a caller that proved something else" in {
    // The fourth case, which lives inside the third rather than beside it: the caller's step is
    // wrong either way and `reason` is what distinguishes them. A driver that accepted this would
    // return a theorem about something the caller never asked for.
    val truth = force(rules.truth)
    val statement = claim(2, truth.conclusion)
    val elsewhere = force(rules.spec(zero, force(peano.fact(Peano.NotBelowZero))))

    bounded.prove(statement)(_ => Right(elsewhere)) match {
      case Left(InstanceRefused(at, _, NotOfForm(expected, found))) =>
        at shouldBe 0
        expected should include("instance")
        found shouldBe elsewhere.conclusion
      case other => fail(s"expected the wrong theorem to be refused, got $other")
    }
  }

  /* --------------------------------------------------------------- the measurements */

  "The budget" should "be measured by building the same driver with the line somewhere else" in {
    // The only way to find out what a limit cuts, and the argument `Linarith.Facts` makes for its
    // own: a limit calibrated on nothing is calibrated on nothing. Same claim, two drivers.
    val statement = force(
      peano.proposition(
        "!i:num. NUM_LT i (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC ZERO))))))))" +
          " ==> real_of_num i < 8"
      )
    )

    def ask(limit: Int): Either[LogicError, Kernel.Thm] =
      force(Bounded.construct(peano, limit)).prove(statement)(instance =>
        Induct.afterRewriting(embedding, instance.goal)(linarith.prove)
      )

    ask(4) match {
      case Left(BoundReached(_, reached, allowed, _)) =>
        reached shouldBe 8
        allowed shouldBe 4
      case other => fail(s"at a limit of four this is out of reach, got $other")
    }

    val proved = force(ask(32))
    proved.conclusion shouldBe statement

    // What the line cuts is a provable claim and what it buys is that a mistake is cheap. Both
    // halves are here so that neither can be asserted without the other.
    info(s"cut at 4, proved at 32 in ${Derivation.size(proved)} inferences")
  }

  "The cost of the assembly" should "be linear in the bound, and that is what it is for" in {
    // Instances that cost nothing, so what is measured is the driver and not the caller. The number
    // is the point of the test rather than the assertion: a reader deciding whether to reach for
    // this needs to know that the cost grows linearly with the bound and no faster.
    val truth = force(rules.truth)

    val sizes = Vector(1, 2, 4, 8).map { bound =>
      val theorem = force(bounded.prove(claim(bound, truth.conclusion))(_ => Right(truth)))
      bound -> Derivation.size(theorem)
    }

    info(sizes.map { case (bound, size) => s"bound $bound: $size inferences" }.mkString(", "))

    // Linear and not worse: each step is one case split and two branches, and nothing in it revisits
    // what earlier steps built. A quadratic assembly here would be the defect this pins.
    val perStep = (sizes.last._2 - sizes.head._2).toDouble / (sizes.last._1 - sizes.head._1)
    val predicted = sizes.head._2 + perStep * (4 - 1)

    math.abs(sizes(2)._2 - predicted) should be < (perStep / 2)
  }
}
