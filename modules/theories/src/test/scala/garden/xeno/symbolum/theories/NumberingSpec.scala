package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The pairing the object language will be coded with, and the two claims its docstring makes.
 *
 * What is asserted beyond the statements and the accounting is the pair of claims a reader has to
 * take on trust otherwise, and both are derived rather than described.
 *
 * **That the bound is not strict, and that this is a fact rather than laziness.** `NUM_PAIR_LE_LEFT`
 * says `a <= NUM_PAIR a b` where a reader wants `<`, and the file says the strict version is false
 * at the origin. That sentence is worth nothing unless the number is produced: `NUM_PAIR ZERO ZERO`
 * is derived to be `ZERO`, and from it `~(NUM_LT ZERO (NUM_PAIR ZERO ZERO))`. So the lemma
 * published is the strongest true one.
 *
 * **That a constructor gets the strict bound back in one step**, which the same docstring promises
 * and leaves to a file that does not exist yet. `!a b. NUM_LT a (SUC (NUM_PAIR a b))` is derived
 * here, from the published bound and `NUM_LT_SUC` through the mixed transitivity, so the promise is
 * a theorem and its cost is visible.
 */
class NumberingSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val numbering = chain.numbering
  private val logic = numbering.logic
  private val rules = logic.rules
  private val numbers = TyApp(Natural.TypeName, Nil)

  private def constant(name: String, ty: Type): Term =
    force(LogicError.lift(numbering.theory.constant(name, ty)))

  private val zero = constant(Natural.NumberZero, numbers)
  private val successor = constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
  private val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))
  private val pair = constant(Numbering.PairName, arithmetic)
  private val plus = constant(Peano.Addition, arithmetic)
  private val triangle = constant(Numbering.TriangleName, Type.fun(numbers, numbers))
  private val below = constant(Peano.StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
  private val code = constant(Numbering.CodeName, arithmetic)

  "The numbering" should "be the statements this development publishes" in {
    Numbering.Statements.foreach { case (name, text) =>
      val theorem = force(numbering.fact(name))
      val expected = force(Parser.proposition(numbering.theory, numbering.notation, text))
      withClue(s"$name: ") {
        theorem.conclusion shouldBe expected
        theorem.hypotheses shouldBe empty
      }
    }
  }

  it should "cost what the naturals cost and nothing more" in {
    val recursion = force(chain.naturals.recursion)
    Numbering.Statements.foreach { case (name, _) =>
      val theorem = force(numbering.fact(name))
      withClue(s"$name: ") {
        Derivation.axiomsOf(theorem) shouldBe Derivation.axiomsOf(recursion)
        Derivation.axiomsOf(theorem) should have size 2
      }
    }
  }

  /**
   * The pairing is Cantor's with the halving never performed, and the definition says so.
   *
   * Asserted against the text because the docstring's argument is about what the definition
   * **avoids**: the familiar `(a + b)(a + b + 1) / 2 + a` would put `NUM_DIV` and its positivity
   * guard into every proof about syntax, and the triangular numbers are there so that it does not.
   * A definition that had quietly acquired a division would make that paragraph false.
   */
  it should "be Cantor's pairing written without a division" in {
    val definition = force(numbering.definition(Numbering.PairName))
    val intended = force(
      Parser.term(
        numbering.theory,
        numbering.notation,
        "\\a:num b:num. NUM_ADD (NUM_TRI (NUM_ADD a b)) a"
      )
    )
    Term.destEq(definition.conclusion).map(_._2) shouldBe Some(intended)
    Derivation.axiomsOf(definition) shouldBe empty
  }

  /**
   * The bound is not strict, and here is the number that makes the strict version false.
   *
   * `NUM_PAIR ZERO ZERO` is `NUM_TRI (ZERO + ZERO) + ZERO`, which is `ZERO`. So a component can
   * equal its own pair, and `NUM_LT` in place of `NUM_LE` in either bound would be a lemma this
   * theory refutes rather than one nobody had proved.
   */
  it should "be equal to its left component exactly at the origin" in {
    val paired = force(LogicError.lift(Term.appAll(pair, List(zero, zero))))
    val opened = force(Conv.unfold(force(numbering.definition(Numbering.PairName)), List(zero, zero)))

    val sumIsZero = force(rules.spec(zero, force(chain.peano.fact(Peano.AddAtZero))))
    val triangleAtSum = force(
      Conv
        .apTerm(triangle, sumIsZero)
        .flatMap(Conv.trans(_, force(numbering.fact(Numbering.TriangleAtZero))))
    )
    val asSum = force(Conv.apTerm(plus, triangleAtSum).flatMap(Conv.apThm(_, zero)))
    val vanishes = force(
      Conv.trans(opened, asSum).flatMap(Conv.trans(_, sumIsZero))
    )
    vanishes.conclusion shouldBe force(LogicError.lift(Term.eq(paired, zero)))

    // And therefore the strict bound is false there, which is what the lemma's shape is about.
    val strict = force(LogicError.lift(Term.appAll(below, List(zero, paired))))
    val assumed = force(LogicError.lift(Kernel.assume(strict)))
    val headed = force(LogicError.lift(Term.app(below, zero)))
    val absurdly = force(
      Conv
        .apTerm(headed, vanishes)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumed)))
    )
    val never = force(rules.spec(zero, force(chain.peano.fact(Peano.StrictIrreflexive))))
    val refuted = force(rules.notIntro(strict, force(rules.notElim(never, absurdly))))

    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe force(logic.mkNot(strict))
  }

  /**
   * The constructor is what a code of the object language will be, and it has no guard.
   *
   * Four facts and three of them unconditional, which is the property that matters above here: a
   * syntactic predicate defined by recursion over codes reaches for the strict bound at every
   * clause, and a bound that had to be discharged would put a hypothesis into every one of them.
   *
   * The fourth, injectivity, is the one with a premise and it is the premise being discharged
   * rather than a guard: two codes being equal is what the caller has.
   */
  it should "give every code a tag, a payload and no guard" in {
    val t = Term.variable("t", numbers)
    val p = Term.variable("p", numbers)
    val coded = force(LogicError.lift(Term.appAll(code, List(t, p))))

    // The definition is the tagged pair the file says it is, successor included.
    val definition = force(numbering.definition(Numbering.CodeName))
    val intended = force(
      Parser.term(numbering.theory, numbering.notation, "\\t:num p:num. SUC (NUM_PAIR t p)")
    )
    Term.destEq(definition.conclusion).map(_._2) shouldBe Some(intended)

    // Both components descend strictly, which the pairing alone cannot give.
    Vector(Numbering.CodeLeft -> t, Numbering.CodeRight -> p).foreach { case (name, component) =>
      val fact = force(rules.specAll(force(numbering.fact(name)), List(t, p)))
      withClue(s"$name: ") {
        fact.conclusion shouldBe force(LogicError.lift(Term.appAll(below, List(component, coded))))
        fact.hypotheses shouldBe empty
      }
    }

    // And no code is zero, which is what lets a predicate over codes refuse zero by shape.
    val refused = force(rules.specAll(force(numbering.fact(Numbering.CodeNotZero)), List(t, p)))
    refused.conclusion shouldBe force(
      logic.mkNot(force(LogicError.lift(Term.eq(coded, zero))))
    )
  }

  /**
   * A constructor gets the strict bound back by adding one, and that is the whole of it.
   *
   * `docs/adr/0014` rests on both components of a code being **strictly** below it, because that is
   * what lets `Descent` recurse. The pairing does not give that and says so; what gives it is that
   * a constructor tags its code, so the code is a successor. This is that step, derived once, so
   * that the file above can be read knowing what it costs.
   */
  it should "give a tagged constructor the strict bound, in one step" in {
    val a = Term.variable("a", numbers)
    val b = Term.variable("b", numbers)
    val paired = force(LogicError.lift(Term.appAll(pair, List(a, b))))
    val tagged = force(LogicError.lift(Term.app(successor, paired)))

    val bounded = force(rules.specAll(force(numbering.fact(Numbering.PairLeft)), List(a, b)))
    val next = force(rules.spec(paired, force(chain.peano.fact(Peano.BelowSuccessor))))
    val strict = force(
      rules
        .conjIntro(bounded, next)
        .flatMap(pieces =>
          rules
            .specAll(force(chain.peano.fact(Peano.AtMostThenBelow)), List(a, paired, tagged))
            .flatMap(rules.mp(_, pieces))
        )
    )
    val general = force(rules.genAll(strict, List(a, b)))

    general.hypotheses shouldBe empty
    Derivation.axiomsOf(general) should have size 2
    general.conclusion shouldBe force(
      Parser.proposition(
        numbering.theory,
        numbering.notation,
        "!a:num b:num. NUM_LT a (SUC (NUM_PAIR a b))"
      )
    )
  }

  /**
   * The projections compose the way a function over codes will use them.
   *
   * A function that takes a binary constructor apart does `NUM_FST (NUM_PAYLOAD c)` and
   * `NUM_SND (NUM_PAYLOAD c)`, and that composition is the only thing about the four equations that
   * is not immediate from each on its own. Derived at a code of the shape the language actually
   * builds rather than at a bare pair.
   */
  it should "take a code with a pair inside it apart in two steps" in {
    val a = Term.variable("a", numbers)
    val b = Term.variable("b", numbers)
    val tag = force(Parser.term(numbering.theory, numbering.notation, "3", numbers))

    def unary(name: String): Term =
      force(LogicError.lift(numbering.theory.constant(name, Type.fun(numbers, numbers))))
    def at(function: Term, argument: Term): Term =
      force(LogicError.lift(Term.app(function, argument)))

    val first = unary(Numbering.FirstName)
    val second = unary(Numbering.SecondName)
    val payloadOf = unary(Numbering.PayloadName)

    val paired = force(LogicError.lift(Term.appAll(pair, List(a, b))))
    val coded = force(LogicError.lift(Term.appAll(code, List(tag, paired))))
    val payload = force(
      rules.specAll(force(numbering.fact(Numbering.PayloadOfCode)), List(tag, paired))
    )

    val leftReached = force(
      Conv
        .apTerm(first, payload)
        .flatMap(Conv.trans(_, force(
          rules.specAll(force(numbering.fact(Numbering.FirstOfPair)), List(a, b)))))
    )
    val rightReached = force(
      Conv
        .apTerm(second, payload)
        .flatMap(Conv.trans(_, force(
          rules.specAll(force(numbering.fact(Numbering.SecondOfPair)), List(a, b)))))
    )

    leftReached.conclusion shouldBe
      force(LogicError.lift(Term.eq(at(first, at(payloadOf, coded)), a)))
    rightReached.conclusion shouldBe
      force(LogicError.lift(Term.eq(at(second, at(payloadOf, coded)), b)))
    leftReached.hypotheses shouldBe empty
    rightReached.hypotheses shouldBe empty
    Derivation.axiomsOf(leftReached) should have size 2
  }

  /**
   * The two projections of a pair are different functions, which is not free.
   *
   * Both are defined by `select` over an existential, and the two existentials differ only in which
   * slot the chosen number sits in. A definition that had both reading the same slot would still be
   * a definition, would still satisfy one of the two equations, and the other equation is what
   * refuses it. Here that is turned into the theorem it implies: at `NUM_PAIR 0 1` the two answers
   * differ, so the two constants are not one constant under two names.
   */
  it should "read two different slots of the same pair" in {
    val zero = force(Parser.term(numbering.theory, numbering.notation, "0", numbers))
    val one = force(Parser.term(numbering.theory, numbering.notation, "SUC 0", numbers))
    val paired = force(LogicError.lift(Term.appAll(pair, List(zero, one))))

    val left = force(rules.specAll(force(numbering.fact(Numbering.FirstOfPair)), List(zero, one)))
    val right = force(rules.specAll(force(numbering.fact(Numbering.SecondOfPair)), List(zero, one)))

    val same = force(LogicError.lift(Term.eq(
      Term.destEq(left.conclusion).map(_._1).getOrElse(fail("an equation")),
      Term.destEq(right.conclusion).map(_._1).getOrElse(fail("an equation"))
    )))
    val assumed = force(LogicError.lift(Kernel.assume(same)))
    val zeroIsOne = force(
      Conv.sym(left).flatMap(Conv.trans(_, assumed)).flatMap(Conv.trans(_, right))
    )
    val never = force(rules.spec(zero, force(chain.naturals.fact(Natural.SuccessorNotZero))))
    val refuted = force(
      rules.notIntro(same, force(rules.notElim(never, force(Conv.sym(zeroIsOne)))))
    )

    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe force(logic.mkNot(same))
    val _ = paired
  }
}
