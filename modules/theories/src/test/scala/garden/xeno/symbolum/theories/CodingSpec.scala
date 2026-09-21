package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The factorial, and the fact the beta function's moduli rest on.
 *
 * What is asserted: the three statements are the text `Coding.Statements` publishes; the divisor
 * lemma is not vacuous, which for this one means the hypothesis it would be easiest to drop is the
 * one that makes it false; and the accounting, which is the assertion worth reading.
 *
 * The accounting is written as an **equality against what it inherits** rather than as a count.
 * `NUM_FACT_DIVIDES` reaches sixteen axioms, fourteen of them the real numbers', and not one of
 * them is reached by anything in this file: they arrive whole from `NUM_DIVIDES_MUL`, which is
 * `Modular`'s and is proved through the embedding. Pinning the sixteen would make this test fail
 * the day somebody improves that derivation, which is the wrong way round. What is pinned is that
 * this development adds nothing of its own, which is the claim the number stood for and which stays
 * true whatever `Modular` costs.
 */
class CodingSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val modular = chain.modular
  private val coding = force(Coding.construct(modular))

  "The factorial" should "be the statements this development publishes" in {
    Coding.Statements.foreach { case (name, text) =>
      val theorem = force(coding.fact(name))
      val expected = force(Parser.proposition(coding.theory, coding.notation, text))
      withClue(s"$name: ") {
        theorem.conclusion shouldBe expected
        theorem.hypotheses shouldBe empty
      }
    }
  }

  it should "add no axiom of its own beyond what its divisibility lemma already costs" in {
    val divides = force(coding.fact(Coding.FactorialDivides))
    val inherited = force(modular.fact(Modular.DividesMul))

    Derivation.axiomsOf(divides) shouldBe Derivation.axiomsOf(inherited)

    // And what that inheritance is worth, since 2026-09-13 it is worth the whole claim: `NUM_FACT`
    // reaches nothing but choice and infinity. It reached sixteen until `NUM_DIVIDES_MUL` stopped
    // sending one associativity to a decision procedure over the reals. Pinned as an equality and
    // not as a ceiling, for the reason `DescentSpec` gives: a count that only has to stay under a
    // bound passes when a derivation stops reaching something it should reach.
    Derivation.axiomsOf(divides) should have size 2

    // And the two recurrences, which touch no divisibility at all, cost what the naturals cost.
    val recurrence = force(coding.fact(Coding.FactorialAtSuccessor))
    Derivation.axiomsOf(recurrence) shouldBe Derivation.axiomsOf(force(chain.naturals.recursion))
    Derivation.axiomsOf(recurrence) should have size 2
  }

  /**
   * The Chinese remainder theorem, and where its sixteen axioms come from.
   *
   * Both reach two, and this one reached sixteen until the evening of 2026-09-13: they arrived
   * whole from `NUM_BEZOUT`, which was proved through the embedding into the reals like
   * twenty-eight of `Modular`'s thirty-eight. Writing the assertion as an equality against what it
   * inherits is what made that change show up here as a number moving rather than as a test to
   * rewrite.
   *
   * **What is not asserted, and why.** No concrete instance is discharged. The premise names
   * `NUM_GCD m n = SUC ZERO`, and settling that at two given numbers means computing a greatest
   * common divisor, which `docs/adr/0010` keeps out of the kernel on purpose: `NUM_GCD` denotes and
   * is not calculated. A test that appeared to check an instance would be checking something else.
   */
  it should "prove the Chinese remainder theorem, adding no axiom to what Bezout costs" in {
    val crt = force(coding.fact(Coding.Remainders))
    val bezout = force(modular.fact(Modular.Bezout))

    Derivation.axiomsOf(crt) shouldBe Derivation.axiomsOf(bezout)
    // Sixteen when this landed, two since `Modular` stopped deciding its own identities through the
    // reals. The equality above is what survived the change and the count is what moved, which is
    // the whole reason it is written as an equality first.
    Derivation.axiomsOf(crt) should have size 2
    crt.hypotheses shouldBe empty
  }

  /**
   * It specialises, which is the weakest useful thing to ask of a theorem nobody can instantiate.
   *
   * Not a formality: the statement quantifies over four numbers and the derivation generalises them
   * in an order nothing else pins, so a consumer that specialised positionally would get a true
   * theorem about the wrong pair. `Rules.specTo` finds the instantiation by matching the body, and
   * the point of using it here is that the assertion then says which instance was meant.
   */
  it should "specialise to the instance a consumer asks for, by the body and not by position" in {
    val crt = force(coding.fact(Coding.Remainders))
    val wanted = force(
      Parser.proposition(
        coding.theory,
        coding.notation,
        "NUM_GCD p:num q:num = SUC ZERO /\\ NUM_LT ZERO p /\\ NUM_LT ZERO q ==> " +
          "(?x:num. NUM_CONG p x (r:num) /\\ NUM_CONG q x (s:num))"
      )
    )
    val instance = force(coding.logic.rules.specTo(crt, wanted))
    instance.conclusion shouldBe wanted
  }

  /**
   * The two pieces the beta function's coprimality argument stands on, and what they cost.
   *
   * `NUM_PROD` is the twin of `Peano.PartialSum` at the product, and it is here rather than in
   * `Peano` for the reason the factorial is: the combined modulus of the Chinese remainder theorem
   * over `n` moduli is a product over a range, and nothing else has wanted one.
   *
   * `NUM_GAUSS` is the piece `Modular` does not have and that `Modular.Euclid` does not cover:
   * Euclid asks for a **prime** divisor, and what the moduli `1 + (i + 1) * k!` need is that a
   * divisor coprime to one factor divides the other, whatever it is made of. Reaching it through
   * primes would have wanted "every number above one has a prime divisor", which nothing here
   * holds either.
   *
   * **What is not asserted, and why.** That the guard `~(a = ZERO) \/ ~(b = ZERO)` is necessary.
   * It is: at `a = b = ZERO` the premise holds for every `c` and the conclusion says `c = ZERO`.
   * Showing it would mean settling `NUM_GCD ZERO ZERO`, and that is a `select` over a set with no
   * greatest element, so nothing decides it. The guard is Bezout's own and travels with it.
   */
  it should "hold the finite product and Gauss's lemma, both at two axioms" in {
    Vector(Coding.ProductAtZero, Coding.ProductAtSuccessor, Coding.Gauss).foreach { name =>
      val theorem = force(coding.fact(name))
      withClue(s"$name: ") {
        theorem.hypotheses shouldBe empty
        Derivation.axiomsOf(theorem) should have size 2
      }
    }
  }

  /**
   * Gauss specialises to the instance the coprimality argument will ask for.
   *
   * By the body and not by position, for the reason the Chinese remainder theorem's own test gives:
   * three of the statement's binders have the same type, so a positional specialisation would come
   * back true and about the wrong pair.
   */
  it should "specialise Gauss to the shape the moduli will want" in {
    val gauss = force(coding.fact(Coding.Gauss))
    val wanted = force(
      Parser.proposition(
        coding.theory,
        coding.notation,
        "(~((d:num) = ZERO) \\/ ~((k:num) = ZERO)) ==> NUM_GCD d k = SUC ZERO ==> " +
          "NUM_DIVIDES d (NUM_MUL k (e:num)) ==> NUM_DIVIDES d e"
      )
    )
    force(coding.logic.rules.specTo(gauss, wanted)).conclusion shouldBe wanted
  }

  /**
   * The moduli of the beta function are pairwise coprime, at two axioms.
   *
   * **The hypothesis `(j - i) | b` is what makes it true and here is the witness.** Take `b = 3`,
   * `i = 0`, `j = 2`: the difference is two, which does not divide three, and the moduli are
   * `1 + 3 = 4` and `1 + 9 = 10`, whose greatest common divisor is two. So the lemma without that
   * premise is false and this is the number that shows it.
   *
   * That witness is **not** discharged here and cannot be: settling `NUM_GCD 4 10 = 2` means
   * computing a greatest common divisor, and `docs/adr/0010` keeps computation out of the kernel,
   * so `NUM_GCD` denotes and is not calculated. Writing the witness in the docstring is what is
   * available: a reader who doubts the premise has a number to check by hand, which is more than a
   * sentence saying the premise is needed.
   */
  it should "prove the moduli pairwise coprime, at the two axioms the naturals cost" in {
    val coprime = force(coding.fact(Coding.ModuliCoprime))
    coprime.hypotheses shouldBe empty
    Derivation.axiomsOf(coprime) should have size 2
  }

  /**
   * The hypothesis a reader would drop is the one that makes the lemma false.
   *
   * `NUM_LT 0 d` reads as bookkeeping beside `NUM_LE d k`, and at `k = 0` the lemma without it
   * claims `NUM_DIVIDES 0 (NUM_FACT 0)`, which is `0 | 1`. Asserted by deriving the instance that
   * would have to hold and showing the theory refutes it, rather than by saying so in a comment.
   */
  it should "be false without its positivity hypothesis, and the theory says so" in {
    val logic = coding.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val zero = force(LogicError.lift(coding.theory.constant(Natural.NumberZero, numbers)))

    // `0 | 1` unfolds to `?k. SUC 0 = NUM_MUL 0 k`, and `NUM_MUL 0 k` is `0`, so it would give
    // `SUC 0 = 0`, which `NUM_SUC_NOT_ZERO` denies.
    val atZero = force(coding.fact(Coding.FactorialAtZero))
    val elimination = force(modular.fact(Modular.DividesElim))
    val zeroTimes = force(chain.peano.fact(Peano.ZeroTimes))
    val notZero = force(chain.naturals.fact(Natural.SuccessorNotZero))

    val one = Term.destEq(atZero.conclusion).map(_._2).getOrElse(fail("an equation was expected"))
    val claim = force(LogicError.lift(Term.appAll(
      force(LogicError.lift(coding.theory.constant(Modular.DividesName,
        Type.fun(numbers, Type.fun(numbers, Type.Bool))))),
      List(zero, one)
    )))
    val assumed = force(LogicError.lift(Kernel.assume(claim)))

    val absurd = force(for {
      opened <- rules.specAll(elimination, List(zero, one)).flatMap(rules.mp(_, assumed))
      predicate <- logic.destExistsPredicate(opened.conclusion).toRight(
        NotOfForm("an existential", opened.conclusion))
      witness = Conv.freshVariable("k", numbers, Term.freeVariables(opened.conclusion))
      applied <- LogicError.lift(Term.app(predicate, witness))
      contraction <- Conv.betaRoot(applied)
      instance <- Term.destEq(contraction.conclusion).map(_._2).toRight(
        NotOfForm("an equation", contraction.conclusion))
      assumedInstance <- LogicError.lift(Kernel.assume(instance))
      collapsed <- rules.spec(witness, zeroTimes)
      isZero <- Conv.trans(assumedInstance, collapsed)
      never <- rules.spec(zero, notZero)
      contradiction <- rules.notElim(never, isZero)
      discharged <- rules.existsElim(opened, witness, contradiction)
    } yield discharged)

    absurd.conclusion shouldBe logic.falsity
    absurd.hypotheses should contain(claim)
  }

  /**
   * The Chinese remainder theorem over `n` moduli, and the premise a reader would drop.
   *
   * The accounting first, as an equality against what it inherits: over `n` moduli it costs exactly
   * what it costs over two, because every axiom it reaches arrives whole from `NUM_CRT_PAIR` and
   * the induction adds none.
   *
   * **Then the assertion with teeth, and it is not a count.** The statement carries a pairwise
   * coprimality premise that reads as bookkeeping beside the positivity one, and a theorem whose
   * premises can never all hold is true and says nothing. What is derived here is the instance that
   * settles both questions at once: the family `m i = 2` at length two satisfies positivity, so the
   * conclusion is reached from the coprimality premise alone, and the conclusion is **false** for
   * that family, because a number congruent to `0` and to `1` modulo two gives `2 | 1`. So what
   * comes out is `|- ~(!i j. i < 2 /\ j < 2 /\ ~(i = j) ==> NUM_GCD 2 2 = SUC ZERO)`, proved
   * **through the theorem itself**: drop that premise and `NUM_CRT` proves a falsehood.
   *
   * That is stronger than the witness `NUM_GCD_SHIFTED_MULTIPLES`'s test leaves in a docstring, and
   * the difference is why this one can be run. That one would have had to settle `NUM_GCD 4 10 = 2`,
   * which means computing a greatest common divisor and `docs/adr/0010` keeps computation out of
   * the kernel. This one never mentions the value of a greatest common divisor: it refutes a
   * **congruence**, which is divisibility, which is derived.
   */
  it should "prove the Chinese remainder theorem over a family, on a premise that cannot be dropped" in {
    val logic = coding.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    def constant(name: String, ty: Type): Term =
      force(LogicError.lift(coding.theory.constant(name, ty)))

    val binary = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))
    val zero = constant(Natural.NumberZero, numbers)
    val successor = constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
    val plus = constant(Peano.Addition, arithmetic)
    val times = constant(Peano.Multiplication, arithmetic)
    val divides = constant(Modular.DividesName, binary)
    val congruence = constant(Modular.CongruenceName, Type.fun(numbers, binary))

    val one = force(LogicError.lift(Term.app(successor, zero)))
    val two = force(LogicError.lift(Term.app(successor, one)))

    val family = force(coding.fact(Coding.RemaindersFamily))
    Derivation.axiomsOf(family) shouldBe Derivation.axiomsOf(force(coding.fact(Coding.Remainders)))
    Derivation.axiomsOf(family) should have size 2
    family.hypotheses shouldBe empty

    /** Open `?x. p x` with a fresh name and hand the instance to the body. */
    def open(existential: Kernel.Thm, name: String)(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val predicate = logic
        .destExistsPredicate(existential.conclusion)
        .getOrElse(fail(s"an existential was expected: ${existential.conclusion}"))
      val variable =
        Conv.freshVariable(name, numbers, Term.freeVariables(existential.conclusion))
      val applied = force(LogicError.lift(Term.app(predicate, variable)))
      val contraction = force(Conv.betaRoot(applied))
      val instance = Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .getOrElse(fail("an equation was expected"))
      val assumed = force(LogicError.lift(Kernel.assume(instance)))
      force(rules.existsElim(existential, variable, reach(variable, assumed)))
    }

    def reduced(theorem: Kernel.Thm): Kernel.Thm = {
      val contraction = force(Conv.betaNormalise(theorem.conclusion))
      force(LogicError.lift(Kernel.eqMp(contraction, theorem)))
    }

    // Nothing is congruent to both zero and one modulo two: the two multiples cancel and what is
    // left is `2 | 1`, which makes two one and one zero.
    val semiring = force(Semiring.construct(chain.peano))
    val claim = force(LogicError.lift(Term.appAll(congruence, List(two, zero, one))))
    val assumedCongruent = force(LogicError.lift(Kernel.assume(claim)))
    val opened = force(
      rules
        .specAll(force(modular.fact(Modular.CongElim)), List(two, zero, one))
        .flatMap(rules.mp(_, assumedCongruent))
    )

    val absurd = open(opened, "p") { (p, outer) =>
      open(outer, "q") { (q, equation) =>
        val product = force(LogicError.lift(Term.appAll(times, List(two, p))))
        val other = force(LogicError.lift(Term.appAll(times, List(two, q))))
        val shifted = force(LogicError.lift(Term.appAll(plus, List(other, one))))
        val sides = Term
          .destEq(equation.conclusion)
          .getOrElse(fail("an equation was expected"))

        val bridged = force(for {
          left <- semiring.prove(sides._1, product)
          right <- semiring.prove(sides._2, shifted)
          fromProduct <- Conv.sym(left)
          across <- Conv.trans(fromProduct, equation)
          result <- Conv.trans(across, right)
        } yield result)

        val reflexive = force(rules.spec(two, force(modular.fact(Modular.DividesRefl))))
        val dividesMul = force(modular.fact(Modular.DividesMul))
        val dividesProduct =
          force(rules.specAll(dividesMul, List(two, two, p)).flatMap(rules.mp(_, reflexive)))
        val dividesOther =
          force(rules.specAll(dividesMul, List(two, two, q)).flatMap(rules.mp(_, reflexive)))
        val context = force(LogicError.lift(Term.app(divides, two)))
        val dividesShifted = force(
          Conv
            .apTerm(context, bridged)
            .flatMap(congruent => LogicError.lift(Kernel.eqMp(congruent, dividesProduct)))
        )
        val dividesUnit = force(
          rules
            .specAll(force(modular.fact(Modular.DividesSummand)), List(two, other, one))
            .flatMap(rules.mp(_, dividesOther))
            .flatMap(rules.mp(_, dividesShifted))
        )
        val twoIsOne = force(
          rules
            .spec(two, force(modular.fact(Modular.DividesOne)))
            .flatMap(rules.mp(_, dividesUnit))
        )
        val oneIsZero = force(
          rules
            .specAll(force(chain.naturals.fact(Natural.SuccessorInjective)), List(one, zero))
            .flatMap(rules.mp(_, twoIsOne))
        )
        val never = force(
          rules.spec(zero, force(chain.naturals.fact(Natural.SuccessorNotZero)))
        )
        force(rules.notElim(never, oneIsZero))
      }
    }

    val refutation = force(rules.notIntro(claim, absurd))
    refutation.hypotheses shouldBe empty

    // The theorem at the family that breaks it: two moduli, both two, wanting residues zero and one.
    val index = Term.variable("i", numbers)
    val moduli = force(LogicError.lift(Term.abs(index, two)))
    val residues = force(LogicError.lift(Term.abs(index, index)))
    val instance = force(rules.specAll(family, List(moduli, residues, two)))
    val firstHalf = logic
      .destImp(instance.conclusion)
      .getOrElse(fail("an implication was expected"))
    val secondHalf = logic.destImp(firstHalf._2).getOrElse(fail("an implication was expected"))
    val (positives, pairwise) = (firstHalf._1, secondHalf._1)

    // Every modulus is positive, which is the premise that does hold.
    val positivity = {
      val stripped = force(Logic.stripForall(positives))
      val bound = stripped._1.headOption.getOrElse(fail("a claim about every index was expected"))
      val body = logic.destImp(stripped._2).getOrElse(fail("an implication was expected"))
      val contraction = force(Conv.betaNormalise(body._2))
      val positive = force(rules.spec(one, force(chain.peano.fact(Peano.SuccessorPositive))))
      val carried = force(
        Conv.sym(contraction).flatMap(back => LogicError.lift(Kernel.eqMp(back, positive)))
      )
      force(rules.disch(body._1, carried).flatMap(rules.gen(bound, _)))
    }

    val assumedPairwise = force(LogicError.lift(Kernel.assume(pairwise)))
    val solved = force(
      rules.mp(instance, positivity).flatMap(rules.mp(_, assumedPairwise))
    )

    val belowTwo = force(rules.spec(one, force(chain.peano.fact(Peano.SuccessorPositive))))
    val oneBelowTwo = force(rules.spec(one, force(chain.peano.fact(Peano.BelowSuccessor))))

    val broken = open(solved, "x") { (_, solves) =>
      val atZero = reduced(force(rules.spec(zero, solves).flatMap(rules.mp(_, belowTwo))))
      val atOne = reduced(force(rules.spec(one, solves).flatMap(rules.mp(_, oneBelowTwo))))
      val witness = atZero.conclusion match {
        case App(App(App(_, _), subject), _) => subject
        case other => fail(s"a congruence was expected: $other")
      }
      val symmetric = force(
        rules
          .specAll(force(modular.fact(Modular.CongSym)), List(two, witness, zero))
          .flatMap(rules.mp(_, atZero))
      )
      val joined = force(
        rules
          .specAll(force(modular.fact(Modular.CongTrans)), List(two, zero, witness, one))
          .flatMap(rules.mp(_, symmetric))
          .flatMap(rules.mp(_, atOne))
      )
      force(rules.notElim(refutation, joined))
    }

    val impossible = force(rules.notIntro(pairwise, broken))
    impossible.hypotheses shouldBe empty
    impossible.conclusion shouldBe force(logic.mkNot(pairwise))
  }

  /**
   * The beta function, its definition, and the claim that it separates two indices.
   *
   * The accounting first, as an equality against what it inherits: the sequence lemma costs what
   * the Chinese remainder theorem costs, because every axiom it reaches arrives through it.
   *
   * **Then the part that is not a count, and it answers a different question from the one the
   * Chinese remainder theorem's test answers.** That statement could have been vacuous, since its
   * premises might never all hold. This one cannot be: it quantifies over every sequence and every
   * length and asserts an existence. What it could be instead is **empty**, if `NUM_BETA` were a
   * function that does not depend on its index, because then one pair would code every sequence and
   * the lemma would be saying nothing about coding.
   *
   * So what is derived here is that it does depend on it: at the sequence `\i. i` and length two,
   * the lemma's own witnesses give `NUM_BETA a b 0 = 0` and `NUM_BETA a b 1 = 1`, and those differ.
   * The theorem that comes out is
   * `|- ?a b. ~(NUM_BETA a b ZERO = NUM_BETA a b (SUC ZERO))`, proved **through the lemma**, so a
   * beta function that ignored its index would make this test fail rather than pass quietly.
   *
   * The definition is asserted separately and against the text, because the docstring above claims
   * decoding is one remainder and that claim is only worth what the constant actually is.
   */
  it should "code a sequence in two numbers, with a beta function that reads its index" in {
    val logic = coding.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    def constant(name: String, ty: Type): Term =
      force(LogicError.lift(coding.theory.constant(name, ty)))

    val zero = constant(Natural.NumberZero, numbers)
    val successor = constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
    val one = force(LogicError.lift(Term.app(successor, zero)))
    val two = force(LogicError.lift(Term.app(successor, one)))

    val lemma = force(coding.fact(Coding.BetaSequence))
    Derivation.axiomsOf(lemma) shouldBe Derivation.axiomsOf(force(coding.fact(Coding.RemaindersFamily)))
    Derivation.axiomsOf(lemma) should have size 2
    lemma.hypotheses shouldBe empty

    // The definition is what the file says it is: one remainder, at a modulus built from the index.
    val definition = force(coding.definition(Coding.BetaName))
    val intended = force(
      Parser.term(
        coding.theory,
        coding.notation,
        "\\a:num b:num i:num. NUM_MOD a (SUC (NUM_MUL (SUC i) b))"
      )
    )
    Term.destEq(definition.conclusion).map(_._2) shouldBe Some(intended)
    Derivation.axiomsOf(definition) shouldBe empty

    def open(existential: Kernel.Thm, name: String)(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val predicate = logic
        .destExistsPredicate(existential.conclusion)
        .getOrElse(fail(s"an existential was expected: ${existential.conclusion}"))
      val variable =
        Conv.freshVariable(name, numbers, Term.freeVariables(existential.conclusion))
      val applied = force(LogicError.lift(Term.app(predicate, variable)))
      val contraction = force(Conv.betaRoot(applied))
      val instance = Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .getOrElse(fail("an equation was expected"))
      val assumed = force(LogicError.lift(Kernel.assume(instance)))
      force(rules.existsElim(existential, variable, reach(variable, assumed)))
    }

    def reduced(theorem: Kernel.Thm): Kernel.Thm = {
      val contraction = force(Conv.betaNormalise(theorem.conclusion))
      force(LogicError.lift(Kernel.eqMp(contraction, theorem)))
    }

    // The sequence that is its own index, over two entries.
    val index = Term.variable("i", numbers)
    val identity = force(LogicError.lift(Term.abs(index, index)))
    val instance = force(rules.specAll(lemma, List(identity, two)))

    val belowTwo = force(rules.spec(one, force(chain.peano.fact(Peano.SuccessorPositive))))
    val oneBelowTwo = force(rules.spec(one, force(chain.peano.fact(Peano.BelowSuccessor))))
    val notZero = force(rules.spec(zero, force(chain.naturals.fact(Natural.SuccessorNotZero))))
    val beta = constant(
      Coding.BetaName,
      Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, numbers)))
    )

    val separates = open(instance, "a") { (a, withB) =>
      open(withB, "b") { (b, codes) =>
        val atZero = reduced(force(rules.spec(zero, codes).flatMap(rules.mp(_, belowTwo))))
        val atOne = reduced(force(rules.spec(one, codes).flatMap(rules.mp(_, oneBelowTwo))))

        atZero.conclusion shouldBe force(
          LogicError.lift(Term.eq(force(LogicError.lift(Term.appAll(beta, List(a, b, zero)))), zero))
        )
        atOne.conclusion shouldBe force(
          LogicError.lift(Term.eq(force(LogicError.lift(Term.appAll(beta, List(a, b, one)))), one))
        )

        val same = force(
          LogicError.lift(
            Term.eq(
              force(LogicError.lift(Term.appAll(beta, List(a, b, zero)))),
              force(LogicError.lift(Term.appAll(beta, List(a, b, one))))
            )
          )
        )
        val assumed = force(LogicError.lift(Kernel.assume(same)))
        val zeroIsOne = force(
          Conv.sym(atZero).flatMap(Conv.trans(_, assumed)).flatMap(Conv.trans(_, atOne))
        )
        val oneIsZero = force(Conv.sym(zeroIsOne))
        val contradiction = force(rules.notElim(notZero, oneIsZero))
        val different = force(rules.notIntro(same, contradiction))

        // Back into the two existentials the lemma opened, in the order they were opened.
        val innerGoal = force(
          logic.mkExists(
            b.asInstanceOf[FVar],
            different.conclusion
          )
        )
        val innerPredicate = logic
          .destExistsPredicate(innerGoal)
          .getOrElse(fail("an existential was expected"))
        val withWitnessB = force(rules.existsIntro(innerPredicate, b, different))
        val outerGoal = force(logic.mkExists(a.asInstanceOf[FVar], withWitnessB.conclusion))
        val outerPredicate = logic
          .destExistsPredicate(outerGoal)
          .getOrElse(fail("an existential was expected"))
        force(rules.existsIntro(outerPredicate, a, withWitnessB))
      }
    }

    separates.hypotheses shouldBe empty
    Derivation.axiomsOf(separates) should have size 2
  }
  /**
   * The binomial coefficient against the three factorials, spent at a pair rather than read.
   *
   * The identity is published additively and holds at every pair with nothing assumed, so there
   * is no hypothesis to detach and the guard has to be a different one: that the textbook form
   * comes back out of it. `C 5 2 * (2! * 3!) = 5!` is that at `i = 2`, `j = 3`, and it is the
   * reading a consumer does — choose `j` and the subtraction never appears.
   *
   * `NUM_CHOOSE_ALL` is spent beside it at the same numeral, because the diagonal is the edge of
   * the induction that the recurrence cannot reach and a statement about it that held only at
   * zero would satisfy every other assertion here.
   */
  "The binomial coefficient" should "meet the three factorials at a pair, and on the diagonal" in {
    val rules = coding.logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    def number(text: String): Term =
      force(Parser.term(coding.theory, coding.notation, text, numbers))

    def proposition(text: String): Term =
      force(Parser.proposition(coding.theory, coding.notation, text))

    val identity = force(coding.fact(Coding.ChooseTimesFactorials))
    val atTwoAndThree = force(
      rules.specAll(identity, List(number("SUC (SUC (SUC ZERO))"), number("SUC (SUC ZERO)"))))

    atTwoAndThree.hypotheses shouldBe empty
    atTwoAndThree.conclusion shouldBe proposition(
      "NUM_CHOOSE (NUM_ADD (SUC (SUC ZERO)) (SUC (SUC (SUC ZERO)))) (SUC (SUC ZERO)) * " +
        "(NUM_FACT (SUC (SUC ZERO)) * NUM_FACT (SUC (SUC (SUC ZERO)))) = " +
        "NUM_FACT (NUM_ADD (SUC (SUC ZERO)) (SUC (SUC (SUC ZERO))))")

    val diagonal = force(
      modular.peano
        .fact(Peano.ChooseDiagonal)
        .flatMap(rules.spec(number("SUC (SUC (SUC ZERO))"), _)))

    diagonal.hypotheses shouldBe empty
    diagonal.conclusion shouldBe proposition(
      "NUM_CHOOSE (SUC (SUC (SUC ZERO))) (SUC (SUC (SUC ZERO))) = SUC ZERO")
  }

  /**
   * It costs the naturals' two axioms and no more, which is the split this file asserts of every
   * other fact in the development.
   *
   * The identity is two inductions over Pascal's recurrence and the factorial's, and every
   * rearrangement in it is `Semiring`, which decides the commutative semiring on `num` without
   * embedding anything. So nothing here reaches the reals, and a derivation that had gone through
   * `Modular.identity` instead would be charging the sixteen for arithmetic that is entirely
   * about `num` — which is the trade `Semiring`'s own docstring exists to refuse. The two are
   * asserted as an **equality** with the recursion's own, which is what the tests above this one
   * do and is stronger than a ceiling: a derivation that quietly started spending a seventeenth
   * would be as much a defect as one that stopped spending the two.
   */
  it should "cost the naturals' two axioms and no more" in {
    val identity = force(coding.fact(Coding.ChooseTimesFactorials))

    Derivation.axiomsOf(identity) shouldBe Derivation.axiomsOf(force(chain.naturals.recursion))
    Derivation.axiomsOf(identity) should have size 2
  }
}
