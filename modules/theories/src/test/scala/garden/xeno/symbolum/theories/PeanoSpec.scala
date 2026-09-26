package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Arithmetic on the naturals, and the two questions that decide whether it is worth having.
 *
 * The first is whether it costs anything: `num` was a type nothing was assumed about, and an
 * operation on it that arrived by assumption would undo that quietly. Every fact here is checked
 * for hypotheses, the axioms of the theory are compared against the ones it was built over, and the
 * proof record is asked which axioms each derivation actually reaches.
 *
 * The second is whether it can be used. A fact that is stated correctly and that nothing can apply
 * is one nobody finds out about until later, so the uses below are the ones a consumer would
 * write: adding two numbers, chaining a bound, turning "at most zero" into "is zero", and
 * handing a natural number to the tactic that decides the reals.
 */
class PeanoSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val peano = Peano.standard
  private val ring = peano.ring
  private val logic = peano.logic
  private val rules = logic.rules
  private val numbers = TyApp(Natural.TypeName, Nil)

  private def fact(name: String): Kernel.Thm = force(peano.fact(name))

  private def rulesOf(names: String*): Vector[Rewrite.Rule] =
    force(Rewrite.Rule.all(logic, names.toVector.map(fact)))

  "The two operations" should "be defined by recursion and print as a reader checks them" in {
    // The recurrences are the definition read back, and both recurse on the second argument. That
    // choice is the file's own and it is what makes distributivity and the two associativities
    // close by rewriting; the price of it is `NUM_ZERO_ADD` and `NUM_SUC_ADD`, which are the same
    // equations from the other side and have to be proved.
    peano.show(fact(Peano.AddAtZero).conclusion) shouldBe "!n:num. n + 0 = n"
    peano.show(fact(Peano.AddAtSuccessor).conclusion) shouldBe
      "!n:num. !m:num. n + SUC m = SUC (n + m)"

    peano.show(fact(Peano.MulAtZero).conclusion) shouldBe "!n:num. n * 0 = 0"
    peano.show(fact(Peano.MulAtSuccessor).conclusion) shouldBe
      "!n:num. !m:num. n * SUC m = n * m + n"

    peano.theory.definitions.keySet should contain allOf (
      Peano.Addition, Peano.Multiplication, Peano.NonStrictOrder, Peano.StrictOrder, Peano.EmbeddingName
    )
  }

  /**
   * Pascal's triangle, stated and then COMPUTED.
   *
   * Three facts fix every entry and a reader agrees with them by reading; what a reader cannot see
   * from them is whether the constant under them is the one they describe. So the second half of
   * this test rewrites a concrete entry with nothing but those three and the recurrences of
   * `NUM_ADD`, and the answer has to be six. An off-by-one in the recursion's `PRE`, or a `COND`
   * opened at the wrong branch, leaves all three facts provable, prints plausibly, and gives a
   * different number here.
   *
   * The row is `SUC (SUC (SUC (SUC ZERO)))` and not `4`, for the reason every recurrence over `num`
   * is stated at a successor: a numeral would have to be spelled by `Successor` first and nothing
   * here needs that.
   */
  "The binomial coefficients" should "be Pascal's triangle, and compute to it" in {
    peano.show(fact(Peano.ChooseNone).conclusion) shouldBe "!n:num. NUM_CHOOSE n 0 = SUC 0"
    peano.show(fact(Peano.ChooseEmpty).conclusion) shouldBe "!n:num. NUM_CHOOSE 0 (SUC n) = 0"
    peano.show(fact(Peano.ChoosePascal).conclusion) shouldBe
      "!n:num. !m:num. NUM_CHOOSE (SUC n) (SUC m) = NUM_CHOOSE n m + NUM_CHOOSE n (SUC m)"

    val entry = force(
      peano.term(
        "NUM_CHOOSE (SUC (SUC (SUC (SUC ZERO)))) (SUC (SUC ZERO))",
        numbers))
    val computed = force(
      Rewrite.rewrite(
        rulesOf(
          Peano.ChooseNone,
          Peano.ChooseEmpty,
          Peano.ChoosePascal,
          Peano.AddAtZero,
          Peano.AddAtSuccessor),
        entry))

    // Four choose two is six, and the triangle above it is the only route to that number: the
    // rewriting walks the whole of rows zero to three to reach it.
    peano.show(computed.conclusion) shouldBe
      "NUM_CHOOSE (SUC (SUC (SUC (SUC 0)))) (SUC (SUC 0)) = SUC (SUC (SUC (SUC (SUC (SUC 0)))))"
  }

  /**
   * The triangle above its diagonal, spent at a pair rather than only printed.
   *
   * Two entries and the second is the control. `2 choose 3` is zero because the column has run
   * past the row, which is the fact under test discharged at a concrete bound; `2 choose 2` is
   * **one**, and it is here because the fact would say zero about it too if its hypothesis were
   * dropped. A lemma whose side condition does no work passes every assertion about the cases it
   * covers, and the only way to see that this one works is to compute an entry it does not cover.
   */
  "The triangle" should "be zero above its diagonal, and not on it" in {
    peano.show(fact(Peano.ChooseAbove).conclusion) shouldBe
      "!n:num. !m:num. n < m ==> NUM_CHOOSE n m = 0"

    val two = force(peano.term("SUC (SUC ZERO)", numbers))
    val three = force(peano.term("SUC (SUC (SUC ZERO))", numbers))

    val past = force(
      rules
        .specAll(fact(Peano.ChooseAbove), List(two, three))
        .flatMap(rules.mp(_, force(rules.spec(two, fact(Peano.BelowSuccessor))))))
    past.hypotheses shouldBe empty
    peano.show(past.conclusion) shouldBe
      "NUM_CHOOSE (SUC (SUC 0)) (SUC (SUC (SUC 0))) = 0"

    // And on the diagonal it is one, computed from the three recurrences and nothing else.
    val onIt = force(
      Rewrite.rewrite(
        rulesOf(
          Peano.ChooseNone,
          Peano.ChooseEmpty,
          Peano.ChoosePascal,
          Peano.AddAtZero,
          Peano.AddAtSuccessor),
        force(peano.term("NUM_CHOOSE (SUC (SUC ZERO)) (SUC (SUC ZERO))", numbers))))
    peano.show(onIt.conclusion) shouldBe
      "NUM_CHOOSE (SUC (SUC 0)) (SUC (SUC 0)) = SUC 0"
  }

  /**
   * An index below a successor is at most its predecessor, which is the bound every argument under
   * `Series.SUM_CONGRUENCE_BELOW` holds and the one none of them could turn into arithmetic.
   *
   * It is spent here rather than only printed, at the pair where the two bounds differ: `1 < 2`
   * gives `1 <= 1`, which is the boundary case and the one a proof by cases would have reached
   * through the equation branch.
   */
  "An index strictly below a successor" should "be at most the number under it" in {
    peano.show(fact(Peano.AtMostBelowSuccessor).conclusion) shouldBe
      "!n:num. !m:num. m < SUC n ==> m <= n"

    val one = force(peano.term("SUC ZERO", numbers))
    val reached = force(
      rules
        .specAll(fact(Peano.AtMostBelowSuccessor), List(one, one))
        .flatMap(rules.mp(_, force(rules.spec(one, fact(Peano.BelowSuccessor))))))
    reached.hypotheses shouldBe empty
    peano.show(reached.conclusion) shouldBe "SUC 0 <= SUC 0"
  }

  "Commutativity of the two operations" should "be derived, since neither recurrence is symmetric" in {
    // The pair the card called the real work. Each needs two inductions before it: addition needs
    // `ZERO + n = n` for its base and `SUC m + n = SUC (m + n)` for its step, and multiplication
    // needs the same two facts one level up.
    peano.show(fact(Peano.AddCommutative).conclusion) shouldBe
      "!n:num. !m:num. n + m = m + n"
    peano.show(fact(Peano.MulCommutative).conclusion) shouldBe
      "!n:num. !m:num. n * m = m * n"
    peano.show(fact(Peano.Distributive).conclusion) shouldBe
      "!n:num. !m:num. !k:num. n * (m + k) = n * m + n * k"
  }

  "The order" should "be the existential a reader would write, and the strict one a step along it" in {
    peano.show(force(peano.definition(Peano.NonStrictOrder)).conclusion) shouldBe
      "NUM_LE = (\\n:num. \\m:num. ?k:num. n + k = m)"
    peano.show(force(peano.definition(Peano.StrictOrder)).conclusion) shouldBe
      "NUM_LT = (\\n:num. \\m:num. SUC n <= m)"

    peano.show(fact(Peano.Reflexive).conclusion) shouldBe "!n:num. n <= n"
    peano.show(fact(Peano.AntiSymmetric).conclusion) shouldBe
      "!n:num. !m:num. n <= m /\\ m <= n ==> n = m"
    peano.show(fact(Peano.BelowSuccessor).conclusion) shouldBe "!n:num. n < SUC n"
  }

  it should "be total, and trichotomous, both derived where the reals assert the second" in {
    // `LT_TOTAL` is one of the sixteen over the reals and it is a theorem here. What makes it one
    // is that a natural number is reached by a finite number of successors and the reals are not
    // reached by anything: totality is an induction, and each half of it is then split on whether
    // the witness closing the gap is zero.
    peano.show(fact(Peano.Total).conclusion) shouldBe
      "!n:num. !m:num. n <= m \\/ m <= n"
    peano.show(fact(Peano.Trichotomy).conclusion) shouldBe
      "!n:num. !m:num. n < m \\/ n = m \\/ m < n"

    Vector(Peano.Total, Peano.Trichotomy).foreach { name =>
      withClue(s"$name: ") { fact(name).hypotheses shouldBe empty }
    }
  }

  "The embedding" should "take zero to zero and a successor to one more" in {
    peano.show(fact(Peano.EmbedsZero).conclusion) shouldBe "real_of_num 0 = 0"
    peano.show(fact(Peano.EmbedsSuccessor).conclusion) shouldBe
      "!n:num. real_of_num (SUC n) = real_of_num n + 1"
    peano.show(fact(Peano.EmbedsSum).conclusion) shouldBe
      "!n:num. !m:num. real_of_num (n + m) = real_of_num n + real_of_num m"
    peano.show(fact(Peano.EmbedsProduct).conclusion) shouldBe
      "!n:num. !m:num. real_of_num (n * m) = real_of_num n * real_of_num m"
  }

  "The Archimedean property" should "rest on completeness, which is what makes it true at all" in {
    // The assertion that matters here is not that the theorem is proved -- the table below proves
    // every statement in the file -- but that it is proved from the RIGHT thing. An ordered field
    // need not be Archimedean: in the rational functions ordered at infinity, `x` is above every
    // natural. So a derivation of this that did not read `COMPLETENESS` would be a derivation of
    // something false, and a passing suite would be saying nothing.
    //
    // This is also the first use of that axiom anywhere in the repository, which is why the
    // assertion is on the axiom and not on the shape of the proof.
    val theorem = fact(Peano.Archimedean)
    val completeness = force(ring.reals.axiom("COMPLETENESS")).conclusion

    Derivation.axiomsOf(theorem) should contain(completeness)
    peano.show(theorem.conclusion) shouldBe "!x:real. ?n:num. x < real_of_num n"
    theorem.hypotheses shouldBe empty

    info(s"${Derivation.size(theorem)} inferences over ${Derivation.axiomsOf(theorem).size} axioms")
  }

  it should "be a fact a caller can actually use, at a real it names" in {
    // The other half, and the reason it is here: a theorem whose statement is right and which no
    // instance can be got out of would pass every row above. This takes the instance.
    val instance = for {
      hundred <- peano.term("100", TyApp(Real.TypeName, Nil))
      specialised <- rules.spec(hundred, fact(Peano.Archimedean))
    } yield specialised

    peano.show(force(instance).conclusion) shouldBe "?n:num. 100 < real_of_num n"
  }

  "The floor and the ceiling" should "cost no axiom, being definitions and not assumptions" in {
    // The whole reason they are named by `select` rather than asserted: an axiom count that moved
    // would be the wrong trade for a convenience. `RealSpec` and `NaturalSpec` count what the
    // theories assert; this counts what naming two more constants did to it, which is nothing.
    peano.theory.axioms.size shouldBe 19
    peano.definitions.keySet should contain(Peano.Floor)
    peano.definitions.keySet should contain(Peano.Ceiling)
  }

  it should "carry the sign condition where a reader sees it, and not answer without it" in {
    // The condition is the point of these four statements and the thing a careless version would
    // have dropped. `num` has no negative numbers, so a `NUM_FLOOR` that answered at a negative
    // argument would be right above zero and silently wrong below it.
    //
    // What is asserted is that every one of the four is an implication whose antecedent is
    // `0 <= x`, rather than that they are proved, which the statement table already covers. A
    // version of this file that quietly stated them unconditionally would pass every other row
    // here and fail this one.
    Vector(
      Peano.FloorAtMost, Peano.FloorAbove, Peano.CeilingAtLeast, Peano.CeilingBelow
    ).foreach { name =>
      withClue(s"$name: ") {
        val statement = fact(name).conclusion
        val body = force(Logic.stripForall(statement))._2
        val antecedent = logic.destImp(body).map(_._1)
        antecedent.map(peano.show) shouldBe Some("0 <= x")
      }
    }
  }

  it should "compose into something neither of them says, which is what makes them usable" in {
    // A lemma that is true and out of which nothing follows would pass every row above. This puts
    // one fact from each constant together and derives a third: the floor is at most the ceiling,
    // because `x` is between them. It is also the row that would fail if either statement had been
    // weakened into something vacuous, since a vacuous premise cannot bracket anything.
    val linarith = force(Linarith.construct(force(Order.construct(ring))))
    val real = TyApp(Real.TypeName, Nil)
    val x = Term.variable("x", real)

    val derived = for {
      // `x:real` and not a bare `x`, because `<=` stands for two constants since `docs/adr/0018`
      // and `0` for two encodings since `docs/adr/0012`. **`real` and not `num`**, which is the
      // half worth writing down: this is `NUM_FLOOR`'s hypothesis and `NUM_FLOOR` takes a real, so
      // the annotation that reads naturally here is the wrong one, and the term it builds has to
      // be the same one `x` three lines above is a variable of. The printed form asserted in the
      // row above is unchanged, which is what says the term did not move.
      nonNegative <- peano.proposition("0 <= x:real")
      assumed <- LogicError.lift(Kernel.assume(nonNegative))
      belowX <- rules.spec(x, fact(Peano.FloorAtMost)).flatMap(rules.mp(_, assumed))
      aboveX <- rules.spec(x, fact(Peano.CeilingAtLeast)).flatMap(rules.mp(_, assumed))
      transitive <- peano
        .proposition("!a:real b:real c:real. a <= b ==> b <= c ==> a <= c")
        .flatMap(linarith.prove)
      floor <- peano.term("real_of_num (NUM_FLOOR x)", real)
      ceiling <- peano.term("real_of_num (NUM_CEIL x)", real)
      instance <- rules.specAll(transitive, List(floor, x, ceiling))
      ordered <- rules.mp(instance, belowX).flatMap(rules.mp(_, aboveX))
      closed <- rules.disch(nonNegative, ordered).flatMap(rules.gen(x, _))
    } yield closed

    peano.show(force(derived).conclusion) shouldBe
      "!x:real. 0 <= x ==> real_of_num (NUM_FLOOR x) <= real_of_num (NUM_CEIL x)"
    force(derived).hypotheses shouldBe empty
  }

  "Every statement the file writes down" should "be proved, and be that statement rather than one like it" in {
    // The table in `Peano.Statements` is what a person checks this development by, so the theorems
    // are compared against it as terms and not as printing: a bound variable has no name, and the
    // letters above are the printer's.
    Peano.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        val theorem = fact(name)
        theorem.conclusion shouldBe force(peano.proposition(text))
        theorem.hypotheses shouldBe empty
      }
    }

    peano.facts.keySet shouldBe Peano.Statements.map { case (name, _) => name }.toSet
  }

  it should "print back as something that reads as the same statement" in {
    Peano.Statements.foreach { case (name, _) =>
      val statement = fact(name).conclusion
      val printed = peano.show(statement)

      withClue(s"$name printed as $printed\n") {
        peano.proposition(printed) shouldBe Right(statement)
      }
    }
  }

  "A bound on an index" should "reach the procedures that decide the reals" in {
    // What the three order lemmas are for, as a derivation rather than a description. Before them a
    // development could carry an index into the reals and know nothing about it there: `LINARITH`
    // reads `real_of_num i` as an atom, and an atom with no fact attached is an unknown real.
    val linarith = force(Linarith.construct(force(Order.construct(peano.ring))))

    val goal = force(peano.proposition("!n:num. !m:num. n < m ==> real_of_num n < real_of_num m"))
    val carried = force(peano.fact(Peano.EmbedsStrictOrder))

    // The step the lemma buys: from `real_of_num i + 1 <= real_of_num k`, which is what it gives,
    // to `real_of_num i < real_of_num k`, which is linear in two atoms.
    val bridge = force(
      linarith.prove(
        force(peano.proposition("!a:real. !b:real. a + 1 <= b ==> a < b"))
      )
    )

    val i = Term.variable("i", TyApp(Natural.TypeName, Nil))
    val k = Term.variable("k", TyApp(Natural.TypeName, Nil))
    val embedding = force(
      LogicError.lift(
        peano.theory
          .constant(Peano.EmbeddingName, Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil)))
      )
    )

    val proved = force(
      for {
        assumption <- peano.proposition("i:num < k")
        assumed <- LogicError.lift(Kernel.assume(assumption))
        crossed <- rules.specAll(carried, List(i, k)).flatMap(rules.mp(_, assumed))
        left <- LogicError.lift(Term.app(embedding, i))
        right <- LogicError.lift(Term.app(embedding, k))
        strict <- rules.specAll(bridge, List(left, right)).flatMap(rules.mp(_, crossed))
        discharged <- rules.disch(assumption, strict)
        closed <- rules.genAll(discharged, List(i, k))
      } yield closed
    )

    proved.conclusion shouldBe goal
    proved.hypotheses shouldBe empty
  }

  it should "carry the integrality and not only the inequality" in {
    // `i < k` over the naturals is a gap of a whole unit, because there is nothing between a number
    // and its successor. Reporting only `real_of_num i < real_of_num k` would throw that away at
    // the one place it is worth anything, so the lemma says `+ 1 <=`.
    peano.show(fact(Peano.EmbedsStrictOrder).conclusion) shouldBe
      "!n:num. !m:num. n < m ==> real_of_num n + 1 <= real_of_num m"
  }

  "The development" should "add no axiom, which is the whole claim about what it costs" in {
    // The theory it extends is the chain's, and the arithmetic is definitions and derivations on
    // top of it. Compared against that theory rather than against a number written here, so the
    // assertion cannot drift from what the chain actually holds.
    peano.theory.axioms shouldBe ring.reals.theory.axioms
    peano.theory.axioms.size shouldBe Chain.standard.naturals.theory.axioms.size + Real.Axioms.size
  }

  it should "divide over the axioms where the mathematics says it should" in {
    // A fact about the naturals alone reaches the two the naturals cost, the choice operator and
    // infinity, both through the recursion theorem: `Recursion` spends the two Peano facts and
    // nothing above it needs them again. A fact about the embedding reaches the reals' as well,
    // because its step is closed by `Ring`, and that is the price of meeting the tactics.
    Derivation.axiomsOf(fact(Peano.AddCommutative)) should have size 2
    Derivation.axiomsOf(fact(Peano.MulCommutative)) should have size 2
    Derivation.axiomsOf(fact(Peano.AntiSymmetric)) should have size 2
    Derivation.axiomsOf(fact(Peano.Trichotomy)) should have size 2

    Derivation.axiomsOf(fact(Peano.EmbedsSum)).size should be > 2
    info(
      s"${Peano.EmbedsSum}: ${Derivation.size(fact(Peano.EmbedsSum))} inferences over " +
        s"${Derivation.axiomsOf(fact(Peano.EmbedsSum)).size} axioms"
    )
  }

  "Addition" should "compute, which is the smallest end-to-end use of the recurrences" in {
    // Two and one make three, in the successor spelling the recurrences hook. The numerals over
    // this type arrived on 2026-09-12 and reach these two lemmas only through `Successor`, which
    // is a separate piece of work and is one. The point here is that the two recurrences settle a
    // closed sum by rewriting alone, with nothing assumed.
    val left = force(peano.term("SUC (SUC 0) + SUC 0"))
    val right = force(peano.term("SUC (SUC (SUC 0))"))
    val proved = force(Rewrite.prove(rulesOf(Peano.AddAtZero, Peano.AddAtSuccessor), left, right))

    proved.hypotheses shouldBe empty
    peano.show(proved.conclusion) shouldBe
      "SUC (SUC 0) + SUC 0 = SUC (SUC (SUC 0))"
  }

  it should "refuse a sum that is not the one asked for, rather than rewrite until it agrees" in {
    // The other half of the same machinery, and the half that makes the first half mean something:
    // both sides reach a normal form, the two normal forms differ, and that is a refusal.
    val left = force(peano.term("SUC 0 + 0"))
    val right = force(peano.term("SUC (SUC 0)"))

    Rewrite.prove(rulesOf(Peano.AddAtZero, Peano.AddAtSuccessor), left, right) should matchPattern {
      case Left(NotEqualTo(_, _)) =>
    }
  }

  "The lemma that needs the sums sorted" should "refuse without the sorting, which is why it is there" in {
    // The file says `NUM_SUC_MUL` is the single step that plain rewriting cannot close, and this is
    // that claim checked instead of asserted. The same induction is run again here with the four
    // recurrences and the associativity of addition and **without** commutativity, and it refuses:
    // both sides reach a normal form, the two differ by one commutation, and the difference is
    // printed so that a reader can see which one it is.
    val statement = force(peano.proposition(Peano.Statements.toMap.apply(Peano.SuccessorTimes)))
    val plain = rulesOf(
      Peano.AddAtZero,
      Peano.AddAtSuccessor,
      Peano.MulAtZero,
      Peano.MulAtSuccessor,
      Peano.AddAssociative
    )

    def settle(available: Vector[Rewrite.Rule])(goal: Term): Either[LogicError, Kernel.Thm] =
      for {
        sides <- Term.destEq(goal).toRight(NotOfForm("an equation", goal))
        proved <- Rewrite.prove(available, sides._1, sides._2)
      } yield proved

    val driver = Induct(logic, ring, force(peano.naturals.fact(Natural.Induction)))
    val attempt = driver.proveBy(
      statement,
      settle(plain),
      opened =>
        val goal = opened.goal
        val hypothesis = opened.hypothesis
        Rewrite.Rule.of(logic, hypothesis).flatMap(rule => settle(plain :+ rule)(goal))
    )

    attempt should matchPattern { case Left(NotEqualTo(_, _)) => }
    attempt.left.toOption match {
      case Some(NotEqualTo(wanted, found)) =>
        info(s"without sorting the step stops at ${peano.show(found)} against ${peano.show(wanted)}")
      case other => fail(s"expected two normal forms that did not meet, got $other")
    }

    // And with the sorting it is a theorem, which is the fact the development records.
    fact(Peano.SuccessorTimes).conclusion shouldBe statement
  }

  "The order" should "chain, which is what transitivity is for" in {
    // `ZERO <= SUC ZERO <= SUC (SUC ZERO)`, by the two facts a consumer would reach for, and then
    // the conclusion is about the ends. Nothing is assumed and no witness is named here: each of
    // the two steps carries its own.
    val zero = force(peano.term("0:num"))
    val one = force(peano.term("SUC 0"))
    val two = force(peano.term("SUC (SUC 0)"))

    val proved = force(
      for {
        first <- rules.spec(zero, fact(Peano.AtMostSuccessor))
        second <- rules.spec(one, fact(Peano.AtMostSuccessor))
        both <- rules.conjIntro(first, second)
        chained <- rules.specAll(fact(Peano.Transitive), List(zero, one, two))
        result <- rules.mp(chained, both)
      } yield result
    )

    proved.hypotheses shouldBe empty
    peano.show(proved.conclusion) shouldBe "0 <= SUC (SUC 0)"
  }

  it should "turn a bound at zero into an equation, which is what a bounded quantifier needs" in {
    // Antisymmetry composed with `0 <= n`, and the shape a consumer meets it in: a number bounded
    // above by zero is zero. Derived here rather than recorded in the file, because it is one
    // application of two facts and a development that needs it can write it.
    val n = Term.variable("n", numbers)
    val zero = force(peano.term("0:num"))

    val proved = force(
      for {
        bound <- Parser.proposition(peano.theory, peano.notation, "n:num <= 0")
        assumed <- LogicError.lift(Kernel.assume(bound))
        least <- rules.spec(n, fact(Peano.ZeroIsLeast))
        both <- rules.conjIntro(assumed, least)
        instance <- rules.specAll(fact(Peano.AntiSymmetric), List(n, zero))
        equal <- rules.mp(instance, both)
        discharged <- rules.disch(bound, equal)
        result <- rules.gen(n, discharged)
      } yield result
    )

    proved.hypotheses shouldBe empty
    peano.show(proved.conclusion) shouldBe "!n:num. n <= 0 ==> n = 0"
  }

  "The embedding" should "put a natural number where the tactic that decides the reals can reach it" in {
    // The reason the rest of the file is worth having. The goal mentions a natural number and no
    // real tactic can read it; the two recurrences of `real_of_num` rewrite it into one that is a
    // ring identity, `Ring` closes that, and the equation carries the result back to the goal as
    // it was written. This is the loop `docs/proving.md` describes, with an index in it.
    val goal = force(peano.proposition("real_of_num (SUC (SUC 0)) = 2"))
    val embedding = rulesOf(Peano.EmbedsZero, Peano.EmbedsSuccessor)

    val proved = force(
      for {
        equation <- Rewrite.rewrite(embedding, goal)
        rewritten <- Term
          .destEq(equation.conclusion)
          .map { case (_, right) => right }
          .toRight(NotOfForm("an equation", goal))
        closed <- ring.prove(rewritten)
        backwards <- Conv.sym(equation)
        result <- LogicError.lift(Kernel.eqMp(backwards, closed))
      } yield result
    )

    proved.hypotheses shouldBe empty
    proved.conclusion shouldBe goal
    peano.show(proved.conclusion) shouldBe "real_of_num (SUC (SUC 0)) = 2"
  }

  it should "carry a sum over, so an index written as an expression meets the arithmetic" in {
    // `real_of_num (m + n + p)` reaches a sum of three reals, which is where `Ring` and `Linarith`
    // start. One rewrite with the homomorphism, applied everywhere it fits, and the shape of the
    // result is the point: no natural number is left in it.
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val p = Term.variable("p", numbers)

    val proved = force(
      for {
        subject <- Parser.term(
          peano.theory,
          peano.notation,
          "real_of_num (m + n + p)"
        )
        equation <- Rewrite.rewrite(rulesOf(Peano.EmbedsSum), subject)
        result <- Right(equation)
      } yield result
    )

    peano.show(proved.conclusion) shouldBe
      "real_of_num (m + n + p) = real_of_num m + real_of_num n + real_of_num p"
    proved.hypotheses shouldBe empty
    Term.freeVariables(force(Term.destEq(proved.conclusion).map { case (_, right) => right }.toRight(
      NotOfForm("an equation", proved.conclusion)
    ))) shouldBe Set(m, n, p)
  }

  it should "decide which of two numbers is the larger, which is what trichotomy is for" in {
    // The use a bounded quantifier makes of it: three cases, exhaustive, and each of them names
    // something a further argument can go on with. Here the pair is `ZERO` and `SUC ZERO`, and the
    // point is that the case analysis arrives as a theorem rather than as an appeal to the reader.
    val zero = force(peano.term("0:num"))
    val one = force(peano.term("SUC 0"))
    val decided = force(rules.specAll(fact(Peano.Trichotomy), List(zero, one)))

    decided.hypotheses shouldBe empty
    peano.show(decided.conclusion) shouldBe
      "0 < SUC 0 \\/ 0 = SUC 0 \\/ SUC 0 < 0"
  }

  "The least-number principle" should "produce a least witness a consumer can use" in {
    // The question this file asks of every fact: can anything apply it. The claim put to it is
    // "some number is a successor", which is true at every successor, and what comes back is a
    // least such number together with the assertion that nothing below it is one.
    //
    // Stated over a predicate, which is what makes it the first higher-order fact here: the
    // instantiation is at `\n. ?m. n = SUC m`, and first-order matching would not reach it.
    val successor = force(
      LogicError.lift(peano.theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers)))
    )
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)
    val isSuccessor = force(
      for {
        applied <- LogicError.lift(Term.app(successor, m))
        equation <- LogicError.lift(Term.eq(n, applied))
        body <- logic.mkExists(m, equation)
        abstracted <- LogicError.lift(Term.abs(n, body))
      } yield abstracted
    )

    val instance = force(rules.spec(isSuccessor, fact(Peano.LeastNumber)))
    val opened = force(
      Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
    )

    peano.show(opened.conclusion) shouldBe
      "(?n:num. ?m:num. n = SUC m) ==> (?n:num. (?m:num. n = SUC m) /\\ (!m:num. m < n ==> " +
        "~(?k:num. m = SUC k)))"
    opened.hypotheses shouldBe empty
  }

  "The greatest element of a bounded set" should "need the bound, which is the asymmetry" in {
    // The dual of the principle above and not symmetric with it: a non-empty set of naturals always
    // has a least element and has a greatest one only if it is bounded. The statement carries both
    // hypotheses and the second is the whole difference.
    val greatest = fact(Peano.GreatestBounded)

    peano.show(greatest.conclusion) shouldBe
      "!f:num -> bool. (?n:num. f n) /\\ (?n:num. !m:num. f m ==> m <= n) ==> (?n:num. f n /\\ " +
        "(!m:num. f m ==> m <= n))"
    greatest.hypotheses shouldBe empty

    // It is a corollary of the least-number principle rather than a second induction, which the
    // proof record shows: it rests on the same two axioms and is the larger derivation of the two.
    Derivation.axiomsOf(greatest) shouldBe Derivation.axiomsOf(fact(Peano.LeastNumber))
    Derivation.size(greatest) should be > Derivation.size(fact(Peano.LeastNumber))

    info(
      s"${Peano.LeastNumber}: ${Derivation.size(fact(Peano.LeastNumber))} inferences, " +
        s"${Peano.GreatestBounded}: ${Derivation.size(greatest)}"
    )
  }

  "The partial sum" should "be the recursion read back, at the naturals rather than the reals" in {
    // `Series.Sum` is the same operator one type up and neither can be the other: one adds with `+`
    // and this one with `NUM_ADD`, which are two constants. What this one is for is an INDEX --
    // `Power b n` takes a `num` exponent, so a development writing 2^{a_1 + ... + a_j} has no term
    // for the exponent without it, and must declare the partial sums and assume their recurrences.
    peano.show(fact(Peano.PartialSumAtZero).conclusion) shouldBe
      "!f:num -> num. NUM_SUM f 0 = 0"
    peano.show(fact(Peano.PartialSumAtSuccessor).conclusion) shouldBe
      "!f:num -> num. !n:num. NUM_SUM f (SUC n) = NUM_SUM f n + f n"

    peano.show(force(peano.definition(Peano.PartialSum)).conclusion) shouldBe
      "NUM_SUM = (\\f:num -> num. select (\\g:num -> num. g 0 = 0 /\\ (!n:num. g (SUC n) = g n + f " +
        "n)))"

    Vector(Peano.PartialSumAtZero, Peano.PartialSumAtSuccessor, Peano.PartialSumCongruenceBelow)
      .foreach(name => fact(name).hypotheses shouldBe empty)

    // It costs what every other definition in this file costs and not more, which is the question
    // a new constant has to answer: the recursion theorem, and nothing else.
    Derivation.axiomsOf(fact(Peano.PartialSumAtZero)) shouldBe
      Derivation.axiomsOf(fact(Peano.AddAtZero))
  }

  it should "carry its congruence with the bound, which is the form a consumer can use" in {
    // Stated bounded the FIRST time rather than after a consumer meets the wall. `Sum f n` never
    // evaluates `f` at or above `n`, so a hypothesis quantified over the whole type asks for
    // evidence about indices the sum cannot see, and two summands that agree exactly where the sum
    // looks -- the ordinary case -- cannot use it at all. `Series.CongruenceBelow` carries the
    // count of the lemmas in this library that still have the unconditional shape.
    peano.show(fact(Peano.PartialSumCongruenceBelow).conclusion) shouldBe
      "!f:num -> num. !g:num -> num. !n:num. (!m:num. m < n ==> f m = g m) ==> NUM_SUM f n " +
        "= NUM_SUM g n"

    // And the use that the unconditional form cannot make, which is why this is a test and not an
    // assertion about a string: over an EMPTY range two arbitrary summands have equal sums, and
    // the agreement that has to be produced for it is agreement below `ZERO`, of which there is
    // none to produce. The unconditional congruence would demand `!i. f i = g i` and no instance
    // of it is available for two distinct variables.
    val summand = Type.fun(numbers, numbers)
    val f = Term.variable("f", summand)
    val g = Term.variable("g", summand)
    val zero = force(LogicError.lift(peano.theory.constant(Natural.NumberZero, numbers)))

    val instance = force(rules.specAll(fact(Peano.PartialSumCongruenceBelow), List(f, g, zero)))
    val (antecedent, conclusion) =
      logic.destImp(instance.conclusion).getOrElse(fail("the congruence is an implication"))
    val (variables, body) = force(Logic.stripForall(antecedent))
    val (below, agreement) =
      logic.destImp(body).getOrElse(fail("a bounded agreement is an implication"))

    // The index is the statement's own, read off it rather than rebuilt: a variable of the same
    // name and type built here is a DIFFERENT variable to nothing, and `notElim` does not refuse
    // the mismatch -- `proveHyp` is total, so a pair that does not meet leaves both hypotheses
    // standing and the theorem is sound and useless. What says it happened is a hypothesis that
    // survives, which is what caught it here.
    val index = variables.lift(0).getOrElse(fail("the agreement binds one index"))
    val assumed = force(LogicError.lift(Kernel.assume(below)))
    val impossible = force(rules.spec(index, fact(Peano.NotBelowZero)))
    val absurd = force(rules.notElim(impossible, assumed))
    val anything = force(rules.falsityElim(agreement, absurd))
    val vacuous = force(rules.disch(below, anything).flatMap(rules.genAll(_, variables.toList)))

    val equal = force(rules.mp(instance, vacuous).flatMap(rules.genAll(_, List(f, g))))
    peano.show(equal.conclusion) shouldBe
      "!f:num -> num. !g:num -> num. NUM_SUM f 0 = NUM_SUM g 0"
    equal.hypotheses shouldBe empty
  }

  "The whole development" should "cost what it costs, measured rather than asserted" in {
    // Built again over the chain that is already standing, so what is measured is this file and
    // not the recursion theorem it rests on, which `Natural` computes once per development and
    // caches. A loose bound for the reason `ChainSpec` gives for its own: if this became slow
    // enough to matter it would be a different finding wanting a different fix.
    val chain = Chain.standard
    val started = System.nanoTime()
    force(Peano.construct(chain.naturals, chain.ring))
    val elapsed = (System.nanoTime() - started) / 1000000

    info(s"the arithmetic of the naturals builds in $elapsed ms, a reading and not an assertion")
  }

  "The size of each proof" should "be reported, since the inductions here are the expensive part" in {
    Vector(
      Peano.AddCommutative,
      Peano.MulCommutative,
      Peano.AntiSymmetric,
      Peano.Trichotomy,
      Peano.EmbedsProduct
    )
      .foreach { name =>
        val theorem = fact(name)
        info(s"$name: ${Derivation.size(theorem)} inferences over ${Derivation.axiomsOf(theorem).size} axioms")
        Derivation.size(theorem) should be > 100
      }
  }

  /**
   * Course-of-values induction, run end to end on a claim that needs it.
   *
   * **What this asserts is that the principle is usable, and not that it is stronger.** The claim it
   * is run on, `!n. NUM_LE ZERO n`, needs nothing of the hypothesis: it is chosen so that the only
   * thing the test can fail on is the machinery, which is instantiating at a predicate,
   * beta-reducing what comes back, discharging the premise and detaching. A statement alone does
   * not say that any of those work.
   *
   * An earlier draft of this comment claimed the claim was chosen so that ordinary induction would
   * not do, and the code underneath it used this one. That is the defect `Generated.scala` records
   * as the worst of its kind: prose describing the right thing beside a line that does not do it.
   * The consumer that will need the strength is one level up, where a fact about a term's code is
   * proved from the same fact about the codes **inside** it, and those are smaller numbers rather
   * than predecessors.
   */
  "Course-of-values induction" should "be instantiable and dischargeable" in {
    val principle = fact(Peano.StrongInduction)
    Derivation.axiomsOf(principle) should have size 2
    principle.hypotheses shouldBe empty

    val index = Term.variable("n", numbers)
    val atMost = force(LogicError.lift(
      peano.theory.constant(Peano.NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))))
    val zero = force(LogicError.lift(peano.theory.constant(Natural.NumberZero, numbers)))

    // `\n. NUM_LE ZERO n`, whose step needs nothing of the hypothesis at all.
    val body = force(LogicError.lift(Term.appAll(atMost, List(zero, index))))
    val predicate = force(LogicError.lift(Term.abs(index, body)))

    val instance = force(
      rules.spec(predicate, principle).flatMap(theorem =>
        Conv
          .betaNormalise(theorem.conclusion)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))
      )
    )
    val (premise, conclusion) = logic.destImp(instance.conclusion).getOrElse(fail("an implication"))

    // The premise: at every `n`, assuming it below `n`, prove it at `n`. Here the assumption is
    // not needed, which is what makes this a test of the machinery rather than of the claim.
    val stripped = force(Logic.stripForall(premise))
    val variable = stripped._1.headOption.getOrElse(fail("a claim about every number"))
    val stepParts = logic.destImp(stripped._2).getOrElse(fail("an implication"))
    val least = force(rules.spec(variable, fact(Peano.ZeroIsLeast)))
    val discharged = force(rules.disch(stepParts._1, least).flatMap(rules.gen(variable, _)))
    discharged.conclusion shouldBe premise

    val everywhere = force(rules.mp(instance, discharged))
    everywhere.conclusion shouldBe conclusion
    everywhere.hypotheses shouldBe empty
    Derivation.axiomsOf(everywhere) should have size 2
  }
}
