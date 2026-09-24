package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The limit development says what it says, costs what it costs, and refuses what it should refuse.
 *
 * Three questions, and the third is the one that is easy to leave out. A development whose
 * predicate held of everything would pass every assertion of the first two kinds: each fact would
 * still be provable, each statement would still read back, and the axiom count would be unchanged.
 * So [[refuses]] below derives a **non**-convergence, which is the assertion that `converges`
 * discriminates, and it is the shape `LanguageSpec` uses for `NUM_TERM` and for the same reason.
 *
 * What it does not check is that the epsilon-N definition is the **right** definition of a limit.
 * Nothing here can: that is a translation from mathematics into this notation and what checks it is
 * a reader, which is what `docs/reading-register.md` is for and why `Limit.ConvergesBody` is
 * written as a sentence rather than assembled.
 */
class LimitSpec extends AnyFlatSpec with Matchers {

  private val chain: Chain = Chain.standard
  private val limit: Limit = chain.limit

  private def force[A](result: Either[LogicError, A]): A =
    result.fold(error => fail(error.message), identity)

  private def proposition(text: String): Term =
    force(Parser.proposition(limit.theory, limit.notation, text))

  "Every fact of the limit development" should "prove the statement it is published as" in {
    Limit.Statements.foreach { case (name, text) =>
      val proved = force(limit.fact(name))
      withClue(s"$name: ") { proved.conclusion shouldBe proposition(text) }
      proved.hypotheses shouldBe empty
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    limit.facts.keySet shouldBe Limit.Statements.map(_._1).toSet
  }

  "The development" should "declare exactly the two constants it is about" in {
    val before = chain.provability.theory.constants.keySet
    (limit.theory.constants.keySet -- before) shouldBe Set(Limit.Converges, Limit.Value)
  }

  it should "add no axiom at all, which is the whole of what a definition costs" in {
    limit.theory.axioms.length shouldBe chain.provability.theory.axioms.length
  }

  /**
   * The costs, pinned as equalities rather than as ceilings.
   *
   * A ceiling is what a reader assumes is being asserted and is not the same claim: it passes when
   * a derivation quietly stops spending something as much as when it starts. `CodingSpec` makes
   * this argument first and this is the same measurement one link up.
   *
   * The two numbers worth reading are the ends of the range. `CONVERGES_EVENTUALLY` costs the
   * naturals' two, choice and infinity, because it moves a proposition about a sequence around and
   * touches no arithmetic at all. `CONVERGES_UNIQUE` costs seventeen, and the two beyond the field
   * and the order are `MUL_INVERSE` and `ONE_NOT_ZERO`: they are what halving the tolerance spends,
   * which is the one step in that proof that leaves the linear fragment.
   */
  "What each fact rests on" should "be what it was measured to rest on" in {
    def axioms(name: String): Int = Derivation.axiomsOf(force(limit.fact(name))).size

    axioms(Limit.Eventually) shouldBe 2
    // The same two and for the same reason: it moves an index along the naturals' order and a
    // proposition about a distance, and decides no arithmetic on the reals at all.
    axioms(Limit.Shifted) shouldBe 2
    axioms(Limit.BelowEveryPositive) shouldBe 11
    axioms(Limit.Constant) shouldBe 13
    axioms(Limit.Unique) shouldBe 17
    axioms(Limit.ValueOfConverges) shouldBe 17

    // The monotone convergence theorem and the order fact under it. The second costs fewer than
    // the convergence facts above and the difference is the whole of what it is: no tolerance is
    // halved in it, so neither `MUL_INVERSE` nor `ONE_NOT_ZERO` appears.
    axioms(Limit.MonotoneBelow) shouldBe 11
    axioms(Limit.MonotoneConverges) shouldBe 15
  }

  /**
   * Completeness is spent once by the absolute convergence theorem, and through the comparison
   * test.
   *
   * The docstring's central claim is that the textbook route, which shows the partial sums are
   * Cauchy, is replaced by one appeal to completeness that was already here. A count cannot say
   * "once", but it can say **where**: the sixteenth axiom is in this derivation, and it is in
   * `SUM_COMPARISON` too, and the facts this theorem also spends — the sum, the negation and the
   * carrying across — are asserted three assertions below to reach no supremum at all. So the
   * only door it can have come through is that one.
   */
  it should "reach the sixteenth axiom, and only where the comparison test does" in {
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion

    Derivation.axiomsOf(force(limit.absolute)) should contain(completeness)
    Derivation.axiomsOf(force(limit.comparison)) should contain(completeness)

    // The other three it rests on do not, which is what leaves the comparison test as the door.
    Derivation.axiomsOf(force(limit.added)) should not contain completeness
    Derivation.axiomsOf(force(limit.negated)) should not contain completeness
    Derivation.axiomsOf(force(limit.eventually)) should not contain completeness
  }

  /**
   * The two bound facts cost the same as each other and less than the facts that halve.
   *
   * Written as a relation rather than as two numbers, because what is being asserted is the claim
   * the pair's docstring makes about itself: they are one argument run on the two sides of a bound,
   * so they reach `abs` through its two different halves and nothing else about them differs. A
   * number would pass that claim and a number beside it would pass its failure.
   *
   * The second assertion is the one with content. Every other convergence fact in this file that
   * compares two quantities halves a tolerance, and halving is what reaches `MUL_INVERSE` and
   * `ONE_NOT_ZERO`; these two do not halve, because a term inside the whole gap of the limit is
   * already strictly past the bound, and the absence of those two axioms is that argument measured
   * rather than repeated.
   */
  it should "cost the same on both sides of the bound, and not the halving" in {
    def axioms(name: String): Set[Term] = Derivation.axiomsOf(force(limit.fact(name)))

    axioms(Limit.BelowBound) shouldBe axioms(Limit.AboveBound)

    val inverse = force(chain.reals.axiom("MUL_INVERSE")).conclusion
    val nonTrivial = force(chain.reals.axiom("ONE_NOT_ZERO")).conclusion
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion

    axioms(Limit.BelowBound) should not contain inverse
    axioms(Limit.BelowBound) should not contain nonTrivial

    // And no supremum is taken here: what these do with a convergence is read it, not obtain it.
    axioms(Limit.BelowBound) should not contain completeness
  }

  it should "spend the choice axiom on the value and not on the epsilon principle" in {
    val choice = force(chain.classical.axiom(Classical.Choice)).conclusion

    Derivation.axiomsOf(force(limit.fact(Limit.ValueOfConverges))) should contain(choice)

    // And not here, which is the claim the file's own docstring makes about the route it takes:
    // the epsilon principle is a disjunction elimination over `LE_CASES` rather than a
    // contradiction, so nothing classical is reached.
    Derivation.axiomsOf(force(limit.fact(Limit.BelowEveryPositive))) should not contain choice
  }

  /**
   * The theorem spends `COMPLETENESS`, which is the claim its own docstring makes.
   *
   * Asserted by name rather than left to the count, because the count moving would not say which
   * axiom arrived and this is the one the theorem is about: an ordered field that is not complete
   * has bounded increasing sequences that converge to nothing, so a derivation of this that did
   * **not** reach the sixteenth axiom would be a derivation of something else.
   */
  "The monotone convergence theorem" should "be where the sixteenth axiom is spent" in {
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion
    val spent = Derivation.axiomsOf(force(limit.monotoneConverges))

    spent should contain(completeness)

    // And the order fact under it does not, which says the induction is about the order alone.
    Derivation.axiomsOf(force(limit.monotoneBelow)) should not contain completeness
  }

  /**
   * It applies to a sequence somebody can name, which is what says it is not vacuous.
   *
   * A theorem whose hypotheses nothing satisfies is provable and useless, and this one takes two.
   * The constant sequence satisfies both, so the theorem hands back a limit for it, and
   * `CONVERGES_UNIQUE` says that limit is the constant itself. The demonstration is worth more
   * than the statement: it is the first time in this repository that a limit is **obtained**
   * rather than assumed.
   */
  it should "apply to a sequence whose hypotheses can be discharged" in {
    val rules = limit.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val c = Term.variable("c", real)
    val n = Term.variable("n", TyApp(Natural.TypeName, Nil))

    val constant = force(
      limit.term("\\n:num. c:real", Type.fun(TyApp(Natural.TypeName, Nil), real)))
    val specialised = force(rules.spec(constant, force(limit.monotoneConverges)))
    val opened = force(
      Conv
        .betaNormalise(specialised.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, specialised))))

    // Both hypotheses, discharged: the constant sequence does not decrease, and it is its own
    // bound.
    val reflexive = force(
      rules
        .specAll(force(chain.order.leOfEq), List(c, c))
        .flatMap(rules.mp(_, Kernel.refl(c))))
    val everywhere = force(rules.gen(n, reflexive))

    val boundedStatement = proposition("?b:real. !n:num. c:real <= b")
    val boundedPredicate = force(
      limit.logic
        .destExistsPredicate(boundedStatement)
        .toRight(MissingDefinition("an existential")))
    val bounded = force(rules.existsIntro(boundedPredicate, c, everywhere))

    val obtained = force(rules.mp(opened, everywhere).flatMap(rules.mp(_, bounded)))
    obtained.conclusion shouldBe proposition("?l:real. converges (\\n:num. c:real) l")
    obtained.hypotheses shouldBe empty
  }

  /**
   * The comparison test on a series a reader can name, and the two bounds on where its limit is.
   *
   * Three facts are under test at once and the composition is the point. `SUM_COMPARISON` obtains a
   * limit for the geometric series at one half: its terms are non-negative because a power of a
   * positive base is positive, it dominates itself, and its partial sums are bounded, which is
   * `SUM_GEOMETRIC` cleared of its denominator and one linear step. Then `CONVERGES_LE` and
   * `CONVERGES_GE` put that limit between zero and two, which is the first time anything in this
   * repository says **where** a limit it obtained sits.
   *
   * The bound two is not an accident of the choice of a half: `SUM_GEOMETRIC` at `q` gives
   * `(q - 1) * S n = q^n - 1`, so at `q = 1/2` the partial sum is `2 - 2 * (1/2)^n` and the power
   * is positive, which is a linear consequence over the two atoms and inside `Linarith`'s fragment.
   * A symbolic `q` would want `S n <= inv (1 - q)`, and that was out of reach while `INV_POSITIVE`
   * was the only fact about `inv` in this chain. `Order.INV_ANTITONE` landed on 2026-09-18 and
   * **does** relate an inverse to an order, so the sentence that used to stand here is corrected
   * rather than kept: what the general series still wants is a bound on `1 - q` that this
   * instance's numerals make trivial and a symbolic ratio does not. The instance below is
   * unchanged, and is what it always was.
   *
   * **The lower bound asserted is zero rather than two, and that is honest rather than weak.** The
   * limit is two, and saying so wants `(1/2)^n` to reach zero, which is the Archimedean property
   * spent on a power and is not written. What is written is that every partial sum is non-negative,
   * so zero is a lower bound, and the pair of assertions below is a sandwich that a later
   * development narrows rather than a claim about the value.
   */
  /**
   * `|- ?l. converges (Sum (\i. Power (1/2) i)) l`, built once for the two tests that spend it.
   *
   * The geometric series at one half is the only convergence this file can obtain from nothing,
   * so both the comparison test's own assertion and the absolute one below it start here. It is a
   * `lazy val` rather than a line in each, because a second copy would be a second thing to keep
   * in agreement and the two tests ask different questions of the same theorem.
   */
  private lazy val geometricConverges: Kernel.Thm = {
    val rules = limit.logic.rules
    val linarith = force(Linarith.construct(chain.order))
    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)

    val half = force(limit.term("(1:real) / 2", real))
    val terms = force(limit.term("\\i:num. Power ((1:real) / 2) i", Type.fun(numbers, real)))
    val positivePower = force(
      rules
        .spec(half, force(chain.series.fact(Series.PowerPositive)))
        .flatMap(rules.mp(_, force(linarith.prove("0 < (1:real) / 2")))))
    val powerAt = force(limit.term("Power ((1:real) / 2) (n:num)", real))
    val sumAt = force(limit.term("Sum (\\i:num. Power ((1:real) / 2) i) (n:num)", real))

    val nonNegative = force(
      rules
        .specAll(
          force(chain.order.fact(Order.LeOfLt)),
          List(force(limit.term("0:real", real)), powerAt))
        .flatMap(rules.mp(_, force(rules.spec(n, positivePower))))
        .flatMap(rules.gen(n, _)))
    val dominates = force(
      rules
        .specAll(force(chain.order.fact(Order.LeOfEq)), List(powerAt, powerAt))
        .flatMap(rules.mp(_, Kernel.refl(powerAt)))
        .flatMap(rules.gen(n, _)))
    val geometric = force(
      rules.specAll(force(chain.series.fact(Series.Geometric)), List(half, n)))
    val everywhereUnderTwo = force(
      linarith
        .prove("!p:real. !s:real. ((1:real) / 2 - 1) * s = p - 1 ==> 0 < p ==> s <= 2")
        .flatMap(rules.specAll(_, List(powerAt, sumAt)))
        .flatMap(rules.mp(_, geometric))
        .flatMap(rules.mp(_, force(rules.spec(n, positivePower))))
        .flatMap(rules.gen(n, _)))

    val boundedStatement =
      proposition("?b:real. !n:num. Sum (\\i:num. Power ((1:real) / 2) i) n <= b")
    val boundedPredicate = force(
      limit.logic.destExistsPredicate(boundedStatement).toRight(MissingDefinition("an existential")))
    val bounded = force(
      rules.existsIntro(boundedPredicate, force(limit.term("2:real", real)), everywhereUnderTwo))

    val specialised = force(rules.specAll(force(limit.comparison), List(terms, terms)))
    val opened = force(
      Conv
        .betaNormalise(specialised.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, specialised))))
    force(
      rules
        .mp(opened, nonNegative)
        .flatMap(rules.mp(_, dominates))
        .flatMap(rules.mp(_, bounded)))
  }

  /**
   * An absolutely convergent series converges, spent on one the comparison test **refuses**.
   *
   * The demonstration is the point rather than the instance. `SUM_COMPARISON` asks for
   * non-negative terms and `-(1/2)^i` is negative at every index, so it cannot be reached that
   * way at all; what settles it is the absolute series, which is the geometric one, and the
   * theorem under test. What comes out carries nothing assumed.
   */
  /**
   * The two tail facts, spent end to end on the one series this file can obtain from nothing.
   *
   * What comes out is `?l. converges (\n. l - Sum f n) 0` with **nothing assumed**: the geometric
   * series has a tail that vanishes. That is the statement the Cauchy product's remaining estimate
   * needs, and it is reached here without a Cauchy criterion, which this repository has not got —
   * for a series of non-negative terms the tail from `N` on is at most `l - Sum f N`, and that is
   * `SUM_BELOW_LIMIT` with `CONVERGES_TAIL` beside it.
   *
   * The first assertion is about the **hypotheses** rather than the conclusion, which is where
   * the content is: `SUM_BELOW_LIMIT` at this series owes the convergence and owes nothing about
   * the terms, because their non-negativity is discharged rather than carried.
   */
  "The tail of a convergent series" should "vanish, and its partial sums stay under the limit" in {
    val rules = limit.logic.rules
    val linarith = force(Linarith.construct(chain.order))
    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val sequences = Type.fun(numbers, real)
    val n = Term.variable("n", numbers)
    val l = Term.variable("l", real)

    val half = force(limit.term("(1:real) / 2", real))
    val terms = force(limit.term("\\i:num. Power ((1:real) / 2) i", sequences))
    val powerAt = force(limit.term("Power ((1:real) / 2) (n:num)", real))
    val positivePower = force(
      rules
        .spec(half, force(chain.series.fact(Series.PowerPositive)))
        .flatMap(rules.mp(_, force(linarith.prove("0 < (1:real) / 2")))))
    val nonNegative = force(
      rules
        .specAll(
          force(chain.order.fact(Order.LeOfLt)),
          List(force(limit.term("0:real", real)), powerAt))
        .flatMap(rules.mp(_, force(rules.spec(n, positivePower))))
        .flatMap(rules.gen(n, _)))

    val converging = force(
      LogicError.lift(
        Kernel.assume(proposition("converges (Sum (\\i:num. Power ((1:real) / 2) i)) (l:real)"))))

    // Under the limit, owing the convergence and nothing about the terms.
    val under = force(
      rules
        .specAll(force(limit.belowLimit), List(terms, l))
        .flatMap(rules.mp(_, nonNegative))
        .flatMap(rules.mp(_, converging)))
    under.hypotheses shouldBe
      List(proposition("converges (Sum (\\i:num. Power ((1:real) / 2) i)) (l:real)"))
    limit.show(under.conclusion) shouldBe
      "!x:num. Sum (\\y:num. Power (1 / 2) y) x <= l"

    // And the tail, carried out of the existential the comparison test hands over.
    val vanishing = force(
      rules.specAll(force(limit.tail), List(terms, l)).flatMap(rules.mp(_, converging)))
    val claim = proposition(
      "?l:real. converges (\\n:num. l - Sum (\\i:num. Power ((1:real) / 2) i) n) 0")
    val predicate = force(
      limit.logic.destExistsPredicate(claim).toRight(MissingDefinition("an existential")))
    val settled = force(
      rules
        .existsIntro(predicate, l, vanishing)
        .flatMap(rules.existsElim(geometricConverges, l, _)))

    settled.hypotheses shouldBe empty
    settled.conclusion shouldBe claim
  }

  /**
   * The two halves of the sandwich, and the assertion is that they **are** one.
   *
   * Each on its own is an inequality a reader can check. What neither shows is that the upper
   * bound of the first is the lower bound of the second, at the same `a`, `b` and `n` and as the
   * same term — and that is the whole of why the Cauchy product's convergence follows without a
   * split, since it is what lets `A * B` be squeezed between `D_n` and `D_{n+n}`.
   *
   * So the assertion compares terms rather than proving anything: the right of the triangle's
   * bound against the left of the square's. A change that moved either statement's middle by an
   * associativity would leave both facts true and the sandwich gone, and nothing else here would
   * notice.
   */
  "The two halves of the sandwich" should "meet at the same term" in {
    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val sequences = Type.fun(numbers, real)
    val a = Term.variable("a", sequences)
    val b = Term.variable("b", sequences)
    val n = Term.variable("n", numbers)
    val rules = limit.logic.rules

    def bodyOf(theorem: Kernel.Thm): Term =
      force(
        rules
          .specAll(theorem, List(a, b, n))
          .map(instance => instance.conclusion))

    def afterTwo(term: Term): Term = term match {
      case App(App(_, _), inner) =>
        inner match {
          case App(App(_, _), body) => body
          case other                => other
        }
      case other => other
    }

    val triangle = afterTwo(bodyOf(force(limit.cauchyBelowSquare)))
    val square = afterTwo(bodyOf(force(limit.squareBelowCauchy)))

    def leftOf(term: Term): Term = term match {
      case App(App(_, left), _) => left
      case other                => other
    }
    def rightOf(term: Term): Term = term match {
      case App(App(_, _), right) => right
      case other                 => other
    }

    val upperOfTriangle = rightOf(triangle)
    val lowerOfSquare = leftOf(square)

    // The same term, not merely the same number: `Sum a n * Sum b n` on both sides.
    upperOfTriangle shouldBe lowerOfSquare
    limit.show(upperOfTriangle) shouldBe "Sum a n * Sum b n"

    // And the two ends are the Cauchy partial sum at `n` and at `n + n`, which is the bracket.
    val lowerOfTriangle = leftOf(triangle)
    val upperOfSquare = rightOf(square)
    limit.show(lowerOfTriangle) shouldBe
      "Sum (\\x:num. Sum (\\y:num. a y * b (NUM_SUB x y)) (SUC x)) n"
    limit.show(upperOfSquare) shouldBe
      "Sum (\\x:num. Sum (\\y:num. a y * b (NUM_SUB x y)) (SUC x)) (n + n)"
  }

  "An absolutely convergent series" should "converge, where the comparison test cannot reach it" in {
    val rules = limit.logic.rules
    val linarith = force(Linarith.construct(chain.order))
    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val sequences = Type.fun(numbers, real)
    val i = Term.variable("i", numbers)
    val l = Term.variable("l", real)

    val half = force(limit.term("(1:real) / 2", real))
    val negated = force(limit.term("\\i:num. -(Power ((1:real) / 2) i)", sequences))
    val positivePower = force(
      rules
        .spec(half, force(chain.series.fact(Series.PowerPositive)))
        .flatMap(rules.mp(_, force(linarith.prove("0 < (1:real) / 2")))))

    // The distance of a negative term from zero is the term back again, which is the one step
    // that makes the absolute series the geometric one.
    val powerAt = force(limit.term("Power ((1:real) / 2) (i:num)", real))
    val negatedAt = force(limit.term("-(Power ((1:real) / 2) (i:num))", real))
    val sizeIsPower = force(
      rules
        .spec(negatedAt, force(chain.magnitude.fact(Magnitude.OfNonPositive)))
        .flatMap(rules.mp(
          _,
          force(
            linarith
              .prove("!p:real. 0 < p ==> -p <= 0")
              .flatMap(rules.spec(powerAt, _))
              .flatMap(rules.mp(_, force(rules.spec(i, positivePower)))))))
        .flatMap(theorem =>
          linarith
            .prove("!a:real. !p:real. a = -(-p) ==> a = p")
            .flatMap(rules.specAll(_, List(force(limit.term("abs (-(Power ((1:real) / 2) (i:num)))", real)), powerAt)))
            .flatMap(rules.mp(_, theorem)))
        .flatMap(rules.gen(i, _)))

    // So the two series of partial sums agree at every index, and the convergence crosses.
    val sizes = force(limit.term("\\i:num. abs (-(Power ((1:real) / 2) i))", sequences))
    val terms = force(limit.term("\\i:num. Power ((1:real) / 2) i", sequences))
    val sameSums = force(
      rules
        .specAll(force(chain.series.fact(Series.Congruence)), List(sizes, terms))
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))
        .flatMap(rules.mp(_, sizeIsPower)))

    val assumedLimit = force(
      LogicError.lift(
        Kernel.assume(proposition("converges (Sum (\\i:num. Power ((1:real) / 2) i)) (l:real)"))))
    val zero = force(limit.term("ZERO", numbers))
    val absoluteConverges = force(
      rules
        .specAll(
          force(limit.eventually),
          List(
            force(limit.term("Sum (\\i:num. Power ((1:real) / 2) i)", sequences)),
            force(limit.term("Sum (\\i:num. abs (-(Power ((1:real) / 2) i)))", sequences)),
            l,
            zero))
        .flatMap(theorem =>
          rules
            .gen(
              i,
              force(
                rules
                  .disch(
                    proposition("NUM_LE ZERO (i:num)"),
                    force(Conv.sym(force(rules.spec(i, sameSums)))))))
            .flatMap(rules.mp(theorem, _)))
        .flatMap(rules.mp(_, assumedLimit)))

    val reached = force(
      rules
        .specAll(force(limit.absolute), List(negated, l))
        .flatMap(rules.mp(_, absoluteConverges)))

    val settled = force(rules.existsElim(geometricConverges, l, reached))

    settled.hypotheses shouldBe empty
    settled.conclusion shouldBe
      proposition("?m:real. converges (Sum (\\i:num. -(Power ((1:real) / 2) i))) m")
  }

  "The comparison test" should "settle a series a reader can name, between two bounds" in {
    val rules = limit.logic.rules
    val linarith = force(Linarith.construct(chain.order))
    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val n = Term.variable("n", numbers)
    val l = Term.variable("l", real)

    val half = force(limit.term("(1:real) / 2", real))
    val terms = force(limit.term("\\i:num. Power ((1:real) / 2) i", Type.fun(numbers, real)))
    val partial = force(limit.term("Sum (\\i:num. Power ((1:real) / 2) i)", Type.fun(numbers, real)))

    /** `|- !n. 0 < Power (1/2) n`, which is where the non-negativity comes from. */
    val positivePower = force(
      rules
        .spec(half, force(chain.series.fact(Series.PowerPositive)))
        .flatMap(rules.mp(_, force(linarith.prove("0 < (1:real) / 2")))))

    val powerAt = force(limit.term("Power ((1:real) / 2) (n:num)", real))
    val sumAt = force(limit.term("Sum (\\i:num. Power ((1:real) / 2) i) (n:num)", real))

    val nonNegative = force(
      rules
        .specAll(force(chain.order.fact(Order.LeOfLt)), List(force(limit.term("0:real", real)), powerAt))
        .flatMap(rules.mp(_, force(rules.spec(n, positivePower))))
        .flatMap(rules.gen(n, _)))

    val dominates = force(
      rules
        .specAll(force(chain.order.fact(Order.LeOfEq)), List(powerAt, powerAt))
        .flatMap(rules.mp(_, Kernel.refl(powerAt)))
        .flatMap(rules.gen(n, _)))

    // The partial sums are bounded by two, from the geometric sum and the positivity of the power.
    val geometric = force(
      rules.specAll(force(chain.series.fact(Series.Geometric)), List(half, n)))
    val underTwo = force(
      linarith
        .prove("!p:real. !s:real. ((1:real) / 2 - 1) * s = p - 1 ==> 0 < p ==> s <= 2")
        .flatMap(rules.specAll(_, List(powerAt, sumAt)))
        .flatMap(rules.mp(_, geometric))
        .flatMap(rules.mp(_, force(rules.spec(n, positivePower)))))
    val everywhereUnderTwo = force(rules.gen(n, underTwo))

    val boundedStatement =
      proposition("?b:real. !n:num. Sum (\\i:num. Power ((1:real) / 2) i) n <= b")
    val boundedPredicate = force(
      limit.logic.destExistsPredicate(boundedStatement).toRight(MissingDefinition("an existential")))
    val bounded = force(
      rules.existsIntro(boundedPredicate, force(limit.term("2:real", real)), everywhereUnderTwo))

    // The comparison test, at the series that dominates itself.
    val specialised = force(rules.specAll(force(limit.comparison), List(terms, terms)))
    val opened = force(
      Conv
        .betaNormalise(specialised.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, specialised))))
    val converging = force(
      rules
        .mp(opened, nonNegative)
        .flatMap(rules.mp(_, dominates))
        .flatMap(rules.mp(_, bounded)))

    converging.conclusion shouldBe
      proposition("?l:real. converges (Sum (\\i:num. Power ((1:real) / 2) i)) l")
    converging.hypotheses shouldBe empty

    // And the limit it hands back sits between zero and two, which is the pair under test.
    val assumed = force(
      LogicError.lift(
        Kernel.assume(
          proposition("converges (Sum (\\i:num. Power ((1:real) / 2) i)) (l:real)"))))
    val guard = proposition("NUM_LE 0 (n:num)")

    val eventuallyUnderTwo = force(
      rules.disch(guard, underTwo).flatMap(rules.gen(n, _)))
    val below = force(
      rules
        .specAll(
          force(limit.belowBound),
          List(partial, l, force(limit.term("2:real", real)), force(limit.term("0:num", numbers))))
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.mp(_, eventuallyUnderTwo)))

    val nonNegativeSums = force(
      rules
        .spec(terms, force(chain.series.fact(Series.NonNegative)))
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))
        .flatMap(rules.mp(_, nonNegative)))
    val eventuallyOverZero = force(
      rules
        .spec(n, nonNegativeSums)
        .flatMap(rules.disch(guard, _))
        .flatMap(rules.gen(n, _)))
    val above = force(
      rules
        .specAll(
          force(limit.aboveBound),
          List(partial, l, force(limit.term("0:real", real)), force(limit.term("0:num", numbers))))
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.mp(_, eventuallyOverZero)))

    below.conclusion shouldBe proposition("l:real <= 2")
    above.conclusion shouldBe proposition("0 <= l:real")
    below.hypotheses shouldBe
      List(proposition("converges (Sum (\\i:num. Power ((1:real) / 2) i)) (l:real)"))
  }

  "The definition" should "unfold to the epsilon-N statement a reader checks" in {
    val sequence =
      Term.variable("s", Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil)))
    val value = Term.variable("l", TyApp(Real.TypeName, Nil))
    val unfolded =
      force(Conv.unfold(force(limit.definition(Limit.Converges)), List(sequence, value)))
    val body = Term.destEq(unfolded.conclusion) match {
      case Some((_, right)) => right
      case None => fail(s"not an equation: ${limit.show(unfolded.conclusion)}")
    }

    // Against the parsed sentence rather than against a printed string: what is being checked is
    // the statement and not the printer's choice of bound names, and the two differ in nothing a
    // reader of this file should have to know about.
    body shouldBe proposition(
      "!e:real. 0 < e ==> ?N:num. !n:num. NUM_LE N n ==> abs ((s:num -> real) n - (l:real)) < e")
  }

  /**
   * `converges` refuses, which is what says it is a predicate rather than a true one.
   *
   * The constant sequence converges to its own value and to nothing else, and the second half is
   * the one worth deriving: it comes straight out of [[Limit.Unique]], so what this really asserts
   * is that uniqueness is not vacuous. A `converges` that held of every pair would make every fact
   * in this file provable and this one false.
   */
  "A constant sequence" should "converge to its value and refuse every other" in {
    val rules = limit.logic.rules
    val c = Term.variable("c", TyApp(Real.TypeName, Nil))
    val d = Term.variable("d", TyApp(Real.TypeName, Nil))

    val converges = force(rules.spec(c, force(limit.constantSequence)))
    limit.show(converges.conclusion) shouldBe "converges (\\x:num. c) c"

    // At the other value: assume it converges there too, and uniqueness closes it.
    val other = proposition("converges (\\n:num. c:real) (d:real)")
    val assumed = force(LogicError.lift(Kernel.assume(other)))
    val sequence = converges.conclusion match {
      case App(App(_, sequence), _) => sequence
      case other => fail(s"not a convergence: ${limit.show(other)}")
    }
    val equal = force(
      rules
        .specAll(force(limit.unique), List(sequence, c, d))
        .flatMap(rules.mp(_, converges))
        .flatMap(rules.mp(_, assumed))
    )
    limit.show(equal.conclusion) shouldBe "c = d"

    val refusal = force(
      limit.logic
        .mkNot(proposition("c:real = d:real"))
        .flatMap(negation => LogicError.lift(Kernel.assume(negation)))
        .flatMap(assumedDifferent => rules.notElim(assumedDifferent, equal))
        .flatMap(clash => rules.notIntro(other, clash))
    )
    limit.show(refusal.conclusion) shouldBe "~(converges (\\x:num. c) d)"
    refusal.hypotheses.map(limit.show).toList shouldBe List("~(c = d)")
  }

  "The value of a convergent sequence" should "be what it converges to" in {
    val rules = limit.logic.rules
    val c = Term.variable("c", TyApp(Real.TypeName, Nil))
    val converges = force(rules.spec(c, force(limit.constantSequence)))
    val sequence = converges.conclusion match {
      case App(App(_, sequence), _) => sequence
      case other => fail(s"not a convergence: ${limit.show(other)}")
    }

    val value = force(
      rules
        .specAll(force(limit.valueOfConverges), List(sequence, c))
        .flatMap(rules.mp(_, converges))
    )
    limit.show(value.conclusion) shouldBe "lim (\\x:num. c) = c"
  }

  /**
   * The additive algebra of limits, and what the two halves of it spend.
   *
   * Two assertions and they answer different questions. The first is that the sum fact costs
   * **exactly** what `CONVERGES_UNIQUE` costs, which is not a coincidence and is the reason to
   * write it as an equality between two measurements rather than as a number: both halve a
   * tolerance, both reach `abs`, and both put two indices together, so anything that moved one and
   * not the other would mean one of those three stopped happening. The second is that the negation
   * costs **strictly less**, and by name rather than by count: what it does not spend is
   * `MUL_INVERSE` and `ONE_NOT_ZERO`, which are what dividing by two spends, and it does not spend
   * them because it divides by nothing.
   *
   * Written as predictions before the suite was run, which is the discipline this file's figures
   * are under: a number copied out of a run is a transcription and not a check.
   */
  "The algebra of limits" should "cost the halving where it halves and not where it does not" in {
    def axioms(name: String): Int = Derivation.axiomsOf(force(limit.fact(name))).size

    axioms(Limit.Added) shouldBe axioms(Limit.Unique)

    val inverse = force(chain.reals.axiom("MUL_INVERSE")).conclusion
    val nonTrivial = force(chain.reals.axiom("ONE_NOT_ZERO")).conclusion

    Derivation.axiomsOf(force(limit.added)) should contain(inverse)
    Derivation.axiomsOf(force(limit.added)) should contain(nonTrivial)

    Derivation.axiomsOf(force(limit.negated)) should not contain inverse
    Derivation.axiomsOf(force(limit.negated)) should not contain nonTrivial
  }

  /**
   * Neither reaches `COMPLETENESS`, and that is the assertion this pair exists to survive.
   *
   * The algebra of limits is arithmetic of an ordered field: a sum of two sequences that each get
   * close gets close, and nothing about a supremum enters. A derivation of either of these that
   * went through `MONOTONE_CONVERGES` would reach the sixteenth axiom, would still prove the
   * statement, and would be a proof of the same sentence for a reason that is not the reason.
   * `LimitSpec` asserts the positive case for the monotone theorem three assertions above; this is
   * the same measurement pointed at where the axiom must **not** appear, which is the half that
   * catches a route changing under a refactoring nobody meant to be about the foundation.
   */
  /**
   * The product, whose cost is the same as the sum's and whose reason for it is not.
   *
   * `MUL_INVERSE` appears in both and is reached by two different things, which is why the first
   * assertion is written beside the second rather than alone: [[Limit.Added]] reaches it by halving
   * a tolerance, where a numeral denominator is a rational coefficient to `Linarith`, and this one
   * reaches it through a **symbolic** reciprocal, which no procedure here decides and which enters
   * as `MUL_INVERSE` at a denominator already known positive. A count cannot tell those apart, and
   * the pair of assertions is the closest a measurement gets: the same axioms, and no supremum in
   * either, so what differs between the two derivations is not the foundation.
   *
   * The equality is written as a relation and not as a number for the reason the sum's is: a number
   * would pass a derivation that quietly stopped spending something.
   */
  it should "cost what the sum costs, reaching the reciprocal for a different reason" in {
    def axioms(name: String): Set[Term] = Derivation.axiomsOf(force(limit.fact(name)))

    val inverse = force(chain.reals.axiom("MUL_INVERSE")).conclusion
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion

    axioms(Limit.Multiplied) should contain(inverse)
    axioms(Limit.Multiplied) should not contain completeness
    axioms(Limit.Multiplied).size shouldBe axioms(Limit.Added).size
  }

  /**
   * The scalar multiple, which this development said it did not have and now gets for nothing.
   *
   * [[Limit.Negated]]'s own docstring gave the reason the scalar multiple was left out: a proof of
   * `converges (\n. c * s n) (c * a)` from the definition divides the tolerance by `abs c` and so
   * has to split on `c = 0` before it can divide at all. That argument is about **that** route. The
   * product fact takes the constant sequence as one of its two arguments and the split never
   * arises, because nothing in it divides by `c`: the denominator it does divide by is
   * `(abs c + 1) + (abs a + 1)`, which is positive whatever `c` is.
   *
   * So the assertion that carries the claim is the last one, and it is about the **hypotheses**:
   * what comes out owes the convergence of `s` and owes nothing about `c`. A test that only checked
   * the conclusion would pass against a theorem carrying `~(c = 0)` beside it, which is exactly the
   * shape the docstring predicted and this shows is not what happens.
   */
  it should "give the scalar multiple, with no side condition on the scalar" in {
    val rules = limit.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val sequences = Type.fun(TyApp(Natural.TypeName, Nil), real)
    val s = Term.variable("s", sequences)
    val a = Term.variable("a", real)
    val c = Term.variable("c", real)

    val converging = proposition("converges (s:num -> real) (a:real)")
    val assumed = force(LogicError.lift(Kernel.assume(converging)))
    val constant = force(rules.spec(c, force(limit.constantSequence)))

    val scaled = force(
      rules
        .specAll(
          force(limit.multiplied),
          List(force(limit.term("\\n:num. (c:real)", sequences)), s, c, a))
        .flatMap(rules.mp(_, constant))
        .flatMap(rules.mp(_, assumed)))

    // The redex the specialisation builds, for the reason the composition test above records.
    val reduced = force(
      Conv
        .betaNormalise(scaled.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, scaled))))

    reduced.conclusion shouldBe
      proposition("converges (\\n:num. (c:real) * (s:num -> real) n) ((c:real) * (a:real))")
    reduced.hypotheses shouldBe List(converging)
  }

  it should "not reach the sixteenth axiom, because no supremum is involved" in {
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion

    Derivation.axiomsOf(force(limit.added)) should not contain completeness
    Derivation.axiomsOf(force(limit.negated)) should not contain completeness
  }

  /**
   * The two compose, and what comes out is a sequence that is identically zero.
   *
   * The assertion that matters here is not that the composite is provable, it is that the two
   * facts **fit together**: `CONVERGES_ADD` wants two convergent sequences and `CONVERGES_NEG`
   * produces one, so putting them in series is the first thing in this development that chains one
   * limit theorem into another. Before them there was nothing to chain, since every fact `Limit`
   * held took a sequence and said something about it alone.
   *
   * It is also the shape the Cauchy product will need and the reason this landed first: that
   * argument ends by adding and subtracting a quantity, which is these two facts and no others.
   */
  it should "compose, so that a sequence and its negation converge together" in {
    val rules = limit.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val s = Term.variable("s", Type.fun(TyApp(Natural.TypeName, Nil), real))
    val a = Term.variable("a", real)

    val assumed = force(LogicError.lift(Kernel.assume(proposition("converges (s:num -> real) (a:real)"))))

    // The negation of the sequence, from the fact under test.
    val negatedSequence = force(
      rules.specAll(force(limit.negated), List(s, a)).flatMap(rules.mp(_, assumed)))

    // And the two added, which is the second fact taking the first one's output as an input.
    val together = force(
      rules
        .specAll(
          force(limit.added),
          List(s, force(limit.term("\\n:num. -((s:num -> real) n)", Type.fun(TyApp(Natural.TypeName, Nil), real))), a, force(limit.term("-(a:real)", real)))
        )
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.mp(_, negatedSequence)))

    together.hypotheses shouldBe List(proposition("converges (s:num -> real) (a:real)"))

    // **Not beta-normal, and this assertion was written expecting it to be.** Specialising the
    // sum's `t` at the lambda leaves `(\\y. -(s y)) x` sitting under the binder rather than
    // `-(s x)`: substitution builds a redex and no rule reduces it on the way past. What came out
    // was a theorem about the sequence a reader means, printed in a form a reader does not write,
    // and the first version of this test compared it against the written form and went red. That
    // is `CLAUDE.md`'s sentence about `specToReduced` met from the other side -- the instance
    // carrying a redex is a **different term** -- and it is worth a red test rather than a silent
    // normalisation, because the reduction is a step the caller takes and not one it is given.
    val reduced = force(
      Conv
        .betaNormalise(together.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, together))))

    reduced.conclusion shouldBe
      proposition(
        "converges (\\n:num. (s:num -> real) n + -((s:num -> real) n)) ((a:real) + -(a:real))")
  }
  /**
   * The Cauchy product, detached at a series this file can name, with nothing left assumed.
   *
   * It is the guard the two assertions below cannot be. `SUM_CAUCHY_PRODUCT_NONNEG` is an
   * implication with four antecedents, and an implication nobody can discharge is a theorem and
   * says nothing: a version of it whose hypotheses were unmeetable would satisfy every reading of
   * the statement and every axiom count. So the geometric series at one half is put in on both
   * sides and the conclusion comes out with `hypotheses` empty.
   *
   * The value is `l * l` under the existential rather than `4`, and that is the honest scope of
   * what is being tested here rather than a shortcut: this file obtains that the geometric series
   * converges and never obtains what it converges to, so the product's limit is named the same
   * way. What the assertion is about is that the convolution converges at all.
   */
  "The Cauchy product" should "settle a product of two series a reader can name" in {
    val rules = limit.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val linarith = force(Linarith.construct(chain.order))
    val n = Term.variable("n", numbers)
    val l = Term.variable("l", real)

    val half = force(limit.term("(1:real) / 2", real))
    val terms = force(limit.term("\\i:num. Power ((1:real) / 2) i", Type.fun(numbers, real)))
    val powerAt = force(limit.term("Power ((1:real) / 2) (n:num)", real))

    val positivePower = force(
      rules
        .spec(half, force(chain.series.fact(Series.PowerPositive)))
        .flatMap(rules.mp(_, force(linarith.prove("0 < (1:real) / 2")))))
    val nonNegative = force(
      rules
        .specAll(
          force(chain.order.fact(Order.LeOfLt)),
          List(force(limit.term("0:real", real)), powerAt))
        .flatMap(rules.mp(_, force(rules.spec(n, positivePower))))
        .flatMap(rules.gen(n, _)))

    val assumed = force(
      LogicError.lift(
        Kernel.assume(proposition("converges (Sum (\\i:num. Power ((1:real) / 2) i)) (l:real)"))))

    // The same series on both sides, so the four antecedents are two facts each used twice.
    val product = force(
      rules
        .specAll(force(limit.cauchyNonNegative), List(terms, terms, l, l))
        .flatMap(rules.mp(_, nonNegative))
        .flatMap(rules.mp(_, nonNegative))
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.mp(_, assumed)))

    // Specialising `a` and `b` at a lambda leaves `(\z. Power (1/2) z) y` under two binders, so
    // what comes back is a theorem about the series a reader means printed in a form a reader
    // does not write. The reduction is the caller's step, which is the last test in this file
    // met from the other side and the reason this line is here rather than inside the derivation.
    val reduced = force(
      Conv
        .betaNormalise(product.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, product))))

    val claim = proposition(
      "?m:real. converges " +
        "(Sum (\\k:num. Sum (\\i:num. Power ((1:real) / 2) i * " +
        "Power ((1:real) / 2) (NUM_SUB k i)) (SUC k))) m")
    val predicate = limit.logic.destExistsPredicate(claim).get
    val wrapped = force(rules.existsIntro(predicate, force(limit.term("(l:real) * l", real)), reduced))

    val settled = force(rules.existsElim(geometricConverges, l, wrapped))

    settled.hypotheses shouldBe empty
    settled.conclusion shouldBe claim
  }

  /**
   * It rests on both halves of the sandwich, which is the claim its docstring makes about itself.
   *
   * A count of axioms cannot say this and neither can the statement: the theorem would read the
   * same if it had been proved by the textbook epsilon argument with a split at `n / 2`. What
   * separates the two routes is which published facts are inside the derivation, and
   * `SUM_SQUARE_BELOW_CAUCHY` is in this one exactly because the split is not: it is what gives
   * `A * B <= l` where the split would have given it by cutting a sum in two.
   *
   * `CONVERGES_MUL` is asserted beside them for the same reason one level out. The bracket's
   * upper end is the limit of `Sum a n * Sum b n`, and knowing that sequence converges to `A * B`
   * is the only place in the argument where anything about a **product** of limits is used.
   */
  it should "rest on both halves of the sandwich and on the limit of a product" in {
    val theorem = force(limit.cauchyNonNegative)

    val sandwich = Set(
      force(limit.cauchyBelowSquare).conclusion,
      force(limit.squareBelowCauchy).conclusion,
      force(limit.multiplied).conclusion)

    Derivation.restingOn(theorem, sandwich) shouldBe sandwich

    // And the comparison test, which is the one door completeness comes through: the sandwich
    // brackets the partial sums and brackets alone converge nothing.
    Derivation.axiomsOf(theorem) should contain(force(chain.reals.axiom("COMPLETENESS")).conclusion)
  }
  /**
   * The general Cauchy product, detached at a series a reader can name, with nothing assumed.
   *
   * The guard the structural assertion below cannot be, and the same one
   * `SUM_CAUCHY_PRODUCT_NONNEG` has: six binders and four antecedents, and an implication nobody
   * can discharge is a theorem that says nothing.
   *
   * **The instance is the geometric series, whose terms are not negative**, and that is worth
   * being plain about rather than hiding behind the word "general": what this test shows is that
   * the hypotheses are meetable and the conclusion comes out, not that the theorem reaches
   * further than [[CauchyNonNegative]]. Reaching further is what the statement says and what the
   * derivation's own facts say, and a series alternating in sign would need `abs (-x) = abs x`
   * carried under a `Sum` twice, which is the test three above this one doing its work again for
   * no new assertion.
   *
   * What the four antecedents cost here is one step: `abs` of a non-negative term is the term, so
   * `Sum (\i. abs (a i))` and `Sum a` agree at every index and [[Eventually]] crosses the
   * convergence. That step is the reason the absolute hypotheses are not free even at a series
   * with no signs in it.
   */
  it should "settle a product of two absolutely convergent series a reader can name" in {
    val rules = limit.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val linarith = force(Linarith.construct(chain.order))
    val i = Term.variable("i", numbers)
    val l = Term.variable("l", real)

    val half = force(limit.term("(1:real) / 2", real))
    val terms = force(limit.term("\\i:num. Power ((1:real) / 2) i", Type.fun(numbers, real)))
    val magnitudes =
      force(limit.term("\\i:num. abs (Power ((1:real) / 2) i)", Type.fun(numbers, real)))
    val powerAt = force(limit.term("Power ((1:real) / 2) (i:num)", real))

    val positivePower = force(
      rules
        .spec(half, force(chain.series.fact(Series.PowerPositive)))
        .flatMap(rules.mp(_, force(linarith.prove("0 < (1:real) / 2")))))

    // `abs` of a non-negative term is the term, so the two series agree at every index.
    val sizeIsTerm = force(
      rules
        .spec(powerAt, force(chain.magnitude.fact(Magnitude.OfNonNegative)))
        .flatMap(rules.mp(
          _,
          force(
            rules
              .specAll(
                force(chain.order.fact(Order.LeOfLt)),
                List(force(limit.term("0:real", real)), powerAt))
              .flatMap(rules.mp(_, force(rules.spec(i, positivePower)))))))
        .flatMap(rules.gen(i, _)))

    val sameSums = force(
      rules
        .specAll(force(chain.series.fact(Series.Congruence)), List(magnitudes, terms))
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))
        .flatMap(rules.mp(_, sizeIsTerm)))

    val assumedLimit = force(
      LogicError.lift(
        Kernel.assume(proposition("converges (Sum (\\i:num. Power ((1:real) / 2) i)) (l:real)"))))
    val zero = force(limit.term("ZERO", numbers))
    val absoluteConverges = force(
      rules
        .specAll(
          force(limit.eventually),
          List(
            force(limit.term("Sum (\\i:num. Power ((1:real) / 2) i)", Type.fun(numbers, real))),
            force(limit.term(
              "Sum (\\i:num. abs (Power ((1:real) / 2) i))", Type.fun(numbers, real))),
            l,
            zero))
        .flatMap(theorem =>
          rules
            .gen(
              i,
              force(
                rules.disch(
                  proposition("NUM_LE ZERO (i:num)"),
                  force(Conv.sym(force(rules.spec(i, sameSums)))))))
            .flatMap(rules.mp(theorem, _)))
        .flatMap(rules.mp(_, assumedLimit)))

    // The same series on both sides, so the four antecedents are two facts each used twice.
    val product = force(
      rules
        .specAll(force(limit.cauchy), List(terms, terms, l, l, l, l))
        .flatMap(rules.mp(_, absoluteConverges))
        .flatMap(rules.mp(_, absoluteConverges))
        .flatMap(rules.mp(_, assumedLimit))
        .flatMap(rules.mp(_, assumedLimit)))

    val reduced = force(
      Conv
        .betaNormalise(product.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, product))))

    val claim = proposition(
      "?m:real. converges " +
        "(Sum (\\k:num. Sum (\\i:num. Power ((1:real) / 2) i * " +
        "Power ((1:real) / 2) (NUM_SUB k i)) (SUC k))) m")
    val predicate = limit.logic.destExistsPredicate(claim).get
    val wrapped =
      force(rules.existsIntro(predicate, force(limit.term("(l:real) * l", real)), reduced))

    val settled = force(rules.existsElim(geometricConverges, l, wrapped))

    settled.hypotheses shouldBe empty
    settled.conclusion shouldBe claim
  }

  /**
   * It rests on the non-negative theorem, on the gap identity and on the squeeze.
   *
   * The three together are the route, and none of them is visible in the statement: the theorem
   * would read the same word for word if it had been proved by the textbook estimate, which
   * splits the square into three regions and bounds each with an epsilon. What separates the two
   * is which published facts are inside the derivation.
   *
   * `SUM_CAUCHY_GAP` is the one to read first. It carries **no hypothesis**, which is what lets
   * one identity serve the signed argument and the non-negative one, and it is the reason this
   * derivation spends [[CauchyNonNegative]] exactly once rather than repeating its sandwich.
   *
   * And `SUM_TAIL_ABS` is asserted here rather than only where it is defined, because it is the
   * step that does not appear in any textbook account of this theorem: the usual estimate bounds
   * a tail of `b` by a tolerance, and this one bounds it by a **difference of two partial sums
   * of the magnitudes**, which is what makes the whole argument an order statement.
   */
  it should "rest on the non-negative product, the gap identity and the squeeze" in {
    val theorem = force(limit.cauchy)

    val route = Set(
      force(limit.cauchyNonNegative).conclusion,
      force(chain.series.fact(Series.CauchyGap)).conclusion,
      force(limit.squeezed).conclusion,
      force(limit.stretchOfMagnitudes).conclusion,
      force(limit.sumOfMagnitudes).conclusion)

    Derivation.restingOn(theorem, route) shouldBe route

    // And it reaches completeness, through the non-negative theorem's comparison test and
    // nowhere else: the squeeze and the two triangle inequalities have no supremum in them.
    val completeness = force(chain.reals.axiom("COMPLETENESS")).conclusion

    Derivation.axiomsOf(theorem) should contain(completeness)
    Derivation.axiomsOf(force(limit.squeezed)) should not contain completeness
    Derivation.axiomsOf(force(limit.sumOfMagnitudes)) should not contain completeness
    Derivation.axiomsOf(force(limit.stretchOfMagnitudes)) should not contain completeness
  }
}
