package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Finite sums and finite products, and the facts a consumer of them asks for.
 *
 * The card that asked for the sum is explicit that Sigma with its recurrence is not enough: what an
 * argument quantifying over its own length needs is summation by parts, and without it the argument
 * stays prose or gets certified at two instances, which is sampling wearing the clothes of a proof.
 *
 * The bounds were the second half of that card, and they are tested differently from the identities
 * on purpose. An identity is checked by reading it: the printed statement is the whole of what a
 * person has to agree with. A bound is checked by **spending** it, so each of the three below is
 * also instantiated at a numeral and carried to a closed theorem with nothing assumed, because a
 * lemma whose hypotheses no caller can ever discharge would pass a printing test and be useless.
 */
class SeriesSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val classical = Classical.standard
  private val naturals = force(Natural.construct(classical))
  private val reals = force(Real.construct(classical.logic, naturals.theory))
  private val ring = force(
    for {
      arithmetic <- Arithmetic.construct(reals)
      built <- Ring.construct(arithmetic)
    } yield built
  )
  private val order = force(Order.construct(ring))
  private val peano = force(Peano.construct(naturals, ring))
  private val series = force(Series.construct(peano, order))
  private val logic = force(naturals.classical.logic.over(reals.theory))
  private val rules = logic.rules

  private def fact(name: String): Kernel.Thm = force(series.fact(name))

  /** A numeral of this theory, as the term a lemma is instantiated at. */
  // At `real` and said so: `Series` reads Peano's notation since 2026-09-12, so it reads a digit
  // string at either type and a bare one is refused. Every numeral this file hands to a lemma is a
  // base or a bound over the reals, which is a fact about these tests rather than about the text.
  private def numeral(value: Int): Term =
    force(series.term(value.toString, TyApp(Real.TypeName, Nil)))

  /** `|- m <= n` for two numerals, which is what the monotonicity lemmas want handed to them. */
  private def atMost(left: Int, right: Int): Kernel.Thm = {
    val strict = force(order.less(BigInt(left), BigInt(right)))
    val weaken = force(order.leOfLt)
    force(rules.mp(force(rules.specAll(weaken, List(numeral(left), numeral(right)))), strict))
  }

  /* ------------------------------------------------------------ the definitions */

  "The sum" should "be defined by recursion, not assumed" in {
    // Two equations that are consequences of a definition. A development had to carry them as
    // hypotheses before the recursion theorem existed, which cost every theorem two it could never
    // discharge; `RecurrenceSpec` is that arrangement and this is what replaces it.
    series.show(fact(Series.AtZero).conclusion) shouldBe "!x:num -> real. Sum x 0 = 0"
    // The quantifiers of the step read summand-then-index since the night of 2026-09-12, and used
    // to read index-then-summand. Nothing about the sum changed: `Series` built its own copy of the
    // recursion driver, that copy generalised the two variables in the other order, and the three
    // lemmas it produced were the only bare claims in the library whose binders disagreed with the
    // argument order of the function they are about. `SUM_ZERO` beside this one takes the summand,
    // so a caller specialising both recurrences of one function had to swap its arguments between
    // them. `Recursion.scala` is the single driver now and carries the count behind "the only".
    series.show(fact(Series.AtSuccessor).conclusion) shouldBe
      "!x:num -> real. !y:num. Sum x (SUC y) = Sum x y + x y"

    series.theory.definitions.keySet should contain(Series.SumName)
    // Nineteen since eta landed in `Classical.scala` on 2026-09-10, and none of the difference is
    // this file's: the sum is a definition and costs nothing.
    series.theory.axioms.size shouldBe 19
  }

  "The power" should "be defined by the same construction, so `2 ^ t` is a definition" in {
    // Point 4 of the card, and the shape a development waiting on the naturals was carrying as two
    // hypotheses on a declared symbol. Same construction as the sum: a base multiplied in at each
    // step rather than a summand added, and one function builds both.
    series.show(fact(Series.PowerAtZero).conclusion) shouldBe "!x:real. Power x 0 = 1"
    // Base then exponent, for the reason the sum's step above carries.
    series.show(fact(Series.PowerAtSuccessor).conclusion) shouldBe
      "!x:real. !y:num. Power x (SUC y) = x * Power x y"

    fact(Series.PowerAtZero).hypotheses shouldBe empty
    fact(Series.PowerAtSuccessor).hypotheses shouldBe empty
    series.theory.definitions.keySet should contain(Series.PowerName)
  }

  "The product" should "be that construction a third time, with one as its base" in {
    // The invariant is that adding a binding operator costs no new machinery: `Prod` differs from
    // `Sum` in the value at zero and in the step, and in nothing else, so it comes out of the same
    // driver rather than out of a second copy of it. The driver is `Recursion.define` and since
    // the night of 2026-09-12 it is also the one the arithmetic on `num` is built by, so the
    // invariant now reaches across the two developments instead of holding inside each.
    series.show(fact(Series.ProdAtZero).conclusion) shouldBe "!x:num -> real. Prod x 0 = 1"
    // Summand then index, for the reason the sum's step above carries.
    series.show(fact(Series.ProdAtSuccessor).conclusion) shouldBe
      "!x:num -> real. !y:num. Prod x (SUC y) = Prod x y * x y"

    fact(Series.ProdAtZero).hypotheses shouldBe empty
    fact(Series.ProdAtSuccessor).hypotheses shouldBe empty
    series.theory.definitions.keySet should contain(Series.ProdName)
    // Nineteen, and none of the difference is this file's: eta landed in `Classical.scala` hours
    // after this test was written, and a product is a definition and costs nothing. The number is
    // asserted here rather than described because that is what caught the collision.
    series.theory.axioms.size shouldBe 19
  }

  /* ------------------------------------------------------------- the identities */

  "Linearity" should "hold for every scalar, every pair of summands and every length" in {
    series.show(fact(Series.Linear).conclusion) shouldBe
      "!x:real. !y:num -> real. !z:num -> real. !u:num. " +
        "Sum (\\v:num. x * y v + z v) u = x * Sum y u + Sum z u"
  }

  it should "be instantiable at the summand a reader would write, and not only at the one spec leaves" in {
    // The shape `Rules.specToReduced` was built for, at the lemma it was reported against, rather
    // than at the miniature in `LogicSpec`. A summand written as a lambda leaves `(\j. h j + 1) i`
    // under `Sum`'s own binder, so the instance `specAll` produces is not the term anybody checks
    // against an informal claim; what a caller wants to say is the reduced one, and saying it is
    // what makes the call independent of the order the quantifiers happen to be written in.
    val wanted = force(
      series.proposition(
        "Sum (\\i:num. a * (h i + 1) + k i) n = a * Sum (\\i:num. h i + 1) n + Sum k n"
      )
    )

    force(rules.specToReduced(fact(Series.Linear), wanted)).conclusion shouldBe wanted

    // And the same target through `specTo` is refused, which is the half that says these are two
    // operations rather than one: what that one compares is the instance with the redex still in
    // it, and a caller writing the readable form would be told so instead of getting a theorem
    // about something else.
    rules.specTo(fact(Series.Linear), wanted) should matchPattern { case Left(NotOfForm(_, _)) => }
  }

  it should "be reachable through a reversal of its own quantifiers, which is the incident itself" in {
    // `LogicSpec` demonstrates this on a lemma built for the purpose, and a miniature can always be
    // accused of being built to pass. This is the same demonstration on `SUM_SUC` itself, which is
    // one of the three lemmas `f7994e3` actually reversed on 2026-09-12 and the one that stopped a
    // consumer's build.
    //
    // The twin is constructed rather than asserted: the lemma is specialised at its own binders and
    // generalised again in the other order, so what it states is exactly what this lemma states and
    // the only difference is the order. Nothing here depends on which order is today's.
    val stated = fact(Series.AtSuccessor)
    val (binders, _) = force(Logic.stripForall(stated.conclusion))
    val reversed = force(
      rules.genAll(force(rules.specAll(stated, binders.toList)), binders.reverse.toList)
    )

    series.show(reversed.conclusion) should not be series.show(stated.conclusion)

    val summand = force(series.term("h:num -> real"))
    val index = force(series.term("n:num"))
    val wanted = force(series.proposition("Sum (h:num -> real) (SUC (n:num)) = Sum h n + h n"))

    // Positional: one of the two refuses, and it refuses because the types differ. That is the
    // luck this whole method exists because of, and it is asserted here so that a reader does not
    // have to take the word for it.
    rules.specAll(stated, List(summand, index)).isRight shouldBe true
    rules.specAll(reversed, List(summand, index)).isLeft shouldBe true

    // By shape: the same answer from both, and it is the term that was asked for.
    force(rules.specTo(stated, wanted)).conclusion shouldBe wanted
    force(rules.specTo(reversed, wanted)).conclusion shouldBe wanted
  }

  "The unit base" should "raise to one at every exponent" in {
    // Asked for by a consumer and then UNasked: the route it took induces on the square rather than
    // on the value and needs neither this nor `POWER_MUL`. Kept for being cheap and general, which
    // is the label `POWER_MUL` carries, and the file says so rather than claiming a consumer that
    // withdrew. Checked absent before it was proved, by name, by constant and by shape;
    // `NUM_POW_ONE` is the same statement over `num` and is a different lemma.
    series.show(fact(Series.PowerOfOne).conclusion) shouldBe "!x:num. Power 1 x = 1"
    fact(Series.PowerOfOne).hypotheses shouldBe empty
  }

  "The telescoping sum" should "collapse to its ends" in {
    series.show(fact(Series.Telescoping).conclusion) shouldBe
      "!x:num -> real. !y:num. Sum (\\z:num. x (SUC z) - x z) y = x y - x 0"
  }

  "Summation by parts" should "hold at every length, which is the point of having it" in {
    // The one the card calls the real consumer. Its two halves were already certified separately as
    // closed forms and as sign lemmas; what was missing in the middle was this, at a length that is
    // a variable rather than at two instances.
    series.show(fact(Series.ByParts).conclusion) shouldBe
      "!x:num -> real. !y:num -> real. !z:num. " +
        "Sum (\\u:num. x u * (y (SUC u) - y u)) z = " +
        "x z * y z - x 0 * y 0 - Sum (\\u:num. y (SUC u) * (x (SUC u) - x u)) z"
  }

  "A sum of two summands" should "split, at the summand anybody would write" in {
    // Not a convenience over `SUM_LINEAR`: that one at `a = 1` gives the summand `1 * f i + g i`,
    // and a rewrite rule is matched syntactically, so the scalar version does not answer a goal
    // written without a scalar. The invariant is that this is a separate fact and not a corollary.
    series.show(fact(Series.Additive).conclusion) shouldBe
      "!x:num -> real. !y:num -> real. !z:num. Sum (\\u:num. x u + y u) z = Sum x z + Sum y z"
  }

  "A constant factor" should "come out of a sum from either side, and both are published" in {
    // Two lemmas and not one, and the reason is `SUM_OF_PRODUCTS` below: its inner collapse binds
    // the factor on the left and what is left over binds it on the right. A development holding
    // one of them would have to commute a product under a binder to use it, which is a congruence
    // over the whole summand rather than a rewrite. Neither is `SUM_LINEAR` specialised, for the
    // reason `SUM_ADD` is not either: `Linear` at `g := \i. 0` gives the summand `a * f i + 0`.
    series.show(fact(Series.Scaled).conclusion) shouldBe
      "!x:real. !y:num -> real. !z:num. Sum (\\u:num. x * y u) z = x * Sum y z"
    series.show(fact(Series.ScaledRight).conclusion) shouldBe
      "!x:real. !y:num -> real. !z:num. Sum (\\u:num. y u * x) z = Sum y z * x"
  }

  "Every product of a term with a term" should "add up to the product of the two sums" in {
    // The finite half of the Cauchy product: a product of two partial sums is a sum over a SQUARE
    // of indices. The two lengths are independent, which is what makes it usable where the two
    // series are cut at different points.
    series.show(fact(Series.Product).conclusion) shouldBe
      "!x:num -> real. !y:num -> real. !z:num. !u:num. " +
        "Sum (\\v:num. Sum (\\w:num. x v * y w) z) u = Sum x u * Sum y z"
  }

  /**
   * The other finite half: the triangle of index pairs, re-cut.
   *
   * Two assertions and the second is the one with content. The first is the statement a reader
   * agrees with; the second **spends** it at a bound small enough to check by hand, which is the
   * discipline this file's opening states for a bound and which applies here for a different
   * reason: an identity about indices can be off by one, stay provable, and print plausibly. At
   * `n = SUC (SUC ZERO)` the left side is the two antidiagonals and the right side is the two rows,
   * and a reader can see that they are the same three entries grouped differently.
   */
  "The triangle of index pairs" should "add up the same by antidiagonals and by rows" in {
    series.show(fact(Series.Diagonal).conclusion) shouldBe
      "!x:num -> num -> real. !y:num. " +
        "Sum (\\z:num. Sum (\\u:num. x u (NUM_SUB z u)) (SUC z)) y = " +
        "Sum (\\z:num. Sum (\\u:num. x z u) (NUM_SUB y z)) y"

    val table = Term.variable(
      "f",
      Type.fun(
        TyApp(Natural.TypeName, Nil),
        Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil))))
    val two = force(series.term("SUC (SUC ZERO)", TyApp(Natural.TypeName, Nil)))

    val opened = force(
      Rewrite.Rule
        .all(
          logic,
          Vector(
            fact(Series.AtZero),
            fact(Series.AtSuccessor),
            force(peano.fact(Peano.SubAtZero)),
            force(peano.fact(Peano.SubSuccessors)),
            force(peano.fact(Peano.ZeroMinus))
          )
        )
        .flatMap { unfolding =>
          rules
            .specAll(fact(Series.Diagonal), List(table, two))
            .flatMap(instance =>
              Rewrite
                .rewrite(unfolding, instance.conclusion)
                .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance))))
        })

    // Three entries on each side. On the left the antidiagonals, `{(0,0)}` then `{(0,1),(1,0)}`;
    // on the right the rows, `{(0,0),(0,1)}` then `{(1,0)}`. Same three pairs, grouped two ways,
    // which is the whole content of the lemma and is what an off-by-one in either length would
    // break while still printing plausibly.
    //
    // The index prints `SUC 0` and not `1` because nothing here spells a numeral: every recurrence
    // over `num` is stated at a successor and `Successor.spell` is what turns one into the other,
    // which this check has no reason to pay for. The leading zeroes are the empty sums the
    // recurrences leave and no normal form anybody chose.
    series.show(opened.conclusion) shouldBe
      "0 + (0 + f 0 0) + (0 + f 0 (SUC 0) + f (SUC 0) 0) = " +
        "0 + (0 + f 0 0 + f 0 (SUC 0)) + (0 + f (SUC 0) 0)"
  }

  /**
   * The binomial theorem, stated and then COMPUTED at a square.
   *
   * The first assertion is the sentence a reader agrees with. The second is the one with content:
   * at `n = SUC (SUC ZERO)` the sum is three explicit terms, and what they add up to has to be
   * `(x + y) * ((x + y) * 1)`, which is the left-hand side with its own recurrence unfolded. A
   * coefficient off by one row, a power off by one, or a subtraction that truncated where it
   * should not would all leave the theorem provable and print plausibly, and none of them
   * survives being asked for a number.
   *
   * `Ring` is what closes it rather than a printed comparison, because the two sides are the same
   * polynomial written two ways and no normal form here is anybody's choice.
   */
  "The binomial theorem" should "hold, and expand to a square a reader can check" in {
    series.show(fact(Series.Binomial).conclusion) shouldBe
      "!x:real. !y:real. !z:num. Power (x + y) z = " +
        "Sum (\\u:num. real_of_num (NUM_CHOOSE z u) * " +
        "(Power x u * Power y (NUM_SUB z u))) (SUC z)"

    val real = TyApp(Real.TypeName, Nil)
    val a = Term.variable("a", real)
    val b = Term.variable("b", real)
    val two = force(series.term("SUC (SUC ZERO)", TyApp(Natural.TypeName, Nil)))

    val square = force(rules.specAll(fact(Series.Binomial), List(a, b, two)))

    val opened = force(
      Rewrite.Rule
        .all(
          logic,
          Vector(
            fact(Series.AtZero),
            fact(Series.AtSuccessor),
            fact(Series.PowerAtZero),
            fact(Series.PowerAtSuccessor),
            force(peano.fact(Peano.ChooseNone)),
            force(peano.fact(Peano.ChooseEmpty)),
            force(peano.fact(Peano.ChoosePascal)),
            force(peano.fact(Peano.SubAtZero)),
            force(peano.fact(Peano.SubSuccessors)),
            force(peano.fact(Peano.AddAtZero)),
            force(peano.fact(Peano.AddAtSuccessor)),
            force(peano.fact(Peano.EmbedsZero)),
            force(peano.fact(Peano.EmbedsSuccessor)),
            force(peano.fact(Peano.EmbedsSum))
          )
        )
        .flatMap(unfolding =>
          Rewrite
            .rewrite(unfolding, square.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, square)))))

    // Three terms, one per column, and their sum is the square. Nothing here is asserted about
    // the shape the rewriting happens to leave: what is asserted is the arithmetic.
    // **The coefficients are visible and they are Pascal's second row.** They print unevaluated,
    // as sums of the embedded naturals, which is what makes this assertion worth reading rather
    // than only running: `(0 + 1)` against the square of the second, `(0 + 1 + (0 + 1 + 0))` in
    // the middle and `(0 + 1 + 0 + (0 + 0))` against the square of the first are **1, 2, 1**, in
    // that order, and a coefficient taken from the wrong row would show here as a different
    // number rather than as a failure somewhere else.
    series.show(opened.conclusion) shouldBe
      "(a + b) * ((a + b) * 1) = 0 + (0 + 1) * (1 * (b * (b * 1))) + " +
        "(0 + 1 + (0 + 1 + 0)) * (a * 1 * (b * 1)) + (0 + 1 + 0 + (0 + 0)) * (a * (a * 1) * 1)"

    // And they add up: the three terms are the square, which is the half the printed form cannot
    // carry. `Ring` closes it, and the two sides are not the same term, so it did work.
    Term.destEq(opened.conclusion).map(sides => sides._1 == sides._2) shouldBe Some(false)
    force(ring.prove(opened.conclusion)).hypotheses shouldBe empty
  }

  /**
   * The Cauchy product's partial sum and the gap to the product, computed at a square.
   *
   * The statements are what a reader agrees with; what reading cannot settle is whether the two
   * sides describe the same region of the index square. At `n = 2` they can be checked by eye:
   * the partial Cauchy sum is the three pairs with `i + j < 2` and the product of the two partial
   * sums is all four, so the gap has to come out as the single corner `a 1 * b 1`. A
   * subtraction that truncated where it should not, or a row read at the wrong length, gives a
   * different corner and the assertion says which.
   */
  "The Cauchy product" should "have a closed partial sum, and a gap that is the corner" in {
    series.show(fact(Series.Cauchy).conclusion) shouldBe
      "!x:num -> real. !y:num -> real. !z:num. " +
        "Sum (\\u:num. Sum (\\v:num. x v * y (NUM_SUB u v)) (SUC u)) z = " +
        "Sum (\\u:num. x u * Sum y (NUM_SUB z u)) z"
    series.show(fact(Series.CauchyGap).conclusion) shouldBe
      "!x:num -> real. !y:num -> real. !z:num. " +
        "Sum x z * Sum y z - Sum (\\u:num. Sum (\\v:num. x v * y (NUM_SUB u v)) (SUC u)) z = " +
        "Sum (\\u:num. x u * (Sum y z - Sum y (NUM_SUB z u))) z"

    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val a = Term.variable("a", Type.fun(numbers, real))
    val b = Term.variable("b", Type.fun(numbers, real))
    val two = force(series.term("SUC (SUC ZERO)", numbers))

    val unfolding = force(
      Rewrite.Rule.all(
        logic,
        Vector(
          fact(Series.AtZero),
          fact(Series.AtSuccessor),
          force(peano.fact(Peano.SubAtZero)),
          force(peano.fact(Peano.SubSuccessors)),
          force(peano.fact(Peano.ZeroMinus))
        )
      ))

    def opened(statement: Kernel.Thm): Kernel.Thm = {
      val instance = force(rules.specAll(statement, List(a, b, two)))
      force(
        Rewrite
          .rewrite(unfolding, instance.conclusion)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance))))
    }

    // The three pairs with `i + j < 2` on each side, grouped by antidiagonal on the left and by
    // row on the right. The index prints `SUC 0` and not `1` for the reason the diagonal's own
    // test gives: nothing here spells a numeral.
    series.show(opened(fact(Series.Cauchy)).conclusion) shouldBe
      "0 + (0 + a 0 * b 0) + (0 + a 0 * b (SUC 0) + a (SUC 0) * b 0) = " +
        "0 + a 0 * (0 + b 0 + b (SUC 0)) + a (SUC 0) * (0 + b 0)"

    // And the gap, whose right-hand side has to reduce to the one corner outside the triangle.
    val gap = opened(fact(Series.CauchyGap))
    force(ring.prove(gap.conclusion)).hypotheses shouldBe empty
    Term.destEq(gap.conclusion).map(sides => sides._1 == sides._2) shouldBe Some(false)

    // The corner named, which is the half `Ring` closing the equation does not show a reader.
    val corner = force(series.term("a (SUC ZERO) * b (SUC ZERO)", real))
    val rightSide = force(
      Term.destEq(gap.conclusion).map(_._2).toRight(MissingDefinition("an equation")))
    force(ring.prove(force(LogicError.lift(Term.eq(rightSide, corner))))).hypotheses shouldBe empty
  }

  /**
   * The bounded monotone, spent on a pair `SUM_MONOTONE` cannot compare.
   *
   * The prediction in `SUM_CONGRUENCE_BELOW`'s note is that the first real consumer of one of the
   * four unbounded lemmas meets a wall and gets a bounded twin. This is that twin, and the test
   * that earns it is not that it proves something — the unbounded one proves the same conclusion
   * whenever it applies — but that it applies where the other **cannot**.
   *
   * `real_of_num i <= 0` holds at `i = 0` and at no other index, so at the bound `SUC ZERO` the
   * bounded hypothesis is dischargeable and the unbounded one is **false**. The second half of
   * this test derives that falsity rather than asserting it, which is what makes the first half a
   * demonstration instead of a coincidence.
   */
  "The bounded monotone" should "compare where the unbounded one cannot" in {
    series.show(fact(Series.MonotoneBelow).conclusion) shouldBe
      "!x:num -> real. !y:num -> real. !z:num. " +
        "(!u:num. u < z ==> x u <= y u) ==> Sum x z <= Sum y z"

    val real = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val i = Term.variable("i", numbers)
    val one = force(series.term("SUC ZERO", numbers))
    val climbing = force(series.term("\\i:num. real_of_num i", Type.fun(numbers, real)))
    val flat = force(series.term("\\i:num. (0:real)", Type.fun(numbers, real)))
    val linarith = force(Linarith.construct(order))

    // Below the bound the only index is zero, and there the two agree.
    val guard = force(
      Parser.proposition(series.theory, series.notation, "NUM_LT (i:num) (SUC ZERO)"))
    val assumed = force(LogicError.lift(Kernel.assume(guard)))
    val isZero = force(
      rules
        .specAll(force(peano.fact(Peano.AtMostBelowSuccessor)), List(force(series.term("ZERO", numbers)), i))
        .flatMap(rules.mp(_, assumed))
        .flatMap(atMost =>
          rules.spec(i, force(peano.fact(Peano.AtMostZero))).flatMap(rules.mp(_, atMost))))
    val below = force(
      Conv
        .apTerm(
          force(LogicError.lift(series.theory.constant(Peano.EmbeddingName, Type.fun(numbers, real)))),
          isZero)
        .flatMap(carried =>
          Conv
            .trans(carried, force(peano.fact(Peano.EmbedsZero)))
            .flatMap(atZero =>
              linarith
                .prove("!e:real. e = 0 ==> e <= 0")
                .flatMap(rules.spec(force(series.term("real_of_num (i:num)", real)), _))
                .flatMap(rules.mp(_, atZero))))
        .flatMap(rules.disch(guard, _))
        .flatMap(rules.gen(i, _)))

    val compared = force(
      rules
        .specAll(fact(Series.MonotoneBelow), List(climbing, flat, one))
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))
        .flatMap(rules.mp(_, below)))
    compared.hypotheses shouldBe empty
    series.show(compared.conclusion) shouldBe
      "Sum (\\x:num. real_of_num x) (SUC 0) <= Sum (\\x:num. 0) (SUC 0)"

    // And the unbounded hypothesis is false at the bound itself, derived rather than asserted:
    // `real_of_num (SUC ZERO)` is `real_of_num ZERO + 1`, which is one.
    val atTheBound = force(
      Conv
        .trans(
          force(rules.spec(force(series.term("ZERO", numbers)), force(peano.fact(Peano.EmbedsSuccessor)))),
          force(
            linarith
              .prove("!z:real. z = 0 ==> z + 1 = 1")
              .flatMap(rules.spec(force(series.term("real_of_num ZERO", real)), _))
              .flatMap(rules.mp(_, force(peano.fact(Peano.EmbedsZero)))))))
    val refused = force(
      linarith
        .prove("!e:real. e = 1 ==> ~(e <= 0)")
        .flatMap(rules.spec(force(series.term("real_of_num (SUC ZERO)", real)), _))
        .flatMap(rules.mp(_, atTheBound)))
    refused.hypotheses shouldBe empty
    series.show(refused.conclusion) shouldBe "~(real_of_num (SUC 0) <= 0)"
  }

  "A sum of zeroes" should "be zero at every length, which SUM_ZERO does not say" in {
    // The two read alike and are different facts: `SUM_ZERO` is about a sum of length zero, this is
    // about a summand of value zero. Keeping them apart is what lets an emptied inner sum collapse.
    series.show(fact(Series.OfZero).conclusion) shouldBe "!x:num. Sum (\\y:num. 0) x = 0"
  }

  "A sum of a constant" should "be the constant times the length, which counts a range" in {
    // The third of three facts that read alike. `SUM_ZERO` is a sum of length zero, `SUM_OF_ZERO`
    // a summand of value zero, and this is a summand of any fixed value; only the third says how
    // long a range is, and until it existed this library could not say that at all.
    series.show(fact(Series.Constant).conclusion) shouldBe
      "!x:real. !y:num. Sum (\\z:num. x) y = real_of_num y * x"
    fact(Series.Constant).hypotheses shouldBe empty
  }

  "The power of a product of bases" should "split into the two powers, at every exponent" in {
    // The first law here about the BASE rather than about the exponent. `POWER_ADD` and
    // `POWER_MUL` are both `Power b (<operation> m n)`; this one is `Power (<operation> a b) n`,
    // which is why it does not carry an operation in its name: that pattern is taken, and a
    // reader who has met the other two parses `POWER_PRODUCT` as a third law of exponents.
    series.show(fact(Series.Multiplicative).conclusion) shouldBe
      "!x:real. !y:real. !z:num. Power (x * y) z = Power x z * Power y z"
    fact(Series.Multiplicative).hypotheses shouldBe empty
  }

  it should "be provable from the power's two recurrences ALONE, which is what its list claims" in {
    // The first version of this test asserted `reached == A ++ (reached -- A)`, which is
    // `A subset-of reached` written as an equality and is true of anything containing A: it could
    // not fail. Replaced by the claim the list actually makes, which can. `BaseStatements` exists
    // as a list of its own because its rule set is the power's two recurrences and nothing else --
    // no arithmetic on `num`, no other law of exponents, not even `POWER_ADD`, which
    // `ExponentStatements` would have said it rests on. Re-proving it here from exactly those two
    // rules is what makes that a fact rather than a comment: if the statement ever changes to one
    // that needs more, this goes red where the construction would quietly pass the larger set.
    val statement = force(series.proposition(
      "!a:real. !b:real. !n:num. Power (a * b) n = Power a n * Power b n"))
    val induction = force(naturals.fact(Natural.Induction))
    val driver = Induct(series.logic, ring, induction)
    val rules = force(Rewrite.Rule.all(series.logic,
      Vector(fact(Series.PowerAtZero), fact(Series.PowerAtSuccessor))))

    val reproved = force(driver.proveWith(statement, rules))
    series.show(reproved.conclusion) shouldBe series.show(fact(Series.Multiplicative).conclusion)
    info(
      s"POWER_MULTIPLICATIVE: ${Derivation.size(fact(Series.Multiplicative))} inferences over " +
        s"${Derivation.axiomsOf(fact(Series.Multiplicative)).size} axioms"
    )
  }

  it should "refuse the same statement with the bases added instead of multiplied" in {
    // The false control, and its error is the one the name is chosen to prevent: a law about the
    // base read as a law about the exponent. Same driver and same rules, so what is measured is
    // the statement and not the machinery.
    val statement = force(series.proposition(
      "!a:real. !b:real. !n:num. Power (a + b) n = Power a n * Power b n"))
    val induction = force(naturals.fact(Natural.Induction))
    val driver = Induct(series.logic, ring, induction)
    val rules = force(Rewrite.Rule.all(series.logic,
      Vector(fact(Series.PowerAtZero), fact(Series.PowerAtSuccessor))))

    driver.proveWith(statement, rules) shouldBe a[Left[?, ?]]
  }

  "A doubled exponent" should "not see the sign of the base" in {
    // Stated at `NUM_ADD n n` rather than at a parity predicate, which is why it has no exception
    // at any length: an exponent written as a sum with itself is even by construction.
    series.show(fact(Series.NegatedDouble).conclusion) shouldBe
      "!x:real. !y:num. Power (0 - x) (y + y) = Power x (y + y)"
    fact(Series.NegatedDouble).hypotheses shouldBe empty
  }

  it should "not close through the rewriting route that was proposed for it" in {
    // A five-rewrite route was proposed: POWER_ADD to split the doubled exponent,
    // POWER_MULTIPLICATIVE BACKWARDS to collect (0-x)(0-x), a ring step, then both forwards
    // again. A rewrite rule fires in ONE direction, so the middle step is not available, and the
    // rule set reduces the two sides to `Power (0-x) n * Power (0-x) n` and `Power x n * Power x
    // n`, which Ring sees as unrelated atoms. Asserted rather than described, because the
    // docstring says so and a sentence about what a tool cannot do decays where nothing re-runs
    // it. If a later library makes that route work, this goes red and the docstring gets
    // rewritten by whoever it stops.
    val statement = force(series.proposition(
      "!x:real. !y:num. Power (0 - x) (y + y) = Power x (y + y)"))
    val induction = force(naturals.fact(Natural.Induction))
    val driver = Induct(series.logic, ring, induction)
    val sketch = force(Rewrite.Rule.all(series.logic, Vector(
      fact(Series.PowerOfSum), fact(Series.Multiplicative),
      force(peano.fact(Peano.AddAtZero)), force(peano.fact(Peano.AddAtSuccessor)))))

    driver.proveWith(statement, sketch) shouldBe a[Left[?, ?]]
  }

  it should "refuse the same statement at an exponent that is not doubled" in {
    // The false control, and its error is the one the statement's shape exists to exclude: at a
    // bare `n` the claim is false at every odd exponent. Same driver, same rules as the real
    // proof, so what is measured is the statement.
    val statement = force(series.proposition(
      "!x:real. !n:num. Power (0 - x) n = Power x n"))
    val induction = force(naturals.fact(Natural.Induction))
    val driver = Induct(series.logic, ring, induction)
    val rules = force(Rewrite.Rule.all(series.logic, Vector(
      fact(Series.PowerAtZero), fact(Series.PowerAtSuccessor),
      force(peano.fact(Peano.AddAtZero)), force(peano.fact(Peano.AddAtSuccessor)),
      force(peano.fact(Peano.SuccessorPlus)))))

    driver.proveWith(statement, rules) shouldBe a[Left[?, ?]]
  }

  "The geometric sum" should "hold at every length, cleared of its denominator" in {
    // Cleared so that `Ring` and not a field closes it, and so that the lemma carries no
    // hypothesis `q != 1` at all: at q = 1 both sides are zero, which is true and uninformative
    // rather than wrong, and that is the right behaviour for a lemma instantiated without looking.
    series.show(fact(Series.Geometric).conclusion) shouldBe
      "!x:real. !y:num. (x - 1) * Sum (\\z:num. Power x z) y = Power x y - 1"
    fact(Series.Geometric).hypotheses shouldBe empty
  }

  it should "refuse the same statement without the cleared denominator's minus one" in {
    // The false control: the sum of q^i for i < n is (q^n - 1)/(q - 1), not q^n/(q - 1), and the
    // missing 1 is exactly the empty range's value. The rules include the distributivity rule the
    // real proof needs, so a refusal here is about the statement and not about the shape.
    val statement = force(series.proposition(
      "!q:real. !n:num. (q - 1) * Sum (\\i:num. Power q i) n = Power q n"))
    val induction = force(naturals.fact(Natural.Induction))
    val driver = Induct(series.logic, ring, induction)
    val spread = force(series.proposition(
      "!a:real. !b:real. !c:real. a * (b + c) = a * b + a * c"))
    val rules = force(Rewrite.Rule.all(series.logic,
      Vector(fact(Series.AtZero), fact(Series.AtSuccessor),
             fact(Series.PowerAtZero), fact(Series.PowerAtSuccessor),
             force(ring.prove(spread)))))

    driver.proveWith(statement, rules) shouldBe a[Left[?, ?]]
  }

  it should "refuse the same statement with one term too many" in {
    // The false control, and the error it is built from is the one a range invites: a sum over n
    // indices read as a sum over n + 1. The same driver and the same rules, so what is measured is
    // the statement and not the machinery.
    val statement = force(series.proposition(
      "!c:real. !n:num. Sum (\\i:num. c) n = real_of_num n * c + c"))
    val induction = force(naturals.fact(Natural.Induction))
    val driver = Induct(series.logic, ring, induction)
    val rules = force(
      Rewrite.Rule.all(
        series.logic,
        Vector(
          fact(Series.AtZero),
          fact(Series.AtSuccessor),
          force(peano.fact(Peano.EmbedsSuccessor)),
          force(peano.fact(Peano.EmbedsZero))
        )
      )
    )

    driver.proveWith(statement, rules) shouldBe a[Left[?, ?]]
  }

  it should "be why the embedding gets a list of its own rather than a line in the first" in {
    // The claim `EmbeddingStatements` rests on, measured rather than asserted: the same induction
    // over the sum's recurrences ALONE does not close, because the length crosses from num to real
    // on the right-hand side and nothing in `Statements`' rule set can move it. If this ever
    // starts passing, the fifth list has stopped earning its existence.
    val statement = force(series.proposition(Series.EmbeddingStatements.toMap.apply(Series.Constant)))
    val induction = force(naturals.fact(Natural.Induction))
    val driver = Induct(series.logic, ring, induction)
    val withoutTheBridge = force(
      Rewrite.Rule.all(series.logic, Vector(fact(Series.AtZero), fact(Series.AtSuccessor))))

    driver.proveWith(statement, withoutTheBridge) shouldBe a[Left[?, ?]]
  }

  "The product" should "pull a constant factor out as a power" in {
    // The product's answer to linearity, and the one fact that ties the two definitions in the file
    // to each other rather than each to the recursion theorem.
    series.show(fact(Series.ProdScales).conclusion) shouldBe
      "!x:real. !y:num -> real. !z:num. Prod (\\u:num. x * y u) z = Power x z * Prod y z"
  }

  /* ---------------------------------------------------------------- the bounds */

  "A positive base" should "give a positive power at every exponent, spendably" in {
    series.show(fact(Series.PowerPositive).conclusion) shouldBe
      "!x:real. 0 < x ==> (!y:num. 0 < Power x y)"

    // The invariant a printed statement cannot show: that the hypothesis is one a caller can
    // actually discharge. Spent at a numeral it has to leave a closed theorem behind, and if the
    // lemma had been stated with a hypothesis nothing proves, this is the line that would say so.
    val atTwo = force(rules.specAll(fact(Series.PowerPositive), List(numeral(2))))
    val spent = force(rules.mp(atTwo, force(order.positive(BigInt(2)))))

    series.show(spent.conclusion) shouldBe "!x:num. 0 < Power 2 x"
    spent.hypotheses shouldBe empty
  }

  "The power" should "be monotone in its base, and spendable there too" in {
    // Monotone in the base and not in the exponent, which is a choice: monotonicity in the exponent
    // is a different fact, wants `1 <= b` rather than `0 < a`, and says nothing about two bases.
    // This is the one a bound on a measured quantity wants, where the base is what is imprecise.
    series.show(fact(Series.PowerMonotone).conclusion) shouldBe
      "!x:real. !y:real. 0 < x ==> x <= y ==> (!z:num. Power x z <= Power y z)"

    val atPair = force(rules.specAll(fact(Series.PowerMonotone), List(numeral(2), numeral(3))))
    val spent = force(
      rules
        .mp(atPair, force(order.positive(BigInt(2))))
        .flatMap(rules.mp(_, atMost(2, 3)))
    )

    series.show(spent.conclusion) shouldBe "!x:num. Power 2 x <= Power 3 x"
    spent.hypotheses shouldBe empty
  }

  "A summand that is never negative" should "give a sum that is never negative" in {
    series.show(fact(Series.NonNegative).conclusion) shouldBe
      "!x:num -> real. (!y:num. 0 <= x y) ==> (!y:num. 0 <= Sum x y)"

    // Spent on a summand nobody interpreted, which is the case the lemma exists for: a development
    // that quantifies over its summand has a bare symbol and no lambda, so the pointwise premise
    // is the only way in.
    val pointwise = force(series.proposition("!i:num. 0 <= (ff:num->real) i"))
    val assumed = force(LogicError.lift(Kernel.assume(pointwise)))
    val summand = Term.variable("ff", Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil)))
    val spent = force(
      rules.mp(force(rules.specAll(fact(Series.NonNegative), List(summand))), assumed)
    )

    series.show(spent.conclusion) shouldBe "!x:num. 0 <= Sum ff x"
    spent.hypotheses should contain(pointwise)
    spent.hypotheses should have size 1
  }

  "A summand below another at every index" should "give a sum below the other's" in {
    // The congruence lemma with `<=` for `=`, and it exists for the same reason: bare summand
    // symbols, no redex for the rewriter to enter, so the comparison has to be carried by a lemma.
    series.show(fact(Series.Monotone).conclusion) shouldBe
      "!x:num -> real. !y:num -> real. (!z:num. x z <= y z) ==> (!z:num. Sum x z <= Sum y z)"
    fact(Series.Monotone).hypotheses shouldBe empty
  }

  "A product of positives" should "be positive, which is what makes it usable as a denominator" in {
    series.show(fact(Series.ProdPositive).conclusion) shouldBe
      "!x:num -> real. (!y:num. 0 < x y) ==> (!y:num. 0 < Prod x y)"
    fact(Series.ProdPositive).hypotheses shouldBe empty
  }

  "Strict positivity and not monotonicity" should "be what costs the multiplication order axiom" in {
    // The measurement that says where the price of a bound is paid, and it is sharper than a count.
    // `LT_MUL` is the only axiom of the theory that concludes anything positive from a product, and
    // exactly the three lemmas whose conclusion is strict reach it. The monotonicity lemmas are
    // non-strict throughout and close their steps by adding and multiplying non-negatives, which
    // needs no axiom of its own beyond what `Order` already derived: `SUM_MONOTONE` proves an
    // inequality about a product-free sum and never touches it.
    val productOfPositives = force(reals.axiom("LT_MUL")).conclusion

    Vector(Series.PowerPositive, Series.PowerMonotone, Series.ProdPositive).foreach { name =>
      withClue(s"$name should reach LT_MUL: ") {
        Derivation.axiomsOf(fact(name)) should contain(productOfPositives)
      }
    }

    Vector(Series.Monotone, Series.NonNegative, Series.Linear, Series.ByParts, Series.ProdScales)
      .foreach { name =>
        withClue(s"$name should not reach LT_MUL: ") {
          Derivation.axiomsOf(fact(name)) should not contain productOfPositives
        }
      }
  }

  /* --------------------------------------------------- the congruence prediction */

  "The rewriter" should "go into a lambda Prod binds, and leave a bare symbol alone" in {
    // The same measurement `ChainSpec` makes for `Sum`, repeated at the operator that arrived
    // after the prediction was written. It is the prediction's content: a written-out summand is
    // rewritten where it stands and needs no lemma at all, and a bare symbol is the case that does.
    val pointwise = force(series.proposition("!i:num. (ff:num->real) i = (gg:num->real) i"))
    val rule = force(Rewrite.Rule.of(logic, force(LogicError.lift(Kernel.assume(pointwise)))))

    def rewritten(text: String): String = {
      val term = force(series.term(text))
      val equation = force(Rewrite.rewrite(Vector(rule), term))
      series.show(Term.destEq(equation.conclusion).get._2)
    }

    rewritten("Prod (\\i:num. (ff:num->real) i) (n:num)") should include("gg")
    rewritten("Prod (\\i:num. 2 * (ff:num->real) i) (n:num)") should include("gg")
    rewritten("Prod (ff:num->real) (n:num)") should not include "gg"
  }

  "Every binding operator" should "want its own congruence, as this file predicted it would" in {
    // The file comment on `SUM_CONGRUENCE` predicted that products, integrals and maxima would each
    // want one of these. `Prod` is the first of them to arrive, so the prediction is now testable
    // rather than believed, and what it asserts is that the two lemmas are the same shape at
    // different constants and that neither is derivable from the other.
    series.show(fact(Series.Congruence).conclusion) shouldBe
      "!x:num -> real. !y:num -> real. (!z:num. x z = y z) ==> (!z:num. Sum x z = Sum y z)"
    series.show(fact(Series.ProdCongruence).conclusion) shouldBe
      "!x:num -> real. !y:num -> real. (!z:num. x z = y z) ==> (!z:num. Prod x z = Prod y z)"

    fact(Series.Congruence).hypotheses shouldBe empty
    fact(Series.ProdCongruence).hypotheses shouldBe empty
  }

  it should "no longer want one, now that extensionality reaches under the binder" in {
    // The prediction held exactly once, for `Prod`, and `docs/adr/0009` names this rewrite as the
    // debt of asserting eta. The two lemmas stay — a caller with a pointwise hypothesis should not
    // have to know which road is cheaper — but they are a convenience now and not a necessity.
    //
    // **The axiom is the assertion that matters, more than the size.** Through the induction these
    // reached choice and infinity, because the induction is over `num` and `num` is carved out of an
    // infinite type. Through `Classical.ext` they reach eta and nothing else, which is what ties an
    // axiom to the lemma that pays for it: eta was asserted for this, and this is where it shows.
    val eta = Classical.standard.axioms(Classical.Eta).conclusion

    Vector(Series.Congruence, Series.ProdCongruence).foreach { name =>
      val theorem = fact(name)
      val axioms = Derivation.axiomsOf(theorem)

      withClue(s"$name rests on ${axioms.size} axioms\n") {
        axioms should contain(eta)
      }

      // And the size fell, which is the measurement `docs/adr/0009` recorded as missing: an
      // induction over the recurrences against three steps. The bound is loose on purpose — what is
      // being pinned is the order of magnitude, not a number that moves when a derived rule does.
      info(s"$name: ${Derivation.size(theorem)} inferences over ${axioms.size} axioms")
      Derivation.size(theorem) should be < 5000
    }
  }

  /* ------------------------------------------------------------------ reindexing */

  "Reindexing" should "reach the offset of one, which is what SUC alone can say" in {
    series.show(fact(Series.Shift).conclusion) shouldBe
      "!x:num -> real. !y:num. Sum (\\z:num. x (SUC z)) y = Sum x (SUC y) - x 0"
    fact(Series.Shift).hypotheses shouldBe empty
  }

  "Reindexing by an arbitrary offset" should "be statable and proved, which it was not until this series stood on Peano" in {
    // This test was the record of what could not be said, and the sentence it carried was right
    // twice over and for two different reasons, which is why it is rewritten rather than deleted.
    //
    // Written first, it said `num` had `ZERO` and `SUC` and no addition, so `i + m` reached for the
    // reals' `+` and the types did not meet. `Peano` landed addition on 2026-09-10, within hours,
    // and the sentence was amended to say that a series built over a chain without `Peano` cannot
    // see it. That was true and it hid the real obstacle: the chain **did** have both from
    // 2026-09-11, and the statement still would not read, because `Sum` had been defined over a
    // theory that had no addition in it. A constant declared after a definition cannot appear
    // inside it, and naming a constant in a goal and using it under a binder of an earlier
    // definition are not the same thing.
    //
    // So the repair was the order of two developments and not a lemma. `Series` is built over
    // `Peano`, `NUM_ADD m i` is a term of the theory the sum is defined in, and the induction
    // `SUM_SHIFT`'s note wrote out in advance closes it unchanged.
    series.show(fact(Series.Reindex).conclusion) shouldBe
      "!x:num -> real. !y:num. !z:num. Sum (\\u:num. x (y + u)) z = Sum x (y + z) - Sum x y"
    fact(Series.Reindex).hypotheses shouldBe empty
  }

  it should "be the general case of the offset-one lemma, which is why both are kept" in {
    // `SUM_SHIFT` is this lemma at `m = SUC ZERO`, and the two right-hand sides are the same claim
    // written with what each theory can spell. Both are kept because the shorter one says what it
    // says without `NUM_ADD` in it, so a development holding the sums and not the arithmetic can
    // still have it.
    //
    // Instantiated rather than argued: the general lemma at `SUC ZERO` gives a statement about
    // `NUM_ADD (SUC ZERO) n`, which is `SUC n` by the recurrences, and what this asserts is that
    // the instance exists and is a theorem of the same shape.
    val one = force(series.term("SUC 0"))
    val f = force(series.term("f:num->real"))
    // `specPrefix` and not `specAll`: the bound is left quantified on purpose, and that has to be
    // asked for by name since 2026-09-12, because a short list to `specAll` is also what handing it
    // another lemma's arguments looks like and is refused there now. This is the one call in the
    // whole suite that wanted a partial instance, and it is the measurement that kept the operation.
    val instance = force(rules.specPrefix(fact(Series.Reindex), List(f, one)))

    series.show(instance.conclusion) should include("SUC 0 +")
    instance.hypotheses shouldBe empty
  }

  /* --------------------------------------------------------------- exponents */

  "An exponent that is a sum" should "split into a product, which is what makes it anything but an atom" in {
    // The lemma the card called the most economical of its group, and the reason it matters is what
    // the absence looked like rather than what the presence proves: `Power 2 (NUM_ADD a b)` and
    // `Power 2 a * Power 2 b` were two terms with no relation, and a development whose exponents
    // are partial sums could not state a single step that moved one.
    series.show(fact(Series.PowerOfSum).conclusion) shouldBe
      "!x:real. !y:num. !z:num. Power x (y + z) = Power x y * Power x z"
    fact(Series.PowerOfSum).hypotheses shouldBe empty
  }

  it should "close a goal whose exponent is a sum, by rewriting and nothing else" in {
    // Spent rather than read, for the reason the bounds above are spent: what a consumer does with
    // this is hand it to the rewriter, and a lemma that prints correctly and does not fire there
    // would pass the test above.
    val rule = force(Rewrite.Rule.of(series.logic, fact(Series.PowerOfSum)))
    val goal = force(series.term("Power b (m + SUC 0)"))
    val rewritten = force(Rewrite.rewrite(Vector(rule), goal))

    series.show(rewritten.conclusion) shouldBe
      "Power b (m + SUC 0) = Power b m * Power b (SUC 0)"
  }

  "An exponent that is a product" should "nest, and it wanted the first law and nothing more" in {
    // The card that proposed this said in as many words that it had not proved it and that it
    // blocked nothing. It costs one line: the step rewrites `NUM_MUL m (SUC n)` into
    // `NUM_ADD (NUM_MUL m n) m`, and from there `POWER_ADD` is exactly what carries it.
    series.show(fact(Series.PowerOfProduct).conclusion) shouldBe
      "!x:real. !y:num. !z:num. Power x (y * z) = Power (Power x y) z"
    fact(Series.PowerOfProduct).hypotheses shouldBe empty
  }

  it should "be why the two laws are proved in order rather than from one rule set" in {
    // The claim the ordering rests on, measured: the same induction over the same rules **without**
    // `POWER_ADD` does not close. If this ever starts passing, `exponentLaws` has stopped earning
    // its existence and the two belong back in `ArithmeticStatements`.
    val statement = force(series.proposition(Series.ExponentStatements.toMap.apply(Series.PowerOfProduct)))
    val without = force(
      Rewrite.Rule.all(
        series.logic,
        Vector(
          fact(Series.PowerAtZero),
          fact(Series.PowerAtSuccessor),
          force(peano.fact(Peano.MulAtZero)),
          force(peano.fact(Peano.MulAtSuccessor))
        )
      )
    )
    val induction = force(naturals.fact(Natural.Induction))
    val driver = Induct(series.logic, ring, induction)

    driver.proveWith(statement, without) shouldBe a[Left[?, ?]]
  }

  /* ---------------------------------------------------------------- swapping */

  "Two finite summations" should "commute, which wanted no arithmetic on num after all" in {
    // This was expected to be behind reindexing and is not: the induction runs on the outer length
    // and the inner one rides along as a parameter, so nothing here ever adds two indices. The
    // expectation being wrong is the finding; the lemma is the evidence.
    series.show(fact(Series.Swapped).conclusion) shouldBe
      "!x:num -> num -> real. !y:num. !z:num. " +
        "Sum (\\u:num. Sum (\\v:num. x u v) y) z = Sum (\\u:num. Sum (\\v:num. x v u) z) y"
    fact(Series.Swapped).hypotheses shouldBe empty
  }

  "The rewriter" should "reach a sum under a binder whose summand mentions that binder" in {
    // The measurement `SUM_SWAP` rests on, and it is not what being first order would suggest.
    // `Matching` binds a pattern variable to a term and never to a function of an argument, so a
    // recurrence looks unusable on `Sum (\i. f i j) (SUC k)` where `j` is bound outside. It is
    // usable, because `Rewrite` opens a binder with a fresh free variable before descending rather
    // than matching underneath it: by the time the pattern is matched there is no bound variable in
    // the way. If that ever changed, `SUM_SWAP` would stop proving and this says why.
    val rules = force(
      Rewrite.Rule.all(
        logic,
        Vector(fact(Series.AtZero), fact(Series.AtSuccessor))
      )
    )

    def rewritten(text: String): String = {
      val term = force(series.term(text))
      val equation = force(Rewrite.rewrite(rules, term))
      series.show(Term.destEq(equation.conclusion).get._2)
    }

    // Nothing under a binder: the recurrence applies, which nobody doubted.
    rewritten("Sum (\\i:num. (ff:num->real) i) (SUC (k:num))") shouldBe
      "Sum (\\x:num. ff x) k + ff k"

    // The case the swap needs: the inner summand mentions the outer binder's variable, and the
    // inner recurrence still fires.
    rewritten("Sum (\\j:num. Sum (\\i:num. (gg:num->num->real) i j) (SUC (k:num))) (m:num)") shouldBe
      "Sum (\\x:num. Sum (\\y:num. gg y x) k + gg k x) m"

    // And the case that stays put, because there is no `SUC` to match rather than because of any
    // binder: a length that is the bound variable itself.
    rewritten("Sum (\\j:num. Sum (\\i:num. (ff:num->real) i) j) (m:num)") shouldBe
      "Sum (\\x:num. Sum (\\y:num. ff y) x) m"
  }

  /* ------------------------------------------------------------- the whole file */

  "Every fact here" should "rest on the theory's own axioms and on no assumption" in {
    // Over whatever the development holds rather than over a list written here, so that a fact
    // added later is covered by this without anybody remembering to add it. Two claims: nothing
    // carries a hypothesis, and no derivation reached an axiom that is not one of the theory's, so
    // the eighteen are still the whole of what this file asks anyone to believe.
    val believed = series.theory.axioms.toSet

    series.facts should not be empty
    series.facts.foreach { case (name, theorem) =>
      withClue(s"$name: ") {
        theorem.hypotheses shouldBe empty
        Derivation.axiomsOf(theorem).diff(believed) shouldBe empty
      }
    }

    // Nineteen since eta, and this is the assertion that says so where it matters: every theorem
    // above reaches only what the theory already believed, and the count says how much that is.
    series.theory.axioms.size shouldBe 19
  }

  "The size of each proof" should "be reported, since these are the largest here" in {
    Vector(
      Series.Linear,
      Series.Telescoping,
      Series.ByParts,
      Series.Shift,
      Series.Reindex,
      Series.Additive,
      Series.Swapped,
      Series.ProdScales,
      Series.PowerPositive,
      Series.PowerMonotone,
      Series.NonNegative,
      Series.Monotone,
      Series.ProdPositive,
      Series.PowerOfSum,
      Series.PowerOfProduct
    ).foreach { name =>
      val theorem = fact(name)
      info(
        s"$name: ${Derivation.size(theorem)} inferences over " +
          s"${Derivation.axiomsOf(theorem).size} axioms"
      )
      Derivation.size(theorem) should be > 1000
    }
  }
}
