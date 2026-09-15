package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Number theory on `num`, and the three questions that decide whether it was worth moving.
 *
 * **The first is whether it says anything.** `Divisibility` states the same first relation over the
 * reals and comes out trivial, which its own docstring says and this file proves rather than
 * repeats: `Divides 2 3` and `Divides 3 2` are both theorems there, with nothing assumed, so no
 * antisymmetry can hold. Over `num` antisymmetry is a theorem. That pair is the measurement of what
 * the move bought and it is the assertion this file exists for.
 *
 * **The second is whether it costs anything.** Both constants are defined, so the trusted base must
 * not move: the theory's axioms are compared against the ones it was built over rather than against
 * a number written here, and every proof is walked to the axioms it actually reaches.
 *
 * **The third is whether it can be used.** A fact that is stated correctly and that nothing can
 * apply is one nobody finds out about until later, so the uses at the end are the ones a consumer
 * would write: dividing six by two, dividing five by two with a remainder, and adding a congruence
 * to a reflexive one mod two. The division theorem's own hypothesis is the sharpest case of that
 * question, and it is why `NUM_ZERO_LT_SUC` was derived at all; it is `Peano`'s since 2026-09-11,
 * along with the four other order facts this file held, and the use below reaches it there.
 */
class ModularSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private val peano = chain.peano
  private val modular = Modular.standard
  private val rules = modular.logic.rules

  private def fact(name: String): Kernel.Thm = force(modular.fact(name))

  private def statement(name: String): String = modular.show(fact(name).conclusion)

  private val Names: Vector[String] = Modular.Statements.map(_._1)

  private def numeral(value: Int): Term =
    force(modular.term(Vector.fill(value)("SUC (").mkString + "0:num" + ")" * value))

  /* --------------------------------------------------- the two constants themselves */

  "Both relations" should "be defined rather than assumed, so the trusted base does not move" in {
    // The comparison is against the theory this one extended rather than against a number written
    // here: a hand-written count would have to be edited when the base moves for an unrelated
    // reason, and editing it is exactly the moment this assertion exists to interrupt.
    modular.theory.axioms shouldBe peano.theory.axioms
    modular.theory.definitions.keySet should contain allOf (
      Modular.DividesName, Modular.CongruenceName
    )

    modular.show(force(modular.definition(Modular.DividesName)).conclusion) shouldBe
      "NUM_DIVIDES = (\\x:num. \\y:num. ?z:num. y = x * z)"
    modular.show(force(modular.definition(Modular.CongruenceName)).conclusion) shouldBe
      "NUM_CONG = (\\x:num. \\y:num. \\z:num. ?u:num. ?v:num. y + x * u = z + x * v)"
  }

  it should "carry every fact without a hypothesis left standing" in {
    // Not a formality. `Rules.mp` discharges an antecedent that matches and leaves one that does
    // not standing as a hypothesis, so a derivation that specialised its quantifiers in the wrong
    // order comes back as a TRUE sequent with an extra premise rather than as an error. The
    // comparison inside `concludeDivides` is the first defence and this sweep is the second.
    Names.foreach(name => withClue(s"$name: ")(fact(name).hypotheses shouldBe empty))
  }

  it should "reach no axiom the chain it was built over does not already reach" in {
    // Walked rather than read off the imports. `Ring` and `LINARITH` are what close the arithmetic
    // here, so the field and order axioms enter; what must not happen is an axiom entering that
    // nothing else in the chain touches, because that would be this development quietly widening
    // what a consumer is asked to believe.
    val reached = Vector(
      peano.facts.values,
      chain.order.facts.values,
      chain.naturals.facts.values,
      chain.series.facts.values
    ).flatMap(_.toVector).flatMap(Derivation.axiomsOf).toSet

    Names.foreach { name =>
      withClue(s"$name: ")(Derivation.axiomsOf(fact(name)).diff(reached) shouldBe empty)
    }
  }

  it should "cost no axiom at all where only the definition is being used" in {
    // Measured, and it is the same result `DivisibilitySpec` records over the reals: introducing
    // and eliminating either relation is pure logic, so a consumer that does nothing else has added
    // nothing to what it asks anyone to believe. Arithmetic is where the axioms enter, and
    // `NUM_DIVIDES_REFL` is the cheapest fact that needs any.
    Vector(
      Modular.DividesIntro,
      Modular.DividesElim,
      Modular.CongIntro,
      Modular.CongElim,
      Modular.CongRefl,
      Modular.CongSym,
      Modular.PrimeAboveOne,
      Modular.PrimeDivisor
    ).foreach(name => withClue(s"$name: ")(Derivation.axiomsOf(fact(name)) shouldBe empty))

    Derivation.axiomsOf(fact(Modular.DividesRefl)) should not be empty
  }

  it should "name every fact the way the convention names one" in {
    // `LibrarySpec` checks this for the names in `docs/lemmas.md`, and this development is not in
    // the chain that document is generated from, so its names are outside that check. The rule is
    // `docs/naming.md`'s and is asserted here rather than left to a reader.
    val shape = "[A-Z][A-Z0-9]*(_[A-Z0-9]+)*".r

    Names.foreach { name =>
      withClue(s"$name: ") {
        shape.matches(name) shouldBe true
        name should startWith("NUM_")
      }
    }

    // One spelling per concept, which is the rule with teeth: the corpus already holds `ANTISYM`,
    // `TRANS`, `REFL` and `SYM`, and a fourth spelling of any of them would start here.
    Names.filter(_.contains("ANTISYMMETRIC")) shouldBe empty
    Names.filter(_.contains("TRANSITIVE")) shouldBe empty
  }

  /* ---------------------------------------------------------------- the statements */

  "Divisibility" should "read as the text this development is checked by" in {
    statement(Modular.DividesIntro) shouldBe
      "!x:num. !y:num. !z:num. y = x * z ==> NUM_DIVIDES x y"
    statement(Modular.DividesElim) shouldBe
      "!x:num. !y:num. NUM_DIVIDES x y ==> (?z:num. y = x * z)"
    statement(Modular.DividesRefl) shouldBe "!x:num. NUM_DIVIDES x x"
    statement(Modular.DividesTrans) shouldBe
      "!x:num. !y:num. !z:num. NUM_DIVIDES x y ==> NUM_DIVIDES y z ==> NUM_DIVIDES x z"
    statement(Modular.DividesMul) shouldBe
      "!x:num. !y:num. !z:num. NUM_DIVIDES x y ==> NUM_DIVIDES x (y * z)"
    statement(Modular.DividesAdd) shouldBe
      "!x:num. !y:num. !z:num. NUM_DIVIDES x y /\\ NUM_DIVIDES x z ==> NUM_DIVIDES x (y + z)"
    statement(Modular.DividesZero) shouldBe "!x:num. NUM_DIVIDES x 0"
    statement(Modular.OneDivides) shouldBe "!x:num. NUM_DIVIDES (SUC 0) x"
    statement(Modular.ZeroDivides) shouldBe "!x:num. NUM_DIVIDES 0 x = (x = 0)"
    statement(Modular.DividesBound) shouldBe
      "!x:num. !y:num. NUM_DIVIDES x y ==> x <= y \\/ y = 0"
  }

  "The congruence" should "read as the text this development is checked by" in {
    statement(Modular.CongRefl) shouldBe "!x:num. !y:num. NUM_CONG x y y"
    statement(Modular.CongSym) shouldBe
      "!x:num. !y:num. !z:num. NUM_CONG x y z ==> NUM_CONG x z y"
    statement(Modular.CongTrans) shouldBe
      "!x:num. !y:num. !z:num. !u:num. NUM_CONG x y z ==> NUM_CONG x z u ==> NUM_CONG x y u"
    statement(Modular.CongAdd) shouldBe
      "!x:num. !y:num. !z:num. !u:num. !v:num. NUM_CONG x y z ==> NUM_CONG x u v ==> NUM_CONG x " +
        "(y + u) (z + v)"
    statement(Modular.CongMul) shouldBe
      "!x:num. !y:num. !z:num. !u:num. !v:num. NUM_CONG x y z ==> NUM_CONG x u v ==> NUM_CONG x " +
        "(y * u) (z * v)"
    statement(Modular.CongModulus) shouldBe "!x:num. !y:num. NUM_CONG x (y + x) y"
  }

  /* ----------------------------------------- what moving to `num` actually bought */

  "Antisymmetry" should "be a theorem here, where over the reals it cannot be one" in {
    // The assertion this file exists for, and both halves are executed rather than described.
    statement(Modular.DividesAntisym) shouldBe
      "!x:num. !y:num. NUM_DIVIDES x y /\\ NUM_DIVIDES y x ==> x = y"
    fact(Modular.DividesAntisym).hypotheses shouldBe empty
  }

  it should "fail over the reals, where two and three divide each other" in {
    // `Divisibility.NonZeroDivides` is `!a b. ~(a = 0) ==> Divides a b`, so both directions hold
    // between any two non-zero reals. With antisymmetry they would give `2 = 3`, which is why that
    // file has no antisymmetry and this one does. Proved rather than quoted: the two theorems below
    // are built here, with nothing assumed.
    val divisibility = Divisibility.standard
    val reals = divisibility.reals
    val realRules = reals.logic.rules
    val linarith = force(Linarith.construct(divisibility.ring))

    def dividing(divisor: String, dividend: String): Kernel.Thm =
      force(
        for {
          nonZero <- divisibility.nonZeroDivides
          left <- reals.term(divisor)
          right <- reals.term(dividend)
          notZero <- reals.proposition(s"~($divisor = 0)").flatMap(linarith.prove)
          instance <- realRules.specAll(nonZero, List(left, right))
          related <- realRules.mp(instance, notZero)
        } yield related
      )

    divisibility.show(dividing("2", "3").conclusion) shouldBe "Divides 2 3"
    divisibility.show(dividing("3", "2").conclusion) shouldBe "Divides 3 2"
    dividing("2", "3").hypotheses shouldBe empty

    // And the absence read off the code rather than off a comment: that development names no
    // antisymmetry, because it could not prove one.
    divisibility.facts.keySet.filter(_.contains("ANTISYM")) shouldBe empty
  }

  /* ------------------------------------------------ the transfer used as a tactic */

  "An identity between naturals" should "be decided by embedding it in the reals" in {
    // There is no `RING` for `num`. `Modular.identity` embeds both sides with `real_of_num`, lets
    // `Ring` decide what is left, and comes back across the injectivity of the embedding. A `num`
    // variable becomes an atom `Ring` cannot take apart, which is the right reading of it, so the
    // identity decided is the same identity in the same number of unknowns.
    val expanded = force(
      modular.identity(
        // `:num` on each variable's first occurrence since `docs/adr/0018`: `+` and `*` stand
        // for two constants here and nothing else in these texts says which. One annotation per
        // name is enough, and the identity is the same one.
        "(a:num + b:num) * (c:num + d:num)",
        "a:num * c:num + a * d:num + (b:num * c + b * d)"
      )
    )

    modular.show(expanded.conclusion) shouldBe
      "(a + b) * (c + d) = a * c + a * d + (b * c + b * d)"
    expanded.hypotheses shouldBe empty
  }

  it should "settle a ground claim written in successors, which is what the recurrences hook" in {
    val arithmetic = force(
      modular.identity(
        "SUC (SUC 0) * SUC (SUC (SUC 0))",
        "SUC (SUC (SUC (SUC (SUC (SUC 0)))))"
      )
    )

    modular.show(arithmetic.conclusion) shouldBe
      "SUC (SUC 0) * SUC (SUC (SUC 0)) = SUC (SUC (SUC (SUC (SUC (SUC 0)))))"
  }

  it should "refuse a claim that is not an identity, and say which two terms differ" in {
    // The absence asserted rather than described, which is what `MagnitudeSpec` does for `floor`.
    // The refusal comes from `Ring` over the embedded terms, so it names the two real forms; that
    // is a worse message than one about naturals and it is the honest one, since the embedded
    // identity is what was actually decided.
    val refusal = modular.identity("NUM_ADD a:num b:num", "a:num * b")

    refusal.isLeft shouldBe true
    refusal.fold(_.message, theorem => modular.show(theorem.conclusion)) should include("real_of_num")
  }

  /* ------------------------------------------------------------ using the lemmas */

  "Two" should "divide six, end to end and with no witness left in the statement" in {
    // The arithmetic is decided by the transfer, the introduction takes it, and what comes back
    // mentions no witness. Six is six successors here, which is the spelling the recurrences
    // produce; `6:num` is a term and is a different one, bridged by `Successor.spell`.
    val theorem = force(
      for {
        product <- modular.term("SUC (SUC 0) * SUC (SUC (SUC 0))")
        equation <- modular.identity(numeral(6), product)
        introduction <- modular.fact(Modular.DividesIntro)
        instance <- rules.specAll(introduction, List(numeral(2), numeral(6), numeral(3)))
        related <- rules.mp(instance, equation)
      } yield related
    )

    modular.show(theorem.conclusion) shouldBe
      "NUM_DIVIDES (SUC (SUC 0)) (SUC (SUC (SUC (SUC (SUC (SUC 0))))))"

    // The hypothesis list and not only the conclusion. Specialising the three quantifiers in the
    // wrong order produces `NUM_DIVIDES 2 3` with the unmatched equation standing as a premise,
    // which is a true sequent and reads as a success; it is what this probe did first.
    theorem.hypotheses shouldBe empty
  }

  "Division with remainder" should "apply at a modulus a consumer can actually write" in {
    // The hypothesis is `NUM_LT ZERO n`, and until `NUM_ZERO_LT_SUC` there was nothing that could
    // discharge it: `Peano` had `NUM_ZERO_LE` and no strict counterpart, and every concrete modulus
    // here is a successor. The lemma is `Peano`'s and the guard is discharged from there, which is
    // the arrangement the move was for: a consumer of this file reaches the order through `Peano`
    // rather than through a copy held here.
    val theorem = force(
      for {
        division <- modular.fact(Modular.Division)
        positive <- peano.fact(Peano.SuccessorPositive)
        one <- modular.term("SUC 0")
        guard <- rules.spec(one, positive)
        instance <- rules.specAll(division, List(numeral(2), numeral(5)))
        applied <- rules.mp(instance, guard)
      } yield applied
    )

    modular.show(theorem.conclusion) shouldBe
      "?x:num. ?y:num. SUC (SUC (SUC (SUC (SUC 0)))) = SUC (SUC 0) * x + y /\\ y < SUC (SUC 0)"
    theorem.hypotheses shouldBe empty
  }

  it should "be unique as well as existent, which is what makes the remainder denote" in {
    // Existence alone was the gap most likely to be assumed away, and it was the gap here until
    // 2026-09-11. The pair is unique now, so "the remainder of `m` mod `n`" denotes and a `NUM_MOD`
    // defined by choice would have facts attached to it rather than being a name for nothing.
    val unique = fact(Modular.DivisionUnique)

    statement(Modular.DivisionUnique) shouldBe
      "!x:num. !y:num. !z:num. !u:num. !v:num. x * y + z = x * u + v /\\ z < x /\\ v < x ==> y = " +
        "u /\\ z = v"
    unique.hypotheses shouldBe empty

    // It needs no hypothesis that the modulus is positive, and that is not an omission: a bound
    // strictly below `x` already says `x` is not `ZERO`.
    modular.show(unique.conclusion) should not include "0 < x"

    // The two constants were asserted absent here until 2026-09-12, on the ground that nothing in
    // this development needed them. What changed is not this lemma but the consumer: the quotient
    // and the remainder are defined below, from this, and the assertion moved with them rather
    // than being deleted. `NUM_DIV_MOD_UNIQUE` is where it went.
    modular.theory.definitions.keySet should contain allOf (Modular.DivName, Modular.ModName)
  }

  it should "apply to two decompositions of one number, which is what a consumer does with it" in {
    // Five as two times two with one over, put against itself: the quotients and the remainders are
    // forced equal. The point of the probe is the guard, which is two strict bounds and nothing
    // about the modulus being positive.
    val theorem = force(
      for {
        unique <- modular.fact(Modular.DivisionUnique)
        belowSuccessor <- peano.fact(Peano.BelowSuccessor)
        instance <- rules.specAll(
          unique,
          List(numeral(2), numeral(2), numeral(1), numeral(2), numeral(1))
        )
        oneBelowTwo <- rules.spec(numeral(1), belowSuccessor)
        bounds <- rules.conjIntro(oneBelowTwo, oneBelowTwo)
        left <- modular.term("SUC (SUC 0) * SUC (SUC 0) + SUC 0")
        equation = Kernel.refl(left)
        premises <- rules.conjIntro(equation, bounds)
        applied <- rules.mp(instance, premises)
      } yield applied
    )

    modular.show(theorem.conclusion) shouldBe
      "SUC (SUC 0) = SUC (SUC 0) /\\ SUC 0 = SUC 0"
    theorem.hypotheses shouldBe empty
  }

  "A congruence" should "add to another one, which is the whole point of having the relation" in {
    // Mod two: three plus two is congruent to three, three is congruent to itself, so the two sums
    // are congruent. An argument carried out mod `2^j` is this step repeated, and without it the
    // relation is a predicate nobody can compute with.
    val theorem = force(
      for {
        addition <- modular.fact(Modular.CongAdd)
        modulus <- modular.fact(Modular.CongModulus)
        reflexive <- modular.fact(Modular.CongRefl)
        shifted <- rules.specAll(modulus, List(numeral(2), numeral(3)))
        same <- rules.specAll(reflexive, List(numeral(2), numeral(3)))
        raised <- modular.term("SUC (SUC (SUC 0)) + SUC (SUC 0)")
        instance <- rules.specAll(
          addition,
          List(numeral(2), raised, numeral(3), numeral(3), numeral(3))
        )
        first <- rules.mp(instance, shifted)
        both <- rules.mp(first, same)
      } yield both
    )

    modular.show(theorem.conclusion) shouldBe
      "NUM_CONG (SUC (SUC 0)) (SUC (SUC (SUC 0)) + SUC (SUC 0) + SUC (SUC (SUC 0))) (SUC (SUC " +
        "(SUC 0)) + SUC (SUC (SUC 0)))"
    theorem.hypotheses shouldBe empty
  }

  it should "be handed out as a term, for a consumer whose numbers were computed" in {
    // The service `Divisibility.divides` provides and for the same reason: a caller whose modulus
    // was computed cannot go through the parser, and building the application itself would mean
    // naming the constant against a theory of its own choosing, which `docs/adr/0008` is about.
    modular.show(force(modular.divides(numeral(2), numeral(6)))) shouldBe
      "NUM_DIVIDES (SUC (SUC 0)) (SUC (SUC (SUC (SUC (SUC (SUC 0))))))"
    modular.show(force(modular.congruent(numeral(2), numeral(3), numeral(1)))) shouldBe
      "NUM_CONG (SUC (SUC 0)) (SUC (SUC (SUC 0))) (SUC 0)"
  }

  it should "be an equivalence relation, with all three facts hypothesis-free" in {
    Vector(Modular.CongRefl, Modular.CongSym, Modular.CongTrans).foreach { name =>
      withClue(s"$name: ")(fact(name).hypotheses shouldBe empty)
    }
  }

  "A name this development does not hold" should "be refused rather than silently missing" in {
    // The lookups return an `Either` and nothing here forces them, so a typo in a consumer's fact
    // name is a refusal that says which name, not a `None` that turns into a null later.
    //
    // The two names this used to probe were `NUM_BEZOUT` and the definition of `NUM_MOD`, and both
    // are held here since 2026-09-12. A probe for a refusal has to name something genuinely absent
    // or it stops testing the refusal: `NUM_GCD_ASSOC` and `NUM_COPRIME` are two this development
    // does not hold and, unlike the pair they replace, are not on anybody's list to add.
    modular.fact("NUM_GCD_ASSOC").isLeft shouldBe true
    modular.definition("NUM_COPRIME").isLeft shouldBe true
  }

  /* ------------------------------------------------- the greatest common divisor */

  "The greatest common divisor" should "be defined by choosing rather than by computing" in {
    // The body is `select` applied to the specification, and the specification is read off
    // `NUM_GREATEST` rather than written twice: the term the definition carries has to be the term
    // the existence proof reaches, and the only way to be sure of that is for there to be one term.
    modular.theory.definitions.keySet should contain(Modular.GcdName)

    modular.show(force(modular.definition(Modular.GcdName)).conclusion) shouldBe
      "NUM_GCD = (\\x:num. \\y:num. select (\\z:num. (NUM_DIVIDES z x /\\ NUM_DIVIDES z y) /\\ " +
        "(!u:num. NUM_DIVIDES u x /\\ NUM_DIVIDES u y ==> u <= z)))"

    // And it costs no axiom the theory did not already carry, which is the same check the two
    // relations get above: a constant introduced by `select` is a definition and not an assumption.
    modular.theory.axioms shouldBe peano.theory.axioms
  }

  it should "apply at a pair a consumer can write, with the guard discharged" in {
    // The guard is `~(a = ZERO) \/ ~(b = ZERO)`, and a consumer discharges it by naming which side
    // is not zero. Six and four: the disjunction's left half is the one used here, and the theorem
    // that comes out is about the two numerals rather than about two variables.
    val theorem = force(
      for {
        divides <- modular.fact(Modular.GcdDividesLeft)
        instance <- rules.specAll(divides, List(numeral(6), numeral(4)))

        // `~(6 = ZERO)` is `NUM_SUC_NOT_ZERO` at five, because six is written as its successor.
        successorNotZero <- peano.naturals.fact(Natural.SuccessorNotZero)
        sixIsNotZero <- rules.spec(numeral(5), successorNotZero)
        zero <- modular.term("0:num")
        fourIsZero <- LogicError.lift(Term.eq(numeral(4), zero))
        otherHalf <- modular.logic.mkNot(fourIsZero)
        guard <- rules.disjIntro1(otherHalf, sixIsNotZero)

        applied <- rules.mp(instance, guard)
      } yield applied
    )

    modular.show(theorem.conclusion) shouldBe
      "NUM_DIVIDES (NUM_GCD (SUC (SUC (SUC (SUC (SUC (SUC 0)))))) " +
        "(SUC (SUC (SUC (SUC 0))))) (SUC (SUC (SUC (SUC (SUC (SUC 0))))))"
    theorem.hypotheses shouldBe empty
  }

  it should "be greatest by the order and, since Bezout, by divisibility as well" in {
    // Until 2026-09-12 this test asserted the absence of `NUM_GCD_DIVIDES`, `NUM_BEZOUT`,
    // `NUM_EUCLID` and `NUM_PRIME`, on the ground that being the largest common divisor does not on
    // its own make every other one divide it. That ground has not moved: the two statements are
    // still different, and the second is a theorem now because Bezout was derived, not because the
    // first implies it. So the assertion becomes the distinction rather than the absence.
    statement(Modular.GcdGreatest) should include("z <= NUM_GCD x y")
    statement(Modular.GcdGreatest) should not include "NUM_DIVIDES z (NUM_GCD"
    statement(Modular.GcdDivides) should include("NUM_DIVIDES z (NUM_GCD x y)")
    statement(Modular.GcdDivides) should not include "NUM_LE"

    // Both are guarded by the same disjunction, which is the honest domain of `NUM_GCD` and not a
    // convenience: at the origin every number is a common divisor and there is no greatest.
    Vector(Modular.GcdGreatest, Modular.GcdDivides).foreach { name =>
      withClue(s"$name: ")(statement(name) should include("~(x = 0) \\/ ~(y = 0)"))
    }
  }

  /* ------------------------------------------ the quotient and the remainder */

  "The quotient and the remainder" should "be defined by choosing, in two stages" in {
    // The second names the first, which is what makes them one answer rather than two choices: a
    // remainder chosen from a predicate of its own would be some remainder, not the one that goes
    // with `NUM_DIV m n`.
    modular.show(force(modular.definition(Modular.DivName)).conclusion) shouldBe
      "NUM_DIV = (\\x:num. \\y:num. select (\\z:num. (?u:num. x = y * z + u /\\ u < y) \\/ y = 0 " +
        "/\\ z = 0))"
    modular.show(force(modular.definition(Modular.ModName)).conclusion) shouldBe
      "NUM_MOD = (\\x:num. \\y:num. select (\\z:num. x = y * NUM_DIV x y + z /\\ z < y \\/ y = 0 " +
        "/\\ z = x))"

    // And the trusted base does not move, which is what "defined" means here.
    modular.theory.axioms shouldBe peano.theory.axioms
  }

  it should "recover the dividend with no hypothesis at all, which is the decision at 0" in {
    // The second disjunct of each predicate is what buys this. A definition that let the choice
    // fall on an empty predicate would leave `NUM_MOD m ZERO` a term nothing is provable about, and
    // this equation would need `NUM_LT ZERO n` in front of it forever.
    //
    // The dividend is on the **right**, which is the shape a rewriter can use: with it on the left
    // the rule matches every term and grows it, and `Novelty` builds a rule set out of the whole
    // library. That is measured rather than argued, in this file's own history: the first form of
    // this lemma hung a suite for an hour.
    statement(Modular.DivisionAt) shouldBe
      "!x:num. !y:num. y * NUM_DIV x y + NUM_MOD x y = x"
    statement(Modular.DivAtZero) shouldBe "!x:num. NUM_DIV x 0 = 0"
    statement(Modular.ModAtZero) shouldBe "!x:num. NUM_MOD x 0 = x"

    Vector(Modular.DivisionAt, Modular.DivAtZero, Modular.ModAtZero).foreach { name =>
      withClue(s"$name: ")(fact(name).hypotheses shouldBe empty)
    }

    // The value at a modulus of `ZERO`, at a dividend a consumer can write. This is the assertion
    // the rejected alternative could not have: "nothing is provable about this term" is a claim no
    // test can interrogate.
    val atZero = force(rules.spec(numeral(5), fact(Modular.ModAtZero)))
    modular.show(atZero.conclusion) shouldBe
      s"NUM_MOD (${modular.show(numeral(5))}) 0 = ${modular.show(numeral(5))}"
  }

  it should "bound the remainder, which is the one thing a modulus of 0 cannot have" in {
    // The guard stays here and no definition could remove it: nothing at all is below `ZERO`.
    statement(Modular.ModBelow) shouldBe
      "!x:num. !y:num. 0 < y ==> NUM_MOD x y < y"
  }

  it should "determine the pair, which is what makes the two names honest" in {
    // `NUM_DIVISION_UNIQUE` transported. Without it both constants would satisfy the equation above
    // and a consumer holding a quotient of its own could not conclude it held *the* quotient, which
    // is the whole content of calling either one a function.
    statement(Modular.DivisionDetermined) shouldBe
      "!x:num. !y:num. !z:num. !u:num. x = y * z + u /\\ u < y ==> z = NUM_DIV x y /\\ u = " +
        "NUM_MOD x y"

    // Five by two, end to end: two and one satisfy the two conditions, so they are the pair the
    // constants name. The point of the probe is that nothing here mentions the definitions.
    val theorem = force(
      for {
        determined <- modular.fact(Modular.DivisionDetermined)
        belowSuccessor <- peano.fact(Peano.BelowSuccessor)
        decomposition <- modular.term(
          "SUC (SUC 0) * SUC (SUC 0) + SUC 0"
        )
        equation <- modular.identity(numeral(5), decomposition)
        bound <- rules.spec(numeral(1), belowSuccessor)
        premises <- rules.conjIntro(equation, bound)
        instance <- rules.specAll(
          determined,
          List(numeral(5), numeral(2), numeral(2), numeral(1))
        )
        applied <- rules.mp(instance, premises)
      } yield applied
    )

    val expected = force(
      for {
        quotient <- modular.quotient(numeral(5), numeral(2))
        remainder <- modular.remainder(numeral(5), numeral(2))
        left <- LogicError.lift(Term.eq(numeral(2), quotient))
        right <- LogicError.lift(Term.eq(numeral(1), remainder))
        both <- modular.logic.mkConj(left, right)
      } yield both
    )

    theorem.conclusion shouldBe expected
    theorem.hypotheses shouldBe empty
  }

  /* --------------------------------------------- Bezout, and what stands on it */

  "Bezout" should "be stated as a disjunction, because `num` carries no sign" in {
    // Over the integers this is `d = a x - b y` with the coefficients of either sign. `num` has no
    // negatives, so the term that would have been negated moves to the other side, and which one
    // moves depends on the pair. A statement that fixed the side would be false for half of them.
    statement(Modular.BezoutExists) shouldBe
      "!x:num. !y:num. ?z:num. ?u:num. ?v:num. NUM_DIVIDES z x /\\ NUM_DIVIDES z y /\\ (x * u = y " +
        "* v + z \\/ y * u = x * v + z)"
    statement(Modular.Bezout) shouldBe
      "!x:num. !y:num. ~(x = 0) \\/ ~(y = 0) ==> (?z:num. ?u:num. x * z = y * u + NUM_GCD x y \\/ " +
        "y * z = x * u + NUM_GCD x y)"

    // The first is unguarded and the second is not, and that is the difference between a common
    // divisor and *the* greatest one: at the origin the first has `ZERO` for every witness and the
    // second is about a term nothing is provable about.
    statement(Modular.BezoutExists) should not include "0)"
    fact(Modular.BezoutExists).hypotheses shouldBe empty
  }

  it should "rest on the additive statement of a subtraction `num` does not have" in {
    // Every step below "and therefore `k` divides what is left over" is this lemma. Over a ring it
    // is `a | x /\\ a | y ==> a | (y - x)`; here the difference cannot be written, so the statement
    // is additive and the proof does what the subtraction would have done.
    statement(Modular.DividesSummand) shouldBe
      "!x:num. !y:num. !z:num. NUM_DIVIDES x y ==> NUM_DIVIDES x (y + z) ==> NUM_DIVIDES x z"
  }

  it should "make every common divisor divide the greatest one, at a pair a consumer writes" in {
    // Two divides six and four, so it divides their greatest common divisor. Before Bezout the
    // most this development could say was that two is no *larger* than it.
    val theorem = force(
      for {
        gcdDivides <- modular.fact(Modular.GcdDivides)
        introduction <- modular.fact(Modular.DividesIntro)

        threeTwos <- modular.term("SUC (SUC 0) * SUC (SUC (SUC 0))")
        twoTwos <- modular.term("SUC (SUC 0) * SUC (SUC 0)")
        sixIsEven <- modular.identity(numeral(6), threeTwos)
        fourIsEven <- modular.identity(numeral(4), twoTwos)
        dividesSix <- rules
          .specAll(introduction, List(numeral(2), numeral(6), numeral(3)))
          .flatMap(rules.mp(_, sixIsEven))
        dividesFour <- rules
          .specAll(introduction, List(numeral(2), numeral(4), numeral(2)))
          .flatMap(rules.mp(_, fourIsEven))

        successorNotZero <- peano.naturals.fact(Natural.SuccessorNotZero)
        sixIsNotZero <- rules.spec(numeral(5), successorNotZero)
        zero <- modular.term("0:num")
        fourIsZero <- LogicError.lift(Term.eq(numeral(4), zero))
        otherHalf <- modular.logic.mkNot(fourIsZero)
        guard <- rules.disjIntro1(otherHalf, sixIsNotZero)

        common <- rules.conjIntro(dividesSix, dividesFour)
        applied <- rules
          .specAll(gcdDivides, List(numeral(6), numeral(4), numeral(2)))
          .flatMap(rules.mp(_, guard))
          .flatMap(rules.mp(_, common))
      } yield applied
    )

    modular.show(theorem.conclusion) shouldBe
      s"NUM_DIVIDES (${modular.show(numeral(2))}) " +
        s"(NUM_GCD (${modular.show(numeral(6))}) (${modular.show(numeral(4))}))"
    theorem.hypotheses shouldBe empty
  }

  /* ------------------------------------------------- primes and Euclid's lemma */

  "A prime" should "be above one and divisible only by one and itself" in {
    // The first conjunct is what keeps one out, which the second alone does not: one is divisible
    // only by one and by itself, and those are the same number there.
    modular.show(force(modular.definition(Modular.PrimeName)).conclusion) shouldBe
      "NUM_PRIME = (\\x:num. SUC 0 < x /\\ (!y:num. NUM_DIVIDES y x ==> y = SUC 0 \\/ y = x))"

    statement(Modular.PrimeAboveOne) shouldBe "!x:num. NUM_PRIME x ==> SUC 0 < x"
    statement(Modular.PrimeDivisor) shouldBe
      "!x:num. !y:num. NUM_PRIME x ==> NUM_DIVIDES y x ==> y = SUC 0 \\/ y = x"
  }

  "Euclid's lemma" should "read as the text it is checked by, and apply to a square" in {
    statement(Modular.Euclid) shouldBe
      "!x:num. !y:num. !z:num. NUM_PRIME x ==> NUM_DIVIDES x (y * z) ==> NUM_DIVIDES x y \\/ " +
        "NUM_DIVIDES x z"

    // The use a consumer makes of it first: a prime dividing a square divides the root. Both
    // branches of the disjunction are the same proposition there, so the case analysis collapses,
    // and what comes back mentions no disjunction at all.
    val theorem = force(
      for {
        euclid <- modular.fact(Modular.Euclid)
        p <- modular.term("p:num")
        a <- modular.term("a:num")
        square <- modular.term("a:num * a")

        primeTerm <- modular.prime(p)
        assumedPrime <- LogicError.lift(Kernel.assume(primeTerm))
        dividesSquare <- modular.divides(p, square)
        assumedDivides <- LogicError.lift(Kernel.assume(dividesSquare))

        disjunction <- rules
          .specAll(euclid, List(p, a, a))
          .flatMap(rules.mp(_, assumedPrime))
          .flatMap(rules.mp(_, assumedDivides))
        dividesRoot <- modular.divides(p, a)
        assumedRoot <- LogicError.lift(Kernel.assume(dividesRoot))
        collapsed <- rules.disjElim(disjunction, assumedRoot, assumedRoot)

        discharged <- rules
          .disch(dividesSquare, collapsed)
          .flatMap(rules.disch(primeTerm, _))
      } yield discharged
    )

    modular.show(theorem.conclusion) shouldBe
      "NUM_PRIME p ==> NUM_DIVIDES p (a * a) ==> NUM_DIVIDES p a"
    theorem.hypotheses shouldBe empty
  }

  /* ------------------------------------------------------------------- the price */

  "The cost of the transfer" should "be paid once and shared, which is why it is worth paying" in {
    // Counted and not timed: this machine's wall clock has read forty-one seconds and six minutes
    // thirty-nine for the same suite on the same day, and three assertions with a stopwatch in them
    // went red on correct code. `Derivation.size` is the number of inferences in the proof's whole
    // acyclic graph, which is a property of the derivation and not of the machine.
    //
    // Measured on 2026-09-11: the injectivity of the embedding is about 25000 inferences, and
    // every fact that uses `Modular.identity` sits just above it because the same sub-derivation is
    // shared. The four facts that use only the definition are three orders of magnitude smaller,
    // which is the shape the numbers should have: introduction and elimination are pure logic.
    //
    // The lemma is `Peano`'s, so the sub-derivation is now shared with every other consumer of it
    // as well, which is half the reason it moved.
    val injective = Derivation.size(force(peano.fact(Peano.EmbedsInjectively)))
    injective should be > 10000
    injective should be < 60000

    Vector(Modular.DividesIntro, Modular.DividesElim, Modular.CongIntro, Modular.CongElim)
      .foreach { name =>
        withClue(s"$name: ")(Derivation.size(fact(name)) should be < 2000)
      }

    // The deepest one in the file, and the bound is loose on purpose: it is here to catch a
    // derivation that grew by an order of magnitude, not to pin a number that has no meaning.
    Derivation.size(fact(Modular.Division)) should be < 120000

    // The twelve that landed on 2026-09-12, read the same day: about 24000 inferences for the
    // equation the two constants satisfy, 28000 for the induction behind Bezout, 38000 for Bezout
    // at the gcd and 40000 for Euclid, each of them sitting on the shared sub-derivation above.
    Derivation.size(fact(Modular.Euclid)) should be < 150000

    // The two at-zero lemmas used to be a different kind of fact and are not any more, and the
    // change is worth more than the assertion it replaces. Deciding what `NUM_DIV m ZERO` is needs
    // the choice operator and the infinity the naturals are built from and no arithmetic at all,
    // which was the contrast: **everything else here reached the field**, twenty-eight of the
    // thirty-eight at sixteen axioms, because `identity` decided a regrouping on `num` by embedding
    // it in the reals and asking `Ring`.
    //
    // Since 2026-09-13 nothing here reaches the field. `Semiring` decides those identities on `num`
    // at the two axioms the naturals cost anyway, and the conversion was decided by measurement:
    // seventy-four of the eighty identities this development decides were already inside that
    // fragment and the six that were not were one shape, `x * SUC j = x + x * j`.
    //
    // So the assertion is now the sweep rather than the contrast, and it is strictly stronger than
    // what it replaces. `Modular.identity` is still the wider procedure and still costs the
    // sixteen; what changed is that no fact of this development spends them.
    Names.foreach { name =>
      withClue(s"$name reaches the field: ")(
        Derivation.axiomsOf(fact(name)).size should be <= 2
      )
    }
    Derivation.axiomsOf(fact(Modular.DivAtZero)).size should be < 5
  }

  it should "not hold the five order lemmas any more, which is where they went" in {
    // Asserted rather than described, the way the absence of `NUM_MOD` is above. All five are about
    // the order or the embedding and mention nothing this file defines; they were derived here on
    // 2026-09-11 because `Peano` was being changed elsewhere, and they moved the same day. A copy
    // left behind would be a second statement of the same fact, free to drift.
    val moved = Vector(
      Peano.SuccessorNotSelf,
      Peano.StrictIrreflexive,
      Peano.SuccessorPositive,
      Peano.BelowOrEqual,
      Peano.EmbedsInjectively
    )

    moved.foreach { name =>
      withClue(s"$name: ") {
        Names should not contain name
        modular.fact(name).isLeft shouldBe true
        peano.fact(name).isRight shouldBe true
      }
    }
  }
}
