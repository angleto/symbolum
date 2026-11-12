package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.theories.{Chain, Library, LinearFact, Rational, Real}

/**
 * The search that produces the assignment, and the two answers that must not be confused.
 *
 * A counterexample is worth having because it can be inspected: `0 < x |- 1 < x` fails, and it fails
 * at a particular `x` between them, which is a different kind of information from a tactic saying it
 * could not prove something. The same search asks whether a premise set is satisfiable at all, which
 * is the question a sequent cannot answer about itself: `h1..hn |- c` is true whenever the premises
 * contradict each other, and nothing else in this repository would notice.
 *
 * What is asserted here is never that something is true. `Survived` means no counterexample turned
 * up in the points tried, and the count is carried so that nobody reads it as a proof.
 */
class RefutationSpec extends AnyFlatSpec with Matchers {

  import Model.*

  private val reals = Real.standard
  private val refutation = Refutation.standard

  private def proposition(text: String): Term =
    reals.proposition(text).fold(error => fail(s"could not read $text: ${error.message}"), identity)

  private def counterexample(premises: Vector[String], conclusion: String): Refutation.Outcome =
    refutation.counterexample(premises.map(proposition), proposition(conclusion))

  private def satisfying(premises: Vector[String]): Refutation.Outcome =
    refutation.satisfying(premises.map(proposition))

  private def quantity(outcome: Refutation.Outcome, name: String): Double = outcome match {
    case Refutation.Found(witness, _) =>
      witness.get(name) match {
        case Some(Quantity(value)) => value
        case other => fail(s"$name is $other in the witness")
      }
    case Refutation.Solved(witness, _) =>
      witness.get(name) match {
        case Some(value) => value.numerator.toDouble / value.denominator.toDouble
        case None => fail(s"$name is not in the witness")
      }
    case other => fail(s"expected a witness, got $other")
  }

  /* ----------------------------------------------------------------- the naturals */

  private lazy val chain = Chain.standard
  private lazy val naturals = Refutation(Evaluate.over(chain.reals, Model.Numbers))

  private def aboutNumbers(text: String): Refutation.Outcome = {
    val claim = chain.widest
      .proposition(text)
      .fold(error => fail(s"could not read $text: ${error.message}"), identity)
    naturals.counterexample(Vector.empty, claim)
  }

  "A false claim about the naturals" should "come back with the number it fails at" in {
    // Until 2026-09-11 every one of these came back `NeverAsked`: `Model.Reals` interprets the
    // reals' own constants and none of them is about `num`, so a point had nothing to say and the
    // honest answer was that nobody could ask. The claims below are the weakenings and operator
    // swaps `Propose` produces from this repository's own library, and they are false at small
    // numbers.
    aboutNumbers("!x:num. !y:num. real_of_num (NUM_ADD x y) = real_of_num x * real_of_num y") shouldBe
      a[Refutation.Found]
    // Base then exponent, which is how `POWER_SUC` reads since the night of 2026-09-12 and so how
    // `Propose` would swap it: these texts claim to be what it produces from the library, and a
    // text that mirrored the old shape would be claiming that and not doing it.
    aboutNumbers("!x:real. !n:num. Power x (SUC n) = x + Power x n") shouldBe a[Refutation.Found]
    aboutNumbers("!x:real. !n:num. 0 < Power x n") shouldBe a[Refutation.Found]
    aboutNumbers("!x:num. !y:num. NUM_ADD x y = NUM_MUL x y") shouldBe a[Refutation.Found]
  }

  it should "carry a witness a reader can check, which means numbers and not closures" in {
    aboutNumbers("!x:num. !y:num. real_of_num (NUM_ADD x y) = real_of_num x * real_of_num y") match {
      case Refutation.Found(witness, _) =>
        val shown = witness.toVector.sortBy(_._1).map { case (name, value) => s"$name=${Model.show(value)}" }
        info(s"false at ${shown.mkString(", ")}")

        witness.values.foreach {
          case Whole(_) => succeed
          case other => fail(s"a natural was sampled as $other")
        }

      case other => fail(s"expected a witness, got $other")
    }
  }

  "A claim about a summand" should "be refutable, which wants a function to be sampled" in {
    // Six of the proposals this was built for quantify over the summand rather than over a number,
    // and `!f n. 0 <= Sum f n` cannot be refuted by an assignment with nothing to put in `f`. The
    // sampled function is a real function: it answers the same way every time it is asked about the
    // same index, which is what makes the witness one.
    val outcome = aboutNumbers("!f:num -> real. !n:num. 0 <= Sum f n")

    outcome match {
      case Refutation.Found(witness, _) =>
        info(s"false at ${witness.toVector.sortBy(_._1).map { case (n, v) => s"$n=${Model.show(v)}" }.mkString(", ")}")

        witness("f") match {
          case Mapping(_, apply) =>
            val first = apply(Whole(3))
            val again = apply(Whole(3))
            withClue("a sampled function asked twice about one index: ") { again shouldBe first }
            first should not be empty
          case other => fail(s"the summand was sampled as $other")
        }

      case other => fail(s"expected a witness, got $other")
    }
  }

  "A true claim about the naturals" should "survive, since surviving is all a sample can do" in {
    Vector(
      "!x:num. !y:num. NUM_ADD x y = NUM_ADD y x",
      "!x:num. NUM_LE x (SUC x)",
      "!x:num. !y:num. real_of_num (NUM_ADD x y) = real_of_num x + real_of_num y",
      "!x:real. !y:num. !z:num. Power x (NUM_ADD y z) = Power x y * Power x z"
    ).foreach { text =>
      withClue(s"$text: ") { aboutNumbers(text) shouldBe a[Refutation.Survived] }
    }
  }

  "A variable with nothing to put in it" should "have no value, rather than being given a real" in {
    // The repair this came with, and the defect it repairs is old: a variable of a type the search
    // cannot sample used to be handed a `Quantity` anyway. `!f g. f = g` then came back refuted "at
    // f = -0.51, g = 1.39", and those are not values of `f` and `g`. The claim is false and the
    // witness was not a witness to it, which is the difference this file exists to keep.
    //
    // Leaving the variable out gives the point no value, so the answer is `NeverAsked`: nothing
    // could be asked, which is what has always been meant by it.
    val claim = Real.standard
      .proposition("!f:real->real. !g:real->real. f = g")
      .fold(error => fail(s"could not read it: ${error.message}"), identity)

    refutation.counterexample(Vector.empty, claim) shouldBe a[Refutation.NeverAsked]
  }

  it should "still have none when the type is one the chain defined, which is new since 2026-09-12" in {
    // The same property at the two types that became statable when `Product` and `Word` joined
    // `Chain`. Before that the sampler could not be asked about either, because no signature this
    // repository assembled could read `prod` or `word` in a goal, and a rule nothing can reach is a
    // rule nobody has tested.
    //
    // `Evaluate.inhabitants` declines a `TyApp` with arguments that is not `fun`, and
    // `Refutation.sampled` declines everything that is not `num`, `real`, `bool` or a function of
    // `num`. So both paths decline and the variable is left out of the point, which is the repair
    // above applied to a case it was written before there was one. What must NOT happen is a
    // witness reporting a value for `p` or `w`: a pair is not a quantity and neither is a word.
    Vector(
      "!p:prod(num,num). !q:prod(num,num). p = q",
      "!v:word(real). !w:word(real). v = w",
      "!w:word(real). WORD_LENGTH w = ZERO"
    ).foreach { text =>
      val defined = chain.widest
        .proposition(text)
        .fold(error => fail(s"could not read $text: ${error.message}"), identity)

      withClue(s"$text: ") {
        naturals.counterexample(Vector.empty, defined) shouldBe a[Refutation.NeverAsked]
      }
    }
  }

  "An equality the grid can land on" should "be settled rather than refused as measure-zero" in {
    // The refusal above is about the reals and says so, and until 2026-09-11 it was asked of the
    // equality's **type**: anything at a type with no finite carrier was refused, which was the
    // same test while the reals were the only thing sampled. `num` is sampled now, as a small range
    // of whole numbers, so an equality between two naturals is hit about once in `Refutation.Span`
    // points and refusing it turned an answer into a refusal.
    def satisfying(texts: Vector[String]): Refutation.Outcome =
      naturals.satisfying(texts.map(text =>
        chain.widest.proposition(text).fold(error => fail(error.message), identity)))

    satisfying(Vector("x:num = y:num")) shouldBe a[Refutation.Found]
    satisfying(Vector("SUC (x:num) = y:num")) shouldBe a[Refutation.Found]

    // And the second half of the same repair: this is an equality **between reals**, and every free
    // variable in it is a natural, so the grid determines it and lands on it at three.
    satisfying(Vector("real_of_num (x:num) = 3")) shouldBe a[Refutation.Found]
  }

  it should "still be refused where a coordinate comes from a continuum" in {
    // What the refusal is for, unchanged. A premise that has to make an equality between two reals
    // true is satisfied on a set a sampler lands on with probability zero, and reporting `Survived`
    // there would say the same thing about `{x = 1 /\ 0 < x}` as about `{0 < x, x < 0}` while one
    // of the two is satisfiable.
    satisfying(Vector("x:real = 1 /\\ 0 < x:real")) shouldBe a[Refutation.Undecided]
  }

  "The model of the naturals" should "refute nothing this repository has proved" in {
    // The property the whole addition rests on, and the one that would have made it a defect rather
    // than a capability. A model that reports a counterexample to a theorem is worse than no model,
    // and a finite carrier for `num` with a saturating successor would do exactly that:
    // `!n. ~(SUC n = n)` is false at the top element of any finite carrier. There is no carrier, and
    // this is the measurement that says the choice was the right one.
    val library = Library.of(chain)
    val refuted = library.entries.flatMap { entry =>
      naturals.counterexample(entry.theorem.hypotheses.toVector, entry.theorem.conclusion) match {
        case Refutation.Found(witness, _) =>
          Some(s"${entry.name} at ${witness.toVector.sortBy(_._1).map { case (n, v) => s"$n=${Model.show(v)}" }.mkString(", ")}")
        case _ => None
      }
    }

    info(s"${library.entries.size} lemmas put to the model, ${refuted.size} refuted")
    withClue(s"theorems the model says are false:\n${refuted.mkString("\n")}\n") {
      refuted shouldBe empty
    }
  }

  /* -------------------------------------------------------------- counterexamples */

  "An entailment that does not hold" should "come back with the assignment that shows it" in {
    val outcome = counterexample(Vector("0 < x:real"), "1 < x:real")
    val witness = quantity(outcome, "x")

    // The witness is the whole point: it satisfies the premise and denies the conclusion, and a
    // reader can check that without trusting anything here. The solver returns a vertex of the
    // region, so it is `1` rather than something strictly inside: `0 < 1` holds and `1 < 1` does
    // not, which is a counterexample and a tidier one than a sampled `0.94`.
    witness should be > 0.0
    witness should be <= 1.0
  }

  it should "open a universal conclusion rather than declining it" in {
    // `!x. x * x = x` is false, and saying so needs one point. The bound variable becomes a free one
    // and is sampled; the premises cannot object, because a bound variable is not one they mention.
    counterexample(Vector.empty, "!x:real. x * x = x") should matchPattern {
      case Refutation.Found(_, _) =>
    }
  }

  it should "decide that there is nothing to find, when the entailment holds" in {
    // An equality as a conclusion is not denied, because its denial is a disjunction and that is
    // two systems rather than one, so this one is still sampled.
    counterexample(Vector.empty, "!x:real. x + 0 = x") should matchPattern {
      case Refutation.Survived(_) =>
    }

    // This one is decided: nothing satisfies `x < y` while denying `x < y + 1`.
    counterexample(Vector("x:real < y:real"), "x:real < y:real + 1") should matchPattern {
      case Refutation.NoCounterexample(_) =>
    }

    // And this one is sampled again, because a product of two unknowns is not a linear atom.
    counterexample(Vector("0 < x:real", "0 < y:real"), "0 < x:real * y:real") should matchPattern {
      case Refutation.Survived(_) =>
    }
  }

  it should "say when it never got an answer, which is not the same as finding nothing" in {
    // A universally quantified premise cannot be checked at a point, so no point is usable and
    // nothing was learned. Reporting this as `Survived` would turn "I could not ask" into "I asked
    // and the answer was reassuring", which is the failure this outcome exists to prevent.
    val outcome = counterexample(Vector("!z:real. z = z"), "x:real < y:real")

    outcome should matchPattern { case Refutation.NeverAsked(_) => }
    outcome.asked shouldBe 0

    // Points were offered and every one of them declined to answer, which is the distinction: the
    // search was run and learned nothing, rather than not being run.
    outcome match {
      case Refutation.NeverAsked(offered) => offered shouldBe Refutation.Points
      case other => fail(s"expected NeverAsked, got $other")
    }
  }

  /**
   * Card 1e3ef954, `docs/adr/0077`. A point where a premise is false answers nothing about an
   * entailment, and until 2026-11-12 it was counted as a point that had: `{x * x < 0}` with the
   * conclusion `x = 7` came back `Survived(100)`. The linear case, `{x < 0, 0 < x}`, was caught a
   * day earlier because the solver decides it; a product of two unknowns is not a linear atom, so
   * this one reaches the sampler, and the sampler is what was wrong.
   *
   * Seen red on 2026-11-12, onto `d47d4901`, with the count put back to what it was by
   * `tools/verify/perturb-refutation-premises.sh`: the first assertion below failed reading
   * `Survived(100)`, the figure the card was opened on. Green on the repair, in the same tree.
   */
  it should "not count a point where a premise fails as one where the claim was tested" in {
    val outcome = counterexample(Vector("x:real * x < 0"), "x:real = 7")
    outcome match {
      case Refutation.PremisesNeverHeld(answered) => answered shouldBe Refutation.Points
      case other => fail(s"expected PremisesNeverHeld, got $other")
    }
    outcome.asked shouldBe 0

    // Why the answer is not `Contradictory`: these premises hold, at `x = 0` among others, and the
    // grid misses the interval they hold on as reliably as it misses the empty one. A sampler
    // cannot tell the two apart, so the outcome names what was seen and decides nothing.
    counterexample(Vector("x:real * x < 1 / 1000000000"), "x:real = 7") should matchPattern {
      case Refutation.PremisesNeverHeld(_) =>
    }

    // The control, so the answer above cannot be the only one this search now gives: the cube is
    // positive at about half the points, and the claim, true everywhere, survives exactly those.
    // Before the repair this read a hundred, the points where the premise failed included.
    counterexample(Vector("0 < x:real * x * x"), "x:real * x * x * x = x * x * (x * x)") match {
      case Refutation.Survived(asked) =>
        asked should be > 0
        asked should be < Refutation.Points
      case other => fail(s"expected Survived, got $other")
    }

    // And the question about the premises alone still counts every point that answered, because
    // there a point where a premise fails is the answer it is asking for.
    satisfying(Vector("x:real * x < 0")) match {
      case Refutation.Survived(asked) => asked shouldBe Refutation.Points
      case other => fail(s"expected the premises' own question to count every point, got $other")
    }
  }

  /* ---------------------------------------------------------------- satisfiability */

  "A premise set" should "be shown satisfiable by an assignment that satisfies it" in {
    val outcome = satisfying(Vector("0 < x:real", "x:real < 1"))
    val witness = quantity(outcome, "x")

    witness should be > 0.0
    witness should be < 1.0
  }

  it should "decide a linear set rather than sample it" in {
    // The case that matters. Each of these proves everything, and each prints as an ordinary
    // sequent. The first is obvious written out; the third is a three-variable cycle, which is the
    // shape that is invisible in a list of hypotheses somebody assembled one at a time. All three
    // used to come back as `Survived`, which is a count of failures to find a point; they are
    // decisions now, because a linear set is a system and its satisfiability has a finite answer.
    satisfying(Vector("0 < x:real", "x:real < 0")) should matchPattern {
      case Refutation.Contradictory(_) =>
    }
    satisfying(Vector("x:real < y:real", "y:real < z:real", "z:real < x:real")) should matchPattern {
      case Refutation.Contradictory(_) =>
    }

    // And a set that is satisfiable comes back with the point, not with a number of tries.
    satisfying(Vector("0 < x:real", "x:real < 1")) should matchPattern {
      case Refutation.Solved(_, _) =>
    }
  }

  it should "still sample what it can neither read as a system nor enumerate" in {
    // A product of two unknowns is neither. It is not a linear atom, so it goes to the other half
    // of the partition; and there `x` and `y` have no carrier, so there is nothing to enumerate.
    // The sampler is what answers it, with the answer it always gave.
    satisfying(Vector("0 < x:real * y:real", "x:real * y:real < 0")) should matchPattern {
      case Refutation.Survived(_) =>
    }
  }

  it should "decide a set it can enumerate, which two propositional atoms always were" in {
    // `{p, ~p}` came back `Survived(100)` until 2026-09-11, and that is a count of failures about a
    // set with exactly two assignments in it. `bool` has a carrier, the partition enumerates it,
    // both assignments are put, and the answer is a decision rather than a number.
    satisfying(Vector("p:bool", "~ p:bool")) should matchPattern {
      case Refutation.Contradictory(_) =>
    }
  }

  it should "never hand back a rational for something that is not a real" in {
    // The invariant, which the partition of 2026-09-11 keeps rather than lifts: an exact rational
    // is offered only for an atom a linear point can realise, and the only thing it can realise is
    // a free variable of type `real`. `LinearFact.of` reads a premise that is neither an order
    // relation nor an equality between reals by making the whole of it an atom, so a bare `p:bool`
    // would reach the system as the fact `0 < p`; a guard that asked only whether an atom is a free
    // variable admitted it and answered with a rational value for a boolean, which is an answer to
    // a question nobody asked wearing the one form a reader is invited to check.
    //
    // `p` is in the enumerated half now, so it is decided and its value is `true` and not a number.
    satisfying(Vector("p:bool")) match {
      case Refutation.Solved(witness, finite) =>
        withClue("the exact half is for the reals and nothing else: ") { witness shouldBe empty }
        finite.get("p") shouldBe Some(Truth(true))
      case other => fail(s"expected a decided witness, got $other")
    }
  }

  it should "solve the reals and enumerate the rest of the same premise set" in {
    // The mixed case at its smallest. One linear constraint and one bit: before 2026-09-11 the bit
    // sent the constraint to the sampler, because the set was admitted whole or not at all, and the
    // answer was a hundred points. The two halves share no variable, so the system is solved once
    // and the enumeration decides the rest.
    satisfying(Vector("0 < x:real", "p:bool")) match {
      case Refutation.Solved(witness, finite) =>
        witness.keySet shouldBe Set("x")
        finite.get("p") shouldBe Some(Truth(true))
      case other => fail(s"expected a decided witness, got $other")
    }
  }

  it should "answer the equalities a sampler could only decline" in {
    // The shape this whole line of work is for, and the reason the refusal below still exists. An
    // article states a definition, which is an equality, and `{x = 1}` is satisfiable at exactly
    // one point that a sampler lands on with probability zero. The refusal was honest and useless;
    // solving gives the point.
    satisfying(Vector("x:real = 1")) should matchPattern { case Refutation.Solved(_, _) => }
    satisfying(Vector("x:real + y:real = 1")) should matchPattern { case Refutation.Solved(_, _) => }
    satisfying(Vector("0 < x:real", "x:real = 1")) should matchPattern {
      case Refutation.Solved(_, _) =>
    }
    satisfying(Vector("x:real = 1", "x:real = 2")) should matchPattern {
      case Refutation.Contradictory(_) =>
    }

    // And the point is the point: exact, and satisfying the equality rather than approaching it.
    satisfying(Vector("2 * x:real = 1")) match {
      case Refutation.Solved(witness, _) => witness("x") shouldBe Rational(1, 2)
      case other => fail(s"expected a solved witness, got $other")
    }

    // And an entailment whose premises are equalities is decided too, in the direction that says
    // the claim is good: nothing satisfies `x = 1` while denying `x < 2`.
    counterexample(Vector("x:real = 1"), "x:real < 2") should matchPattern {
      case Refutation.NoCounterexample(_) =>
    }
  }

  it should "read the polarity of a compound premise rather than hunting for an equals sign" in {
    // Where an analysis like this goes wrong is De Morgan, so each shape is pinned here with the
    // reason it has. A conjunction that must hold drags in both conjuncts, so one pinned side is
    // enough; a disjunction that must hold can be satisfied by either side, so it is pinned only
    // when both are; and negating either swaps which of those two rules applies.
    satisfying(Vector("x:real = 1 /\\ 0 < x:real")) should matchPattern {
      case Refutation.Undecided(_) =>
    }
    satisfying(Vector("x:real = 1 \\/ y:real = 2")) should matchPattern {
      case Refutation.Undecided(_) =>
    }

    satisfying(Vector("0 < x:real /\\ x:real < 1")) should matchPattern {
      case Refutation.Found(_, _) =>
    }
    // Falsifying a disjunction means falsifying both sides, and an equality is false almost
    // everywhere, so this is a set a sampler settles at the first point it tries.
    satisfying(Vector("~ (x:real = 1 \\/ x:real = 2)")) should matchPattern {
      case Refutation.Found(_, _) =>
    }
    // Falsifying a conjunction needs only one side false, and `0 < x` is false often enough.
    satisfying(Vector("~ (0 < x:real /\\ x:real = 1)")) should matchPattern {
      case Refutation.Found(_, _) =>
    }
  }

  it should "report an answer that was not sampled as having asked nothing" in {
    // Neither a refusal nor a decision is a search that came back empty. Nothing was tried in
    // either, and the count says so.
    satisfying(Vector("x:real = 1 /\\ 0 < x:real")).asked shouldBe 0
    satisfying(Vector("x:real = 1")).asked shouldBe 0
    satisfying(Vector("0 < x:real", "x:real < 0")).asked shouldBe 0
  }

  it should "not refuse an equality that has to be false, or one over a finite type" in {
    // `~(x = 0)` is `MUL_INVERSE`'s side condition and one of the commonest premises in this theory.
    // An equality that has to be false is false almost everywhere, which is where the sampler
    // already looks, so tripping on it would make the refusal useless.
    satisfying(Vector("~ (x:real = 0)")) should matchPattern { case Refutation.Found(_, _) => }

    // Under an implication the equality can be escaped by falsifying the antecedent.
    satisfying(Vector("x:real = 1 ==> x:real < 2")) should matchPattern {
      case Refutation.Found(_, _) =>
    }

    // A disjunction is pinned only if every branch is; this one has a branch that is not.
    satisfying(Vector("x:real = 1 \\/ 0 < x:real")) should matchPattern {
      case Refutation.Found(_, _) =>
    }

    // And an equality over `bool` has a carrier to enumerate, so there is nothing to refuse. Since
    // 2026-09-11 the enumeration is the partition's rather than the grid's, and four assignments
    // put in full is a decision: `Found` became `Solved` here, which is the same witness with the
    // stronger claim about how it was arrived at.
    satisfying(Vector("p:bool = q:bool")) should matchPattern {
      case Refutation.Solved(_, _) =>
    }
  }

  it should "carry how many points answered, so that nobody reads it as a proof" in {
    // No witness at four points and no witness at four hundred are different findings, and the only
    // thing telling them apart is this number. `Discovery.Unsettled` carries it for the same reason.
    // The premises here are a product of two unknowns, which is not a system, so this is the
    // sampler answering and the count is what it is worth.
    val outcome = satisfying(Vector("0 < x:real * y:real", "x:real * y:real < 0"))

    outcome.asked should be > 50
  }

  /* ------------------------------------------------------------- over a domain */

  "A search over a declared domain" should "enumerate it rather than sample it" in {
    // The case the file was built for. Three agents in a cycle, each threatening the next, and two
    // claims about them: one false, with the agent that shows it, and one pair of premises that no
    // assignment satisfies. Neither is arithmetic, and neither could be asked before.
    val agents = TyApp("agent", Nil)
    val relation = Type.fun(agents, Type.fun(agents, Type.Bool))

    val threatens = (for {
      withType <- reals.theory.declareTypeOperator("agent", 0)
      withConstant <- withType.declareConstant("threatens", relation)
      constant <- withConstant.constant("threatens", relation)
    } yield constant).fold(error => fail(s"could not extend the theory: ${error.message}"), identity)

    val cycle: Value = Mapping(
      agents,
      {
        case Element(_, from) =>
          Some(Mapping(agents, {
            case Element(_, to) => Some(Truth((from + 1) % 3 == to))
            case _ => None
          }))
        case _ => None
      }
    )

    val over = Refutation(
      Evaluate.over(reals, Model.Reals.sizing("agent", 3).interpreting("threatens", cycle))
    )

    val a = Term.variable("a", agents)
    val b = Term.variable("b", agents)
    def claim(left: Term, right: Term): Term =
      Term.appAll(threatens, List(left, right))
        .fold(error => fail(s"could not build the term: ${error.message}"), identity)

    // Nobody threatens themselves in a cycle, and the witness names which agent shows it. The grid
    // enumerates the three rather than sampling them, so this cannot depend on luck.
    over.counterexample(Vector.empty, claim(a, a)) should matchPattern {
      case Refutation.Found(_, _) =>
    }

    // And no pair of agents threatens each other, which is a fact about this model that no amount
    // of staring at the premises would show. Nine pairs, all nine put: `Survived(100)` until
    // 2026-09-11, which was a count of sampled points about a question with nine answers in it, and
    // a decision since. A decision about **this** model, which is what every answer here is.
    over.satisfying(Vector(claim(a, b), claim(b, a))) should matchPattern {
      case Refutation.Contradictory(_) =>
    }
  }

  /* --------------------------------------------------------------- the mixed case */

  /**
   * Three agents, a real-valued measure over them, and the reals beside both.
   *
   * The shape a premise set about entities actually has, and the one the all-or-nothing rule was
   * exactly wrong for: one premise the linear reader could not take sent every other premise to the
   * sampler, so a set that is half a system and half nine assignments was answered with a hundred
   * points. `risk` is what makes it the mixed case rather than the finite one: `risk a < risk b` is
   * an order relation over the reals whose atoms are not free variables, so it belongs to neither
   * half on its own and is settled by evaluating it where `a` and `b` have been given agents.
   */
  private val entityType = TyApp("entity", Nil)

  /** `risk`, as a constant of a theory extended only far enough to name it. */
  private lazy val risk: Term =
    (for {
      withType <- reals.theory.declareTypeOperator("entity", 0)
      withRisk <- withType.declareConstant("risk", Type.fun(entityType, Real.realType))
      constant <- withRisk.constant("risk", Type.fun(entityType, Real.realType))
    } yield constant).fold(error => fail(s"could not extend the theory: ${error.message}"), identity)

  /** `risk left < risk right`, built by hand because the parser's theory has no `risk` in it. */
  private def riskBelow(left: String, right: String): Term = {
    val order = Type.fun(Real.realType, Type.fun(Real.realType, Type.Bool))

    (for {
      below <- reals.theory.constant(Real.Order, order)
      first <- Term.app(risk, Term.variable(left, entityType))
      second <- Term.app(risk, Term.variable(right, entityType))
      applied <- Term.appAll(below, List(first, second))
    } yield applied).fold(error => fail(s"could not build the term: ${error.message}"), identity)
  }

  /** The same search over a model that sizes `entity` at three, with or without a `risk` to read. */
  private def entities(interpreted: Boolean): Refutation = {
    // Distinct and increasing with the index, so the order over the three is total and a reader can
    // check the witness by reading the index off it.
    val measure: Value = Mapping(
      entityType,
      {
        case Element(_, index) => Some(Quantity(index.toDouble))
        case _ => None
      }
    )

    val sized = Model.Reals.sizing("entity", 3)
    Refutation(
      Evaluate.over(reals, if (interpreted) sized.interpreting("risk", measure) else sized)
    )
  }

  "A premise set that is half a system and half a domain" should "be decided as both" in {
    // The end of the all-or-nothing rule. `0 < x` and `x < 1` are a system of two constraints over
    // one real unknown; `risk a < risk b` is an order relation whose two atoms are applications
    // rather than free variables, so no linear point could realise it, and it is evaluated instead
    // at each of the nine assignments of `a` and `b` over the carrier. Until 2026-09-11 the third
    // premise sent the first two to the grid and the whole set came back `Survived`.
    val premises =
      Vector(proposition("0 < x:real"), proposition("x:real < 1"), riskBelow("a", "b"))

    entities(interpreted = true).satisfying(premises) match {
      case Refutation.Solved(witness, finite) =>
        info(
          s"solved at ${witness.toVector.sortBy(_._1).map { case (n, v) => s"$n=$v" }.mkString(", ")}" +
            s"; ${finite.toVector.sortBy(_._1).map { case (n, v) => s"$n=${Model.show(v)}" }.mkString(", ")}"
        )

        // The rational half is the reals and nothing else, and the point is inside the interval the
        // two constraints cut out.
        witness.keySet shouldBe Set("x")
        val point = witness("x").numerator.toDouble / witness("x").denominator.toDouble
        point should be > 0.0
        point should be < 1.0

        // The finite half names inhabitants, and the pair it names satisfies the premise it was
        // found for: `risk` is the index here, so the witness is checked by reading the indices.
        (finite.get("a"), finite.get("b")) match {
          case (Some(Element("entity", first)), Some(Element("entity", second))) =>
            first should be < second
          case other => fail(s"the entities were assigned $other")
        }

      case other => fail(s"expected the partition to decide it, got $other")
    }
  }

  it should "call a set contradictory only when every assignment is infeasible" in {
    val search = entities(interpreted = true)

    // `risk` is a function, so `risk a < risk b` and `risk b < risk a` cannot both hold at any of
    // the nine pairs, and every one of the nine was put. That is what `Contradictory` says, and why
    // it is not a count: `Survived(100)`, which is what this used to be, is the same answer this
    // search gives a set it simply failed to land on.
    search.satisfying(Vector(riskBelow("a", "b"), riskBelow("b", "a"))) should matchPattern {
      case Refutation.Contradictory(_) =>
    }

    // The other half of the same rule. The system alone has no point, so the set is contradictory
    // whatever the domain half says, and this one is decided without the enumeration being run.
    search.satisfying(
      Vector(proposition("0 < x:real"), proposition("x:real < 0"), riskBelow("a", "b"))
    ) should matchPattern { case Refutation.Contradictory(_) => }
  }

  it should "decide nothing where an assignment could not be evaluated" in {
    // The rule that keeps `Contradictory` a decision. Nothing interprets `risk` in this model, so
    // none of the nine assignments has a value and none of them is an assignment that failed. Zero
    // of nine answered, so the partition declines and the sampler says what happened: no point
    // could be asked at all, which is `NeverAsked` and never `Contradictory`.
    entities(interpreted = false)
      .satisfying(Vector(riskBelow("a", "b"), riskBelow("b", "a"))) should matchPattern {
      case Refutation.NeverAsked(_) =>
    }
  }

  "The bound on how many assignments are enumerated" should "be where the number says it is" in {
    // A bound with its two measurements, which is what this file's rule asks of any sampled or
    // enumerated count. What it buys is that the enumeration cannot run away: a model is free to
    // size a type at anything, and a premise set over four variables of a type sized at sixty
    // would otherwise be twelve million evaluations inside a search that is supposed to be cheaper
    // than the proof it screens. What it cuts is stated as a carrier size here, exactly: a set over
    // one variable of a type sized at the bound is decided, and one past it is `Refutation.Points`
    // sampled points.
    def over(size: Int): Refutation.Outcome = {
      val agents = TyApp("crowd", Nil)
      val predicate = Type.fun(agents, Type.Bool)

      val never = (for {
        withType <- reals.theory.declareTypeOperator("crowd", 0)
        withConstant <- withType.declareConstant("marked", predicate)
        constant <- withConstant.constant("marked", predicate)
      } yield constant).fold(error => fail(error.message), identity)

      val search = Refutation(
        Evaluate.over(
          reals,
          Model.Reals
            .sizing("crowd", size)
            .interpreting("marked", Mapping(agents, _ => Some(Truth(false))))
        )
      )

      val claim = Term
        .app(never, Term.variable("c", agents))
        .fold(error => fail(error.message), identity)

      search.satisfying(Vector(claim))
    }

    over(Refutation.Assignments) should matchPattern { case Refutation.Contradictory(_) => }

    // One past it, and the answer drops back to what the sampler has: `Refutation.Points` points
    // out of the `Refutation.Assignments + 1` there are, none of which was it, reported as the
    // count it is rather than as a decision.
    over(Refutation.Assignments + 1) match {
      case Refutation.Survived(asked) => asked shouldBe Refutation.Points
      case other => fail(s"expected the sampler to take it back, got $other")
    }
  }

  /* ------------------------------------------------- the model against the axioms */

  "The intended model" should "satisfy the axioms the theory holds, where it can evaluate them" in {
    // A check on `Model.Reals` rather than on the search: if `+` or `<` were interpreted wrongly,
    // one of the axioms it can evaluate would fail here and the failure would name it. Two hundred
    // points takes well under a second.
    //
    // `Double` is not the reals and addition on it is not associative, so `ADD_ASSOC` passes only
    // because equality here is the relative tolerance the screening uses everywhere. That is the
    // tolerance earning its place rather than a detail: without it the intended model would be a
    // counterexample to the theory it is a model of.
    val outcomes = Real.Laws.map { case (name, _) =>
      val statement = reals
        .law(name)
        .fold(error => fail(s"could not read the axiom $name: ${error.message}"), identity)

      name -> refutation.counterexample(Vector.empty, statement.conclusion, 200)
    }

    val broken = outcomes.collect { case (name, Refutation.Found(witness, _)) => s"$name at $witness" }
    withClue(s"false in the intended model: ${broken.mkString("; ")}\n") {
      broken shouldBe empty
    }

    // And exactly one of them cannot be asked at all, which is the honest statement of the limit:
    // completeness quantifies over a set of reals, that is a function `real -> bool`, and there is
    // no finite carrier to enumerate. Naming it here means a change that made it evaluable, or made
    // another one unevaluable, is a failure rather than a silent drift.
    val silent = outcomes.collect { case (name, _: Refutation.NeverAsked) => name }
    silent shouldBe Vector("COMPLETENESS")
  }
}
