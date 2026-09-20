package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.scan.Comments

import java.nio.file.{Files, Path, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import scala.jdk.CollectionConverters.*
import garden.xeno.symbolum.{Dsl, Num, Var}
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Rational, Real}

/**
 * The next step named for every refusal a caller can receive.
 *
 * Exhaustiveness is the compiler's job: every mapping in `Remedy` is a total match over a sealed
 * type, so a case added without a next step does not build. What a compiler cannot check is whether
 * the next step is the right one, and in particular whether two refusals that imply opposite moves
 * come back as the same move. That is what this file asserts, refusal by refusal.
 *
 * The assertions are about which remedy, never about the wording. A message is for a person and is
 * allowed to be improved; pinning it here would make an improvement a test failure and teach
 * whoever met it to relax the assertion.
 */
class RemedySpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val reals = Real.standard
  private val realType: Type = TyApp(Real.TypeName, Nil)
  // Annotated, because a bare name carries no type and this theory's reader refuses to guess one.
  // `NotationRoundTripSpec` pins that; here it is only how a variable is obtained.
  private val x = force(reals.term("x:real"))

  /* --------------------------------------------- the distinction that matters most */

  "A refusal about the input and a refusal about a defect" should "not be the same next step" in {
    // A caller answers the first by asking something else and cannot answer the second at all.
    val absent = Remedy.of(FromLogic(FromKernel(UnknownConstant("cos"))))
    val defect = Remedy.of(FromLogic(FromKernel(TermsDiffer(x, x, "eqMp"))))

    absent shouldBe a[ExtendTheTheory]
    defect shouldBe a[ReportADefect]
  }

  it should "tell a session that rephrasing will not help" in {
    // The whole point of ReportADefect: nothing the caller writes changes the answer, so a session
    // that keeps rewriting its question is wasting every attempt.
    val remedy = Remedy.of(FromLogic(FromKernel(VariableIsFreeInHypotheses(x, List(x)))))

    remedy.message should include("defect")
    // The blocking hypothesis is named and not counted. A caller reading this has to know WHICH
    // hypothesis mentions the variable, because a recursion stated at one length is repaired by
    // restating it universally and an assumption about one value is repaired by discharging it.
    remedy.message should include(reals.show(x))
  }

  /* ------------------------------------------------------------ tactic refusals */

  "A tactic refusal" should "send an expression outside the fragment to the theory" in {
    Remedy.of(OutsideFragment(Dsl.cos(Var("x")), "no cosine")) shouldBe a[ExtendTheTheory]
  }

  it should "name the budget that a large numeral reached" in {
    Remedy.of(BeyondBudget("999999999999999 * 2", BigInt("999999999999999"))) match {
      case RaiseALimit(limit, _) => limit should include("NumeralBudget")
      case other => fail(s"expected a limit to raise, got $other")
    }
  }

  it should "distinguish a rewriter that ran out from a claim that did not hold" in {
    // The pair this file exists for. Both are `NotCertified` and both print as "could not certify";
    // one is answered by raising a limit and the other by a person deciding the claim is false.
    val ranOut = Remedy.of(NotCertified("x + 1 = 1 + x", NotNormalised(x)))
    val didNotHold = Remedy.of(NotCertified("x + 1 = 2 + x", NotOfForm("an equation", x)))

    ranOut shouldBe a[RaiseALimit]
    didNotHold shouldBe a[APersonLooks]
  }

  it should "separate a price to accept from a hypothesis a rule was never given" in {
    // Both name something to assume and the two moves are different. `MissingHypothesis` says a
    // rule was handed the wrong hypothesis list, and supplying it makes the same call succeed.
    // `ProvableOnlyUnder` says the goal as written is not a theorem: accepting the condition
    // changes what is claimed, because the variable it names can no longer be generalised.
    Remedy.of(ProvableOnlyUnder(x, Vector(x))) shouldBe a[AcceptTheConditions]
    Remedy.of(FromLogic(MissingHypothesis(x, "eliminating an existential"))) shouldBe a[AssumeMore]
  }

  it should "report an illegible term as a defect rather than as a question to rephrase" in {
    Remedy.of(NotLegible(x, None)) shouldBe a[ReportADefect]
    Remedy.of(NotLegible(x, Some(x))) shouldBe a[ReportADefect]
  }

  /* ------------------------------------------ the notation boundary, by the case that crossed it */

  /**
   * The atoms of a propositional countermodel, written in the reader's notation.
   *
   * The measurement that opened the card: `!x:real. 1 < x ==> 0 < x \/ x = 99` came back telling
   * whoever wrote `99` that it fails at `(x = (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 1)))))))`. It
   * happened because `Propositional` is in `modules/logic`, which has no notation to render with,
   * and it rendered anyway, into the prose of a `NotOfForm` where nothing downstream could reach
   * the term again.
   *
   * Both directions are asserted and the second is what makes the first worth anything. A message
   * that had simply stopped naming the atom would pass "does not say BIT1" while telling the reader
   * less than before, so the same refusal is put to the mapping **without** a theory, where the
   * kernel's printer is all there is and the encoding is the right answer.
   */
  "A propositional countermodel" should "name its atoms in the theory's notation" in {
    val ninetyNine = force(reals.term("x:real = 99"))
    val positive = force(reals.term("0:real < x"))
    val goal = force(reals.term("!x:real. 1 < x ==> 0 < x \\/ x = 99"))
    val refusal = SkeletonFailsAt(goal, Vector(positive -> false, ninetyNine -> false))

    val written = Remedy.of(reals, refusal).message
    withClue(s"with the theory: $written\n") {
      written should include("99")
      written should not include "BIT1"
    }
  }

  it should "fall back to the kernel's printer where the caller has no theory" in {
    val ninetyNine = force(reals.term("x:real = 99"))
    val refusal = SkeletonFailsAt(ninetyNine, Vector(ninetyNine -> false))

    val written = Remedy.of(refusal).message
    withClue(s"without a theory: $written\n") {
      // The encoding, and it is the right answer here: nobody said which notation to use. This is
      // what says the assertion above measured the theory and not the atom having been dropped.
      written should include("BIT1")
    }
  }

  it should "send a countermodel to a restatement and not to a decision" in {
    // `DoesNotFollow` goes to `Settled`, because a linear search that finished has an answer that
    // no rephrasing changes. This one is the opposite: the atoms are uninterpreted, so restating
    // the goal is exactly the move that can change the answer, and `PropositionalSpec` holds the
    // goal that is true and fails here.
    val atom = force(reals.term("0:real < x"))
    Remedy.of(reals, SkeletonFailsAt(atom, Vector(atom -> false))) shouldBe a[RestateTheProblem]
  }

  /**
   * The agreement `Remedy`'s own comment claims, asserted rather than described.
   *
   * `Discovery.why` sorts a refusal into four situations for the screening loop and `Remedy.of`
   * sorts the same refusal into a next step. They are two classifications of one thing, written in
   * two files, and nothing but this stops them drifting apart into two answers a session would have
   * to reconcile.
   */
  "Remedy and Discovery.why" should "agree about every refusal Discovery can produce" in {
    // A kernel `UnknownConstant` is deliberately not here, and finding out why is what this
    // assertion was worth. `Remedy` reads it as a constant to declare and `Discovery.why` reads it
    // as a lead for a person, and they do not have to agree because `Discovery` cannot produce it:
    // `Translate` refuses an expression the theory has no constant for, by name, before any term
    // reaches the kernel. Adding it here would assert an agreement about a path that does not exist,
    // and the repair would have been to widen `Discovery.why` for a case it never sees.
    val refusals: Vector[TacticError] = Vector(
      OutsideFragment(Dsl.cos(Var("x")), "no cosine"),
      NotCertified("x = x", NotNormalised(x)),
      NotCertified("x = x", NotOfForm("an equation", x)),
      FromLogic(NotOfForm("an equation", x))
    )

    refusals.foreach { refusal =>
      val expected = Discovery.why(refusal) match {
        case Discovery.Why.OutsideTheFragment => "extend"
        case Discovery.Why.BeyondTheBudget => "limit"
        case Discovery.Why.RewriterRanOut => "limit"
        case Discovery.Why.NotProvableHere => "other"
      }

      val found = Remedy.of(refusal) match {
        case _: ExtendTheTheory => "extend"
        case _: RaiseALimit => "limit"
        case _ => "other"
      }

      withClue(s"$refusal: ") { found shouldBe expected }
    }
  }

  /* ------------------------------------------------------- the seven model answers */

  "The model search's seven outcomes" should "not collapse into fewer next steps" in {
    // `Refutation` keeps seven answers apart because collapsing any two turns "I could not ask"
    // into "I asked and it was fine". The three that are not answers must stay three here too.
    val survived = Remedy.of(Refutation.Survived(300))
    val neverAsked = Remedy.of(Refutation.NeverAsked(100))
    val undecided = Remedy.of(Refutation.Undecided("a premise forces an equality between reals"))

    survived shouldBe a[APersonLooks]
    neverAsked shouldBe a[InterpretMore]
    undecided shouldBe a[AskDifferently]

    Set(survived, neverAsked, undecided) should have size 3
  }

  it should "read a contradictory premise set as something to restate, not as an answer" in {
    // The one outcome that is a decision and still demands action: everything follows from
    // premises that cannot hold, so reporting it as settled would hide the defect in the question.
    Remedy.of(Refutation.Contradictory(3)) shouldBe a[RestateTheProblem]
    Remedy.of(Refutation.NoCounterexample(3)) shouldBe a[Settled]
  }

  it should "settle a witness whether it was sampled or solved" in {
    Remedy.of(Refutation.Found(Map("x" -> Model.Quantity(1.5)), 12)) shouldBe a[Settled]
    Remedy.of(Refutation.Solved(Map("x" -> Rational(1, 2)))) shouldBe a[Settled]
  }

  /* ------------------------------------ the two procedures that decide without certifying */

  "A decision over the quantifiers" should "be settled without being readable as a proof" in {
    // `Quantified` eliminates the quantifiers over a model of the reals and builds no theorem, so
    // its two decisions are answers that asking again cannot change. The wording is asserted here
    // rather than only the remedy, against this file's own rule and for one reason: a message that
    // stopped saying so would be offering a session a proof of something nothing here has proved,
    // which is the single claim this arm must never make.
    val holds = Remedy.of(Quantified.Holds)
    val fails = Remedy.of(Quantified.Fails)

    holds shouldBe a[Settled]
    fails shouldBe a[Settled]
    Set(holds, fails) should have size 2
    holds.message should include("not certified")
    fails.message should include("not certified")
  }

  it should "send what it will not decide to another address, carrying the reason it gave" in {
    // A refusal from a real run rather than a constructed one. A product of two unknowns is the
    // atom the linear reading holds opaque, which `QuantifiedSpec` pins; what matters here is that
    // the reason travels into the remedy, since the reason is what names the other address.
    val refused = force(Quantified.standard.decide("?x:real. !y:real. x * y = 0"))

    Remedy.of(refused) match {
      case AskDifferently(what) => what should include("atom")
      case other => fail(s"expected another address, got $other")
    }
  }

  "A screened candidate" should "keep its disagreement, its agreement and its two absences apart" in {
    // Four real runs of the screen, and what is asserted is that the four answers do not collapse.
    // The candidate is the variable itself throughout, so what changes is only how many steps it is
    // screened against and where: at one step it disagrees with iteration, at none it agrees, past
    // `CollatzScreen.Exact` the comparison is one a double cannot make, and a candidate written in
    // a variable the screen does not substitute has no value at all. The last two are absences and
    // neither is a disagreement, which is the distinction `Refutation` keeps seven outcomes for.
    val n = Var("n")

    val disagrees = Remedy.of(CollatzScreen.screen(n, 1, Vector(BigInt(3))))
    val agreed = Remedy.of(CollatzScreen.screen(n, 0, Vector(BigInt(3))))
    val notExact = Remedy.of(CollatzScreen.screen(n, 0, Vector(CollatzScreen.Exact * 4)))
    val notEvaluable = Remedy.of(CollatzScreen.screen(Var("m"), 1, Vector(BigInt(3))))

    disagrees shouldBe a[Settled]
    agreed shouldBe a[APersonLooks]
    notExact shouldBe a[RestateTheProblem]
    notEvaluable shouldBe a[InterpretMore]

    Set(disagrees, agreed, notExact, notEvaluable) should have size 4
  }

  it should "report agreement as evidence, with how many points agreed" in {
    // Agreement in numbers is reported as agreement in numbers. The count is what such an answer is
    // worth, so it is in the message rather than only in the verdict it came from: four points and
    // four hundred are the same remedy and not the same evidence.
    Remedy.of(CollatzScreen.Agreed(400)).message should include("400")
  }

  // The two counters of this file that reach one, and BOTH DIRECTIONS IN ONE TEST for the reason
  // `LedgerSpec` and `CostSpec` give at the same shape: the condition is one shared helper, so a
  // wrong comparison inside it turns every count on every page singular and a test written on the
  // plural alone reports that as repaired.
  //
  // The second of the two is not in the census the card of 2026-09-18 carried and was found by
  // reading the range rather than the site: `Relation.NotCredible` is produced only when
  // `confirmed < Relation.Confirmation`, which is ten, and `confirmed` is `max(0, ...)`, so the
  // number this message prints lives in 0 to 9 and one is inside it. That is what separates it
  // from `Collatz`'s `${Rules.size} clauses`, where the count is the constant eleven.
  "The two digit counts of this file" should "take the singular at one and the plural elsewhere" in {
    val separated = (agreement: Int) =>
      Remedy.of(Discovery.Separated(Var("x"), Var("y"), Map("x" -> BigDecimal(2)), agreement)).message

    separated(1) should include("agreed to 1 digit and no further")
    separated(40) should include("agreed to 40 digits and no further")

    val notCredible = (confirmed: Int) =>
      Remedy.of(Algebraic.Outcome.NotCredible(Vector(BigInt(3), BigInt(5)), confirmed, 4)).message

    // The colon is part of the assertion and not decoration: `RaiseALimit` puts the limit
    // and the reason in one line, so a bare `include("more than 1 digit")` passes on
    // "more than 1 digits" as well. This test was seen red on exactly that.
    notCredible(1) should include("more than 1 digit:")
    notCredible(9) should include("more than 9 digits:")
    // Zero takes the plural, and here it is the answer a reader meets most: nothing the precision
    // supported at all.
    notCredible(0) should include("more than 0 digits:")
  }

  /* ------------------------------------------------------------ the ledger's table */

  "Every ledger verdict" should "carry a next step" in {
    // This replaced the table in a comment, so the assertion is that the replacement is total:
    // eight verdicts, eight remedies, and the three that mean "never ask again" are the three the
    // comment names.
    //
    // Three since 2026-09-11, when `DecidedNotCertified` landed. It joins the two that were there
    // because the thing to do about it is know it rather than ask again: it holds, nothing here has
    // a theorem for it, and `docs/adr/0005` is why those are not the same sentence.
    val remedies = Ledger.Verdict.values.toVector.map(Remedy.of)

    remedies should have size 8
    Remedy.of(Ledger.Verdict.Proved) shouldBe a[Settled]
    Remedy.of(Ledger.Verdict.Disproved) shouldBe a[Settled]
    Remedy.of(Ledger.Verdict.DecidedNotCertified) shouldBe a[Settled]
    remedies.count(_.isInstanceOf[Settled]) shouldBe 3

    // And the one that must not read as a proof: its remedy says what settled it, and the word
    // "certif" appears in it only as a denial.
    Remedy.of(Ledger.Verdict.DecidedNotCertified).message should include("certifies nothing")
  }

  /* -------------------------------------------------------------- the logic layer */

  "A refusal from the logic" should "tell a caller to assume rather than to restate" in {
    // `LogicError` argues this distinction where it is raised; here it survives the mapping.
    Remedy.of(FromLogic(MissingHypothesis(x, "eliminating an existential"))) shouldBe a[AssumeMore]
    Remedy.of(FromLogic(NotOfForm("an implication", x))) shouldBe a[RestateTheProblem]
  }

  "Every outcome of the closed-form search" should "send a reader somewhere different" in {
    // Four answers and four moves. The one that must not be `Settled` is the fit that was not
    // proved: it is the screen having passed something the kernel then refused, which is the whole
    // reason the screen is not the answer.
    val family = Family.standard

    Remedy.of(family.of("\\i:num. real_of_num i")) shouldBe a[Settled]
    Remedy.of(family.of("\\i:num. Power 2 i")) shouldBe a[AskDifferently]
    Remedy.of(family.of("\\i:num. inv (real_of_num i)")) shouldBe a[RestateTheProblem]

    Remedy.of(
      Family.Outcome.NotCertified(force(reals.proposition("!x:real. 0 < x")), "no certificate")
    ) shouldBe a[APersonLooks]
  }

  it should "tell a bound that stopped a search from a claim that does not follow" in {
    // The pair `NotNormalised` already makes one procedure over, and the reason both exist: "I
    // stopped" and "it does not hold" imply opposite next moves, and until 2026-09-11 LINARITH
    // reported the first as the second. The limit is named because there is more than one of them.
    val goal = force(reals.proposition("!x:real. 0 < x"))

    Remedy.of(reals, FromLogic(BoundReached("Linarith.Facts", 76, 48, goal))) match {
      case RaiseALimit(limit, reached) =>
        limit shouldBe "Linarith.Facts"
        reached should include("76")
        reached should include("48")
      case other => fail(s"expected a limit to raise, got $other")
    }

    Remedy.of(reals, FromLogic(NotNormalised(goal))) shouldBe a[RaiseALimit]
  }

  it should "carry the position of a syntax error and admit having none for a type error" in {
    Remedy.of(FromLogic(SyntaxError("expected a term", 7))) match {
      case RepairTheText(_, position) => position shouldBe Some(7)
      case other => fail(s"expected a repair, got $other")
    }

    Remedy.of(FromLogic(TypeError("the type of x is undetermined"))) match {
      case RepairTheText(_, position) => position shouldBe None
      case other => fail(s"expected a repair, got $other")
    }
  }


  /* ----------------------------------- the one remedy whose sentence nothing was reading */

  "The remedy for a symbol `num` does not share" should "name the constant and why it differs" in {
    // Nothing in this file reached `WriteTheConstant` at all until 2026-09-16, which is how its
    // sentence went false without anything failing. `Counterpart` is thoroughly tested and builds
    // the per-symbol instructions; the sentence that frames them lives here and no assertion read
    // it. So this case exists to reach it, and the one below to say what it must not claim.
    val refusal = TypeError("real and num cannot be the same type")
    val remedy = Remedy.spelling(reals, "!x:num. !y:num. x - y = x", refusal)

    remedy match {
      case Some(found: WriteTheConstant) =>
        found.message should include(garden.xeno.symbolum.theories.Peano.Subtraction)
        // The caveat is the half that makes the advice safe rather than merely actionable: the
        // counterpart is not the same function, and a reader told to write it without being told
        // that has been handed a different claim.
        found.message should include("truncates at zero")
      case other => fail(s"expected a spelling remedy, got $other")
    }
  }

  it should "not tell a reader that `num` has no operator symbols, which stopped being true" in {
    // `docs/adr/0018` gave `num` `+`, `*`, `<` and `<=`. The sentence here went on saying "num has
    // no OPERATOR notation of its own", so a reader who wrote `x + y - y = x` was told that in a
    // claim whose `+` had just read, beside advice that was itself correct.
    //
    // What this assertion is and is not: a tripwire on the retired wording, not a proof that the
    // replacement is true. What would make the replacement false is a symbol moving between the
    // shared set and the table, and `CounterpartSpec` is what asserts that partition, in both
    // directions. This catches the cheaper failure, which is the sentence being restored by
    // somebody reverting a wording change without the record in front of them.
    val remedy = Remedy.spelling(
      reals,
      "!x:num. !y:num. x + y - y = x",
      TypeError("real and num cannot be the same type")
    )

    val message = remedy.map(_.message).getOrElse(fail("expected a spelling remedy"))
    message should not include "has no OPERATOR notation"

    // And the pairing that gives the assertion something to be about: the advice is still only
    // ever about the symbol that refuses. `+` is in the text above and must not be proposed for
    // rewriting, because it reads.
    message should not include garden.xeno.symbolum.theories.Peano.Addition
  }

  /* ------------------------------------------------- the census, made executable */

  /**
   * Every constructor of every refusal a caller can receive, put through the mapping.
   *
   * The compiler already guarantees that each match is total. What it cannot guarantee is that a
   * branch was ever run, and an unrun branch is a next step nobody has read: the message is built
   * from the refusal's own fields, so a branch that names the wrong field is wrong in exactly the
   * way a session would notice and a type checker would not.
   *
   * So this is the census as a list. It used to say that its value was having to be extended by
   * hand when a refusal is added; on 2026-09-11 that turned out to be its defect rather than its
   * value. `BoundReached` and `NotEqualTo` had been `LogicError` cases with `Remedy` arms for as
   * long as they had existed and were in neither list, so two branches had never been run. The
   * scan below now reads the three refusal sets off their own sources and fails both on a case
   * missing here and on a name here that no longer exists.
   */
  private val everyKernelRefusal: Vector[KernelError] = Vector(
    TypeMismatch(realType, Type.Bool, "an application"),
    NotAFunction(realType),
    NotLocallyClosed(x),
    NotAnEquation(x),
    NotABetaRedex(x),
    NotAProposition(x, realType),
    TermsDiffer(x, x, "eqMp"),
    UnknownConstant("cos"),
    UnknownTypeOperator("nat"),
    ArityMismatch("fun", 2, 1),
    NotAnInstance("=", Type.fun(realType, realType), realType),
    AlreadyDeclared("+"),
    VariableIsFreeInHypotheses(x, List(x)),
    DefinitionIsNotClosed(Set(x)),
    TypeVariablesEscape(Set("A")),
    TheoremHasHypotheses(List(x)),
    NotAnApplication(x)
  )

  private val everyLogicRefusal: Vector[LogicError] =
    everyKernelRefusal.map(FromKernel.apply) ++ Vector(
      NotOfForm("an implication", x),
      DoesNotFollow(x, "LINARITH"),
      // Two atoms and not one, because the remedy joins them and a single pair would run a
      // `mkString` over a vector of length one without ever exercising the separator.
      SkeletonFailsAt(x, Vector(x -> true, Term.variable("y", realType) -> false)),
      NotNormalised(x),
      BoundReached("Linarith.Facts", 76, 48, x),
      NotEqualTo(x, Term.variable("y", realType)),
      SyntaxError("expected a term", 3),
      TypeError("undetermined"),
      MissingDefinition("le"),
      EscapingVariable(Term.variable("w", realType), "the conclusion"),
      MissingHypothesis(x, "eliminating an existential"),
      Undetermined(Term.variable("y", realType)),
      PartialInstance(5, 4, x),
      // The driver below the reals, which holds no closer and says so. It is in the census as a
      // `ReportADefect` rather than a limit: the two refusals above it are procedures that looked
      // and could not, and this one is a driver built with nothing to look with, so no restatement
      // of the goal and no raised limit reaches it.
      NoCloser(x, "the induction driver over num"),
      // Both arms of the one refusal that carries another: a caller's procedure that refused, and a
      // caller's procedure that returned something else. The remedy is read off the inner reason, so
      // the branch is only worth running when the two inner reasons take different arms there.
      InstanceRefused(6, x, NotNormalised(x)),
      InstanceRefused(0, x, NotOfForm("a proof of the instance at 0", x))
    )

  private val everyTacticRefusal: Vector[TacticError] =
    everyLogicRefusal.map(FromLogic.apply) ++ Vector(
      OutsideFragment(Dsl.cos(Var("x")), "no cosine"),
      NotCertified("x = x", NotNormalised(x)),
      NotCertified("x = x", NotOfForm("an equation", x)),
      BeyondBudget("2 * 2", BigInt(2)),
      NotLegible(x, None),
      NotLegible(x, Some(x)),
      ProvableOnlyUnder(x, Vector(x))
    )

  "Every refusal in the census" should "produce a next step that says something" in {
    everyTacticRefusal.foreach { refusal =>
      withClue(s"$refusal: ") {
        val message = Remedy.of(refusal).message

        message should not be empty
        // The refusal's own message is not the next step, and a remedy that only echoed it would
        // be the prose this file replaced.
        message should not be refusal.message
      }
    }
  }

  it should "cover the kernel's whole error set without two of them meaning the same thing" in {
    // Seventeen kernel refusals, and they must not all collapse into one move: two of them name
    // something absent and the theory gains it, the rest split between an ill-typed input and a
    // defect above. The last two arrived with `defineType` on 2026-09-10 and are restated rather
    // than reported, because a caller defining a type chose the witness and can choose another.
    val remedies = everyKernelRefusal.map(Remedy.of)

    remedies should have size 17
    remedies.count(_.isInstanceOf[ExtendTheTheory]) shouldBe 2
    remedies.count(_.isInstanceOf[ReportADefect]) shouldBe 7
    remedies.count(_.isInstanceOf[RestateTheProblem]) shouldBe 8
  }

  "Every model outcome and every verdict" should "produce a next step that says something" in {
    val outcomes: Vector[Refutation.Outcome] = Vector(
      Refutation.Found(Map("x" -> Model.Quantity(1.0)), 4),
      Refutation.Survived(50),
      Refutation.NeverAsked(50),
      Refutation.Solved(Map("x" -> Rational(3, 4))),
      Refutation.Contradictory(2),
      Refutation.NoCounterexample(2),
      Refutation.Undecided("an equality between reals")
    )

    // Every case of the two procedures that decide without certifying. Neither type has a `values`
    // of its own, so a case nobody mapped is caught by the compiler and a whole type nobody mapped
    // by the scan below; what is caught here is a branch that was never run, which is a next step
    // nobody has read.
    val propositional: Vector[Consistency.Verdict] = Vector(
      Consistency.Verdict.Contradictory,
      Consistency.Verdict.NotContradictory(Vector("p" -> true)),
      Consistency.Verdict.Refused("a statement with no quantifier in it")
    )
    propositional.foreach(verdict => Remedy.of(verdict).message should not be empty)

    val decided: Vector[Quantified.Verdict] =
      Vector(Quantified.Holds, Quantified.Fails, Quantified.Refused("a linear statement"))

    val screened: Vector[CollatzScreen.Verdict] = Vector(
      CollatzScreen.Disagrees(BigInt(3), garden.xeno.symbolum.CollatzSeries.iterate(BigInt(3), 1), BigInt(3)),
      CollatzScreen.Agreed(16),
      CollatzScreen.NotExact(CollatzScreen.Exact * 4, 3.6e16),
      CollatzScreen.NotEvaluable(BigInt(3))
    )

    outcomes should have size 7
    outcomes.foreach(outcome => Remedy.of(outcome).message should not be empty)
    Ledger.Verdict.values.foreach(verdict => Remedy.of(verdict).message should not be empty)
    decided.foreach(verdict => Remedy.of(verdict).message should not be empty)
    screened.foreach(verdict => Remedy.of(verdict).message should not be empty)
  }

  "A screening outcome" should "carry the next step of the refusal underneath it" in {
    // `Discovery.Outcome` defers rather than re-deciding, which is what makes the agreement above
    // assertable at all. Here the three shapes are exercised, proof included.
    val theorem = force(garden.xeno.symbolum.theories.Order.standard.zeroLessOne)
    val left = Var("x")
    val right = Var("x")

    Remedy.of(Discovery.Proved(left, right, theorem)) shouldBe a[Settled]
    Remedy.of(Discovery.Disproved(left, Num(1), Map("x" -> 0.5), 0.5)) shouldBe a[Settled]
    Remedy.of(
      Discovery.Unsettled(left, right, Discovery.Why.RewriterRanOut, NotCertified("x = x", NotNormalised(x)), 100)
    ) shouldBe a[RaiseALimit]
  }

  /* -------------------------------------------------------- what a real run produces */

  "A refusal taken from a real run" should "arrive with a next step" in {
    // Not a constructed error: `Translate` is asked for something the theory has no constant for,
    // and what comes back is what a session would receive.
    val refused = Oracle.standard.certifyIdentity(Dsl.cos(Var("x")), Dsl.cos(Var("x")))

    refused match {
      case Left(error) => Remedy.of(error) shouldBe a[ExtendTheTheory]
      case Right(theorem) => fail(s"expected a refusal, got ${theorem.conclusion}")
    }
  }

  it should "arrive with a next step when a goal is written in the wrong shape" in {
    // `x < y` stood here as the example of a wrong shape and it is not one: it is a goal LINARITH
    // reads perfectly well, with no hypotheses, which it searched to the end of and did not find.
    // Being told to restate it was the conflation `DoesNotFollow` exists to end, and the goal moved
    // to the test below. A wrong shape is one the procedure cannot read at all.
    val refused = garden.xeno.symbolum.theories.Linarith.standard.prove("!p:bool. p ==> p")

    refused match {
      case Left(error) => Remedy.of(FromLogic(error)) should not be a[Settled]
      case Right(theorem) => fail(s"expected a refusal, got ${theorem.conclusion}")
    }
  }

  it should "say nothing is left to try when the procedure decided, which is not the same" in {
    garden.xeno.symbolum.theories.Linarith.standard.prove("x < y") match {
      case Left(error) => Remedy.of(FromLogic(error)) shouldBe a[Settled]
      case Right(theorem) => fail(s"expected a refusal, got ${theorem.conclusion}")
    }
  }

  /* ------------------------------------------- the boundary the compiler cannot check */

  /**
   * The verdicts this module declares that `Remedy` deliberately does not map, and why not.
   *
   * An entry is a claim that a caller meeting this type is not meeting a refusal. The scan below
   * fails on an entry naming something no longer declared, so an excuse cannot outlive what it
   * excuses.
   */
  private val OutsideTheCensus: Vector[String] = Vector(
    // The four situations `Discovery` sorts a refusal into for the screening loop. A caller never
    // receives one: `of(Discovery.Outcome)` defers to the refusal underneath rather than deciding
    // again from `Why`, which is what makes the agreement asserted above assertable at all.
    "Discovery.Why",

    // What a term denotes in a model. A witness is made of these, and `point` writes a witness out
    // whatever its values are, so none of them is a question put to a caller.
    "Model.Value",

    // Which procedure a goal's shape belongs to, answered before anything is attempted. What comes
    // back from attempting it is a `TacticError`, and that is mapped.
    "Prove.Address",

    // Which procedures a prover assembled. It sits beside `Prove.Address` and the reason above is
    // NOT the reason here, which is worth the extra lines because this list is what somebody reads
    // when deciding whether a new enumeration belongs on it. An address is received: a goal is
    // sent somewhere and a `TacticError` comes back, mapped. A `Search` is received by nobody.
    //
    // Measured rather than argued, because the two enumerations are one word apart and excusing
    // the wrong one silences a gate that was right: `Prove.searches` is the only site in the
    // repository that produces a `Search`, its callers are three assertions in
    // `DocumentationSpec`, nothing under `src/main` outside `Prove.scala` names the type at all,
    // and no case of `TacticError` carries one. So what this entry claims is the strong half of
    // what the paragraph above this list asks for: not that a caller meeting this type is not
    // meeting a refusal, but that no caller meets it.
    "Prove.Search",

    // What a proof that SUCCEEDED came back as. Both its cases carry a theorem, so neither is a
    // refusal, and the refusal a caller meets when nothing is proved is still the `TacticError`
    // the address chose, which is mapped.
    //
    // It is worth more than one line because `CutShort` is the one case on this list that reads
    // like a complaint: it names a search and the depth it stopped at, which is the shape of
    // `BoundReached`, and that one IS mapped. The two are a bound read in opposite directions.
    // `BoundReached` says the bound is why nothing came back and a caller who raises it may get a
    // theorem; `CutShort` says a theorem came back and a bound was passed on the way, so the
    // classical route paid for it. There is no next step to offer: the goal is settled, and what
    // the caller does with the price is read it.
    "Prove.Outcome",

    // Which of its five questions a report answers. `Cost.render` already sends the refusal the
    // report carries through `Remedy`, and reads the outcome only for the label above it.
    "Cost.Outcome",

    // A premise a proof rested on, cited or not. Both cases are answers: it is a reading of a
    // proof rather than a refusal.
    "Provenance.Premise",

    // Which mutation made a proposal. It says where a candidate came from, not what happened to it,
    // and nothing a caller receives carries it as a refusal: `Novelty.Standing` is what a reader of
    // a proposal acts on, and that one is named above for its own reason.
    "Propose.Source",

    // Which type an expression's variables stand at. It is an argument a caller supplies rather
    // than an answer it receives, and what comes back from translating at a target it cannot meet
    // is an `OutsideFragment`, which is mapped.
    "Translate.Target",

    // What a user wrote in a cell. An input, for the reason `Translate.Target` is one: a caller
    // supplies it and never receives it. A line that did not read comes back as `Session.Outcome`,
    // which is the entry below.
    "Session.Command",

    // What a command did, and the reason it is here is the reason `Cost.Outcome` is. Its refusal
    // case carries the next step already, because `Session` asks `Remedy` at the three points where
    // a refusal is still a value: `Remedy.of` for a `LogicError`, a `TacticError` and a
    // `KernelError`. Deciding again from the outcome would be a second mapping of one thing.
    //
    // This entry is only true while that holds, and it did not hold when the file was first
    // written: every refusal was turned into its message where it arrived, so a page could not
    // offer what `Ask` already offers for the same mistake. This assertion is what found that.
    "Session.Outcome"
  )

  "Every verdict this module declares" should "be mapped by Remedy or named as an exception" in {
    // What this probes. Every mapping in `Remedy` is a total match, so the compiler catches a new
    // *case* of a type already mapped and can catch nothing about a new *type*: `Quantified` and
    // `CollatzScreen` landed on 2026-09-10 with a verdict each, every match stayed exhaustive, and
    // a caller could receive a refusal with no next step attached. So the population is read from
    // the sources rather than listed here, and a type leaves it only by being named above.
    //
    // Comments come off both sides first, for the reason `Sources.code` exists one module over: a
    // file that explains why it does not map something has to name it in order to say so, and
    // reading that prose as code would make every such explanation into the thing it warns about.
    //
    // What it does not cover: the refusal sets of `modules/logic` and `modules/kernel`, which
    // reach a caller through `TacticError` and whose cases the compiler does guard, and anything
    // private, which no caller can receive.
    val declared = tacticsSources.flatMap(verdictsDeclaredIn)
    val mapped = withoutComments(Files.readString(locate(RemedyPath)))

    val unmapped = declared.filterNot(OutsideTheCensus.contains).filterNot(mapped.contains)
    withClue(s"declared in this module and mapped nowhere: ${unmapped.mkString(", ")}\n") {
      unmapped shouldBe empty
    }

    val stale = OutsideTheCensus.filterNot(declared.contains)
    withClue(s"named as an exception and no longer declared: ${stale.mkString(", ")}\n") {
      stale shouldBe empty
    }

    // And it is not passing because it read nothing: the two types it was written for are in it.
    declared should contain("Quantified.Verdict")
    declared should contain("CollatzScreen.Verdict")
  }

  /**
   * The three refusal sets, each against the source that declares it.
   *
   * The census above is a list of values, and a list of values is the one thing the compiler cannot
   * check against the type it enumerates. This closes that: every `final case class` in each of the
   * three files is a case a caller can receive, so the file is the population and the census has to
   * match it exactly.
   *
   * **Both directions, which is the half that was missing.** A case declared and not enumerated is
   * a `Remedy` branch nobody has run; a name enumerated and no longer declared would not compile,
   * but a name enumerated *twice* while another is absent would, and the sets catch that too.
   *
   * `modules/checker` is not here and cannot be: `Check.Verdict` is outside `Remedy` by the
   * dependency direction, and `Remedy`'s own docstring carries the argument.
   */
  private val RefusalSources: Vector[(String, String)] = Vector(
    "KernelError" -> "modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/KernelError.scala",
    "LogicError" -> "modules/logic/src/main/scala/garden/xeno/symbolum/logic/LogicError.scala",
    "TacticError" -> "modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/TacticError.scala"
  )

  "The census" should "hold exactly the refusals the three error types declare" in {
    val enumerated: Map[String, Set[String]] = Map(
      "KernelError" -> everyKernelRefusal.map(_.getClass.getSimpleName).toSet,
      "LogicError" -> everyLogicRefusal.map(_.getClass.getSimpleName).toSet,
      "TacticError" -> everyTacticRefusal.map(_.getClass.getSimpleName).toSet
    )

    RefusalSources.foreach { case (name, path) =>
      val declared = refusalsDeclaredIn(locate(path))

      withClue(s"$name: declared and never put through Remedy: ") {
        declared.diff(enumerated(name)) shouldBe empty
      }
      withClue(s"$name: in the census and no longer declared: ") {
        enumerated(name).diff(declared) shouldBe empty
      }
      // And it is not passing because the scan read nothing.
      declared.size should be > 3
    }
  }

  /**
   * The refusal cases a file declares.
   *
   * Every `final case class` in one of the three files is a case of that file's sealed trait; none
   * of them declares anything else, and a file that started to would make this scan wrong rather
   * than make it fail, which is why the three paths are named one by one instead of walked.
   */
  private def refusalsDeclaredIn(path: Path): Set[String] = {
    val declares = """^final case class ([A-Za-z][A-Za-z0-9]*)""".r

    withoutComments(Files.readString(path)).linesIterator
      .flatMap(line => declares.findFirstMatchIn(line).map(_.group(1)))
      .toSet
  }

  private val RemedyPath = "modules/tactics/src/main/scala/garden/xeno/symbolum/tactics/Remedy.scala"

  /** Every Scala source of this module, from wherever the tests were started. */
  private def tacticsSources: Vector[Path] =
    Files
      .walk(locate("modules/tactics/src/main"))
      .iterator
      .asScala
      .toVector
      .filter(path => Files.isRegularFile(path) && path.toString.endsWith(".scala"))
      .sortBy(_.toString)

  /**
   * The sealed traits and enums a file declares, qualified the way `Remedy` has to name them.
   *
   * A nested declaration comes back as `Owner.Name`, the owner being the last top-level `object`,
   * `class` or `trait` above it, because the qualified name is what a mapping in another file
   * writes and the bare one would match `Ledger.Verdict` for `Quantified`'s. A line that starts
   * with a modifier matches neither pattern, which is how `Abduce`'s own verdict stays out: it is
   * private, so no caller can receive it.
   */
  private def verdictsDeclaredIn(path: Path): Vector[String] = {
    val declares =
      """^\s*(?:sealed\s+trait|sealed\s+abstract\s+class|enum)\s+([A-Za-z][A-Za-z0-9]*)""".r
    val encloses =
      """^(?:final\s+|sealed\s+|abstract\s+)*(?:object|class|trait)\s+([A-Za-z][A-Za-z0-9]*)""".r

    val start = (Option.empty[String], Vector.empty[String])

    withoutComments(Files.readString(path)).linesIterator
      .foldLeft(start) { case ((owner, found), line) =>
        val nested = line.startsWith(" ") || line.startsWith("\t")
        val declared = declares.findFirstMatchIn(line).map(_.group(1))
        val qualified = declared.map(name =>
          if (nested) owner.fold(name)(outer => s"$outer.$name") else name
        )

        val enclosing =
          if (nested) owner else encloses.findFirstMatchIn(line).map(_.group(1)).orElse(owner)

        (enclosing, found ++ qualified.toList)
      }
      ._2
  }

  /**
   * A source with its comments removed, so a name in prose is not read as a mapping.
   *
   * `scan.Comments` since 2026-09-16, where the same question is answered for the two other modules
   * that ask it. The line structure survives now, which it did not: the substitution this replaces
   * put one space where a block comment had been, newlines included, so a docstring of four lines
   * merged the line above it with the line below. This fold reads lines, and the shape it read
   * depended on how the prose around the declarations had been wrapped.
   */
  private def withoutComments(text: String): String = Comments.withoutComments(text)

  /**
   * Find a repository file from wherever the tests were started.
   *
   * Walking up rather than assuming the working directory, the way `DocumentationSpec` does it: a
   * scan that silently passes because it found no files would be worse than one that fails.
   */
  private def locate(relative: String): Path = {
    def search(directory: Path, remaining: Int): Path =
      if (directory == null || remaining < 0)
        fail(s"could not find $relative from ${Paths.get("").toAbsolutePath}")
      else {
        val candidate = directory.resolve(relative)
        if (Files.exists(candidate)) candidate else search(directory.getParent, remaining - 1)
      }

    search(Paths.get("").toAbsolutePath, 5)
  }
}
