package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.{Add, Derivative, Div, Dsl, Integral, Mul, Num, Sin, SimplificationConfig, Solve, Var}
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.*

/**
 * The examples printed in the documentation, executed.
 *
 * A document that shows what a system does is believed, and a document whose examples stopped
 * working some months ago is believed anyway, which is why this file exists. Every example in
 * `docs/proving.md` and in the front of `README.md` is run here, and the axiom table in the guide
 * is compared with the axioms the theory actually holds.
 *
 * If you change an example in a document, change it here in the same commit. If this fails, the
 * document is wrong, not the test.
 */
class DocumentationSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val reals = Real.standard
  private val ring = Ring.standard
  private val x = Var("x")

  /* ------------------------------------------------------- README, both halves */

  "The README algebra examples" should "produce what the README says they produce" in {
    import garden.xeno.symbolum.Dsl.*
    import garden.xeno.symbolum.SimplificationRule.*

    val y = Var("y")
    val a = Var("a")
    val b = Var("b")
    val logs = SimplificationConfig.Default.withRule(ExpandLogarithms)
    val exps = SimplificationConfig.Default.withRule(ExpandExponentials)
    val cosines = SimplificationConfig.Default.withRule(ProductOfCosToSumOfCos)

    ((x + Num(1)) ^ Num(2)).expand().toString shouldBe "x^2 + 2 * x + 1"
    ((x + Num(1)) ^ Num(3)).expand().toString shouldBe "x^3 + 3 * x + 3 * x^2 + 1"
    Derivative(x ^ Num(2), "x").simplify().toString shouldBe "2 * x"
    Derivative(Sin(x ^ Num(2)), "x").simplify().toString shouldBe "2 * x * cos(x^2)"
    Integral(x, "x").simplify().toString shouldBe "x^2/2"
    Integral.definite(x, "x", Num(0), Num(1)).toString shouldBe "1/2"
    ((x ^ Num(2)) ^ Num(3)).simplify().toString shouldBe "x^6"
    (Num(2) * Var("n") + Num(3) * Var("n") - Num(1)).simplify().toString shouldBe "5 * n - 1"
    (a * (b + Var("c"))).expand().toString shouldBe "a * b + a * c"

    // The ones the default configuration does not perform, each with the rule the README now
    // shows. These were documented without their configuration and did nothing as written.
    (Dsl.cos(a) * Dsl.cos(b)).expand(cosines).toString shouldBe "(cos(a + b) + cos(a - b))/2"
    Dsl.log(x * y).expand(logs).toString shouldBe "log(x) + log(y)"
    Dsl.log(x / y).expand(logs).toString shouldBe "-log(y) + log(x)"
    Dsl.log(x ^ Num(2)).simplify(logs).toString shouldBe "2 * log(x)"
    Dsl.exp(x + y).expand(exps).toString shouldBe "exp(x) * exp(y)"

    // The inverse properties, which do hold with the default set.
    Dsl.exp(Dsl.log(x)).simplify().toString shouldBe "x"
    Dsl.log(Dsl.exp(x)).simplify().toString shouldBe "x"
    Dsl.sin(-x).simplify().toString shouldBe "-sin(x)"
  }

  "The README's two assignments" should "be the text the document holds, not a paraphrase of it" in {
    // The hole this closes, found on 2026-09-15 by compiling the README's own line from a project
    // outside this repository. The test above evaluates `Num(2) * Var("n") + ...`; the README
    // printed `2 * n + 3 * n - 1`, which does not compile anywhere, because a bare integer to the
    // LEFT of an operator wants two implicit conversions chained, Int to Expr and then Expr to the
    // class carrying the operators, and Scala applies one. The guard was green about a program the
    // document does not contain, and the first example on the front page did not run.
    //
    // The agreement is asserted rather than the text executed: running the block would need a
    // compiler at test time, and what drifted was the spelling. The two halves together say it,
    // since the spellings below are compiled by this file and the document is asserted to hold
    // them character for character.
    import garden.xeno.symbolum.Dsl.*
    import scala.language.implicitConversions

    val n = Var("n")
    val readme = read("README.md")

    (Num(2) * n + Num(3) * n - Num(1)).simplify().toString shouldBe "5 * n - 1"
    readme should include("val expr = Num(2) * n + Num(3) * n - Num(1)")

    (x * x + Num(2) * x + 1).eval(Map("x" -> 3.0)) shouldBe 16.0
    readme should include("val expr = x * x + Num(2) * x + 1")

    // What would make that vacuous: the spellings that do not compile sitting somewhere else in
    // the file while these two pass. Neither string is a substring of its repair.
    readme should not include "val expr = 2 * n + 3 * n - 1"
    readme should not include "val expr = x * x + 2 * x + 1"
  }

  "The README solving examples" should "produce the stated roots" in {
    import garden.xeno.symbolum.Dsl.*

    Solve.solve(x + Num(2), "x").map(_.toString) shouldBe List("-2")
    Solve.solve((x ^ Num(2)) - (Num(5) * x) + Num(6), "x").map(_.toString).toSet shouldBe
      Set("2", "3")
    Solve.solve((x ^ Num(2)) - (Var("a") * x), "x").map(_.toString).toSet shouldBe Set("a", "0")
    Solve.solve((x ^ Num(2)) - (Num(4) * x) + Num(3), "x").map(_.toString).toSet shouldBe
      Set("1", "3")
  }

  "The README worked examples" should "produce what they print" in {
    import garden.xeno.symbolum.Dsl.*
    import garden.xeno.symbolum.SimplificationRule.*

    val poly = (x ^ Num(3)) + (Num(3) * (x ^ Num(2))) - (Num(2) * x) + Num(1)
    val derivative = Derivative(poly, "x").simplify()
    derivative.toString shouldBe "3 * x^2 + 6 * x - 2"
    Integral(derivative, "x").simplify().toString shouldBe "x^3 - 2 * x + 3 * x^2"

    val cosines = SimplificationConfig.Default.withRule(ProductOfCosToSumOfCos)
    (Dsl.cos(x) * Dsl.cos(x)).expand(cosines).toString shouldBe "(cos(2 * x) + 1)/2"
    Derivative(Dsl.sin(x), "x").simplify().toString shouldBe "cos(x)"

    val k = Var("k")
    val t = Var("t")
    val rate = Derivative(Dsl.exp(k * t), "t").simplify()
    rate.toString shouldBe "k * exp(k * t)"
    rate.eval(Map("t" -> 2.0, "k" -> 0.5)) shouldBe 1.359 +- 0.001
  }

  "The README proof examples" should "each produce a theorem" in {
    force(ring.prove("!x:real y:real. (x + y) * (x + y) = x * x + 2 * (x * y) + y * y"))
    force(Linarith.standard.prove("!x:real y:real. x < y ==> x + 1 < y + 1"))

    reals.show(force(Arithmetic.standard.multiply(3, 4)).conclusion) shouldBe "3 * 4 = 12"
  }

  "The README bridge examples" should "certify one and refuse the other" in {
    import garden.xeno.symbolum.Dsl.*

    force(Oracle.standard.certifyExpansion((x + Num(1)) * (x + Num(1))))
    Oracle.standard.certifyIdentity(Add(Vector(x, x)), Mul(Vector(Num(3), x))).isLeft shouldBe true
  }

  /* --------------------------------------------------------- docs/proving.md */

  "The guide's opening example" should "prove the square of a successor" in {
    force(ring.prove("!x:real. (x + 1) * (x + 1) = x * x + 2 * x + 1"))
  }

  "The guide's statement about undetermined types" should "hold" in {
    Parser.proposition(Logic.standard.theory, "x = y").isLeft shouldBe true
  }

  "The guide's ring examples" should "all be proved" in {
    force(ring.prove("!x:real y:real. (x - y) * (x + y) = x * x - y * y"))
    force(ring.prove("!x:real y:real. -(x + y) = -x + -y"))
    force(ring.prove("2 * 3 = 6"))
  }

  "The guide's linear arithmetic examples" should "all be proved" in {
    force(Linarith.standard.prove("!x:real y:real z:real. x < y /\\ y < z ==> x < z"))
    force(Linarith.standard.prove("!x:real y:real. 2 * x < 2 * y ==> x < y"))
    force(Linarith.standard.prove("!x:real. x < x + 1"))
    force(
      Linarith.standard.prove(
        "!x:real y:real. 3 * x < 2 * y /\\ 2 * y < 5 * x ==> 0 < x"
      )
    )
    force(Linarith.standard.prove("!x:real y:real z:real. x <= y /\\ y < z ==> x < z"))
    force(Linarith.standard.prove("!a:real b:real. a = 53 * b /\\ 0 < b ==> a <= 60 * b"))
  }

  "The guide's quotient examples" should "be decided as they are written" in {
    // The second is E02 of the frozen set: a claim from an article, in the form its author wrote
    // it. Reading it used to mean cross-multiplying by hand first, which checks a statement
    // nobody wrote.
    force(Linarith.standard.prove("!e:real. e / 3 + e / 3 + e / 3 <= e"))
    force(Linarith.standard.prove("3967 / 285489 < 14 / 1000"))
  }

  "The guide's provenance example" should "name the sources it names" in {
    val register = force(
      Provenance.of(
        reals,
        Vector(
          "deaths:real = 53 * beds:real" -> "ARS 2022, table 4",
          "0 < beds:real" -> "ISPRA Tab. 3.1, 2026 edition"
        )
      )
    )

    val trail = force(
      register.trail(
        Linarith.standard,
        "deaths:real = 53 * beds:real /\\ 0 < beds:real ==> deaths <= 60 * beds"
      )
    )

    force(register.report(trail)).linesIterator.toVector shouldBe Vector(
      "rests on:",
      "  ARS 2022, table 4: deaths = 53 * beds",
      "  ISPRA Tab. 3.1, 2026 edition: 0 < beds (weighed 7)"
    )
  }

  "The guide's arithmetic examples" should "produce the stated theorems" in {
    reals.show(force(Arithmetic.standard.add(1000, 1000)).conclusion) shouldBe "1000 + 1000 = 2000"
    reals.show(force(Arithmetic.standard.multiply(3, 4)).conclusion) shouldBe "3 * 4 = 12"
  }

  "The guide's support example" should "name the premises it names" in {
    val support = force(
      Linarith.standard.support(
        "x:real < y:real /\\ z:real < w:real /\\ y:real < z:real ==> x < z"
      )
    )

    support.map { case (hypothesis, weight) => (reals.show(hypothesis), weight) } shouldBe
      Vector(("x < y", BigInt(1)), ("y < z", BigInt(1)))
  }

  "The guide's abduction examples" should "sort the candidates into the buckets the guide prints" in {
    // The point is not asserted, because it is a sampled witness and the guide shows one run of it.
    // What is asserted is which bucket each candidate landed in, which is the whole of what the
    // section claims and the only part that could go wrong silently.
    val found = force(Abduce.standard.missing("!x:real y:real. 0 < x ==> 0 < x * y"))

    found.found.map(reals.show) shouldBe Vector("0 < y")
    found.vacuous.map(reals.show) should contain("x < 0")
    found.circular.map(reals.show) shouldBe Vector("0 < x * y")
    found.point should not be empty

    // The second block, which is the same candidate under premises nothing can decide. `x < 0` is
    // impossible under `0 < x` in both, and only the first of the two can say so.
    val undecided = force(Abduce.standard.missing("!x:real y:real. 0 < x /\\ x * y = 1 ==> 2 < x"))

    undecided.unchecked.map(reals.show) should contain("x < 0")
    undecided.found shouldBe empty
    undecided.vacuous shouldBe empty
  }

  "The guide's closed-form examples" should "find what the guide prints, and decline what it declines" in {
    // The inference count in the guide is a photograph and the claim is not: the closed form for a
    // sum of squares is the polynomial it is, so that one is asserted, and the count is left to the
    // spec that reports it.
    Family.standard.of("\\i:num. real_of_num i * real_of_num i") match {
      case found: Family.Outcome.Found =>
        found.degree shouldBe 3
        Chain.standard.widest.show(found.claim) should include(
          "real_of_num x * (real_of_num x - 1) / 2 + " +
            "real_of_num x * (real_of_num x - 1) * (real_of_num x - 2) / 3"
        )
        found.theorem.hypotheses shouldBe empty
      case other => fail(s"expected a closed form, got $other")
    }

    Family.standard.of("\\i:num. Power 2 i") match {
      case Family.Outcome.NotPolynomial(samples, _) =>
        samples.take(6).map(_.toString) shouldBe Vector("0", "1", "3", "7", "15", "31")
      case other => fail(s"expected a refusal to fit, got $other")
    }
  }

  "The guide's sweep example" should "run, and produce a line per source in the shape it prints" in {
    // The numbers in the guide are a photograph of one run against this repository's library and
    // move when the library does, so what is pinned is the shape. A figure worth pinning would have
    // to be about something that does not change every time somebody proves a lemma.
    val directory = java.nio.file.Files.createTempDirectory("symbolum-guide-sweep")
    val report = Sweep(Propose.standard, Ledger.at(directory.resolve("run.tsv"))).run()

    report.lines should have size Propose.Source.values.length
    every(report.lines) should include("offered")
    every(report.lines) should include("open per settled")
    report.lines.exists(_.startsWith("Substituted")) shouldBe true
    report.lines.exists(_.startsWith("Weakened")) shouldBe true
  }

  "The guide's order examples" should "produce the stated theorems" in {
    val order = Order.standard
    val rules = order.reals.logic.rules

    reals.show(force(order.zeroLessOne).conclusion) shouldBe "0 < 1"
    reals.show(force(order.positive(12)).conclusion) shouldBe "0 < 12"
    reals.show(force(order.less(53, 60)).conclusion) shouldBe "53 < 60"

    val inverse = for {
      two <- order.reals.term("2")
      positive <- order.positive(2)
      lemma <- order.inversePositive
      atTwo <- rules.spec(two, lemma)
      result <- rules.mp(atTwo, positive)
    } yield result
    reals.show(force(inverse).conclusion) shouldBe "0 < inv 2"
  }

  "The guide's application examples" should "hand back the obligations the guide prints" in {
    val order = Order.standard
    val logic = force(order.reals.logic.over(order.reals.theory))

    val used = force(
      for {
        goal <- order.reals.proposition("0 < inv 2")
        lemma <- order.inversePositive
        applied <- Apply.to(logic, lemma, goal)
      } yield applied
    )

    used.obligations.map(reals.show) shouldBe Vector("0 < 2")
    reals.show(used.theorem.conclusion) shouldBe "0 < 2 ==> 0 < inv 2"
  }

  it should "prove the goal the guide says was refused until the lookup existed" in {
    // `!x. 0 <= x * x` is `SQUARE_NONNEG`. LINARITH is the right address for an inequality and
    // cannot take a goal whose atom is a product of unknowns, so this was a refusal from a system
    // holding the lemma. The guide claims it is proved now; this is the claim.
    val goal = force(Prove.standard.reals.proposition("!x:real. 0 <= x * x"))

    Prove.standard(goal).map(_.hypotheses) shouldBe Right(Nil)
  }

  it should "decide the guide's rule set contradictory, as the guide prints" in {
    Consistency.standard.reading(
      Vector("p:bool ==> q:bool", "q:bool ==> r:bool", "p:bool", "~(r:bool)")
    ) shouldBe Consistency.Verdict.Contradictory
  }

  it should "leave the domain example to the file that runs it end to end" in {
    // Named, not copied, for the same reason as the completeness one below: `DomainSpec` states the
    // same argument, proves it, checks that it costs no axiom, and holds both boundaries beside it.
    // A copy here would be a second test that agrees until it does not.
    read("docs/proving.md") should include("(tierTwo p ==> gated p)")
    read("docs/proving.md") should include("`Derivation.axiomsOf` of it is EMPTY")
  }

  it should "leave the completeness example to the file that runs it end to end" in {
    // Named here and not copied here. `CompletenessSpec` in `modules/theories` states the same goal,
    // asserts the same instantiation and the same obligation, and then discharges them, which is
    // more than this file could assert without becoming a second copy of it. What is checked here
    // is that the guide still points at an axiom the theory holds under that name.
    Real.standard.axioms.keySet should contain("COMPLETENESS")
    read("docs/proving.md") should include("P := \\x:real. x < 1")
  }

  "The evaluation document" should "say which of its figures are alive and which are a photograph" in {
    // The class of staleness that has bitten most often here, and the one repair that stops it
    // recurring: a reader cannot tell a live figure from a hand-measured one by looking, so the
    // document says which is which. What this asserts is that the table exists and names the
    // mechanisms, not the figures themselves, which have their own assertions elsewhere.
    val evaluation = read("docs/evaluation.md")

    evaluation should include("Which figures here are alive, and which are a photograph")
    evaluation should include("a number without a test that ties it to the code is a number")

    Vector("Asserted from the live theory", "Hand-measured", "Executed").foreach { mechanism =>
      withClue(s"the table does not name `$mechanism`: ") { evaluation should include(mechanism) }
    }
  }

  "The library modules" should "publish under their own coordinates, which five of them did not" in {
    // Until 2026-09-15 `publish / skip := true` sat on all five prover modules and only `core`
    // could ship, on the argument that a published artifact is a promise and the surface is still
    // moving. What that produced was a README documenting an installation nobody could perform:
    // `gh api user/packages?package_type=maven` answered `[]` that day, so the one module allowed
    // to ship had not shipped either.
    //
    // Read from the build rather than asserted through sbt, because what regresses is the line.
    val build = read("build.sbt")

    val applied = build.linesIterator.count(_.contains(".settings(publishSettings)"))
    withClue("the six library modules and the aggregate take the publishing settings: ") {
      applied shouldBe 7
    }

    // The half of the assertion that can go empty. Counting the modules that publish says nothing
    // about a module that quietly started publishing beside them, and `mark` is the one that would
    // hurt: it regenerates two files under `docs/`, so a consumer resolving it gets a tool that
    // writes into their working directory. The count above would not move.
    // Comment lines dropped first: the paragraph above these settings names the setting it is
    // about, so a count over the whole file counts a sentence as a module.
    val skipped = build.linesIterator
      .map(_.trim)
      .filterNot(line => line.startsWith("//") || line.startsWith("*"))
      .count(_.contains("publish / skip := true"))
    withClue("`root`, `examples`, `mark` and `dist` are the four that do not publish: ") {
      skipped shouldBe 4
    }
  }

  "The distribution" should "carry a launcher for every entry point a person reaches" in {
    // The other half of what ships, and the half that had no artifact at all: `Ask`, `Find` and
    // `Notebook` were reachable only as `sbt "tactics/runMain ..."` inside a checkout. The
    // allowlist is what this pins. Discovery over what `dist` reaches finds every main class in the
    // graph, including `Lemmas`, `Register` and `Mark`, which write into `docs/` and would write
    // into a consumer's working directory instead.
    val build = read("build.sbt")

    val launchers = Vector(
      "garden.xeno.symbolum.tactics.Ask",
      "garden.xeno.symbolum.tactics.Find",
      "garden.xeno.symbolum.tactics.Notebook",
      "garden.xeno.symbolum.examples.WhatAClaimCosts",
      "garden.xeno.symbolum.dist.Repl"
    )
    launchers.foreach(entry => build should include(s"\"$entry\""))

    // What would make that vacuous: an allowlist that is a superset of the entry points, which is
    // discovery with extra steps. The five mains that regenerate documents through `Generated` are
    // named here, so that adding one to the distribution fails rather than passes. `Generated`
    // resolves `docs/...` against the working directory, so one of these in a tarball is a command
    // that writes into wherever the person who installed it happened to be standing.
    val writers = Vector(
      "garden.xeno.symbolum.theories.Lemmas",
      "garden.xeno.symbolum.theories.Register",
      "garden.xeno.symbolum.theories.Guide",
      "garden.xeno.symbolum.theories.Examples",
      "garden.xeno.symbolum.theories.Foundation"
    )
    writers.foreach(entry => build should not include s"\"$entry\"")
  }

  "The guide's cost report" should "be the page the system prints, line for line" in {
    // The page is pinned whole rather than by a phrase, and the inference count is part of it. That
    // number moves when `Field` changes, and it is meant to: what the guide shows a reader is what
    // a second checker will have to replay, and a figure the document keeps after the tactic has
    // changed is the stale reference this file exists to prevent. If this fails, update the block
    // in `docs/proving.md` in the same commit.
    val cost = Cost.standard
    val guide = read("docs/proving.md")

    val priced = force(cost.of("!x:real y:real. (x * y) / y = x").flatMap(cost.render))
    val broken = force(cost.of("!x:real. 0 < x ==> 1 < x").flatMap(cost.render))

    withClue(s"the guide does not show this page:\n$priced\n") {
      guide.contains(priced) shouldBe true
    }
    withClue(s"the guide does not show this page:\n$broken\n") {
      guide.contains(broken) shouldBe true
    }
  }

  "The guide's remedy examples" should "be the messages the system produces, word for word" in {
    // Pinned the way the cost report above is pinned, and for the same reason one step further
    // along: what the guide shows here is the sentence a session acts on, so a wording improved in
    // `Remedy` and not here leaves a reader following advice the system no longer gives. The
    // assertion is about the message rather than about the remedy alone, which is the opposite of
    // `RemedySpec`'s rule: there a message is free to improve, here it is quoted.
    val guide = read("docs/proving.md")

    val refusal = Prove.standard("!x:real y:real. (x * y) / y = x") match {
      case Left(error) => error
      case Right(theorem) =>
        fail(s"the guide says this is not a theorem as written, and got ${theorem.conclusion}")
    }

    val price = Remedy.of(reals, refusal)
    price shouldBe a[AcceptTheConditions]
    withClue(s"the guide does not show this message:\n${price.message}\n") {
      guide.contains(price.message) shouldBe true
    }

    // The other half of the section: an answer is mapped too, and the message says in its own
    // words that nothing was certified. A `Settled` that stopped saying so would be offering a
    // session a proof of something nothing here has proved.
    val settled = Remedy.of(force(Quantified.standard.decide("!x:real. ?y:real. x < y")))
    settled shouldBe a[Settled]
    withClue(s"the guide does not show this message:\n${settled.message}\n") {
      guide.contains(settled.message) shouldBe true
    }
  }

  "The guide's readback report" should "be the page the system prints, line for line" in {
    val guide = read("docs/proving.md")

    val goal = force(reals.proposition("!x:real y:real. x < y ==> x + 1 < y + 1"))
    val proved = TacticError.lift(Linarith.standard.prove(goal))
    val report = force(
      Readback.report(reals, "y is above x, so x plus one is below y plus one", goal, proved)
    )

    withClue(s"the guide does not show this report:\n$report\n") {
      guide.contains(report) shouldBe true
    }

    // The claim the guide makes about a goal that was not proved: the first two lines are the
    // same, and the verdict becomes two of its own. The refusal's own wording belongs to the
    // procedure that refused and is not quoted in the guide, so it is not pinned here either.
    val refusedGoal = force(reals.proposition("!x:real y:real. x <= y ==> x < y"))
    val refused = TacticError.lift(Linarith.standard.prove(refusedGoal))
    refused.isLeft shouldBe true

    val second = force(
      Readback.report(reals, "x is at most y, so it is below y", refusedGoal, refused)
    )

    second.linesIterator.toVector.take(2) shouldBe Vector(
      "source: x is at most y, so it is below y",
      s"formalised: ${reals.show(refusedGoal)}"
    )
    second should include("\nnot proved: ")
    second should include("\nnext: ")
  }

  "The guide's table of order facts" should "name exactly the facts the order holds" in {
    // The same guard as the axiom table below, for the same reason: a fact added to `Order` and
    // not written down is a fact nobody outside this repository can find.
    val guide = read("docs/proving.md")
    val names = Order.standard.facts.keys.toVector.sorted

    val quoted = names.filter(guide.contains)
    withClue(s"missing from docs/proving.md: ${names.diff(quoted).mkString(", ")}\n") {
      quoted shouldBe names
    }
  }

  "The guide's hand proof" should "reach the theorem it claims" in {
    val rules = reals.logic.rules
    val real = TyApp(Real.TypeName, Nil)
    val a = Term.variable("a", real)
    val b = Term.variable("b", real)

    val theorem = force(
      for {
        commutativity <- reals.axiom("ADD_SYM")
        atA <- rules.spec(a, commutativity)
        atB <- rules.spec(b, atA)
      } yield atB
    )

    reals.show(theorem.conclusion) shouldBe "a + b = b + a"
  }

  "The guide's proof by cases" should "reach the theorem it claims" in {
    val logic = Logic.standard
    val rules = logic.rules
    val p = Term.variable("p", Type.Bool)
    val q = Term.variable("q", Type.Bool)

    val theorem = force(
      for {
        disjunction <- logic.mkDisj(p, q)
        assumed <- LogicError.lift(Kernel.assume(disjunction))
        fromLeft <- LogicError.lift(Kernel.assume(p)).flatMap(rules.disjIntro2(q, _))
        fromRight <- LogicError.lift(Kernel.assume(q)).flatMap(rules.disjIntro1(p, _))
        eliminated <- rules.disjElim(assumed, fromLeft, fromRight)
        theorem <- rules.disch(disjunction, eliminated)
      } yield theorem
    )

    Show.show(theorem) shouldBe "|- p \\/ q ==> q \\/ p"
  }

  "The guide's discovery example" should "sort the three candidates as described" in {
    import garden.xeno.symbolum.Dsl.*

    val candidates = Vector(
      (x + Num(1)) * (x + Num(1)),
      Add(Vector(Mul(Vector(x, x)), Mul(Vector(Num(2), x)), Num(1))),
      Add(Vector(Mul(Vector(x, x)), Num(1)))
    )

    val outcomes = Discovery.standard.identities(candidates, Discovery.grid(candidates, 100))

    outcomes.count(_.isInstanceOf[Discovery.Proved]) shouldBe 1
    outcomes.count(_.isInstanceOf[Discovery.Disproved]) shouldBe 2
  }

  "The guide's refutation examples" should "produce the outcomes the guide reports" in {
    val premise = force(reals.proposition("0 < x:real"))
    val claim = force(reals.proposition("1 < x:real"))

    Refutation.standard.counterexample(Vector(premise), claim) match {
      case Refutation.Solved(witness, _) =>
        // The guide shows the point the solver returns, which is a vertex of the region: `x` is
        // one, `0 < 1` holds and `1 < 1` does not.
        witness.get("x") shouldBe Some(Rational.one)
      case other => fail(s"the guide says the point is solved for, and got $other")
    }

    val cycle = Vector("x:real < y:real", "y:real < z:real", "z:real < x:real")
      .map(text => force(reals.proposition(text)))

    Refutation.standard.satisfying(cycle) should matchPattern {
      case Refutation.Contradictory(_) =>
    }

    // The guide names two premises as solved rather than sampled, and this is the first:
    // `{x = 1}`, which a sampler lands on with probability zero. The exact half it reports for
    // `{2 * x = 1}` is not asserted here.
    Refutation.standard.satisfying(Vector(force(reals.proposition("x:real = 1")))) should matchPattern {
      case Refutation.Solved(_, _) =>
    }
  }

  "The guide's ledger example" should "answer the second call from the file" in {
    val directory = Files.createTempDirectory("symbolum-guide")
    val ledger = Ledger.at(directory.resolve("run.tsv"))

    val left = Mul(Vector(Add(Vector(x, Num(1))), Add(Vector(x, Num(1)))))
    val right = Add(Vector(Mul(Vector(x, x)), Mul(Vector(Num(2), x)), Num(1)))
    val samples = Discovery.grid(Vector(left, right), 100)

    val first = ledger.settle(Discovery.standard, left, right, samples)
    first.verdict shouldBe Ledger.Verdict.Proved
    first.evidence shouldBe "certified by the kernel"

    // The claim the guide makes about it: the second call is a lookup, so it returns the entry the
    // first one wrote rather than a new one.
    ledger.settle(Discovery.standard, left, right, samples) shouldBe first
    ledger.entries should have length 1
  }

  "The guide's extension example" should "build the whole chain over a declared constant" in {
    val extended = force(
      Real.standard.extended(
        Vector("agent" -> 0),
        Vector("selectivity" -> TyApp("real", Nil))
      )
    )

    val theorem = force(
      for {
        arithmetic <- Arithmetic.construct(extended)
        ring <- Ring.construct(arithmetic)
        order <- Order.construct(ring)
        linarith <- Linarith.construct(order)
        proved <- linarith.prove("!x:real. selectivity < x ==> selectivity < x + 1")
      } yield proved
    )

    extended.show(theorem.conclusion) shouldBe "!x:real. selectivity < x ==> selectivity < x + 1"
    extended.theory.axioms should have length 16
  }

  "The guide's lemma example" should "be provable the way it is written" in {
    force(reals.proposition("x:real * (y:real + 1) = x * y + x").flatMap(ring.prove))
  }

  /* ------------------------------------------------------ the axiom table */

  "The axiom table in the guide" should "name exactly the axioms the theory holds, in order" in {
    val guide = read("docs/proving.md")
    val names = Real.Axioms.map { case (name, _) => name }

    val quoted = names.filter(name => guide.contains(name))
    withClue(s"missing from docs/proving.md: ${names.diff(quoted).mkString(", ")}\n") {
      quoted shouldBe names
    }

    // In the order the theory holds them, so a reordering of the axioms shows up here too.
    val positions = names.map(guide.indexOf)
    positions shouldBe positions.sorted
  }

  "The architecture document" should "state the size of the trusted base as it is" in {
    val architecture = read("docs/architecture.md")

    // Spelled from the live count rather than matched against a literal, which is the same
    // arrangement the line bound below has had since it was written and the reason that one has
    // never gone stale. A literal `include("16 propositions")` passes for as long as the document
    // says sixteen, whatever the theory holds; this fails the moment the two disagree, in either
    // direction. The axiom counts moved twice on 2026-09-10 alone, so the difference is not
    // theoretical.
    architecture should include(s"${Real.Axioms.length} propositions, a complete ordered field")
    architecture should include(s"${garden.xeno.symbolum.logic.Classical.Axioms.length} propositions, both from")

    // The other half of the trusted base is its size, and until this was written the documents
    // carried "about 900 lines" for some months after the kernel passed it. A bound rather than a
    // count, because what the figure stands for is that one person can read the whole of it: an
    // exact number would be re-measured after every edit and would say no more than this does.
    //
    // **It measures the four files a defect in which can produce a false theorem, and not the
    // directory.** Those are two different things and they were the same number until 2026-09-10,
    // when a proof record arrived and pushed the directory past the bound while what has to be
    // believed had not moved. Raising the bound for that would have been the measurement eroding
    // rather than the base growing, which is the failure this file exists to prevent one level up.
    val kernel = TrustedFiles.map(lineCountOf).sum
    withClue(s"the trusted base is now $kernel lines; raise the bound in both documents, or explain\n") {
      kernel should be < TrustedBaseLineBound
    }

    // The claim is spelled from the bound rather than beside it, so the two cannot disagree.
    val claim = s"under $TrustedBaseLineBound lines"
    architecture should include(claim)
    read("CLAUDE.md") should include(claim)
  }

  it should "classify every file of the kernel, so a new one is a decision and not a default" in {
    // The guard that keeps the split above honest. Excluding a file from the count is a claim that
    // a defect in it cannot produce a false theorem, and a claim like that is made deliberately per
    // file or not at all: a new file landing in the directory has to appear in one of the two lists
    // before this passes, which is the same discipline `RealSpec` applies to `assertAxiom`.
    val present = java.nio.file.Files
      .list(java.nio.file.Paths.get("modules/kernel/src/main/scala/garden/xeno/symbolum/kernel"))
      .map[String](path => path.getFileName.toString)
      .toArray
      .toVector
      .map(_.toString)
      .sorted

    present shouldBe (TrustedFiles ++ RecordAndDisplay).sorted

    // And the reason every one of them is out: none can make a theorem. The constructor is
    // private to `object Kernel`, so this is checkable rather than asserted.
    RecordAndDisplay.foreach { name =>
      withClue(s"$name: ") { fileOf(name) should not include "new Thm(" }
    }
    fileOf("Kernel.scala") should include("new Thm(")
  }

  "The evaluation document" should "describe limits the tactics still have" in {
    // Each of these is a refusal the document reports as the state of the art here. When one of
    // them starts succeeding, the tactic has improved and the document is stale: update the
    // ladder, the fragment claims and the build order in the same commit.
    import garden.xeno.symbolum.Dsl.*

    ring.prove("!x:real. x + x = 3 * x").isLeft shouldBe true

    // The multiplier and the shape of the hypothesis were the limits these lines used to record,
    // and both went on 2026-09-05. The product of two unknowns was the limit after them, and it
    // went on 2026-09-09: LINARITH multiplies its hypotheses in pairs when the linear search has
    // failed, which is the move `nlinarith` makes, so the axiom below is proved rather than
    // refused for being an atom no combination reaches.
    force(Linarith.standard.prove("!x:real y:real. 2 * x < 2 * y ==> x < y"))
    force(Linarith.standard.prove("!x:real y:real. x <= y ==> x <= y + 1"))
    force(Linarith.standard.prove("!x:real y:real. 0 < x /\\ 0 < y ==> 0 < x * y"))
    force(Linarith.standard.prove("!x:real. 0 < x ==> 0 < x * x"))

    // What used to be left of that limit was a missing lemma rather than a missing move, and the
    // lemma arrived on 2026-09-10 as `Order.MUL_NONNEG_BOTH`. The two things this comment then
    // named as what was left, a degree the pairs do not produce and a case analysis on the sign of
    // a product, both went later the same day and neither was a lemma either. Degree three is a
    // second round of products, over the pairs times the originals, and it runs only when the goal
    // names an atom the pairs did not reach. The sign analysis is the negation of the goal joining
    // the facts, which is what `nlinarith` multiplies over and this did not.
    force(Linarith.standard.prove("!x:real y:real. 0 <= x /\\ 0 <= y ==> 0 <= x * y"))
    force(Linarith.standard.prove("!x:real y:real. 0 < x /\\ 0 < y /\\ 0 < z:real ==> 0 < x * y * z"))
    force(Linarith.standard.prove("!x:real y:real. 0 < x * y /\\ 0 < x ==> 0 < y"))

    // Degree four is the limit now, and it is the same shape of limit one round up: a third round
    // would reach it and nothing measured has asked for one.
    Linarith.standard
      .prove("!w:real x:real y:real. 0 < w /\\ 0 < x /\\ 0 < y /\\ 0 < z:real ==> 0 < w * x * y * z")
      .isLeft shouldBe true

    // Not a limit but the thing that must stay refused, since it is false.
    Linarith.standard.prove("!x:real y:real. x <= y ==> x < y").isLeft shouldBe true
    // A numeral denominator is settled since 2026-09-09, so the witness for a quotient RING will
    // not take is a symbolic one: cancelling `x` against `inv x` costs `~(x = 0)`, and that is the
    // hypothesis `Field` carries and `Ring` refuses to invent.
    force(Ring.standard.prove("!x:real. x / 2 + x / 2 = x"))
    Oracle.standard
      .certifyIdentity(Div(Vector(Mul(Vector(Num(2), x)), x)), Num(2))
      .left
      .exists(_.isInstanceOf[NotCertified]) shouldBe true
    Oracle.standard.certifyIdentity(Sin(Dsl.pi), Num(0)).left.exists(_.isInstanceOf[OutsideFragment]) shouldBe true
    force(Arithmetic.standard.multiply(12, 12))
  }

  /* ----------------------------------------------------------------- reading */

  /**
   * The four files a defect in which can produce a false theorem.
   *
   * The rules, the representation they run on, the types, and the signature they are checked
   * against. This is what "the trusted base" names, and it is what the bound below measures.
   */
  private val TrustedFiles: Vector[String] =
    Vector("Kernel.scala", "Term.scala", "Type.scala", "Theory.scala")

  /**
   * The rest of the directory, with the reason each one is not counted.
   *
   * `Printer.scala` is display: its own comment says nothing there can build a theorem and no rule
   * consults it. `KernelError.scala` is the refusal surface: a defect there is a wrong message, and
   * the rule has already decided by the time one is built. `Derivation.scala` is the proof record:
   * recording is not checking, so a derivation that does not replay is a false alarm from a checker
   * and never a false theorem. `Proof.scala` writes that record out as text, and the same argument
   * covers it one step further along: a proof written down wrongly is a table that fails to check.
   *
   * None of the four can construct a `Thm`, which the test below checks rather than trusting this
   * paragraph.
   */
  private val RecordAndDisplay: Vector[String] =
    Vector("Printer.scala", "KernelError.scala", "Derivation.scala", "Proof.scala")

  /**
   * What the trusted base may grow to before somebody has to decide.
   *
   * It has been 1200 since it was written and it is still 1200, which is worth a sentence because
   * it was raised to 1400 on 2026-09-10 and put back the same day. What had grown past it was the
   * kernel *directory*, and the four files above had not: a proof record and a printer are read by
   * nobody who is deciding whether to believe a theorem. Raising a bound because the wrong thing
   * was being measured is how a bound stops meaning anything.
   *
   * What it protects is that one person can read the whole of what they are asked to believe in a
   * sitting. Two records have spent against it deliberately, `docs/adr/0006` for the type
   * definition rule and `docs/adr/0008` for the identity on constants, and that is the only way it
   * is allowed to move.
   */
  private val TrustedBaseLineBound: Int = 1200

  private def fileOf(name: String): String =
    read(s"modules/kernel/src/main/scala/garden/xeno/symbolum/kernel/$name")

  private def lineCountOf(name: String): Int = fileOf(name).linesIterator.size

  private def read(relative: String): String =
    Files.readAllLines(locate(relative)).asScala.mkString("\n")

  /** Total lines of Scala under `relative`, which is how the documents measure the kernel. */
  private def lineCount(relative: String): Int = {
    val sources = Files.walk(locate(relative)).iterator.asScala.toVector
      .filter(path => Files.isRegularFile(path) && path.toString.endsWith(".scala"))
    sources.map(path => Files.readAllLines(path).size).sum
  }

  /**
   * Find a repository file from wherever the tests were started.
   *
   * Walking up rather than assuming the working directory, because a test that silently passes when
   * it cannot find the document would be worse than one that fails.
   */
  private def locate(relative: String): Path = {
    def search(directory: Path, remaining: Int): Path =
      if (remaining < 0) fail(s"could not find $relative from ${Paths.get("").toAbsolutePath}")
      else {
        val candidate = directory.resolve(relative)
        if (Files.exists(candidate)) candidate else search(directory.getParent, remaining - 1)
      }

    search(Paths.get("").toAbsolutePath, 5)
  }
  "The guide's argument page" should "be the page `ArgumentSpec` builds, down to the three buckets" in {
    // The example is run by `ArgumentSpec`, which owns the development it needs; what is checked
    // here is that the page in the guide is the page that comes out, and in particular that the
    // three lines a reader acts on are quoted rather than paraphrased.
    val guide = read("docs/proving.md")

    guide should include("3 claims, 3 proved, 0 decided, 0 open")
    guide should include("weighed 1, from ARS 2022, table 4: load <= 60 * rate")
    guide should include("assumed and never weighed: 0 < load (ARS 2022, table 7)")
    guide should include("cited and never assumed: load < cap (Decreto 152/2006 art. 99)")
  }

}
