package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.scan.Comments

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
 * **What "run here" means, precisely, since it did not mean what it said until 2026-09-16.** What
 * this file runs is a Scala program written beside the assertion that says what the document's
 * example produces. That is the ANSWER being checked, and it is worth checking; it is not the
 * document's own text being checked, and for two blocks of the front page the two had drifted so
 * far apart that one of them did not compile. `ReadmeSpec` is where the text itself is read from
 * `README.md` and compiled, for every Scala block the file holds. The two are a pair: that one
 * says the example is a program, this one says the program gives the answer printed beside it.
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
    // What this is for CHANGED on 2026-09-16 and the test did not, which is worth a line. It was
    // written when running the block was out of reach, so it asserted the agreement of two
    // spellings instead: the one below, compiled by this file, and the one in the document,
    // asserted character for character. `ReadmeSpec` now compiles the block itself, so the
    // agreement half is covered there and covered for all twenty-four blocks rather than two.
    // What survives here, and is not covered there, is the ANSWER: `5 * n - 1` and `16.0` are what
    // the document tells a reader to expect, and a block that runs is not a block that is right.
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

  /**
   * The front page's row about proof search, asserted by running the search rather than by reading.
   *
   * It said "no clause queue, no given-clause loop, no choice point anywhere" until 2026-09-15, and
   * the third of those was false: `Prove` routes a propositional goal to the propositional address,
   * and the search there backtracks. The same clause was in `docs/evaluation.md` twice, which is
   * why the repair moved three cells and not one.
   *
   * A negative absolute claim about the code is the worst kind of sentence to leave unchecked,
   * because a reader does not go and verify one. This repository's own rule is that a stale
   * reference is worse than a missing one; this is that rule where the document names no file and
   * denies a property instead.
   *
   * == What makes a guard like this vacuous, which is the thing to get right ==
   *
   * A test that searched `README.md` for a string would pass whatever the code did, and would BE
   * the defect it is correcting written as a test. So the property is exercised first and the
   * document is compared against what happened: the row and the code go red together.
   *
   * What it does NOT cover, said rather than left to be assumed: "no clause queue" and "no
   * given-clause loop" are absences, and a test cannot exhibit one. They are read by a person.
   */
  "The README row about proof search" should "hold of the search the tactics actually run" in {
    val logic = Logic.standard
    val minimal = Minimal.standard
    val readme = read("README.md")

    val p = Term.variable("p", Type.Bool)
    val q = Term.variable("q", Type.Bool)
    def imp(left: Term, right: Term): Term = force(logic.mkImp(left, right))
    def disj(left: Term, right: Term): Term = force(logic.mkDisj(left, right))
    def all(variables: List[FVar], body: Term): Term =
      variables.foldRight(body)((variable, inner) => force(logic.mkForall(variable, inner)))

    // The choice point, exercised rather than asserted. The left alternative of the disjunction is
    // `q`, which does not follow from `p`, and the goal is proved anyway: the failed branch was
    // explored and the search resumed. The first line is what makes the second one evidence.
    minimal.prove(all(List(p, q), imp(p, q))).isLeft shouldBe true
    minimal.prove(all(List(p, q), imp(p, disj(q, p)))).isRight shouldBe true

    // And it is a search that does not settle the fragment a classical reader would expect, which
    // is the half of the row a document of this repository does not leave out. `MinimalSpec` owns
    // this witness; it is repeated here because the README sentence is about it.
    minimal.prove(all(List(p, q), imp(imp(imp(p, q), p), p))).isLeft shouldBe true

    // The calculus itself, which is what `Prove` routes a propositional goal to since 2026-09-18
    // and what the test below reads the row for. Exercised at both ends: it takes a statement with
    // a negation in it, which is what the gate in front of it refuses and what the prover therefore
    // could not reach for free until the routing moved, and it stops at the two goals the row names
    // as its boundary.
    val intuitionistic = Intuitionistic.standard
    // `denial` rather than `not`, because a local `not` here shadows the matcher three lines below
    // and the error it produces names an overload rather than the shadowing.
    def denial(inner: Term): Term = force(logic.mkNot(inner))

    intuitionistic
      .prove(all(List(p), denial(force(logic.mkConj(p, denial(p))))))
      .isRight shouldBe true
    intuitionistic.prove(all(List(p, q), imp(imp(imp(p, q), p), p))).isLeft shouldBe true
    intuitionistic.prove(all(List(p), disj(p, denial(p)))).isLeft shouldBe true

    readme should include("The search under it backtracks")
    readme should include("it refuses Peirce's law and the excluded middle")

    // And that the row still says the gate is a gate, which is the sentence that stops a reader
    // concluding `Minimal` is the search: the two are one implementation and the fragment is what
    // separates them. Since 2026-09-18 the row has to say the other half too, that the gate decides
    // the address and no longer answers the goal, because a reader who takes `Minimal` for the
    // search reads every cost in this row against the wrong procedure.
    readme should include("a **fragment gate** rather than a search of its own")
    readme should include("it decides the **address**")

    // The sentence the row carried while `Prove` asked `Minimal` and not the calculus. It was true
    // when it was written and became false the day the routing moved, which is the one shape of
    // stale sentence nothing else here would have caught: it is a denial, and a denial of a
    // property no reader goes and checks.
    readme should not include "nothing routes a goal there"
    read("docs/evaluation.md") should not include "this list does not name"

    // The goal the routing exists for, put to the PROVER rather than to the calculus, which is the
    // difference between "the procedure can do it" and "asking the system gets it". Two negations,
    // no classical extension anywhere in `Prove.standard`, and nothing believed at the end of it.
    val reached = force(Prove.standard("!p:bool. ~(p /\\ ~p)")).theorem
    Derivation.axiomsOf(reached) shouldBe empty

    // The sentence that was there, in the two places that carried it, so that it cannot come back
    // by anybody rewriting the row from memory.
    readme should not include "no choice point anywhere"
    read("docs/evaluation.md") should not include "no choice point anywhere"
  }

  /**
   * The same row, on the other question it answers: **which** searches, rather than what they are.
   *
   * The row carried a count of them until 2026-09-16 and the count was a fact written twice. It
   * opened *"Two"* from the day it was written, while naming three of them in the same cell, and
   * nothing anywhere went red: `docs/evaluation.md` and the front page had both been read for the
   * sentence about backtracking, which the test above pins, and neither reader recounted the
   * paragraph they were standing in. Two further copies of the same number were in the prose, as
   * the ordinals introducing *"the second"* and *"the third"*, and a fourth search would have made
   * all three stale at once while each of them read as English rather than as a figure.
   *
   * The repair is the third of the three this repository uses for a fact written twice, and it is
   * the one its own `Generated` docstring says is met most often and chosen least: the number is
   * **deleted** rather than generated or watched, because the paragraph beneath it is the
   * enumeration and the argument never needed a count on top of one. Generating it was not
   * available anyway and the reason is mechanical rather than a preference: the row is a cell of a
   * GitHub-flavoured markdown table, a generated region is delimited by an HTML comment on a line
   * of its own, and such a line ends the table.
   *
   * So what is left to go stale is the enumeration, and this is what watches it. Both directions,
   * because a guard that only caught the missing one would pass forever on a row still describing a
   * search that has been deleted.
   *
   * **What makes it non-vacuous**, which is the question `RestsOnSpec` asks of a guard like this:
   * the population is `Prove.searches`, taken from a prover that was built rather than described,
   * so a configuration reaching no search at all would make the first assertion trivially true.
   * The second assertion below is the one that refuses that: the standard chain's prover reaches
   * every search there is, and if it ever reached fewer, this stops rather than quietly checking a
   * shorter list.
   *
   * **What it does not cover.** It reads the row for the name and not for the sentence beside it:
   * a paragraph that names `Chaining` and then describes something else passes here. What that
   * paragraph says about each one is read by a person, and the test above is what covers the one
   * claim in it that a machine can exercise.
   */
  it should "name every search the prover reaches, and none it does not, in both documents that list them" in {
    val prover = force(Prove.construct(Chain.standard))

    // Two cells and not one, and the second is the reason this test is worth more than a repair of
    // the front page would have been. `docs/evaluation.md` opened the same list with *"there are
    // three of them now"*, so the figure the README kept by hand was kept by hand twice, in two
    // files, with nothing comparing them to each other or to the code. It was found by grepping for
    // the claim rather than for the number, which is the only way a count spelled as a word gets
    // found at all.
    val cells = Vector(
      ("README.md", "| Automated proof search of any kind |"),
      ("docs/evaluation.md", "| CASC, SMT-COMP (LRA, NRA) |")
    ).map { case (document, opening) =>
      (document, read(document).linesIterator
        .find(_.startsWith(opening))
        .getOrElse(fail(s"$document no longer holds the row beginning `$opening`")))
    }

    cells.foreach { case (document, row) =>
      // Over the whole closed set rather than over what the prover happens to hold, so that a
      // search dropped from `Prove` leaves the row describing it and fails here.
      Prove.Search.values.foreach { search =>
        val named = row.contains(s"`${search.spelling}`")
        val reached = prover.searches.contains(search)
        withClue(
          if (reached) s"`${search.spelling}` is a search the standard prover reaches and $document does not name it: "
          else s"$document names `${search.spelling}` and the standard prover does not reach it: "
        ) {
          named shouldBe reached
        }
      }
    }

    // And the guard against the guard: the assertions above are about a prover, and a prover with
    // no classical extension and no library reaches `Intuitionistic` and nothing else, so a mistake
    // in `Prove.construct` would leave every other name unchecked in both documents and every
    // assertion above green.
    prover.searches should contain theSameElementsAs Prove.Search.values.toVector

    // The counts are gone rather than corrected, in every form they took: the front page's opening
    // numeral, the two ordinals that introduced the searches after the first, and the guide's own
    // sentence. Written as the strings the documents held, so that rewriting a paragraph from
    // memory puts one back and this says so.
    val (readme, evaluation) = (cells(0)._2, cells(1)._2)
    readme should not include "**Three, and what each of them is not is the point.**"
    readme should not include "is the second:"
    readme should not include "The third is"
    evaluation should not include "there are three of them now"
    evaluation should not include "None of the three"

    info(s"${prover.searches.size} searches named in ${cells.size} documents: " +
      prover.searches.map(_.spelling).mkString(", "))
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

    Prove.standard(goal).map(_.theorem.hypotheses) shouldBe Right(Nil)
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

  it should "settle the guide's domain claim at the accounting the guide prints beside it" in {
    // The block below that one is run by `GuideBlocksSpec`, which says the text compiles; this says
    // the answer printed under it is the answer it gives. The two guards are the pair that section
    // describes, and this is the half that would catch a summary line rewritten by hand.
    val onChange = Type.fun(TyApp("change", Nil), Type.Bool)
    val gate = Domain(
      name = "the release gate",
      typeOperators = Vector("change" -> 0),
      constants = Vector("TwoReviews" -> onChange, "Ships" -> onChange),
      axioms = Vector("ShipsOnlyReviewed" -> "!r:change. Ships r ==> TwoReviews r")
    )
    val built =
      force(Domain.build(Classical.standard.theory, Classical.standard.notation, gate))

    val summary = built.settle(Classical.standard, "!r:change. ~(TwoReviews r) ==> ~(Ships r)") match {
      case Domain.Verdict.Settled(_, spending) => spending.summary
      case other => fail(s"the guide's own claim must be settled: $other")
    }

    summary shouldBe "the release gate: 1 of 1: ShipsOnlyReviewed, and no foundational axiom at all"
    read("docs/proving.md") should include(s"// Settled: $summary")
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

  "Every module directory" should "be aggregated by the root, or its suite does not run" in {
    // What this probes, and it is not tidiness. `sbt test` runs the projects the root aggregates and
    // nothing tells anybody about one it does not: `sat` landed on 2026-09-15 without its name on
    // that line and the whole suite went green over a module whose sixteen tests were never
    // executed. The figure reported for it that hour came from running `sat/test` by hand, which is
    // a different claim from "the gate covers it" and reads identically.
    //
    // Read from the directories rather than from a list written here, for the reason the verdict
    // census one file over is read from the sources: a list in a test is one more place to forget.
    val build = read("build.sbt")
    val aggregated = "\\.aggregate\\(([^)]*)\\)".r
      .findFirstMatchIn(build)
      .map(_.group(1).split(",").map(_.trim).toSet)
      .getOrElse(Set.empty)

    val directories = java.nio.file.Files
      .list(locate("build.sbt").getParent.resolve("modules"))
      .filter(java.nio.file.Files.isDirectory(_))
      .map[String](_.getFileName.toString)
      .toArray
      .map(_.toString)
      .toSet

    // `aggregate` is a directory holding no source: it is the pom that names the others, and it is
    // in the list under the name the build gives it rather than the name on disk.
    val missing = directories -- aggregated - "aggregate"
    withClue(s"module directories the root does not aggregate, so their tests never run: ${missing.mkString(", ")}\n") {
      missing shouldBe empty
    }

    // The half that can go empty: a regex that matched nothing would report no module missing.
    aggregated should contain("sat")
    aggregated.size should be > 8
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
    withClue("the seven library modules and the aggregate take the publishing settings: ") {
      // Seven since 2026-09-15, when `sat` landed. It publishes for the reason the other six do and
      // not because everything does: `logic` depends on it, so a consumer resolving `symbolum-logic`
      // from a registry cannot get a jar without it.
      applied shouldBe 8
    }

    // The half of the assertion that can go empty. Counting the modules that publish says nothing
    // about a module that quietly started publishing beside them, and `mark` is the one that would
    // hurt: it regenerates two files under `docs/`, so a consumer resolving it gets a tool that
    // writes into their working directory. The count above would not move.
    // Comment lines dropped first: the paragraph above these settings names the setting it is
    // about, so a count over the whole file counts a sentence as a module. `scan.Comments` decides
    // which lines those are since 2026-09-16, where the five other sites asking the same question
    // decide it too; what this one had was the loosest of the three line filters, with no state for
    // a block comment at all, so a `publish / skip` named inside one would have counted.
    val skipped = Comments
      .codeLines(build)
      .count(_.code.contains("publish / skip := true"))
    withClue(
      "`root`, `examples`, `mark`, `dist`, `scan` and the two fatal-warnings probes are the " +
        "seven that do not publish: "
    ) {
      // Seven since 2026-09-18, when the two probe projects landed: a source that must not compile
      // and the control that compiles the same source without `-Xfatal-warnings`. Neither is a
      // module of this system, the root aggregates neither, and publishing a project whose
      // compilation is expected to fail would be publishing a build error under a coordinate.
      skipped shouldBe 7
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
      case Right(outcome) =>
        fail(s"the guide says this is not a theorem as written, and got ${outcome.theorem.conclusion}")
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
    //
    // **It read the whole document and one direction until 2026-09-18, and both halves of that let
    // a defect through.** Measured that day rather than reasoned about: with `LE_MUL_BOTH` and
    // `INV_ANTITONE` added to `Order`, the table left untouched, and the two names written into a
    // PROSE paragraph three screens away, the old assertion passed. What a reader of this guide
    // looks at is the table, so a name satisfying the guard from a sentence somewhere else is the
    // guard being satisfied by something that is not the thing. **Both observations are runs and
    // not readings**: the old assertion was seen passing with the rows gone and the prose present,
    // and this one was seen failing on the same document, naming `LE_MUL_BOTH` as in the order and
    // not in the table.
    //
    // So the population is the table's rows, and the check is both directions. The second is not
    // symmetric decoration: a row naming a fact that has been deleted is a reader sent to look for
    // something that is gone, which this repository calls worse than a gap.
    //
    // **What it still does not cover**, said rather than left to be assumed: it reads each row for
    // the NAME and not for the statement beside it, so a row whose statement has drifted from the
    // lemma passes here. `OrderSpec` is what reads the statements, by printing each one and
    // comparing the text, and the two halves live in different modules because the statements are
    // `theories`' to print and the table is a document this module can read.
    // The table and not every table: this document holds a second one, of the classical facts, whose
    // rows have the same shape. The population is the run of rows that follows the sentence
    // introducing this one, so the scan is anchored to the prose rather than to a line number.
    val opening = "Each is proved, and `OrderSpec` prints every one of them:"
    val lines = read("docs/proving.md").linesIterator.toVector
    val at = lines.indexWhere(_.contains(opening))
    withClue(s"docs/proving.md no longer holds the sentence `$opening`: ") { at should be >= 0 }

    val row = """^\| `([A-Z_]+)` \|""".r
    val tabled = lines
      .drop(at)
      .dropWhile(line => !line.startsWith("|"))
      .takeWhile(_.startsWith("|"))
      .flatMap(line => row.findFirstMatchIn(line).map(_.group(1)))
      .toSet
    val held = Order.standard.facts.keySet

    withClue(s"in the order and not in the guide's table: ${(held -- tabled).toVector.sorted.mkString(", ")}\n") {
      (held -- tabled) shouldBe empty
    }
    withClue(s"in the guide's table and not in the order: ${(tabled -- held).toVector.sorted.mkString(", ")}\n") {
      (tabled -- held) shouldBe empty
    }

    // What would make both assertions above pass without reading anything, which is the question
    // `RestsOnSpec` asks of a guard of this shape: a pattern that matched no row leaves both
    // differences empty and reports no defect. The floor is what the table held when this was
    // written and can only rise.
    withClue(s"the row pattern matched ${tabled.size} row(s), which is too few to be the table: ") {
      tabled.size should be >= 25
    }
    info(s"${tabled.size} order facts, in the guide's table and in `Order.standard` alike")
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

  it should "list the notebook's cells as the code publishes them, so an eighth cannot go unlisted" in {
    // **`derive` landed and this list stayed at seven for a day**, in the paragraph a session reads
    // before touching the notebook, and three things passed over it without seeing it: a full suite
    // of 2271, a verification of the card that added the command, and a session that rewrote the
    // very next paragraph of that file to repair a *different* false sentence about `derive`. That
    // is where this test comes from rather than a worry about the future: what watches a sentence
    // is something in the tree it gets compared against, and until this test every reading of
    // `CLAUDE.md` here compared a number. This one compares a list, so the shape that had nothing
    // watching it was not "prose without a figure" but prose no test had an anchor in.
    //
    // The shape is the one the test below uses on the kernel's directory, pointed at an enumeration
    // instead: a hand-kept list compared with a live one by equality in both directions, so a
    // command added without the document moving fails here, and a command removed from the code
    // while the document still advertises it fails here too. The second direction is not
    // decoration — a cell a reader is told about and cannot type is the worse of the two.
    //
    // **And this guard does not extend to the same figure written inside a Scala source, which is
    // where the fourth one was.** `Session.scala` said "naming the seven" eight lines under the
    // enumeration that holds eight; the repair deleted the count, and the question asked before
    // closing that card was whether it could have been watched instead. Measured on 2026-09-16,
    // and the answer is no for three different reasons, of which only the last is interesting:
    //
    //   - **A census is the wrong order of magnitude.** The shape `the <cardinal>` with the
    //     pronoun `the one` excluded stands at 2548 sites in 283 Scala files, 136 of them in
    //     `modules/tactics/src/main`. This comment is one of the 2548 and the number moved while
    //     it was being written, which is the honest form of the argument: it is an order of
    //     magnitude and not a figure anything can pin. A hand-kept list against a live one works
    //     one paragraph above because the hand-kept side is eight entries.
    //   - **Reading the number instead of listing it needs to know what it counts, and English
    //     does not say.** The narrowest rule that fires on the defect — a cardinal in a comment
    //     sentence that also names a command, a keyword or a cell — finds four sentences in
    //     `Session.scala` and three of them are innocent: a forty-cell session, `cell 9` citing
    //     `cell 7`, and the two theories `SoundnessAttackSpec` needs. A gate that is wrong three
    //     times in four is one somebody argues with rather than fixes. And it still finds four
    //     after the repair, because the sentence that was the defect is now the sentence that
    //     records it and matches just as well, which is the next point.
    //   - **A ban fires on the record of the repair, which is the one that settles it.** This
    //     repository writes the defect's history beside the code, and that history quotes the
    //     wrong number: the docstring on `Session.Command` carries "six" and "eight" because it
    //     is the repair of the third sentence, and the repair of the fourth carries "seven" for
    //     the same reason. Any rule that recounts or forbids cardinals in comments goes red on
    //     the fix, so the discipline that catches these and the guard that would watch them are
    //     in each other's way. Neither repair is cited by line above, because a line number in a
    //     comment is this same defect one level up.
    //
    // What can be watched is a sentence with an anchor, which is what the regular expression above
    // is, and the price is that the wording is frozen: a rewrite that loses the anchor also
    // disarms the guard, which is why the `getOrElse(fail(...))` and the emptiness clue above are
    // load-bearing rather than defensive. The other route is the one both repairs in that file
    // took, to delete the number and cite the enumeration with a scaladoc link — and **that form
    // is not checked here today**: scaladoc reports an unresolvable link and nothing fails on it.
    // Measured the same day, `sbt tactics/doc` exits 0 while naming six of them in
    // `modules/tactics/src/main`; `-Xfatal-warnings` is already set and does not reach them, and
    // neither does `-Wconf:msg=No DRI found:e`. Arming that is a gate of its own and has a card.
    val document = read("CLAUDE.md")
    val sentence = """of cells over one `Session`:(.*?)\. The chain is built""".r
      .findFirstMatchIn(document.replace("\n", " "))
      .map(_.group(1))
      .getOrElse(fail("CLAUDE.md no longer introduces the notebook's cells; this guard reads that sentence"))

    val listed = """`([a-z]+)`""".r.findAllMatchIn(sentence).map(_.group(1)).toVector

    // The empty case is what would make the equality below pass on a sentence that lists nothing,
    // and it is reachable: the regular expression above is the only thing tying this to the
    // document's wording, and prose is what moves here.
    withClue(s"the sentence this read was `$sentence`: ") { listed should not be empty }

    // Named in both directions rather than left to a reader diffing two eight-element vectors by
    // eye, which is what the bare equality printed when it was first fired at its own defect. A
    // guard whose failure has to be decoded is one somebody re-runs to see whether it is real.
    val published = Session.Command.Keywords
    withClue(
      s"listed and not published: ${(listed.toSet -- published.toSet).mkString(", ")}; " +
        s"published and not listed: ${(published.toSet -- listed.toSet).mkString(", ")}\n"
    ) {
      listed.sorted shouldBe published.sorted
    }
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

  "The name of the widest link" should "be read off the field, because four sentences had it wrong" in {
    // **This is the fourth, fifth, sixth and seventh occurrence of one defect, and the first guard
    // over it.** `Chain.widest` is whatever link extended the theory last, and the field's own
    // docstring says the name is not written in prose anywhere because it had already gone stale
    // twice by 2026-09-13. On 2026-09-17 it was stale in four more places at once: `CLAUDE.md` said
    // `Inductive` was the widest, `Chain`'s own docstrings said `Transcendental` and `Reaching`
    // were, and two of them added that their link was the last one. The field read `forward`, and
    // two links had landed on top of the newest of those claims on the day it was written.
    //
    // What makes this worth a test rather than another careful sentence is the shape: nothing goes
    // red when a link lands, the sentence that was true yesterday reads exactly like one that is
    // true today, and the file that warns against writing the name carried the claim four hundred
    // lines further down. This compares the claim with the field.
    //
    // **What it does not cover, which is half of what was found.** A docstring saying its link
    // "is last" is the same defect and has no shape a regular expression can separate from the
    // prose around it: `deduction`'s says "the last link and the widest signature stopped being the
    // same thing", which is a general statement and true, and `rotation`'s says "what is last is
    // the only thing that moved". A ban on the words fires on both, and on the record of every
    // repair, which is the argument the notebook guard above makes at length about cardinals. So
    // the positional claim is left to reading and only the widest one is held here.
    //
    // `docs/adr/` is not scanned, deliberately: a record made on the day of a decision may name the
    // widest link truthfully and is superseded rather than edited afterwards, so a gate over it
    // would demand rewriting history to stay green.
    //
    // **Both halves were seen failing before they were believed**, which for a guard written after
    // the fact is the whole of the evidence. The prose half was run against `CLAUDE.md` at
    // `fff7434` and returned `Inductive`; the docstring half was run with
    // "and [[widest]] since 2026-09-16" put back on `reaching` and answered
    // "`widest` is `forward` and these docstrings say otherwise: reaching". Neither perturbation is
    // in the tree: what is kept is the sentence above and the positive control below.
    val chain = read("modules/theories/src/main/scala/garden/xeno/symbolum/theories/Chain.scala")

    val constructor = chain.split("\n\\) \\{").head
    val widest = """val widest: Signature = (\w+)""".r
      .findFirstMatchIn(chain)
      .map(_.group(1))
      .getOrElse(fail("Chain.scala no longer defines `widest` as one of its own fields; this guard reads that line"))

    // `(?s)` because a docstring is many lines and `.` does not cross one without it, which is the
    // way this guard would have read zero docstrings and passed.
    val documented = """(?s)/\*\*(.*?)\*/\s*\n\s*val (\w+): \w+""".r
      .findAllMatchIn(constructor)
      .map(matched => matched.group(2) -> matched.group(1))
      .toVector

    // The half that can go empty: a pairing that matched nothing would report no false claim. The
    // chain had thirty fields and twenty-two documented ones when this was written, and what the
    // bound is for is a regular expression that stops pairing, not a link that arrives undocumented.
    withClue(s"the docstrings of `Chain`'s fields no longer parse, so this guard reads nothing: ") {
      documented.size should be > 15
    }

    val claiming = """(and \[\[widest\]\] since|is \[\[widest\]\]|is `Chain\.widest`)""".r
    val claimants = documented.collect { case (link, text) if claiming.findFirstIn(text).isDefined => link }
    withClue(s"`widest` is `$widest` and these docstrings say otherwise: ${claimants.mkString(", ")}\n") {
      claimants.filterNot(_ == widest) shouldBe empty
    }

    // The prose half, over the documents a reader is sent to rather than the sources. Normalised
    // first, because every one of these is hard-wrapped and the sentence that was wrong spanned two
    // lines: a pattern matched against the file as it is stored finds nothing and reads as a pass.
    val shape = """`([A-Z]\w+)`[^`]{0,60}?is `Chain\.widest`""".r

    // Fired against the sentence it was written for before being trusted, which is the only thing
    // that separates a guard from a decoration. This is `CLAUDE.md` as of `fff7434`.
    withClue("the pattern no longer matches the defect it was written against: ") {
      shape
        .findFirstMatchIn("The set defined by rules is `Inductive`, and it is `Chain.widest` since 2026-09-16.")
        .map(_.group(1)) shouldBe Some("Inductive")
    }

    Vector("CLAUDE.md", "README.md", "docs/architecture.md", "docs/proving.md", "docs/evaluation.md")
      .foreach { document =>
        val prose = read(document).replaceAll("\\s+", " ")
        val named = shape.findAllMatchIn(prose).map(_.group(1)).toVector.filterNot(_ == widest)
        withClue(s"$document names ${named.mkString(", ")} as the widest link, and it is `$widest`: ") {
          named shouldBe empty
        }
      }
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
  /* ------------------------------------------------- the map of the chain */

  /**
   * The first column of the guide's map of the chain, as the document writes it.
   *
   * Read out of that one section rather than out of the whole file, which is the difference between
   * an assertion and a vacuous one: `Order`, `Series`, `Peano` and `Limit` are all named in the
   * prose elsewhere in the guide, so a check that merely asked whether the file contains the word
   * would pass with the map deleted.
   */
  private def mappedDevelopments(guide: String): Vector[String] = {
    val lines = guide.linesIterator.toVector
    val opens = lines.indexWhere(_.startsWith("## What the chain holds"))
    if (opens < 0) fail("docs/proving.md no longer holds the section this test is about")
    val closes = lines.indexWhere(line => line.startsWith("## "), opens + 1)
    val rows = lines.slice(opens + 1, if (closes < 0) lines.length else closes)

    rows.flatMap("""^\| `([A-Za-z]+)` \|""".r.findFirstMatchIn(_)).map(_.group(1))
  }

  "The guide's map of the chain" should "name every development the library holds, and no others" in {
    // The population is the library's own, which is where `docs/lemmas.md` gets its headings: a
    // development the chain assembles and nobody collected is `ChainCoverageSpec`'s defect and not
    // this one. The label carries what it was collected under, `Real, assumed` beside
    // `Real, defined`, and the map has one row per development rather than one per label, so the
    // comparison is on the name before the comma.
    val guide = read("docs/proving.md")
    val held = Library.of(Chain.standard).entries
      .map(_.development.takeWhile(_ != ','))
      .distinct
      .sorted
    val mapped = mappedDevelopments(guide)

    // A link added to `Chain.construct` and collected by `Library.of` lands here, which is what the
    // guide's own sentence about this test promises a reader.
    withClue(s"held by the library and not in the guide's map: ${held.diff(mapped).mkString(", ")}\n") {
      held.diff(mapped) shouldBe empty
    }

    // And the other direction, which is the one that rots quietly: a row describing a development
    // that has been renamed or removed is a stale reference, and this repository treats one of
    // those as worse than a missing entry.
    withClue(s"in the guide's map and not held by the library: ${mapped.diff(held).mkString(", ")}\n") {
      mapped.diff(held) shouldBe empty
    }

    // The rows are unique, because a name written twice would let one of the two carry a wrong
    // description while the set comparison above stayed green.
    mapped.distinct shouldBe mapped
    info(s"${mapped.size} developments in the guide's map")
  }

  it should "say what each development puts in the signature, which is the column that carries the map" in {
    // The guard above is satisfied by a table of names and empty cells, and a map of empty cells is
    // exactly the shape a coverage check rewards. So the width of a row is asserted too: three
    // columns, and the middle one says something.
    val guide = read("docs/proving.md")
    val lines = guide.linesIterator.toVector
    val opens = lines.indexWhere(_.startsWith("## What the chain holds"))
    val closes = lines.indexWhere(line => line.startsWith("## "), opens + 1)

    val rows = lines
      .slice(opens + 1, if (closes < 0) lines.length else closes)
      .filter(line => """^\| `[A-Za-z]+` \|""".r.findFirstIn(line).isDefined)

    rows.foreach { row =>
      val cells = row.split('|').toVector.map(_.trim).filter(_.nonEmpty)
      withClue(s"a row of the map is not three columns wide: $row\n") {
        cells.size shouldBe 3
      }
      withClue(s"the map says nothing about what this development is for: $row\n") {
        cells(2).length should be > 40
      }
    }
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

  "The build commands a session copies" should "go through the wrapper, which has to be there to go through" in {
    // **What this is about is not tidiness, and the measurement that produced it is not about this
    // repository at all.** The machine these sessions run on caps how many builds run at once,
    // because eight sbt JVMs out of eight worktrees killed two coverage runs and turned a
    // two-minute run into a twelve-minute one on 2026-09-16. The cap lives outside every checkout,
    // so nothing here can enforce it; what this file can do is make sure the instructions do not
    // send a reader around it. Measured that evening, five of the seven builds running had never
    // asked the cap for anything, and every one of them was a session running what `CLAUDE.md`
    // told it to run. The cap was not exceeded, it was bypassed, by people doing as they were told.
    //
    // So the assertion is on the document rather than on any behaviour: no command in it starts
    // `sbt`, and `tools/sbt` is a file that exists and can be executed. The second half is what
    // keeps the first from being a rename: a document whose commands all name a script that is not
    // there is worse than one naming `sbt`, because it fails at the shell instead of at the cap.
    val instructions = read("CLAUDE.md")

    withClue("a command in `CLAUDE.md` starts `sbt`, so copying it skips the machine's cap: ") {
      instructions should not include "`sbt "
    }

    // And the non-vacuous half. A document that stopped carrying commands would satisfy the line
    // above, so what is asserted is a relation inside the document instead of an absence: every
    // `runMain` it names is introduced by the wrapper, and there is at least one.
    val runners = instructions.linesIterator.filter(_.contains("runMain")).toVector
    runners should not be empty
    runners.foreach { line =>
      withClue(s"a `runMain` that is not run through the wrapper: $line\n") {
        line should include("tools/sbt \"")
      }
    }

    val wrapper = locate("tools/sbt")
    withClue(s"$wrapper is not executable, so every command in `CLAUDE.md` fails at the shell: ") {
      Files.isExecutable(wrapper) shouldBe true
    }

    // That it is the wrapper and not a stub with the right name. The variable is the whole of its
    // interface with the machine: a `tools/sbt` that does not read it is a `sbt` with a longer name.
    read("tools/sbt") should include("SYMBOLUM_BUILD_WRAPPER")

    // **What this does not cover, and the shape of it rather than a count that would go stale.**
    // `README.md`, `TESTING.md`, `CONTRIBUTING.md` and the documents under `docs/` still carry bare
    // invocations, and most of those under `docs/` are inside generated regions, so moving them is
    // a change to the generators rather than to the documents. Nor does it cover the `val Command`
    // constants that print `sbt "..."` at a user who has asked how to regenerate something. Both
    // populations are one grep away, which is the point of not writing their sizes here:
    //
    //     git grep -n '`sbt ' -- '*.md'
    //     git grep -n 'val Command: String = "sbt' -- modules
    //
    // What is asserted is what the card asked for: a session reading `CLAUDE.md` and nothing else
    // cannot start a build outside the cap without deciding to. The rest is a decision of its own.
  }

}
