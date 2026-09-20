package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * The rewriting combinators, on equations assumed rather than proved.
 *
 * Assuming an equation gives a theorem like any other, and rewriting with it produces a theorem
 * that carries the assumption. That is the property to watch in the first test: a rewrite does not
 * quietly drop what it depended on.
 *
 * The variables here are called `u` and `w` rather than `a` and `b` because ScalaTest's matchers
 * already define values with those names, and shadowing them is a compile error rather than a
 * confusion.
 */
class RewriteSpec extends AnyFlatSpec with Matchers {


  /**
   * Abstraction, forced.
   *
   * `Term.abs` refuses a body that is not locally closed, since 2026-09-10, so it returns a
   * refusal like `app` and `eq` do. Every body below is built out of variables and constants a
   * line or two above and none of them can be open, so forcing here is reading the signature and
   * not ignoring it. A test that meant to hand it an open body says so by calling `Term.abs`
   * directly and looking at the `Left`.
   */
  private def lam(variable: FVar, body: Term): Term =
    Term.abs(variable, body).fold(error => fail(s"unexpected refusal: $error"), identity)

  private val logic = Logic.standard
  private val alpha = TyVar("A")

  private val u = Term.variable("a", alpha)
  private val w = Term.variable("b", alpha)
  private val f = Term.variable("f", Type.fun(alpha, alpha))

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private def assumedRule(left: Term, right: Term): Rewrite.Rule =
    force(Rewrite.Rule.of(logic, force(Kernel.assume(force(Term.eq(left, right))))))

  private def rightOf(theorem: Kernel.Thm): Term =
    Term.destEq(theorem.conclusion).map(_._2).getOrElse(fail("expected an equation"))

  "Rewriting at the root" should "replace the term and keep what it assumed" in {
    val rule = assumedRule(u, w)
    val theorem = force(Rewrite.rewriteConv(rule)(u))

    theorem.conclusion shouldBe force(Term.eq(u, w))
    theorem.hypotheses shouldBe List(force(Term.eq(u, w)))
  }

  it should "leave a term no rule matches alone" in {
    val rule = assumedRule(u, w)
    val theorem = force(Rewrite.rewriteConv(rule)(w))

    Rewrite.changed(theorem) shouldBe false
  }

  /* ------------------------------------------------- what a pass over nothing costs */

  "A pass that changes nothing" should "build no proof of it" in {
    // The repair of 2026-09-11, and the measurement it is worth is in `CostCorpusSpec`: about a
    // third of every proof in somebody else's corpus was a rewriting pass reporting, in primitive
    // inferences, that it had done nothing. A congruence over two identities is the identity on the
    // application, and a chain through an identity is the other step; both were being built.
    val rule = assumedRule(u, w)
    val term = force(Term.app(f, w))
    val theorem = force(Rewrite.depthConv(Rewrite.rewriteConv(rule))(term))

    Rewrite.changed(theorem) shouldBe false
    Rewrite.idle(theorem) shouldBe true

    // One node, and it is the reflexivity the caller asked for rather than a congruence and two
    // chains that arrive at the same place.
    Derivation.size(theorem) shouldBe 1
  }

  it should "be the same theorem it was before, and not merely a theorem like it" in {
    // What makes the repair safe: the conclusion is what the congruence would have concluded and
    // the hypotheses are what it would have carried. Nothing above is an optimisation of the
    // answer, only of the work.
    val rule = assumedRule(u, w)
    val term = force(Term.app(f, force(Term.app(f, w))))
    val theorem = force(Rewrite.rewrite(Vector(rule), term))

    theorem.conclusion shouldBe force(Term.eq(term, term))
    theorem.hypotheses shouldBe empty
  }

  "A pass that changes one leaf of many" should "pay for that leaf and not for the rest" in {
    // The other half of the claim. A term where one rule fires once still needs a congruence up
    // every level from the leaf to the root, and that is the cost of saying where the change was;
    // what it no longer needs is a congruence across the parts that did not change.
    val rule = assumedRule(u, w)
    val deep = force(Term.app(f, force(Term.app(f, force(Term.app(f, u))))))
    val theorem = force(Rewrite.rewrite(Vector(rule), deep))

    Rewrite.changed(theorem) shouldBe true
    rightOf(theorem) shouldBe force(Term.app(f, force(Term.app(f, force(Term.app(f, w))))))

    // Three congruences, the instance of the rule, and the chains that put them together. The
    // number is pinned because the point of the change is that it is a function of the depth of
    // the change rather than of the size of the term.
    Derivation.size(theorem) should be < 20
  }

  "An identity step" should "be told from a step that merely looks like one" in {
    // `idle` is deliberately narrower than `changed`: the same object on both sides, and nothing
    // assumed. A step that rewrote a term into something structurally equal is not idle, and a
    // step that changed nothing while resting on an assumption is not either, because dropping the
    // assumption would make the finished theorem claim to rest on less than it does.
    val reflexivity = Kernel.refl(u)
    Rewrite.idle(reflexivity) shouldBe true
    Rewrite.changed(reflexivity) shouldBe false

    val assumed = force(Kernel.assume(force(Term.eq(u, u))))
    Rewrite.changed(assumed) shouldBe false
    Rewrite.idle(assumed) shouldBe false

    val moved = force(Rewrite.rewriteConv(assumedRule(u, w))(u))
    Rewrite.idle(moved) shouldBe false
  }

  "Rewriting at depth" should "reach inside an application" in {
    val rule = assumedRule(u, w)
    val theorem = force(Rewrite.depthConv(Rewrite.rewriteConv(rule))(force(Term.app(f, u))))

    rightOf(theorem) shouldBe force(Term.app(f, w))
  }

  it should "reach under a binder and put the binder back" in {
    val rule = assumedRule(u, w)
    val abstraction = lam(Term.variable("z", alpha), force(Term.app(f, u)))
    val theorem = force(Rewrite.depthConv(Rewrite.rewriteConv(rule))(abstraction))

    rightOf(theorem) shouldBe lam(Term.variable("z", alpha), force(Term.app(f, w)))
  }

  it should "reach under a binder even when the rewrite brings its own hypothesis" in {
    // The variable that opens the binder is chosen before the conversion runs, so it can collide
    // with a variable in the hypothesis the conversion attaches. The second attempt knows the
    // hypotheses and avoids them. Same shape as the defect an audit probe found in conjIntro.
    val v = Term.variable("v", alpha)
    val rule = assumedRule(u, v)
    val abstraction = lam(Term.variable("z", alpha), force(Term.app(f, u)))

    val theorem = force(Rewrite.depthConv(Rewrite.rewriteConv(rule))(abstraction))

    rightOf(theorem) shouldBe lam(Term.variable("z", alpha), force(Term.app(f, v)))
    theorem.hypotheses shouldBe List(force(Term.eq(u, v)))
  }

  "A quantified theorem" should "become a rule over the variables it quantified" in {
    // `!x. f x = x` rather than `!x. x = x`, which is what this read until 2026-09-12. The two make
    // the same point about the plumbing and only one of them is a rule: a left side that is one of
    // the rule's own variables matches every subterm there is, and `Rule.of` refuses that shape
    // since the day a lemma of it ran a suite for an hour. The refusal is asserted below.
    val x = Term.variable("x", alpha)
    val body = force(Term.eq(force(Term.app(f, x)), x))
    val quantified = force(Kernel.assume(force(logic.mkForall(x, body))))
    val rule = force(Rewrite.Rule.of(logic, quantified))

    rule.variables should have size 1
    Term.typeOf(rule.lhs) shouldBe alpha
  }

  it should "be refused when its left side is one of those variables, rather than diverging" in {
    // Measured rather than argued. `NUM_DIV_MOD` was first stated as `m = n * (m DIV n) + m MOD n`,
    // `Novelty` turns every equation in the library into a rule, and the rewriter then replaced
    // every term with a larger one containing it: the suite did not fail, it ran for an hour on a
    // term that doubled every step and was killed. A step limit cannot help, because the size grows
    // by a factor per step rather than by a term.
    //
    // Both halves of the refusal are here. The second is the rule whose right side asks for
    // something matching cannot determine.
    val x = Term.variable("x", alpha)
    val growing = force(logic.mkForall(x, force(Term.eq(x, force(Term.app(f, x))))))
    Rewrite.Rule.of(logic, force(Kernel.assume(growing))).isLeft shouldBe true

    val y = Term.variable("y", alpha)
    val undetermined = force(
      logic.mkForall(x, force(logic.mkForall(y, force(Term.eq(force(Term.app(f, x)), y)))))
    )
    Rewrite.Rule.of(logic, force(Kernel.assume(undetermined))).isLeft shouldBe true
  }

  /* ----------------------------------- a rule that puts its own left side back */

  "A rule with no variables whose right side contains its left" should
    "be refused by everything that repeats, rather than running out of heap" in {
    // Found on 2026-09-18 and not by reading. Turning an equation already derived into a rule is
    // the obvious move, and `NUM_ADD ZERO ZERO = ZERO` read the other way round is
    // `ZERO -> NUM_ADD ZERO ZERO`. Neither guard above bites, because both are about a variable and
    // this rule has none; the right side holds two copies of the left, so each round of
    // `repeatConv` doubles them and the size is exponential in the number of rounds. `DefaultLimit`
    // is 200 and 2^200 arrives at the heap first, which is the sentence `Rule.of` already carries
    // for `NUM_DIV_MOD`. The run that found it was gone in four and a half minutes.
    val reproducing = assumedRule(u, force(Term.app(f, u)))

    // **The rule is built**, and that is the decision this test is about as much as the refusal is:
    // whether a rule can be iterated is not a property of the rule alone, so `Rule.of` is not where
    // this can be asked. The test below says what it would have cost there.
    reproducing.reproduces shouldBe true

    // **Seen failing before it was trusted**, 2026-09-18: with `Rule.reproduces` forced to `false`,
    // which is the tree that carries the defect, this test goes red and the three below it stay
    // green. That is the shape the observation has to have, because the three are controls and a
    // perturbation that reddened them too would mean the guard was refusing more than this.
    // The two published ways to iterate a rule set, and the door the incident came through.
    Rewrite.rewrite(Vector(reproducing), u).isLeft shouldBe true
    Rewrite
      .inTheorem(Vector(reproducing), force(Kernel.assume(force(Term.eq(u, u)))))
      .isLeft shouldBe true
    Rewrite
      .normaliser(Vector(reproducing), Vector.empty, Ordering.by(Rewrite.nodesOf))(u)
      .isLeft shouldBe true
  }

  it should "still be usable by a caller that does not repeat, as four derivations here do" in {
    // `Arithmetic.timesZero` derives `x * 0 = 0` by rewriting `x * 0` with `0 = 0 + 0`, which is
    // exactly this shape, and `Order` and `Linarith` do the same with `0 = 0 - x` and its
    // relatives. Counted on 2026-09-18 over every rule the whole suite builds, those four are all
    // of it, and every one hands its rule to a single `depthConv`: one pass, one replacement,
    // finished. A refusal in `Rule.of` would have meant rewriting four derivations the arithmetic
    // and the order rest on, to satisfy a guard with no way of seeing the driver.
    val reproducing = assumedRule(u, force(Term.app(f, u)))
    val once = force(Rewrite.depthConv(Rewrite.rewriteConv(reproducing))(u))

    rightOf(once) shouldBe force(Term.app(f, u))
  }

  it should "not take a closed rule that merely grows, the criterion the count corrected" in {
    // The card that asked for this guard asked for a refusal on SIZE, and the count refused the
    // card. Of the distinct closed rules the whole suite builds whose right side has more nodes
    // than their left, all but the four above do not contain their left side and are ordinary:
    // every definition unfolded as a rule is one, `MAT_MUL` at 91 nodes against 1 being the
    // largest, and `NUM_ONE = SUC ZERO`, which is what `Successor` opens every numeral with, the
    // smallest. A guard on size takes all of them. This is the assertion that says containment is
    // the criterion.
    val grows = assumedRule(u, force(Term.app(f, w)))

    grows.reproduces shouldBe false
    Rewrite.rewrite(Vector(grows), u).isRight shouldBe true
  }

  it should "leave a rule that has a variable alone, since nothing here is a termination check" in {
    // `!x. f x = f (f x)` reproduces its own left side under every match, and it is accepted and
    // diverges: the step limit is what stops it, and `Rule.of` says of itself that it is not a
    // termination check. `reproduces` is asked only of a rule with nothing to instantiate, because
    // for one with variables the answer depends on what the matcher put there and no property of
    // the rule settles it. Without this line the guard could have become the check it is not, and
    // nothing else here would have noticed.
    val x = Term.variable("x", alpha)
    val pattern = force(Term.app(f, x))
    val diverging = force(
      Rewrite.Rule.of(
        logic,
        force(
          Kernel.assume(
            force(logic.mkForall(x, force(Term.eq(pattern, force(Term.app(f, pattern))))))
          )
        )
      )
    )

    diverging.reproduces shouldBe false
    Rewrite.rewrite(Vector(diverging), u).isRight shouldBe true
  }

  it should "then apply at every instance of its pattern" in {
    // `!x. f x = x` assumed as a whole rather than generalised from an assumption about one x:
    // generalising over a variable that is free in a hypothesis is exactly what the kernel's
    // abstraction rule refuses, and rightly.
    val x = Term.variable("x", alpha)
    val statement = force(logic.mkForall(x, force(Term.eq(force(Term.app(f, x)), x))))
    val rule = force(Rewrite.Rule.of(logic, force(Kernel.assume(statement))))

    val nested = force(Term.app(f, force(Term.app(f, u))))
    val theorem = force(Rewrite.rewrite(Vector(rule), nested))

    rightOf(theorem) shouldBe u
    theorem.hypotheses shouldBe List(statement)
  }

  "Repeating a conversion" should "stop when nothing changes" in {
    val rule = assumedRule(u, w)
    val theorem = force(Rewrite.repeatConv(Rewrite.rewriteConv(rule))(u))

    rightOf(theorem) shouldBe w
  }

  it should "stop at the limit rather than run forever" in {
    // Two rules that undo each other: rewriting alternates for as long as it is allowed to. The
    // theorem it returns is still an equation between the term it started from and the one it
    // reached, which is true whichever way the alternation stopped.
    val there = assumedRule(u, w)
    val back = assumedRule(w, u)
    val alternating = Rewrite.firstConv(Vector(there, back).map(Rewrite.rewriteConv))
    val theorem = force(Rewrite.repeatConv(alternating, 7)(u))

    Term.destEq(theorem.conclusion).map(_._1) shouldBe Some(u)
    rightOf(theorem) should (equal(u) or equal(w))
  }

  "Beta conversion" should "contract a redex found while rewriting" in {
    val identity = lam(u, u)
    val redex = force(Term.app(identity, w))
    val theorem = force(Rewrite.betaConv(redex))

    rightOf(theorem) shouldBe w
  }

  "Proving by rewriting" should "join two sides that reach the same form" in {
    val rule = assumedRule(u, w)
    val theorem = force(Rewrite.prove(Vector(rule), force(Term.app(f, u)), force(Term.app(f, w))))

    theorem.conclusion shouldBe force(Term.eq(force(Term.app(f, u)), force(Term.app(f, w))))
  }

  it should "refuse when the two sides do not meet" in {
    val rule = assumedRule(u, w)
    val other = Term.variable("c", alpha)

    // Both sides reach a normal form and the normal forms differ, so the identity is the thing at
    // fault. That is what `NotEqualTo` means, and the test below is the case it must not cover.
    //
    // It carries the two terms rather than a printed sentence, which is the point of the case: the
    // layer that raises it knows the connectives and not the arithmetic, so a term printed here
    // would be printed with a notation that does not know `+`. The surface renders them instead.
    // What it carries is the two normal forms, not the two inputs: the left side was rewritten on
    // the way. Asserting they differ is asserting the whole meaning of the case, since two normal
    // forms that met would not be a refusal at all.
    Rewrite.prove(Vector(rule), u, other) match {
      case Left(NotEqualTo(wanted, found)) => wanted should not be found
      case unexpected => fail(s"expected the two normal forms to be carried, got $unexpected")
    }
  }

  it should "say it ran out of steps rather than blame the identity" in {
    // Two rules that undo each other, so the rewriting alternates until the limit and stops at a
    // waypoint rather than at a normal form. The two sides then differ exactly as they do when the
    // identity is false, and the two findings must not arrive wearing the same `Left`: one says
    // raise the limit, the other says stop believing the claim.
    val there = assumedRule(u, w)
    val back = assumedRule(w, u)
    val other = Term.variable("c", alpha)

    Rewrite.prove(Vector(there, back), u, other, 7).left.map(_.getClass) shouldBe
      Left(classOf[NotNormalised])
  }

  it should "say so at any limit, and not only at an odd one" in {
    // What that assertion missed until 2026-09-10. The finished-or-not question was asked with the
    // **repeated** conversion, so a pair of rules that undo each other came back where it started
    // whenever the limit was even, `changed` was false, and the term was declared finished when the
    // rewriting had not finished at all. `DefaultLimit` is 200 and even, so the shape a caller
    // actually meets was the one this reported wrongly; the line above passed on its choice of 7.
    val there = assumedRule(u, w)
    val back = assumedRule(w, u)
    val other = Term.variable("c", alpha)

    Vector(6, 7, 8, Rewrite.DefaultLimit).foreach { limit =>
      withClue(s"at a limit of $limit: ") {
        Rewrite.prove(Vector(there, back), u, other, limit).left.map(_.getClass) shouldBe
          Left(classOf[NotNormalised])
      }
    }
  }

  /* ------------------------------------------ the boundary the compiler cannot check */

  /**
   * Every `src/main` under `modules/`, asked of the disk rather than written down.
   *
   * The two censuses below each carried `Vector("kernel", "logic", "theories", "tactics", "core",
   * "checker")` until 2026-09-19, the second copied from the first with a comment saying so, and
   * the list was wrong in both directions at once. Measured against `build.sbt` on that day:
   * `kernel`, `core` and `sat` declare no dependency and `checker` depends on `kernel` alone, so
   * **three of the six roots cannot name `Rewrite` however the scan is written**; and `examples`
   * depends on `tactics` and `dist` on `tactics` and `examples`, so **two modules whose `src/main`
   * does reach `Rewrite` were read by neither census**. Both censuses were green, because a scan
   * that does not look somewhere reports nothing from there and reads exactly like a scan that
   * looked and found nothing.
   *
   * Nothing was being missed on the day this was repaired: `repeatConv(` over all twelve modules
   * returns `logic/Rewrite.scala` and `theories/Field.scala` and nothing else, and the first
   * census's three patterns return files in `logic`, `theories` and `tactics` alone. The hole was
   * latent, and the repair is worth making while it still is.
   *
   * **A derived list is not a shorter way to write the list; it is a different kind of thing.**
   * `SourceLanguageSpec` reached this shape first and its docstring carries the argument: a module
   * added tomorrow is scanned tomorrow, where a written list is scanned when somebody remembers.
   * `NotationBoundarySpec.moduleRoots` is the same walk, and this is deliberately a third copy
   * rather than a shared helper. The three cannot disagree, because all three ask one filesystem;
   * the six-name list could and did. Sharing them would want either a fourth module or a
   * `test->test` edge from `logic`, and `modules/scan`'s own docstring measures what that edge
   * costs for removing one copy of one function.
   *
   * What it does not cover: a project outside `modules/`. `tools/fatal-warnings-probe` is two such
   * projects, and the note beside the probe already records that they sit outside every scan that
   * reads `modules/`.
   */
  private def moduleRoots: Vector[java.nio.file.Path] = {
    val stream = java.nio.file.Files.list(java.nio.file.Paths.get("modules"))
    try
      stream
        .toArray
        .toVector
        .map(_.asInstanceOf[java.nio.file.Path].resolve("src/main"))
        .filter(java.nio.file.Files.isDirectory(_))
        .sortBy(_.toString)
    finally stream.close()
  }

  /** Every Scala source under one of [[moduleRoots]]. */
  private def mainSources: Vector[java.nio.file.Path] =
    moduleRoots.flatMap { root =>
      val stream = java.nio.file.Files.walk(root)
      try
        stream
          .toArray
          .toVector
          .map(_.asInstanceOf[java.nio.file.Path])
          .filter(_.toString.endsWith(".scala"))
      finally stream.close()
    }

  /**
   * Every call of `Rewrite.rewrite` in the repository, with what each one does about the limit.
   *
   * An entry is a claim that this call site does not read a later failure as a statement about the
   * mathematics. The scan below fails on a call site that is not listed, so a new one has to be
   * thought about once rather than found later.
   */
  private val ReviewedEntries: Vector[(String, String)] = Vector(
    // The one of 2026-09-16, and the first whose safety rests on a comparison against WRITTEN
    // statements rather than on termination alone.
    "Collatz.scala" ->
      ("four calls. Three unfold a definition of this file's own into the eleven-clause " +
        "disjunction it stands for, and what comes back is handed straight to a decision " +
        "procedure or refuted clause by clause, so an exhausted limit shows up as a goal the " +
        "procedure does not recognise rather than as a theorem about a half-unfolded term. The " +
        "fourth computes a word's length and IS given a limit it could reach: the rule set walks " +
        "a sum of `SUC 0`s down to a numeral, so a limit that ran out would leave an addition " +
        "unevaluated. It is not left to the limit to say so. What the caller does with the " +
        "answer is ask `NUM_SUC_INJECTIVE` to peel it, and a term still holding a `+` has no " +
        "successor at its root, so the peeling refuses by name instead of continuing"),
    "Forward.scala" ->
      ("two calls, both `Rewrite.inTheorem` and both moving a theorem between the two spellings " +
        "of one set, `INDUCTIVE op` and `WORD_RFC R`. The rule set each is given is a single " +
        "defining equation read in one direction, so there is nothing for a limit to run out on " +
        "that is not that equation failing to apply. It is not left to the limit to say so: the " +
        "result is compared against the operator's own clause and refused by `NotOfForm` naming " +
        "that clause when it does not land on it, which is the arrangement `Reaching` uses and " +
        "the reason a silent partial rewrite cannot reach the kernel from here"),
    "Reaching.scala" ->
      ("eight, and they fall into two arrangements. Six are a matched pair per site: the same rules " +
        "at the same default limit are walked FORWARD to learn the normal form a proof should be " +
        "aimed at, then BACKWARD across the same equation to hand the proof back in the shape the " +
        "machinery produced. A short walk gives the same short answer both times, so nothing is " +
        "unsound; what it would corrupt is the published statement, which would carry " +
        "`FST (PAIR y k)` where the caller wrote `y`. That is caught rather than argued: " +
        "`ReachingSpec` compares all five facts against `Reaching.Statements` as TERMS, so a walk " +
        "that stopped early fails the comparison. The other two are in the potential lemma, where " +
        "two independently rewritten sides have to MEET: the induction hypothesis is carried " +
        "forward and the goal backward, and `eqMp` refuses unless the two land on the same term, " +
        "so an exhausted limit is a refusal there rather than a weaker theorem. On termination, " +
        "all seven rule sets strictly reduce or cannot re-fire: the two projections and " +
        "`0 + n = n` shrink the term; `m + SUC n = SUC (m + n)` and `SUC m + n = SUC (m + n)` move " +
        "a successor outward and strictly reduce the successors under a sum; `INDUCTIVE op = " +
        "REACH R A x` fires once per occurrence because its right side holds no `INDUCTIVE`; and " +
        "the three ground equations taken from assumptions have left sides their own right sides " +
        "do not contain"),
    // The seven below arrived on 2026-09-15, when the scan was extended to `Rewrite.inTheorem`
    // and named them. Each is a reading of every call in the file, not of one of them.
    "Order.scala" ->
      ("seven, all through `inTheorem`, and this development publishes into a map with no table " +
        "of written statements, so what makes them safe is TERMINATION rather than a comparison " +
        "afterwards. Five rule sets strictly reduce: `x + -x = 0`, `0 + x = x`, `(y - x) + x = y`, " +
        "`c * 0 = 0`, `c * x + c * -x = 0`, and an assumed `x = 0` that puts a constant where a " +
        "variable was. One GROWS and terminates anyway, `(y - x) * c = y * c - x * c`, because its " +
        "own right side has no subterm of the shape `(A - B) * C`: the two products under it are " +
        "at variables. One INVERTS and terminates anyway, `1 = x * inv x`, because its right side " +
        "contains no `1`. What would catch a short walk even so is `OrderSpec`, which pins the " +
        "printed form of every fact this file publishes"),
    "Positivity.scala" ->
      ("two, one rule each, `0 + y = y` and an assumed `x = 0`, both strictly reducing. Neither " +
        "result is read as a normal form: one goes to `mp` against an instance of transitivity " +
        "and the other to `notElim` against `~(0 < 0)`, and both refuse unless the theorem is " +
        "exactly the shape they expect, so a limit that ran out refuses at the next step"),
    "Coding.scala" ->
      ("two, one rule each, replacing a greatest common divisor by the numeral an assumption says " +
        "it is, which strictly reduces. Both results feed `withTwoWitnesses`, which destructures " +
        "what it is handed as an existential over a disjunction, so a rule that had not fired " +
        "leaves the gcd standing and the destructuring refuses by shape"),
    "Divisibility.scala" ->
      ("one rule carrying a cancellation into a grouping, and what comes back is joined by " +
        "`Conv.trans` to an identity derived separately, which refuses unless the two sides meet. " +
        "The arrangement `Recursion` uses, for the same reason"),
    "Coefficient.scala" ->
      ("one, and the only site in this census whose termination rests on a guard in a different " +
        "function, so it is the one to re-read if either of those moves. The rule is " +
        "`product -> left * right` over numerals, and its right side would CONTAIN its left if " +
        "either factor were one, which is a walk that runs to the limit. Neither caller can " +
        "produce that: the multiplication path splits on `leftBottom == 1` and `rightBottom == 1` " +
        "before reaching it, and the addition path cannot reach it at all with a unit " +
        "denominator, because `valueOf` reports a denominator only when it is above one and `add` " +
        "routes every whole case to another lemma. With both factors above one the product " +
        "exceeds either, so the right side cannot contain the left. What comes back is then the " +
        "fact `instantiate` discharges a hypothesis with, and it refuses if it is not the form " +
        "the lemma asks for"),
    "Deduction.scala" ->
      ("one, two substitution rules, and the answer is written at the call site rather than only " +
        "here: a rewriting that ran out leaves a substitution standing, and `checked` then " +
        "refuses the rule against its published statement rather than publishing a code nobody " +
        "can read"),
    "Recorder.scala" ->
      ("one, and the only entry here whose answer is not in the file it is about. The rules are a " +
        "parameter, `equations: Vector[Kernel.Thm]`, so what a step limit means depends on the " +
        "caller's rule set and no reading of this file settles it. What this file owes instead is " +
        "that the step it records is the step that was taken: it hands the equations and a " +
        "`detail` naming them to `step`, so a walk that ran out is recorded as the rewriting it " +
        "actually did and a reader of the proof can see which rules were offered. The question " +
        "one level out is answered by the third door below and by `Magnitude.scala`'s entry, " +
        "which is the caller. Only `rewriteIn` is a walk: `Recorder.rewrite` is `depthConv` on " +
        "its own, one traversal of a finite term, and `rewriteSides`, `rewriteRight` and " +
        "`replace` are single kernel applications with no limit between them"),
    // The file the third door exists for, and the only caller that reaches the rewriter through
    // `Recorder` rather than directly. It holds ZERO `Rewrite.rewrite(` and zero
    // `Rewrite.inTheorem(`, so it was invisible to this scan while the scan read two doors, which
    // is the hole `Recorder.scala`'s entry declined to fill and could not fill from where it sits.
    "Magnitude.scala" ->
      ("eight through `Recorder.rewriteIn`, and none of them can reach the limit. The equations " +
        "are read off the recorded steps of `Magnitude.standard` rather than off how they are " +
        "built, which is what makes them seven and not eight: 34 recorded steps over 17 scripts " +
        "carry seven distinct rules, and 1169 and 1172 share one. Three fold a constant the same " +
        "expression has just defined, `select (\\y. ...) -> sgn x`, `select (\\z. ...) -> max x y` " +
        "and `max x (-x) -> abs x`: a constant cannot occur in its own body, so the body is gone " +
        "after one pass. Two rewrite with the branch equation of `MAX_CASES`, `max x y -> x` and " +
        "`max x y -> y`, whose right side is a variable that cannot contain the left. Three have " +
        "a closed right side: `abs x -> 0` twice, and `x -> 0` in `notBesideZero`. " +
        "**That last one is the one whose argument differs**, and it is why `every rule shrinks " +
        "the term` is not what this entry says: its LEFT side is a bare variable, so it matches " +
        "every subterm of type real rather than reducing anything. It terminates because its " +
        "right side is closed, so nothing it produces can match it again. " +
        "And the second half, because `cannot` is a reading and the first half rests on it: " +
        "three of the eight are refused at the call site if the rule had not fired, by " +
        "`Conv.trans` inside `chain`, by `modusPonens` against a stated antecedent, and by " +
        "`contradiction` against a negation. The other five publish, and what catches those is " +
        "`MagnitudeSpec`, which compares EVERY published fact's conclusion against a written " +
        "statement in the theory's own notation, so a fold that had not fired reads `select ...` " +
        "where the text says `abs` and fails naming the fact: 17 accessors published and 17 " +
        "pinned, with nothing on either side of the difference. " +
        "**What this measures and what it does not.** It measures the equations these eight " +
        "sites ARE handed in `Magnitude.standard`, which is the only construction that exists. " +
        "`lesserCases` and the sign lemmas take theirs as a parameter, so the orientation of a " +
        "rule is a property of the call and not of this file, which is this census's own point " +
        "one level further in. That no caller could ever hand a looping one is not measured and " +
        "is not claimed"),
    "Limit.scala" ->
      ("one, in the comparison test, and it cannot reach the limit. The rule is `SUM_SUC` " +
        "REVERSED, `Sum f n + f n = Sum f (SUC n)`, so the application removes the sum it " +
        "matches and the right side contains no sum of that shape: one pass and nothing to " +
        "match twice. It is the same argument as the folding entries under `Magnitude.scala` " +
        "above, and it arrives by the same door, `Rewrite.inTheorem`. This entry exists because " +
        "the scan asked for it: adding a rewriting step to a file that had none made " +
        "`Limit.scala` a call site, and the census went red on the same day its twentieth entry " +
        "was settled"),
    "Induct.scala" ->
      "asks `finished` after the closer refuses, which is where this guard was first written",
    "Family.scala" ->
      "asks `finished` when the sample is not a number, and says which of the two it was",
    "Recursion.scala" ->
      ("one rule carrying `select ... = name` into the step the recursion theorem produced; it " +
        "replaces one chosen term by one constant and cannot loop, and what comes back is handed " +
        "to `Conv.trans`, which refuses unless the two sides meet, so a limit that ran out is a " +
        "refusal about the rewriting and never a claim about the recurrence. The two copies of " +
        "this carry, one in `Peano` and one in `Series`, were joined here on 2026-09-12"),
    "Algebraic.scala" ->
      ("one call, carrying the assumed defining equations of the radicals into the certificate " +
        "the untrusted half produced. Each rule replaces a product of variables by a numeral, so " +
        "every step makes the term smaller and it cannot loop. What comes back is handed to " +
        "`RING` as `that = 0`, which is refused unless every defining factor has actually " +
        "collapsed, so a limit that ran out is a refusal about the certificate and never a claim " +
        "about the polynomial"),
    // It was `Peano.scala` until 2026-09-15 and is the same two calls: `docs/adr/0016` split the
    // file and both of them are on the half that names a real. The entry MOVED rather than being
    // joined by a second, since a reviewed call site that no longer has a call is a reading of
    // something that is not there.
    "Embedding.scala" ->
      ("two, and neither reads a normal form on trust. One rule carrying the successor equation " +
        "of the embedding into a crossed order, which replaces a constant and cannot loop, and " +
        "whose caller then requires the result to be the statement the table writes; and the " +
        "recurrences carried into the left side of a written statement, whose residue is handed " +
        "to `RING` and rejoined by `Conv.trans`, so the rewriting settles what it can and a " +
        "decision procedure settles the rest. Both end at `Peano.checked`, which compares what " +
        "came out against the statement written in `Peano.Statements` and refuses with `<name> as " +
        "it is written` otherwise, so a step limit that ran out is a refusal naming the lemma and " +
        "never a theorem about a half-rewritten term. Two more calls go through `inTheorem`, " +
        "and both pass a SINGLE rule built by `Rule.of` from a derived equation: each firing " +
        "removes its own left side and the right side does not contain it, so the walk is one " +
        "pass and the limit is unreachable by construction rather than by a check"),
    "Series.scala" ->
      ("two hand-written induction steps, and both refuse by naming the rewriting. The base of " +
        "the bounded congruence requires the two sides it is left with to be the SAME TERM and " +
        "says `an empty range on both sides` otherwise; the step of `SUM_SWAP` compares what the " +
        "rewriting left against a separately derived instance and says `the step as the " +
        "rewriting left it` rather than blaming the identity"),
    "Modular.scala" ->
      ("three rules carrying definitions of multiplication and addition at zero and one, to " +
        "bring a division witness to a closed form; the caller then destructures the result and " +
        "requires the two sides to be the SAME TERM, refusing `two sides the arithmetic brings " +
        "together` otherwise, so a limit that ran out is a refusal about the rewriting and never " +
        "a statement about the quotient"),
    "Successor.scala" ->
      ("two, and both ask `finished` and refuse by naming the rewriting rather than the number. " +
        "One opens a numeral of `num` into its successors, one opens a power at a written " +
        "exponent over a variable base; both rule sets strictly reduce the encoding, so neither " +
        "can loop, and how long each walk is was measured rather than assumed: `k + 2` steps at " +
        "every exponent read, which is where the ceiling comes from. Reaching it is a " +
        "`NotNormalised` about the walk, and a caller that got one would be reading a refusal " +
        "and never a claim about the power"),
    "Language.scala" ->
      ("one, evaluating `NUM_SUBST_FORM` at a concrete code out of the nine substitution clauses, " +
        "two derived conditional rules and one decision per index the code mentions. The caller " +
        "does not read the result as a normal form: it requires the right side to carry no " +
        "`NUM_SUBST_FORM`, no `NUM_SUBST_TERM` and no `COND`, and refuses by naming the term " +
        "otherwise. That covers a limit that ran out completely rather than by luck, because " +
        "every rule strictly removes one of those three and nothing else is rewritten, so a walk " +
        "that stopped early ALWAYS leaves one standing. A caller that got the refusal is reading " +
        "a statement about the rewriting and never about the substitution. Two more go through " +
        "`inTheorem`: one folds a definition body back into its constant, and one applies the " +
        "four projections to a code just constructed. Every rule in both strictly reduces and " +
        "none can fire twice"),
    "Digits.scala" ->
      ("two calls, and neither reads what comes back as a normal form. Both lift the successors " +
        "out of one side of a numeral lemma, and what is done with the result is `Conv.trans` " +
        "around an answer from `Semiring`: a lifting that ran out leaves a side whose core is not " +
        "the other's, so `Semiring` refuses, or leaves the two sides carrying different numbers of " +
        "successors, which the site refuses by naming both counts. Neither path can produce a " +
        "theorem about a half-lifted term, because every step of the chain is an equation the " +
        "kernel built. The computations themselves go through `Rewrite.prove`, which asks the " +
        "question this list is about on the caller's behalf"),
    "Value.scala" ->
      ("one call, and what it rewrites is `real_of_num` over a numeral of `num` with the four " +
        "lemmas that carry the embedding through the bit encoding. The equation it returns is not " +
        "read as a normal form: it is handed to `Rules.mp` as the premise of a goal whose text the " +
        "caller wrote, so a rewriting that stopped short produces a theorem that is not the " +
        "premise and the detachment refuses. It cannot produce a wrong value, because the value is " +
        "what the two characterisations and the trichotomy settle and this equation only lets " +
        "`Linarith` read an atom as a number"),
    "Matrix.scala" ->
      ("four calls, and none of them reads what comes back as a normal form on trust. Two require " +
        "it to be `MAT2` applied to four terms and refuse by naming the term they stopped at, so " +
        "a limit that ran out is reported as the rewriting rather than as the mathematics; one " +
        "compares it against a named variable; one is joined to a separately derived equation by " +
        "`Conv.trans`, which refuses unless the two meet. The component equations that then reach " +
        "`Ring` ask `finished` on the failing path, which is `Induct`'s arrangement reused. A fifth " +
        "goes through `inTheorem` with a single folding rule, and what comes back is compared " +
        "against the goal the method was asked for and refused as `NotOfForm` otherwise, which " +
        "that site's own comment argues for at length"),
    "Integer.scala" ->
      ("four calls and one `rewrite` among them, and that one is the only place in the file that " +
        "has to ask. `Laws.normalise` brings an equation between integers to a single " +
        "`INT_OF_PAIR` applied to a pair, and `Laws.projected` reads what comes back: where it is " +
        "not that shape it asks `finished` and refuses with two different messages, one naming a " +
        "rule set that did not settle and one naming a term the rules have nothing to say about, " +
        "which is the distinction this census exists for. The other three arrive through " +
        "`inTheorem` with rules that strictly shrink the term and therefore cannot loop: " +
        "`FST (PAIR a b) = a` and its twin remove two applications each, " +
        "`INT_OF_PAIR (INT_OF_PAIR_repr a) = a` removes two and its right side contains neither, " +
        "and the two tidying rules of the embedding's injectivity replace a projection of a pair " +
        "by a constant and a sum by a summand. Each of the three hands what comes back to " +
        "`Conv.trans`, to `Kernel.eqMp` or to `Rules.genAll`, and the published statement is " +
        "compared against `Integer.Statements` by `IntegerSpec`, so a rewriting that stopped early " +
        "is a red statement rather than a quiet one"),
    "Inclusion.scala" ->
      ("three doors, two `inTheorem` and one `rewrite`, and the answer is the same at all three " +
        "because of where the conclusion comes from: **not one of them is built from what the " +
        "rewriting produced**. `Route.equation` parses both sides, rewrites each, closes the gap " +
        "with `Ring` and chains the three with `Conv.trans`, so the theorem that comes out is " +
        "`left = right` at the two parsed texts however far either normalisation got; " +
        "`respectfulness` builds the equation it discharges out of the four images of components " +
        "and reads the rewritten premise only to carry it across; and `injectivity` builds its " +
        "hypothesis from `real_of_int (INT_OF_PAIR x)` and its conclusion from `INT_EQ_PAIRS`. " +
        "So an exhausted limit cannot produce a theorem about a half-rewritten term here: it " +
        "leaves `Ring` an identity over atoms it cannot relate and that is refused, or it leaves " +
        "`partsOfDifference` something that is not a difference, or it leaves `checkPredicate` an " +
        "obligation that is not the one the lift wants, which refuses by name one level out. And " +
        "the eight published statements are compared against `Inclusion.Statements` by " +
        "`InclusionSpec`, which is the same last line of defence `Integer.scala` has above"),
    // 2026-09-20, with `exp 1 > 2`.
    "Transcendental.scala" ->
      ("three, and none of them is left to the limit to report. One is `Rewrite.rewrite` on the " +
        "third partial sum of the exponential's series, which the recurrences of the sum, the " +
        "power, the factorial, the product and the embedding walk down to an expression in " +
        "numerals; what it is handed to is `Linarith`, and a walk that stopped early leaves a " +
        "`real_of_num (NUM_FACT ...)` or a `Power 1 ...` standing, which is an atom the procedure " +
        "knows nothing about and cannot bound, so the refusal is the procedure's rather than a " +
        "weaker theorem. The other two are `Rewrite.inTheorem`, moving `real_of_num` inwards " +
        "across the embedding and folding `real_of_num 0` to `0`, and each result is handed to " +
        "`Rules.mp` against an instance of a schematic implication proved beforehand: `mp` is " +
        "strict here, so a half-rewritten hypothesis does not match `p <= 2 * f` or `0 + 1 <= a` " +
        "and is refused by name. On termination, every rule strictly reduces: the recurrences " +
        "open one successor each, the embedding rules move `real_of_num` under a constructor, and " +
        "the three ground `Ring` equations that fold `0 + 1`, `1 + 1` and `1 * 1` have right sides " +
        "their own left sides do not contain")
  )

  /**
   * The same table as a map, which is what the two censuses below look a file up in.
   *
   * The declaration above is a `Vector` and this is its projection, rather than the `Map(...)`
   * literal it was until 2026-09-19, and the difference is what a repeated key does. A map literal
   * absorbs one silently, keeping the last: both assertions of the census would go on passing,
   * because a duplicated entry is still an entry the scan finds and still a file the scan reaches,
   * so neither "every site is reviewed" nor "every review is still a site" can see it. What is lost
   * is the review a reader thinks is here. Measured on 2026-09-19, no file is named twice here nor
   * in any of the four tables repaired with it, three in `NotationBoundarySpec` and one in
   * `ChainCoverageSpec`, so the guard below is latent rather than a repair of a live defect.
   *
   * The count is taken off the `Vector` and not off the source text. Counting the lines of the
   * literal and comparing them with `size` was the other way to ask, and it is the shape that
   * mismeasured this the first time it was tried, reading two tables in one file as one table and
   * declaring a duplicate that was not there: an entry here spans eleven lines as often as one.
   */
  private val ReviewedCallSites: Map[String, String] = ReviewedEntries.toMap

  "The table of reviewed call sites" should "not have absorbed a repeated file name" in {
    val repeated = ReviewedEntries.map(_._1).groupBy(identity).filter(_._2.size > 1).keys.toVector
    withClue(s"file named twice in `ReviewedEntries`: ${repeated.sorted.mkString(", ")}\n") {
      repeated shouldBe empty
    }

    // And it is not passing because the table is empty, which is the one way an equality between
    // two sizes holds for free. About half of what it held on 2026-09-19; a floor and not a pin,
    // because the census below is what keeps this table tracking the call sites.
    ReviewedEntries.size should be >= 13
    ReviewedCallSites.size shouldBe ReviewedEntries.size
  }

  "The sources the two censuses walk" should
    "be every module's, including any module added after this was written" in {
    // Two readings that must agree, rather than a list. The first is the modules the walk actually
    // produced a file from; the second is the directories under `modules/` that carry Scala under
    // `src/main`, computed without going through `mainSources`. A derivation can return nothing,
    // and two empty readings agree, so the floor below is what separates agreement from silence.
    val reached = mainSources.map(_.getName(1).toString).distinct.sorted

    val stream = java.nio.file.Files.list(java.nio.file.Paths.get("modules"))
    val holdingMain =
      try
        stream
          .toArray
          .toVector
          .map(_.asInstanceOf[java.nio.file.Path])
          .filter { module =>
            val main = module.resolve("src/main")
            java.nio.file.Files.isDirectory(main) && {
              val walk = java.nio.file.Files.walk(main)
              try walk.toArray.toVector.exists(_.toString.endsWith(".scala"))
              finally walk.close()
            }
          }
          .map(_.getFileName.toString)
          .sorted
      finally stream.close()

    reached shouldBe holdingMain

    // A floor and not an equality, because modules are added and this is not a budget. It sits
    // below what the tree held on 2026-09-19 and above the six the two censuses used to name, so a
    // list written back in place of the walk cannot clear it. `aggregate` is a directory under
    // `modules/` that holds no source of its own, which is why this is not a count of `modules/`.
    withClue(s"modules reached: ${reached.mkString(", ")}\n") {
      reached.size should be >= 10
    }

    // And the two the repair of 2026-09-19 was about. Both depend on `tactics` and so can name
    // `Rewrite`, and the six-name list both censuses used to carry read neither: these are the
    // entries that disappear first if anybody writes the list back.
    reached should contain("examples")
    reached should contain("dist")

    info(s"${reached.size} modules, ${mainSources.size} sources: ${reached.mkString(", ")}")
  }

  "Every caller of the rewriter" should "have been asked what it does when the limit runs out" in {
    // The census the card asked for, as a scan rather than as a reading somebody did once. The
    // defect is that `rewrite` hands back the theorem it had when the step limit ran out, so a rule
    // set that does not settle looks exactly like a false identity; it was closed in
    // `Rewrite.prove`, came back the same day in `Induct.settle`, and came back again in `Family`
    // on the day this list was written. It will come back in the next place that does this.
    val callers = mainSources
      .filter { path =>
        val text = new String(java.nio.file.Files.readAllBytes(path), "UTF-8")
        text.contains("Rewrite.rewrite(") ||
        // `inTheorem` since 2026-09-15, and it was the gap this file's own docstring
        // predicted. It calls `rewrite` with the same default limit and hands the result to
        // `eqMp`, so a walk that ran out yields a TRUE theorem about a half-rewritten term,
        // which is the defect this list is about arriving by a second door. Twenty call
        // sites across ten files were unread until a session adding one of its own noticed.
        text.contains("Rewrite.inTheorem(") ||
        // `Recorder.rewriteIn` since 2026-09-15, and it is a door rather than a call site
        // dressed up as one: it takes its rules as a PARAMETER, so `Recorder.scala` can say
        // what it records and cannot say what an exhausted limit means, and its own entry
        // above declined to. A caller reaching the rewriter through it was invisible here.
        // `Magnitude.scala` is that caller and holds zero calls at either of the two doors
        // above, which is how eight sites in the shared recording layer went unread while
        // this scan reported itself complete.
        text.contains(".rewriteIn(")
      }
      .map(_.getFileName.toString)
      .distinct
      .sorted

    withClue(s"call sites: ${callers.mkString(", ")}\n") {
      callers.filterNot(ReviewedCallSites.contains) shouldBe empty
    }

    // And it is not passing because it read nothing: the two that carry the guard are in it.
    callers should contain("Induct.scala")
    callers should contain("Family.scala")

    // And the second door is not passing because it was quietly closed again. `Order.scala` has
    // no `Rewrite.rewrite(` in it at all and seven calls to `inTheorem`, so it is in this list
    // only while the scan reads both, and it is the file that disappears first if one is dropped.
    callers should contain("Order.scala")

    // And the third door, by the same test: `Magnitude.scala` calls the rewriter zero times
    // directly and eight times through `Recorder`, so it is in this list only while the scan reads
    // `.rewriteIn(` and it is the file that disappears first if that door is dropped.
    callers should contain("Magnitude.scala")

    val stale = ReviewedCallSites.keys.toVector.filterNot(callers.contains)
    withClue(s"reviewed and no longer a call site: ${stale.mkString(", ")}\n") {
      stale shouldBe empty
    }
  }

  "Every rule set that is repeated" should
    "be reachable by the check that refuses one that cannot be" in {
    // The guard above refuses a rule set that cannot reach a fixed point, and it is asked in
    // `Rewrite.rewrite` and `Rewrite.normaliser`, which are the two published ways to iterate a
    // rule set. That covers everything **only while nothing assembles its own repetition**, and on
    // 2026-09-18 two files did: `Peano.normalisation` had written out the six lines of
    // `normaliser`, and `Field.normalisation` builds two passes of a shape of its own. A guard with
    // two holes on the day it lands is a convention, and this is what makes it a property.
    //
    // `Peano.scala` is not in the list below because it stopped being a call site rather than
    // because it was excused: `passOver` was published so that it could call it, which removed the
    // third copy of the pass at the same time.
    val reviewedEntries = Vector(
      "Field.scala" ->
        ("two passes over rules it has just built, asked through `Rewrite.Rule.iterable` before " +
          "either is repeated. It is not `normaliser`: it carries no ordered rules and no beta, " +
          "and the argument for that shape is written above the function")
    )
    val reviewed = reviewedEntries.toMap
    withClue(s"file named twice: ${reviewedEntries.map(_._1).mkString(", ")}\n") {
      reviewed.size shouldBe reviewedEntries.size
    }

    // The same sources the census above walks, which since 2026-09-19 is every `src/main` under
    // `modules/` and not the six names both censuses carried. The comment that stood here said
    // "the same roots the census above walks, and not `modules/theories` alone", because a gate
    // that reads where the answer already is would not have seen a third site in `tactics`. The
    // argument was right and the list stopped one module short of it: it also does not read
    // `examples` or `dist`, which is where a fourth site would be invisible in exactly the way
    // this sentence was warning about. `moduleRoots` carries the measurement.
    //
    // `Rewrite.scala` is where `repeatConv` is defined and where the two published drivers use it,
    // so it is the one file excluded.
    val callers = mainSources
      .filter { path =>
        path.getFileName.toString != "Rewrite.scala" &&
        // `repeatConv(` and not `Rewrite.repeatConv(`: a site written under `import Rewrite.*`
        // spells it without the qualifier, and a gate that depends on how a call is spelled
        // is the defect this repository already records about an order and ASCII. The looser
        // pattern can only over-report, which costs an entry and never a miss.
        new String(java.nio.file.Files.readAllBytes(path), "UTF-8")
          .contains("repeatConv(")
      }
      .map(_.getFileName.toString)
      .distinct

    withClue(s"assembles its own repetition: ${callers.sorted.mkString(", ")}\n") {
      callers.filterNot(reviewed.contains) shouldBe empty
    }

    // And it is not passing because it read nothing. `Field.scala` is the one file that does this,
    // so this line is what separates a scan that found one from a scan that found none.
    callers should contain("Field.scala")
  }

  it should "tell a normal form from a term the rewriter stopped at" in {
    // The question underneath both tests above, asked directly. `repeatConv` returns a true theorem
    // either way, so this is the only thing that separates them.
    val settling = Rewrite.repeatConv(Rewrite.rewriteConv(assumedRule(u, w)))
    val alternating = Rewrite.repeatConv(
      Rewrite.firstConv(Vector(assumedRule(u, w), assumedRule(w, u)).map(Rewrite.rewriteConv)),
      7
    )

    force(Rewrite.atFixedPoint(settling, w)) shouldBe true
    force(Rewrite.atFixedPoint(alternating, u)) shouldBe false
  }
}
