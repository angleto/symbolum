package garden.xeno.symbolum.checker

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The refusals, which are the half nothing else can exercise.
 *
 * A checker that accepts every proof it is shown has been tested only on proofs that are right, and
 * there is no way to obtain a wrongly derived theorem from the kernel in order to show it one. So
 * the claims here are built in this checker's own terms and put to the rule check directly, which
 * is the reason that entry point takes data rather than a theorem.
 */
class CheckSpec extends AnyFlatSpec with Matchers {

  private val bool = Ty.Bool
  private val p = Expr.Free("p", bool)
  private val q = Expr.Free("q", bool)

  private def equals(left: Expr, right: Expr): Expr = {
    val ty = Expr.typeOf(left).getOrElse(bool)
    Expr.Apply(
      Expr.Apply(Expr.Constant(Expr.EqualityName, Ty.fun(ty, Ty.fun(ty, bool)), None), left),
      right
    )
  }

  private def refused(verdict: Either[Check.Verdict, Set[Expr]]): String =
    verdict match {
      case Left(Check.Fails(_, rule, why)) => s"$rule: $why"
      case other => fail(s"expected a refusal, got $other")
    }

  "Reflexivity" should "be refused when the two sides are not the term" in {
    refused(
      Check.node(Claim(Vector.empty, equals(p, q)), Step.Reflexivity(Expr.Free("p", bool)), Vector.empty)
    ) should include("reflexivity")
  }

  it should "be refused when it arrives carrying a hypothesis" in {
    // `|- t = t` and nothing else. A reflexivity that had a hypothesis would be a way of putting an
    // assumption into a proof without assuming it.
    refused(
      Check.node(Claim(Vector(p), equals(p, p)), Step.Reflexivity(Expr.Free("p", bool)), Vector.empty)
    ) should include("reflexivity")
  }

  /* ------------------------------- what a hand-written table can claim */

  "A definition node" should "be refused when the constant is not the one being defined" in {
    // Built to find out rather than to confirm: the audit said this arm certifies falsity and the
    // card said to demonstrate it before repairing it. What the arm checked was that the right side
    // equals the declared body, that the body is closed, that there are no hypotheses, and that the
    // left side is SOME constant. It read neither the name the step declares nor the constant's
    // origin, so `|- T = F` presented as a definition of anything at all came back accepted.
    //
    // That is a false equation certified by the artifact whose whole purpose is to certify, and it
    // is enough on its own: nobody has to reach `|- F` for a checker that says yes to `|- T = F` to
    // be worth nothing.
    val truth = Expr.Constant("T", bool, Some(Expr.Lambda(bool, Expr.Bound(0))))
    val falsity = Expr.Constant("F", bool, Some(Expr.Free("body", bool)))

    refused(
      Check.node(Claim(Vector.empty, equals(truth, falsity)), Step.Definition("F", falsity), Vector.empty)
    ) should include("definition")
  }

  it should "accept the one it is actually about, so the repair is not a refusal of everything" in {
    // The must-accept half. A definition node is right when the constant carries the body as its
    // origin, which is what `docs/adr/0008` made a constant's identity and what `Read` carries
    // across. Without this the arm above could be fixed by refusing every definition.
    val body = Expr.Lambda(bool, Expr.Bound(0))
    val defined = Expr.Constant("id", Ty.fun(bool, bool), Some(body))

    Check.node(Claim(Vector.empty, equals(defined, body)), Step.Definition("id", body), Vector.empty) match {
      case Right(axioms) => axioms shouldBe empty
      case Left(problem) => fail(s"a real definition was refused: $problem")
    }
  }

  "A type definition node" should "be refused when the shape merely brackets like the real one" in {
    // The same weakness as the definition arm, one rule along: the first half asked only that the
    // left side be a nested application, so any `|- (f (g h)) = anything` passed. It is tied to the
    // two names the step declares now.
    val a = Expr.Free("a", bool)
    val f = Expr.Constant("f", Ty.fun(bool, bool), None)
    val g = Expr.Constant("g", Ty.fun(bool, bool), None)
    val bracketed = Expr.Apply(f, Expr.Apply(g, a))

    refused(
      Check.node(
        Claim(Vector.empty, equals(bracketed, p)),
        Step.TypeDefinition("num", "mk", "dest", Step.Half.AbstractionOfRepresentation),
        Vector(Claim(Vector.empty, p))
      )
    ) should include("type definition")
  }

  it should "accept the half it really is, over the constants the step names" in {
    val a = Expr.Free("a", bool)
    val mk = Expr.Constant("mk", Ty.fun(bool, bool), None)
    val dest = Expr.Constant("dest", Ty.fun(bool, bool), None)
    val roundTrip = Expr.Apply(mk, Expr.Apply(dest, a))

    Check.node(
      Claim(Vector.empty, equals(roundTrip, a)),
      Step.TypeDefinition("num", "mk", "dest", Step.Half.AbstractionOfRepresentation),
      Vector(Claim(Vector.empty, p))
    ) match {
      case Right(axioms) => axioms shouldBe empty
      case Left(problem) => fail(s"a real half was refused: $problem")
    }
  }

  "Transitivity" should "be refused when the middles do not meet" in {
    val left = Claim(Vector.empty, equals(p, q))
    val right = Claim(Vector.empty, equals(p, q))

    refused(
      Check.node(
        Claim(Vector.empty, equals(p, q)),
        Step.Transitivity,
        Vector(left, right)
      )
    ) should include("transitivity")
  }

  it should "be refused when a hypothesis is dropped on the way" in {
    // The shape a wrong rule would have if it forgot to carry the hypotheses: the conclusion would
    // be right and would rest on less than it does, which is the failure that matters most.
    val left = Claim(Vector(p), equals(p, q))
    val right = Claim(Vector.empty, equals(q, p))

    refused(
      Check.node(
        Claim(Vector.empty, equals(p, p)),
        Step.Transitivity,
        Vector(left, right)
      )
    ) should include("transitivity")
  }

  "An assumption" should "be refused when the conclusion is not what was assumed" in {
    refused(
      Check.node(Claim(Vector(p), q), Step.Assumption(p), Vector.empty)
    ) should include("assumption")
  }

  it should "be refused when what is assumed is not a proposition" in {
    val number = Expr.Free("n", Ty.Operator("real", Nil))

    refused(
      Check.node(Claim(Vector(number), number), Step.Assumption(number), Vector.empty)
    ) should include("assumption")
  }

  "An abstraction" should "be refused when its variable is free in a hypothesis" in {
    // The side condition that is the whole content of that rule: without it an assumption about one
    // value becomes a statement about all of them.
    val from = Claim(Vector(equals(p, q)), equals(p, q))
    val abstracted = Expr.Lambda(bool, Expr.close(p, p))

    refused(
      Check.node(
        Claim(Vector(equals(p, q)), equals(abstracted, abstracted)),
        Step.Abstraction(p),
        Vector(from)
      )
    ) should include("abstraction")
  }

  "A beta step" should "be refused when the right side is not the contraction" in {
    val redex = Expr.Apply(Expr.Lambda(bool, Expr.Bound(0)), p)

    refused(
      Check.node(
        Claim(Vector.empty, equals(redex, q)),
        Step.BetaStep(Expr.Free("r", bool)),
        Vector.empty
      )
    ) should include("beta")
  }

  "An axiom" should "be refused when it is not closed, since then it is a schema" in {
    // This one is worth having even though the kernel checks it, because it is the one node a
    // checker can never verify: it can only report what is being believed, so it had better be
    // sure that what it reports is a statement rather than a family of them.
    refused(
      Check.node(Claim(Vector.empty, p), Step.Axiom(p), Vector.empty)
    ) should include("axiom")
  }

  "The checker's own machinery" should "be its own, which is what makes a second reading worth anything" in {
    // Not the kernel's: these are the operations the 2026-09-03 hole lived in, re-decided here.
    Expr.isClosed(Expr.Bound(0)) shouldBe false
    Expr.isClosed(Expr.Lambda(bool, Expr.Bound(0))) shouldBe true

    Expr.typeOf(Expr.Apply(p, q)) shouldBe None
    Expr.typeOf(Expr.Lambda(bool, Expr.Bound(0))) shouldBe Some(Ty.fun(bool, bool))

    Expr.betaReduce(Expr.Apply(Expr.Lambda(bool, Expr.Bound(0)), q)) shouldBe Some(q)
    Expr.substitute(Map(p -> q), Expr.Lambda(bool, p)) shouldBe Expr.Lambda(bool, q)
    Expr.close(p, Expr.Apply(p, q)) shouldBe Expr.Apply(Expr.Bound(0), q)
  }

  "The source" should "never reach for one of the kernel's rules" in {
    // The property the whole module rests on. A checker that called `Kernel.trans` to check a
    // transitivity would agree with the kernel about exactly the thing a second implementation
    // exists to disagree about.
    val rules = Vector(
      "Kernel.refl", "Kernel.trans", "Kernel.mkComb", "Kernel.abs", "Kernel.beta", "Kernel.assume",
      "Kernel.eqMp", "Kernel.deductAntisym", "Kernel.inst", "Kernel.instType",
      "Kernel.defineConstant", "Kernel.assertAxiom", "Kernel.defineType",
      "Term.substitute", "Term.typeOf", "Term.isLocallyClosed", "Term.betaReduce", "Term.abs"
    )

    val sources = java.nio.file.Files
      .walk(java.nio.file.Paths.get("modules/checker/src/main"))
      .filter(path => path.toString.endsWith(".scala"))
      .map[String](path => java.nio.file.Files.readString(path))
      .toArray
      .toVector
      .map(_.toString)
      .mkString("\n")

    val reached = rules.filter(sources.contains)
    withClue(s"the checker reaches for: ${reached.mkString(", ")}\n") { reached shouldBe empty }
  }
}
