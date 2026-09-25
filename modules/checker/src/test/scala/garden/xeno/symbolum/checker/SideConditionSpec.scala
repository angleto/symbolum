package garden.xeno.symbolum.checker

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * The side conditions of every rule, enumerated from the rules rather than from the defects.
 *
 * `SoundnessAttackSpec` holds the attacks that occurred to a reader, and says of itself that a
 * corpus of attacks proves only what it contains. On 2026-09-10 that was demonstrated the hard way:
 * it enumerated the operations that must refuse a loose index, it had six of them, and `Term.abs`
 * was the seventh and the only one that did not check. A list built from the defects already known
 * cannot contain the one nobody has met.
 *
 * So this is built the other way round. Every primitive rule and every theory extension is listed
 * with the conditions that make it sound, taken from what the rule needs and not from what has gone
 * wrong, and each condition is either exercised by a case that must be refused or **named as not
 * exercised**. The second half is the point: a coverage list that silently omits what it does not
 * cover reads as though it covered everything, which is exactly how the checker's `Definition` arm
 * came to accept `|- T = F` for a month.
 *
 * == Why this file is in the checker's tests ==
 *
 * Because the wall has two sides and this is the only test scope that sees both. A condition is
 * only really guarded when the kernel enforces it **and** the second reading would notice its
 * absence, and until they are listed together nobody can see which conditions have only one of the
 * two. The pairing assertion at the end is the whole reason the file exists in one piece.
 */
class SideConditionSpec extends AnyFlatSpec with Matchers {

  private val bool = Type.Bool
  private val alpha = TyVar("A")
  private val p = Term.variable("p", bool)
  private val q = Term.variable("q", bool)
  private val other = Term.variable("a", alpha)

  private def force[T](result: Either[?, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  /** A term with a loose index, obtained the only way it can be: by destructuring a lambda. */
  private val loose: Term = force(Term.abs(p, p)) match {
    case Abs(_, body) => body
    case other => fail(s"expected an abstraction, got $other")
  }

  /**
   * One condition of one rule, and how each side of the wall is known to notice it.
   *
   * `kernel` and `checker` are `None` when nothing exercises that side, and that is a fact the
   * suite reports rather than a gap it hides.
   */
  private final case class Guarded(
    rule: String,
    condition: String,
    kernel: Option[() => Boolean],
    checker: Option[() => Boolean],
    note: String = ""
  )

  private def refuses(result: Either[?, ?]): Boolean = result.isLeft

  private def throws(work: => Any): Boolean =
    try { work; false }
    catch { case _: KernelInvariantViolation => true }

  private def equals(left: Expr, right: Expr): Expr = {
    val ty = Expr.typeOf(left).getOrElse(Ty.Bool)
    Expr.Apply(
      Expr.Apply(Expr.Constant(Expr.EqualityName, Ty.fun(ty, Ty.fun(ty, Ty.Bool)), None), left),
      right
    )
  }

  private val ep = Expr.Free("p", Ty.Bool)
  private val eq = Expr.Free("q", Ty.Bool)

  private def checkerRefuses(claim: Claim, step: Step, premises: Vector[Claim]): Boolean =
    Check.node(claim, step, premises).isLeft

  /* ------------------------------------------------------------------ the table */

  private val Conditions: Vector[Guarded] = Vector(
    Guarded(
      "refl",
      "the term is one: locally closed and well typed",
      Some(() => throws(Kernel.refl(loose))),
      Some(() =>
        checkerRefuses(Claim(Vector.empty, equals(ep, eq)), Step.Reflexivity(ep), Vector.empty)
      ),
      "The kernel defends itself by throwing here, because `refl` returns a theorem and not an Either."
    ),
    Guarded(
      "refl",
      "no hypothesis is carried",
      None,
      Some(() =>
        checkerRefuses(Claim(Vector(ep), equals(ep, ep)), Step.Reflexivity(ep), Vector.empty)
      ),
      "Unreachable in the kernel by construction: `refl` builds the sequent itself and cannot be handed one."
    ),
    Guarded(
      "trans",
      "the middles meet",
      Some(() => refuses(Kernel.trans(Kernel.refl(p), Kernel.refl(q)))),
      Some(() =>
        checkerRefuses(
          Claim(Vector.empty, equals(ep, ep)),
          Step.Transitivity,
          Vector(Claim(Vector.empty, equals(ep, eq)), Claim(Vector.empty, equals(ep, eq)))
        )
      )
    ),
    Guarded(
      "mkComb",
      "the argument's type is the function's domain",
      Some(() => refuses(Kernel.mkComb(Kernel.refl(p), Kernel.refl(other)))),
      Some(() =>
        checkerRefuses(
          Claim(Vector.empty, equals(Expr.Apply(ep, eq), Expr.Apply(ep, eq))),
          Step.Congruence,
          Vector(Claim(Vector.empty, equals(ep, ep)), Claim(Vector.empty, equals(eq, eq)))
        )
      ),
      "Delegated in the kernel to `Term.app`, which is where the check lives."
    ),
    Guarded(
      "abs",
      "the variable is free in no hypothesis",
      Some(() => refuses(Kernel.abs(p, force(Kernel.assume(p))))),
      Some(() => {
        val from = Claim(Vector(equals(ep, eq)), equals(ep, eq))
        val abstracted = Expr.Lambda(Ty.Bool, Expr.close(ep, ep))
        checkerRefuses(
          Claim(Vector(equals(ep, eq)), equals(abstracted, abstracted)),
          Step.Abstraction(ep),
          Vector(from)
        )
      })
    ),
    Guarded(
      "beta",
      "the term is locally closed",
      Some(() => refuses(Kernel.beta(loose))),
      Some(() =>
        checkerRefuses(
          Claim(Vector.empty, equals(ep, eq)),
          Step.BetaStep(Expr.Bound(0)),
          Vector.empty
        )
      )
    ),
    Guarded(
      "beta",
      "the term is a redex",
      Some(() => refuses(Kernel.beta(p))),
      Some(() =>
        checkerRefuses(Claim(Vector.empty, equals(ep, eq)), Step.BetaStep(ep), Vector.empty)
      )
    ),
    Guarded(
      "assume",
      "the proposition is locally closed",
      Some(() => refuses(Kernel.assume(loose))),
      Some(() =>
        checkerRefuses(
          Claim(Vector(Expr.Bound(0)), Expr.Bound(0)),
          Step.Assumption(Expr.Bound(0)),
          Vector.empty
        )
      )
    ),
    Guarded(
      "assume",
      "it is a proposition and not a term of another type",
      Some(() => refuses(Kernel.assume(other))),
      Some(() => {
        val number = Expr.Free("n", Ty.Operator("real", Nil))
        checkerRefuses(Claim(Vector(number), number), Step.Assumption(number), Vector.empty)
      })
    ),
    Guarded(
      "eqMp",
      "the antecedent is the equation's left side",
      Some(() => refuses(Kernel.eqMp(Kernel.refl(p), force(Kernel.assume(q))))),
      Some(() =>
        checkerRefuses(
          Claim(Vector.empty, eq),
          Step.EqualityElimination,
          Vector(Claim(Vector.empty, equals(ep, eq)), Claim(Vector.empty, eq))
        )
      )
    ),
    Guarded(
      "deductAntisym",
      "each conclusion is discharged from the other's hypotheses",
      None,
      Some(() =>
        checkerRefuses(
          Claim(Vector(ep), equals(ep, eq)),
          Step.Antisymmetry,
          Vector(Claim(Vector(ep), ep), Claim(Vector(eq), eq))
        )
      ),
      "The kernel has no condition to refuse: it computes the discharge rather than being told it. " +
        "The checker recomputes it, which is where a wrong one is caught."
    ),
    Guarded(
      "inst",
      "each replacement has the variable's type and is locally closed",
      Some(() => refuses(Kernel.inst(Map(p -> other), Kernel.refl(p)))),
      Some(() =>
        checkerRefuses(
          Claim(Vector.empty, equals(eq, eq)),
          Step.Instantiation(Map(ep -> Expr.Bound(0))),
          Vector(Claim(Vector.empty, equals(ep, ep)))
        )
      ),
      "Delegated in the kernel to `Term.substitute`."
    ),
    Guarded(
      "instType",
      "the substitution is applied to the hypotheses as well",
      None,
      Some(() =>
        checkerRefuses(
          Claim(Vector(ep), equals(ep, ep)),
          Step.TypeInstantiation(Map("A" -> Ty.Bool)),
          Vector(Claim(Vector.empty, equals(ep, ep)))
        )
      ),
      "The kernel has no condition to refuse: type instantiation is sound for any substitution, and " +
        "what could go wrong is applying it to only part of the sequent, which the kernel does not do " +
        "and the checker recomputes."
    ),
    Guarded(
      "defineConstant",
      "the body is closed",
      Some(() => refuses(Kernel.defineConstant(Theory.primitive, "c", p))),
      Some(() =>
        checkerRefuses(
          Claim(Vector.empty, equals(Expr.Constant("c", Ty.Bool, Some(ep)), ep)),
          Step.Definition("c", ep),
          Vector.empty
        )
      )
    ),
    Guarded(
      "defineConstant",
      "no type variable of the body escapes its type",
      Some(() => {
        val polymorphic = force(Term.abs(other, force(Term.eq(p, p))))
        refuses(Kernel.defineConstant(Theory.primitive, "c", polymorphic))
      }),
      None,
      "Not exercised on the checker's side, and this is the one condition the two do not share. " +
        "`Check`'s Definition arm gained the escaping-variable test on 2026-09-10 and a case that " +
        "trips it has not been built: it needs a body whose type variables its type does not mention."
    ),
    Guarded(
      "defineConstant",
      "the constant is the one being defined, carrying the body as its origin",
      None,
      Some(() => {
        val truth = Expr.Constant("T", Ty.Bool, Some(Expr.Lambda(Ty.Bool, Expr.Bound(0))))
        val falsity = Expr.Constant("F", Ty.Bool, Some(ep))
        checkerRefuses(
          Claim(Vector.empty, equals(truth, falsity)),
          Step.Definition("F", falsity),
          Vector.empty
        )
      }),
      "Unreachable in the kernel by construction: `defineConstant` builds the constant itself. It is " +
        "the checker's alone, and it is the arm that accepted `|- T = F` until 2026-09-10."
    ),
    Guarded(
      "assertAxiom",
      "the proposition is one, and is closed",
      Some(() => refuses(Kernel.assertAxiom(Theory.primitive, other))),
      Some(() =>
        checkerRefuses(Claim(Vector.empty, ep), Step.Axiom(ep), Vector.empty)
      )
    ),
    Guarded(
      "defineType",
      "the witness holds outright, with no hypothesis",
      None,
      Some(() =>
        checkerRefuses(
          Claim(Vector.empty, equals(ep, eq)),
          Step.TypeDefinition("t", "mk", "dest", Step.Half.AbstractionOfRepresentation),
          Vector(Claim(Vector(ep), ep))
        )
      ),
      "The kernel's case is in `SoundnessAttackSpec`, which builds a real theory to reach it; " +
        "duplicating that here would be a second copy of a construction rather than a second check."
    ),
    Guarded(
      "defineType",
      "the half returned is over the constants the step names",
      None,
      Some(() => {
        val f = Expr.Constant("f", Ty.fun(Ty.Bool, Ty.Bool), None)
        val g = Expr.Constant("g", Ty.fun(Ty.Bool, Ty.Bool), None)
        checkerRefuses(
          Claim(Vector.empty, equals(Expr.Apply(f, Expr.Apply(g, ep)), eq)),
          Step.TypeDefinition("t", "mk", "dest", Step.Half.AbstractionOfRepresentation),
          Vector(Claim(Vector.empty, ep))
        )
      }),
      "The kernel builds the two halves itself and cannot be handed a wrong one, so this is the " +
        "checker's alone. It accepted any nested application until 2026-09-10."
    ),
    Guarded(
      "cite",
      "the sequent is the cited fact's, hypotheses included",
      None,
      Some(() =>
        checkerRefuses(Claim(Vector.empty, ep), Step.Citation("P"), Vector(Claim(Vector(ep), ep)))
      ),
      "The kernel restates the cited sequent itself and cannot be handed another, so this is the " +
        "checker's alone. The case drops a hypothesis, which is the one change that would matter."
    )
  )

  /* ------------------------------------------------------------------ the assertions */

  "Every condition with a kernel case" should "be refused by the kernel" in {
    val accepted = Conditions.filter(_.kernel.exists(check => !check()))

    withClue(s"the kernel did not refuse: ${accepted.map(c => s"${c.rule}/${c.condition}").mkString("; ")}\n") {
      accepted shouldBe empty
    }
  }

  "Every condition with a checker case" should "be refused by the checker" in {
    val accepted = Conditions.filter(_.checker.exists(check => !check()))

    withClue(s"the checker did not refuse: ${accepted.map(c => s"${c.rule}/${c.condition}").mkString("; ")}\n") {
      accepted shouldBe empty
    }
  }

  "Every rule and extension" should "appear in the table, so a new one has to be classified" in {
    // The same discipline `DocumentationSpec` applies to the kernel directory: a rule that is not
    // in the list is a rule nobody decided about, and the suite says so before it passes.
    val named = Conditions.map(_.rule).distinct.toSet
    val expected = Set(
      "refl", "trans", "mkComb", "abs", "beta", "assume", "eqMp", "deductAntisym", "inst",
      "instType", "cite", "defineConstant", "assertAxiom", "defineType"
    )

    withClue(s"in the kernel and not in this table: ${(expected -- named).mkString(", ")}\n") {
      expected -- named shouldBe empty
    }
    withClue(s"in this table and not a rule: ${(named -- expected).mkString(", ")}\n") {
      named -- expected shouldBe empty
    }
  }

  "The conditions guarded on only one side" should "be named rather than left to be discovered" in {
    // The half of this file that makes the other half worth anything. A coverage list that omits
    // what it does not cover reads as though it covered everything, which is how the checker's
    // `Definition` arm came to accept `|- T = F`.
    val oneSided = Conditions.filter(condition => condition.kernel.isEmpty || condition.checker.isEmpty)

    every(oneSided.map(_.note)) should not be empty

    // The number is asserted below, and this comment once gave a smaller one before anybody had
    // counted, which is the small version of the habit this whole file exists against. It is
    // asserted so that one more is a decision rather than a drift, and so that a condition gaining
    // its second side lowers it on purpose.
    //
    // Most of them have no kernel case by construction, because the kernel BUILDS the thing the
    // condition is about rather than being handed it: it builds the reflexive sequent, computes the
    // discharge, applies a type substitution to the whole sequent, restates a cited fact's sequent,
    // constructs the defined constant with its origin, and produces both halves of a type
    // definition. Those are the checker's alone
    // and always will be. The type definition's witness has its kernel case in
    // `SoundnessAttackSpec` instead of here. And one is a real gap on the other side: the escaping
    // type variable has no checker case.
    oneSided.size shouldBe 8
  }

  "The conditions guarded on both sides" should "be the majority, which is the property claimed" in {
    val both = Conditions.count(c => c.kernel.isDefined && c.checker.isDefined)

    both should be > Conditions.size / 2
  }
}
