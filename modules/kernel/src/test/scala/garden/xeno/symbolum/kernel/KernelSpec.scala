package garden.xeno.symbolum.kernel

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The inference rules, each in the case where it applies and in the case where it must refuse.
 *
 * The refusals matter more than the derivations. A rule that proves what it should is visible the
 * first time anyone uses it; a rule that also proves what it should not is visible only here.
 */
class KernelSpec extends AnyFlatSpec with Matchers {


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

  private val A = TyVar("A")
  private val B = TyVar("B")

  private val x = Term.variable("x", A)
  private val y = Term.variable("y", A)
  private val p = Term.variable("p", Type.Bool)
  private val q = Term.variable("q", Type.Bool)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private def equation(lhs: Term, rhs: Term): Term = force(Term.eq(lhs, rhs))

  "Reflexivity" should "prove a term equal to itself with no hypotheses" in {
    val theorem = Kernel.refl(x)

    theorem.conclusion shouldBe equation(x, x)
    theorem.hypotheses shouldBe empty
  }

  "Transitivity" should "join two equations that share a side, keeping both sets of hypotheses" in {
    val z = Term.variable("z", A)
    val first = force(Kernel.assume(equation(x, y)))
    val second = force(Kernel.assume(equation(y, z)))

    val theorem = force(Kernel.trans(first, second))

    theorem.conclusion shouldBe equation(x, z)
    theorem.hypotheses shouldBe List(equation(x, y), equation(y, z)).sorted(using Term.ordering)
  }

  it should "refuse two equations that do not share a side" in {
    Kernel.trans(Kernel.refl(x), Kernel.refl(y)).left.map(_.getClass) shouldBe
      Left(classOf[TermsDiffer])
  }

  it should "refuse a theorem that is not an equation" in {
    val assumption = force(Kernel.assume(p))
    Kernel.trans(assumption, Kernel.refl(x)).left.map(_.getClass) shouldBe
      Left(classOf[NotAnEquation])
  }

  "Congruence" should "apply both sides of a function equation to both sides of an argument" in {
    val identity = lam(x, x)
    val theorem = force(Kernel.mkComb(Kernel.refl(identity), Kernel.refl(y)))

    theorem.conclusion shouldBe equation(force(Term.app(identity, y)), force(Term.app(identity, y)))
  }

  it should "refuse an argument the function cannot take" in {
    val identity = lam(x, x)
    val wrongType = Term.variable("z", B)

    Kernel.mkComb(Kernel.refl(identity), Kernel.refl(wrongType)).left.map(_.getClass) shouldBe
      Left(classOf[TypeMismatch])
  }

  "Abstraction" should "generalise an equation over a variable" in {
    val theorem = force(Kernel.abs(x, Kernel.refl(x)))

    theorem.conclusion shouldBe equation(lam(x, x), lam(x, x))
    Term.typeOf(Term.destEq(theorem.conclusion).get._1) shouldBe Type.fun(A, A)
  }

  it should "refuse a variable that occurs free in the hypotheses" in {
    // From `x = x |- x = x` this would give a statement about every value of x from an assumption
    // about one of them.
    val assumption = force(Kernel.assume(equation(x, x)))

    Kernel.abs(x, assumption).left.map(_.getClass) shouldBe
      Left(classOf[VariableIsFreeInHypotheses])
  }

  "Beta conversion" should "prove a redex equal to its contraction" in {
    val redex = force(Term.app(lam(x, x), y))
    val theorem = force(Kernel.beta(redex))

    theorem.conclusion shouldBe equation(redex, y)
  }

  it should "refuse a term that is not a redex" in {
    Kernel.beta(x).left.map(_.getClass) shouldBe Left(classOf[NotABetaRedex])
  }

  "Assumption" should "prove a proposition from itself" in {
    val theorem = force(Kernel.assume(p))

    theorem.hypotheses shouldBe List(p)
    theorem.conclusion shouldBe p
  }

  it should "refuse a term that is not a proposition" in {
    Kernel.assume(x).left.map(_.getClass) shouldBe Left(classOf[NotAProposition])
  }

  "Modus ponens on an equation" should "give the right side from the left" in {
    val pq = Kernel.deductAntisym(force(Kernel.assume(p)), force(Kernel.assume(q)))
    val theorem = force(Kernel.eqMp(pq, force(Kernel.assume(p))))

    theorem.conclusion shouldBe q
    theorem.hypotheses should contain(p)
  }

  it should "refuse an antecedent that is not the left side" in {
    val pq = Kernel.deductAntisym(force(Kernel.assume(p)), force(Kernel.assume(q)))

    Kernel.eqMp(pq, force(Kernel.assume(q))).left.map(_.getClass) shouldBe
      Left(classOf[TermsDiffer])
  }

  "Antisymmetry of deduction" should "discharge each conclusion from the other's hypotheses" in {
    val theorem = Kernel.deductAntisym(force(Kernel.assume(p)), force(Kernel.assume(q)))

    theorem.conclusion shouldBe equation(p, q)
    theorem.hypotheses shouldBe List(p, q).sorted(using Term.ordering)
  }

  "Instantiation" should "replace a free variable in conclusion and hypotheses" in {
    val assumption = force(Kernel.assume(equation(x, x)))
    val theorem = force(Kernel.inst(Map(x -> y), assumption))

    theorem.conclusion shouldBe equation(y, y)
    theorem.hypotheses shouldBe List(equation(y, y))
  }

  it should "refuse a replacement of the wrong type" in {
    Kernel.inst(Map(x -> Term.variable("z", B)), Kernel.refl(x)).left.map(_.getClass) shouldBe
      Left(classOf[TypeMismatch])
  }

  "Type instantiation" should "carry a theorem to an instance of its type variables" in {
    val theorem = Kernel.instType(Map("A" -> Type.Bool), Kernel.refl(x))
    val expected = Term.variable("x", Type.Bool)

    theorem.conclusion shouldBe equation(expected, expected)
  }

  it should "carry the hypotheses to the same instance" in {
    // The branch that instantiates the hypotheses was reached by nothing until an audit noticed:
    // replacing it with the empty list would have passed every test in the repository, and would
    // have been a theorem with its assumptions dropped.
    val theorem = Kernel.instType(Map("A" -> Type.Bool), force(Kernel.assume(equation(x, y))))
    val xBool = Term.variable("x", Type.Bool)
    val yBool = Term.variable("y", Type.Bool)

    theorem.hypotheses shouldBe List(equation(xBool, yBool))
    theorem.conclusion shouldBe equation(xBool, yBool)
  }

  it should "identify two variables that differed only in their type, as it documents" in {
    // `h (x:A) (x:B)` at A := bool, B := bool is `h (x:bool) (x:bool)`: one variable where there
    // were two. Sound, because the statement held for every value of both.
    val h = Term.variable("h", Type.fun(A, Type.fun(B, Type.Bool)))
    val xAtB = Term.variable("x", B)
    val statement = force(Term.appAll(h, List(x, xAtB)))

    val theorem =
      Kernel.instType(Map("A" -> Type.Bool, "B" -> Type.Bool), force(Kernel.assume(statement)))

    val hBool = Term.variable("h", Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool)))
    val xBool = Term.variable("x", Type.Bool)
    Term.freeVariables(theorem.conclusion) shouldBe Set(hBool, xBool)
    theorem.conclusion shouldBe force(Term.appAll(hBool, List(xBool, xBool)))
  }

  "The hypotheses of a theorem" should "not depend on the order the rules were applied in" in {
    val left = Kernel.deductAntisym(force(Kernel.assume(p)), force(Kernel.assume(q)))
    val right = Kernel.deductAntisym(force(Kernel.assume(q)), force(Kernel.assume(p)))

    left.hypotheses shouldBe right.hypotheses
  }

  /**
   * Symmetry is not a rule of the kernel. Deriving it here is the adequacy check on the ten that
   * are: if the primitive set were missing something, this is where it would show.
   */
  "The primitive rules" should "be enough to derive symmetry of equality" in {
    def symmetry(theorem: Kernel.Thm): Either[KernelError, Kernel.Thm] =
      Term.destEq(theorem.conclusion) match {
        case None => Left(NotAnEquation(theorem.conclusion))
        case Some((lhs, _)) =>
          val equalityConstant = Kernel.refl(Term.equalityAt(Term.typeOf(lhs)))
          for {
            applied <- Kernel.mkComb(equalityConstant, theorem)
            both <- Kernel.mkComb(applied, Kernel.refl(lhs))
            result <- Kernel.eqMp(both, Kernel.refl(lhs))
          } yield result
      }

    val assumption = force(Kernel.assume(equation(x, y)))
    val reversed = force(symmetry(assumption))

    reversed.conclusion shouldBe equation(y, x)
    reversed.hypotheses shouldBe List(equation(x, y))
  }
}
