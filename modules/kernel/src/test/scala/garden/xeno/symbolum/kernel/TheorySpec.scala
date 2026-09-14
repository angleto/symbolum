package garden.xeno.symbolum.kernel

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Extending a theory, and the boundary between the extensions that are conservative and the one
 * that is not.
 *
 * The assertion that the primitive theory has no axioms, and that defining constants adds none,
 * is the F2 version of the check the arithmetic theory will need: the trusted base grows only
 * where someone asked for it to grow.
 */
class TheorySpec extends AnyFlatSpec with Matchers {


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
  private val real = TyApp("real", Nil)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  private val withReal: Theory = force(Theory.primitive.declareTypeOperator("real", 0))

  "The primitive theory" should "assert nothing" in {
    Theory.primitive.axioms shouldBe empty
    Theory.primitive.definitions shouldBe empty
  }

  it should "know equality and nothing else" in {
    Theory.primitive.constants.keySet shouldBe Set(Term.EqualityName)
    Theory.primitive.undefinedConstants shouldBe Set(Term.EqualityName)
  }

  it should "know exactly the two type operators the kernel mentions" in {
    Theory.primitive.typeOperators.keySet shouldBe Set("bool", "fun")
  }

  "A declared type operator" should "be rejected at the wrong arity" in {
    withReal.checkType(TyApp("real", List(Type.Bool))).left.map(_.getClass) shouldBe
      Left(classOf[ArityMismatch])
  }

  it should "be rejected when it was never declared" in {
    Theory.primitive.checkType(real).left.map(_.getClass) shouldBe
      Left(classOf[UnknownTypeOperator])
  }

  "A declared constant" should "be usable at an instance of its schema" in {
    val theory = force(withReal.declareConstant("zero", A))

    theory.constant("zero", real) shouldBe Right(new Const("zero", real, None))
  }

  it should "not be usable at a type that is not an instance" in {
    val theory = force(withReal.declareConstant("negate", Type.fun(real, real)))

    theory.constant("negate", Type.fun(Type.Bool, Type.Bool)).left.map(_.getClass) shouldBe
      Left(classOf[NotAnInstance])
  }

  it should "not be declared twice" in {
    val theory = force(withReal.declareConstant("zero", real))

    theory.declareConstant("zero", real).left.map(_.getClass) shouldBe Left(classOf[AlreadyDeclared])
  }

  it should "not shadow equality" in {
    Theory.primitive.declareConstant(Term.EqualityName, A).left.map(_.getClass) shouldBe
      Left(classOf[AlreadyDeclared])
  }

  "Defining a constant" should "prove it equal to its definition and assert nothing" in {
    val identity = lam(Term.variable("x", A), Term.variable("x", A))
    val (theory, theorem) = force(Kernel.defineConstant(Theory.primitive, "I", identity))

    theorem.hypotheses shouldBe empty
    Term.destEq(theorem.conclusion).map(_._2) shouldBe Some(identity)
    theory.axioms shouldBe empty
    theory.definitions.keySet shouldBe Set("I")
  }

  it should "refuse a definition with a free variable" in {
    val open = Term.variable("x", A)

    Kernel.defineConstant(Theory.primitive, "c", open).left.map(_.getClass) shouldBe
      Left(classOf[DefinitionIsNotClosed])
  }

  it should "refuse a definition whose type variables do not all reach its type" in {
    // `(\x:A. x) = (\x:A. x)` is a closed proposition, so its type is bool and A has nowhere to
    // appear. A constant defined by it would be one name for a different value at every
    // instantiation of A.
    val identity = lam(Term.variable("x", A), Term.variable("x", A))
    val proposition = force(Term.eq(identity, identity))

    Kernel.defineConstant(Theory.primitive, "c", proposition).left.map(_.getClass) shouldBe
      Left(classOf[TypeVariablesEscape])
  }

  it should "refuse a name the theory already has" in {
    val identity = lam(Term.variable("x", A), Term.variable("x", A))
    val (theory, _) = force(Kernel.defineConstant(Theory.primitive, "I", identity))

    Kernel.defineConstant(theory, "I", identity).left.map(_.getClass) shouldBe
      Left(classOf[AlreadyDeclared])
  }

  it should "refuse a definition mentioning a constant of another theory" in {
    val other = force(Theory.primitive.declareConstant("elsewhere", Type.Bool))
    val foreign = force(other.constant("elsewhere", Type.Bool))

    Kernel.defineConstant(Theory.primitive, "c", foreign).left.map(_.getClass) shouldBe
      Left(classOf[UnknownConstant])
  }

  "Asserting an axiom" should "add exactly one proposition to the theory" in {
    // A closed one. `p = p` with `p` free was what this test asserted until an audit pointed out
    // that an axiom with a free variable is a schema, and the kernel now refuses it.
    val identity = lam(Term.variable("x", A), Term.variable("x", A))
    val (theory, theorem) =
      force(Kernel.assertAxiom(Theory.primitive, force(Term.eq(identity, identity))))

    theory.axioms.length shouldBe 1
    theorem.hypotheses shouldBe empty
    theorem.conclusion shouldBe theory.axioms.head
  }

  it should "refuse a term that is not a proposition" in {
    Kernel.assertAxiom(Theory.primitive, Term.variable("x", A)).left.map(_.getClass) shouldBe
      Left(classOf[NotAProposition])
  }

  it should "refuse a proposition with a free variable, which would be a schema" in {
    val p = Term.variable("p", Type.Bool)

    Kernel.assertAxiom(Theory.primitive, force(Term.eq(p, p))).left.map(_.getClass) shouldBe
      Left(classOf[DefinitionIsNotClosed])
  }

  it should "be the only extension that grows the axioms" in {
    val identity = lam(Term.variable("x", A), Term.variable("x", A))
    val (defined, _) = force(Kernel.defineConstant(Theory.primitive, "I", identity))
    val declared = force(defined.declareConstant("c", A))
    val withOperator = force(declared.declareTypeOperator("list", 1))

    withOperator.axioms shouldBe empty
  }
}
