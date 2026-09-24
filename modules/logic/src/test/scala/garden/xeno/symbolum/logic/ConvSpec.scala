package garden.xeno.symbolum.logic

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * The conversions the derived rules are built out of.
 *
 * Two properties matter here and neither is about the result being pretty. Normalisation has to
 * produce a theorem whose left side is the term that went in, because the callers chain it with
 * `trans` and a left side that drifted would break the chain silently. And unfolding a definition
 * has to leave its left side alone, because that is what the caller matches a theorem against.
 */
class ConvSpec extends AnyFlatSpec with Matchers {


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

  private val bool = Type.Bool
  private val logic = Logic.standard

  private val p = Term.variable("p", bool)
  private val q = Term.variable("q", bool)

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"expected success, got $error"), identity)

  "Beta normalisation" should "leave a term with no redex alone" in {
    val theorem = force(Conv.betaNormalise(p))

    theorem.conclusion shouldBe force(Term.eq(p, p))
  }

  it should "contract a chain of applications to a nested lambda" in {
    val a = Term.variable("a", bool)
    val b = Term.variable("b", bool)
    val selector = lam(a, lam(b, a))
    val applied = force(Term.appAll(selector, List(p, q)))

    val theorem = force(Conv.betaNormalise(applied))

    theorem.conclusion shouldBe force(Term.eq(applied, p))
  }

  it should "reduce under a binder and rebuild the binder it opened" in {
    val x = Term.variable("x", bool)
    val y = Term.variable("y", bool)
    val identity = lam(y, y)
    val term = lam(x, force(Term.app(identity, x)))

    val theorem = force(Conv.betaNormalise(term))

    theorem.conclusion shouldBe force(Term.eq(term, lam(x, x)))
  }

  "Unfolding a definition" should "leave the left side as the caller wrote it" in {
    val definition = force(logic.definitionOf(Logic.Conjunction))
    val theorem = force(Conv.unfold(definition, List(p, q)))

    Term.destEq(theorem.conclusion).map(_._1) shouldBe Some(force(logic.mkConj(p, q)))
  }

  it should "substitute the arguments into the body rather than leaving them pending" in {
    val definition = force(logic.definitionOf(Logic.Conjunction))
    val theorem = force(Conv.unfold(definition, List(p, q)))
    val body = Term.destEq(theorem.conclusion).map(_._2)

    // The body is an equation between two functions, not an application waiting to be reduced.
    body.flatMap(Term.destEq) should not be None
  }

  it should "put an argument into the body as it was written, redex included" in {
    // Only the application the unfolding makes is contracted. The first version normalised the
    // whole right side, so an argument containing a redex came out reduced on the right and as
    // written on the left, and no rule could move a theorem across that equation.
    val z = Term.variable("z", bool)
    val redex = force(Term.app(lam(z, z), p))
    val definition = force(logic.definitionOf(Logic.Negation))
    val theorem = force(Conv.unfold(definition, List(redex)))

    theorem.conclusion shouldBe
      force(Term.eq(force(logic.mkNot(redex)), force(logic.mkImp(redex, logic.falsity))))
  }

  "Symmetry" should "reverse an equation" in {
    val theorem = force(Conv.sym(Kernel.refl(p)))

    theorem.conclusion shouldBe force(Term.eq(p, p))
  }

  it should "refuse a theorem that is not an equation" in {
    Conv.sym(force(Kernel.assume(p))).left.map(_.getClass) shouldBe Left(classOf[NotOfForm])
  }

  "A fresh variable" should "avoid the names it was told to avoid" in {
    val taken = Set(Term.variable("v", bool), Term.variable("v1", bool))
    val fresh = Conv.freshVariable("v", bool, taken)

    fresh.name shouldBe "v2"
  }

  /* ------------------------------------------------ the shared reflexivity leaves */

  "Reflexivity on an atom" should "be one object however many times it is asked for" in {
    // What the cache is for, and the only observable difference it makes. A proof node is counted
    // by identity, so two objects with the same sequent are two inferences; over the standard
    // library that was 134532 nodes that were the same leaf built again.
    val first = Conv.refl(p)
    val second = Conv.refl(p)

    (first eq second) shouldBe true
    first.conclusion shouldBe force(Term.eq(p, p))
    first.hypotheses shouldBe Nil
  }

  it should "be the same theorem the rule gives, which is what makes the sharing sound" in {
    // Nothing about the theorem changes: same sequent, same derivation node. If this stopped
    // holding, the cache would be handing out something other than reflexivity.
    val cached = Conv.refl(p)
    val built = Kernel.refl(p)

    cached shouldBe built
    cached.derivation shouldBe built.derivation
  }

  it should "hold a constant and a bound-free variable alike, and not an application" in {
    // The population the cache is bounded by. An application is not shared, because a table keyed
    // by arbitrary terms is unbounded in the size of what anyone proves and pays an O(size) hash
    // per lookup. `Conv`'s docstring carries the census over the library, dated, that compared the
    // distinct atoms with the distinct terms and what sharing each would recover.
    val implication = force(logic.mkImp(p, q))

    (Conv.refl(logic.truth) eq Conv.refl(logic.truth)) shouldBe true
    (Conv.refl(q) eq Conv.refl(q)) shouldBe true
    (Conv.refl(implication) eq Conv.refl(implication)) shouldBe false
    Conv.refl(implication).conclusion shouldBe force(Term.eq(implication, implication))
  }

  it should "stop growing at its bound rather than refusing" in {
    // The behaviour at the cap, which is not a refusal: past it the rule is called directly and
    // only the saving stops. Asserted on the number rather than by filling the table, because
    // filling it would leave `Conv.Atoms` entries behind for every suite that runs after this one.
    Conv.Atoms should be > 4287
  }

  "Symmetry" should "build one reflexivity and not two" in {
    // `sym` wants `|- lhs = lhs` on both sides of its assembly and used to build it twice, which
    // was two nodes where the proof has one. Counted rather than described.
    // Three leaves before the repair and two after: the equality constant, and the left side,
    // which the assembly wants on both sides of itself and used to build once for each.
    val theorem = force(Conv.sym(Conv.refl(q)))
    val leaves = Derivation.census(theorem).getOrElse("Reflexivity", 0)

    leaves shouldBe 2
  }
}
