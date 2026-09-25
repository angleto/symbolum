package garden.xeno.symbolum.kernel

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * A theorem carries how it was obtained.
 *
 * Until 2026-09-10 it carried nothing, and `docs/evaluation.md` had a row it could not fill for
 * that reason: a kernel benchmark here had to be adversarial rather than differential, because
 * there was nothing for a second checker to replay.
 */
class DerivationSpec extends AnyFlatSpec with Matchers {


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

  private def force[T](result: Either[KernelError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val bool = Type.Bool
  private val p = Term.variable("p", bool)
  private val q = Term.variable("q", bool)

  "Every rule" should "record itself, with the theorems it was given" in {
    val reflexive = Kernel.refl(p)
    reflexive.derivation shouldBe Derivation.Reflexivity(p)

    val assumed = force(Kernel.assume(p))
    assumed.derivation shouldBe Derivation.Assumption(p)

    val symmetric = force(Kernel.trans(reflexive, reflexive))
    symmetric.derivation shouldBe Derivation.Transitivity(reflexive, reflexive)

    val antisymmetric = Kernel.deductAntisym(assumed, force(Kernel.assume(q)))
    antisymmetric.derivation shouldBe
      Derivation.Antisymmetry(assumed, force(Kernel.assume(q)))
  }

  it should "leave the record out of what makes two theorems equal" in {
    // The rules compare theorems to drop a duplicate hypothesis and to discharge one, so two proofs
    // of one sequent have to be interchangeable there. A derivation says how this one was reached
    // and not what it says, so it takes no part.
    val direct = Kernel.refl(p)
    val roundabout = force(Kernel.trans(Kernel.refl(p), Kernel.refl(p)))

    direct shouldBe roundabout
    direct.derivation should not be roundabout.derivation
  }

  "A proof" should "be a graph, so a step used twice is counted once" in {
    val once = Kernel.refl(p)
    val twice = force(Kernel.trans(once, once))

    // Three nodes and not four: `once` is one object reached by two edges.
    Derivation.size(twice) shouldBe 2
    Derivation.size(once) shouldBe 1
  }

  "The axioms a theorem rests on" should "be exactly the ones its proof reaches" in {
    // The question nothing could answer before. A derivation that turns up no axiom rests on the
    // inference rules alone, and one that turns up an axiom names it.
    val theory = force(Theory.primitive.declareConstant("c", bool))
    val statement = force(theory.constant("c", bool))
    val (extended, axiom) = force(Kernel.assertAxiom(theory, statement))

    Derivation.axiomsOf(axiom) shouldBe Set(statement)
    Derivation.axiomsOf(Kernel.refl(p)) shouldBe empty

    // And through a derivation: what the conclusion rests on is what its premises rest on.
    val carried = force(Kernel.trans(Kernel.refl(statement), Kernel.refl(statement)))
    Derivation.axiomsOf(carried) shouldBe empty

    val resting = force(Kernel.eqMp(Kernel.deductAntisym(axiom, axiom), axiom))
    Derivation.axiomsOf(resting) shouldBe Set(statement)
    extended.axioms shouldBe List(statement)
  }

  "A definition and a type definition" should "record what extended the theory" in {
    val identity = lam(p, p)
    val (_, defined) = force(Kernel.defineConstant(Theory.primitive, "id", identity))

    defined.derivation shouldBe Derivation.Definition("id", identity)
    Derivation.axiomsOf(defined) shouldBe empty
  }

  /* ------------------------------------------------------------------ a cited fact */

  /**
   * A fact with a proof of several steps resting on one axiom, cited once, and a proof using it
   * both through the citation and around it, which is the comparison `docs/adr/0047` is about.
   */
  private object Cited {
    val theory: Theory = force(Theory.primitive.declareConstant("c", bool))
    val statement: Term = force(theory.constant("c", bool))
    val axiom: Kernel.Thm = force(Kernel.assertAxiom(theory, statement))._2
    val fact: Kernel.Thm = force(
      Kernel.eqMp(
        Kernel.refl(statement),
        force(Kernel.eqMp(Kernel.deductAntisym(axiom, axiom), axiom))
      )
    )
    val cited: Kernel.Thm = Kernel.cite("F", fact)
    val through: Kernel.Thm = force(Kernel.eqMp(Kernel.refl(statement), cited))
    val around: Kernel.Thm = force(Kernel.eqMp(Kernel.refl(statement), fact))
  }

  "A citation" should "restate the fact's sequent and record which fact it is" in {
    Cited.cited shouldBe Cited.fact
    Cited.cited.derivation shouldBe Derivation.Citation("F", Cited.fact)
    Derivation.premises(Cited.cited.derivation) shouldBe List(Cited.fact)
  }

  it should "be one inference to a proof that cites it, whatever the fact's own proof holds" in {
    // The proof through the citation holds itself, a reflexivity and the citation: three, where
    // the one around it holds those two and every step of the fact's proof. That difference is the
    // whole of what the boundary is for, so both are measured rather than only the smaller one.
    Derivation.size(Cited.fact) should be > 1
    Derivation.size(Cited.through) shouldBe 3
    Derivation.size(Cited.around) shouldBe 2 + Derivation.size(Cited.fact)
    Derivation.census(Cited.through).get("Citation") shouldBe Some(1)
  }

  it should "still be the fact's proof when it is the thing asked about" in {
    // A published fact asked about by name is asked about for its proof. Stopping at the root
    // would answer one for every fact in a library, which is the vacuous reading of the boundary.
    Derivation.size(Cited.cited) shouldBe Derivation.size(Cited.fact)
    Derivation.census(Cited.cited) shouldBe Derivation.census(Cited.fact)
  }

  it should "leave what a proof rests on exactly what it was" in {
    // Stopping the walk must not stop the answer: the axiom is under the citation and is reported
    // through it, from the summary the citation keeps.
    Derivation.axiomsOf(Cited.through) shouldBe Set(Cited.statement)
    Derivation.axiomsOf(Cited.through) shouldBe Derivation.axiomsOf(Cited.around)
    Derivation.foreignTo(Theory.primitive, Cited.through).axioms shouldBe Set(Cited.statement)

    // And the named facts a proof used include the ones inside a cited fact, since that question
    // is asked of any named collection and no summary kept on the citation could answer it.
    Derivation.restingOn(Cited.through, Set(Cited.statement)) shouldBe Set(Cited.statement)
  }

  it should "be written out with its fact, so a checker replays the whole of it" in {
    val written = Proof.write(Cited.through)

    written.linesIterator.count(_.contains(" cite F ")) shouldBe 1
    written.linesIterator.count(_.startsWith("s ")) shouldBe Derivation.size(Cited.around) + 1
  }

  /* ----------------------------------------- whether a theorem is one this theory would sign */

  "A theorem resting on nothing" should "be foreign to no theory that can state it" in {
    // The case whose answer is known before it runs, and the one that says the check is not simply
    // reporting everything. `|- p = p` rests on no axiom and names only equality, which every
    // theory has by name and no theory declares.
    val reflexive = Kernel.refl(p)

    Derivation.foreignTo(Theory.primitive, reflexive).clean shouldBe true
  }

  "An axiom another theory asserted" should "be reported as foreign, and as an axiom" in {
    // Two theories that DECLARE one name, which is the case `docs/adr/0008` deliberately leaves
    // open: `c` has no origin in either, so nothing on the term tells them apart. What tells them
    // apart is that one of them asserted something about it.
    val declaring = force(Theory.primitive.declareConstant("c", bool))
    val statement = force(declaring.constant("c", bool))
    val (holder, resting) = force(Kernel.assertAxiom(declaring, statement))

    // Against the theory that asserted it, nothing is foreign; against the sibling that declared
    // the same name and asserted nothing, the axiom is. Both halves, because either alone is
    // satisfied by a check that always answers the same way.
    Derivation.foreignTo(holder, resting).clean shouldBe true
    Derivation.foreignTo(declaring, resting).axioms shouldBe Set(statement)
    Derivation.foreignTo(declaring, resting).constants shouldBe empty
  }

  "A constant another theory defined" should "be reported as foreign, and as a constant" in {
    // The half `docs/adr/0008` already makes safe, reported here so that a caller meets it by name
    // at a boundary instead of several inferences later. Two theories define `id` differently, so
    // the two constants are different terms; a theorem of the first names something the second
    // does not have under that origin.
    val identity = lam(p, p)
    val constantly = lam(p, force(Term.app(lam(q, p), p)))

    val (first, _) = force(Kernel.defineConstant(Theory.primitive, "id", identity))
    val (second, _) = force(Kernel.defineConstant(Theory.primitive, "id", constantly))

    val theirs = Kernel.refl(force(first.constant("id", Type.fun(Type.Bool, Type.Bool))))

    Derivation.foreignTo(first, theirs).clean shouldBe true
    Derivation.foreignTo(second, theirs).constants should have size 1
    Derivation.foreignTo(second, theirs).axioms shouldBe empty
  }

  "A theory that holds strictly more" should "certify what a smaller one proved" in {
    // The property an extension has to have, or the check would refuse every lemma of every stage
    // below the one asking. Extension only adds axioms and constants, so a subset stays a subset.
    val declaring = force(Theory.primitive.declareConstant("c", bool))
    val statement = force(declaring.constant("c", bool))
    val (holder, resting) = force(Kernel.assertAxiom(declaring, statement))
    val widened = force(holder.declareConstant("d", bool))
    val (wider, _) = force(Kernel.assertAxiom(widened, force(widened.constant("d", bool))))

    Derivation.foreignTo(wider, resting).clean shouldBe true
  }
}
