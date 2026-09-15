package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A claim about something that is not mathematics, formalised end to end and costing nothing.
 *
 * The stated purpose of this system includes expressing axioms and rules from domains that are not
 * logical or mathematical — software engineering, economics, the social sciences — in order to
 * argue about the real world. `proving.md` has had the *mechanism* for a while: a theory is a value,
 * declaring a type and a constant costs nothing to believe, and a model's assumptions belong on the
 * left of the turnstile rather than in `assertAxiom`. What it did not have is a worked argument.
 *
 * This is one, and the domain is a consignment rule: a hazardous shipment carries a manifest; a
 * manifest means an itemised list or a countersignature; either of those is traceable. Therefore a
 * hazardous shipment is traceable.
 *
 * **The rule is invented, and until 2026-09-15 it was not.** It was the tiering rule of the
 * practice this repository is developed under, which made a fragment of a private document the
 * subject of a public test. Nothing here depended on whose rule it was: what the derivation costs
 * is fixed by the shape, an implication into a disjunction whose two arms reach one conclusion, and
 * every rule of that shape costs the same. `DomainTheorySpec` was changed the same day for the same
 * reason and says so in the same words.
 *
 * == What the reader should take from it, in order ==
 *
 * **The conclusion costs zero axioms.** Not "few". The premises are hypotheses, so they are visible
 * in the sequent and a reader can argue with the model; the derivation uses connectives that are
 * definitional extensions; and nothing here reaches the sixteen, the choice operator or infinity.
 * `Derivation.axiomsOf` is empty and the test says so.
 *
 * **The case split is done by the machine.** *A manifest means an itemised list or a
 * countersignature* is a disjunction, and the argument has to go both ways round it. That is `Minimal`, on the fragment
 * with no negation in it, and it is why this is automation on a domain and not only bookkeeping.
 *
 * **The declared constants are conservative.** `shipment`, `hazardous`, `manifested`,
 * `itemised`, `countersigned` and `traceable` are declared and never defined, so they prove exactly what their absence proves.
 * The theory holds no axiom of its own and the argument is entirely in what was assumed.
 *
 * == The limits, which are the interesting half ==
 *
 * **Nothing checks that the premises are consistent.** `h |- c` holds vacuously when the hypotheses
 * contradict each other, and a domain model is exactly where that happens. `Refutation.satisfying`
 * is the untrusted answer and it is not run here.
 *
 * **A declared type cannot be said to be inhabited.** As far as the theory knows there may be no
 * shipments at all, and `?p:shipment. T` is not derivable. Asserting it would be an axiom.
 *
 * **The fragment is propositional.** An argument whose premises quantify over something other than
 * the subject, or that needs a negation, is outside what `Minimal` reaches, and is a hand
 * derivation with `Rules` or nothing. That is stated rather than worked around.
 */
class DomainSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private val shipment: Type = TyApp("shipment", Nil)
  private val predicate: Type = Type.fun(shipment, Type.Bool)

  /** The domain: one type and five predicates on it, declared and never defined. */
  private val theory: Theory = force(
    Vector("hazardous", "manifested", "itemised", "countersigned", "traceable")
      .foldLeft(Logic.standard.theory.declareTypeOperator("shipment", 0)) { (acc, name) =>
        acc.flatMap(_.declareConstant(name, predicate))
      }
  )

  /**
   * The connectives over the domain, which is the step a domain theory cannot skip.
   *
   * `Logic.standard` has never heard of `shipment`, and quantifying over it means asking the theory
   * for the quantifier constant at that type. `Divisibility` documents the same widening for the
   * reals and the reason is identical.
   */
  private val domain: Logic = force(Logic.standard.over(theory))

  private def at(name: String, subject: Term): Term =
    force(Term.app(force(theory.constant(name, predicate)), subject))

  private def read(text: String): Term = force(Parser.proposition(theory, Notation.standard, text))

  private val premises = Vector(
    "!p:shipment. hazardous p ==> manifested p",
    "!p:shipment. manifested p ==> itemised p \\/ countersigned p",
    "!p:shipment. itemised p ==> traceable p",
    "!p:shipment. countersigned p ==> traceable p"
  )

  private val claim = "!p:shipment. hazardous p ==> traceable p"

  "An argument from a domain nobody has axiomatised" should "be proved, and cost no axiom at all" in {
    // The premises are stated at the subject rather than assumed for every shipment, which is what
    // makes this one statement of the fragment: the universals come off, the argument is about one
    // `p`, and the quantifier goes back on at the end.
    val stated =
      s"!p:shipment. (hazardous p ==> manifested p) /\\ " +
        "(manifested p ==> itemised p \\/ countersigned p) /\\ " +
        "(itemised p ==> traceable p) /\\ (countersigned p ==> traceable p) " +
        "==> (hazardous p ==> traceable p)"

    val theorem = force(Minimal(domain).prove(read(stated)))

    theorem.conclusion shouldBe read(stated)
    theorem.hypotheses shouldBe empty

    withClue("a domain argument must not be believed on anything: ") {
      Derivation.axiomsOf(theorem) shouldBe empty
    }

    info(s"${Derivation.size(theorem)} inferences, no axiom, over a theory nobody axiomatised")
  }

  it should "carry its premises where a reader can argue with them" in {
    // The other arrangement, and the one `proving.md` argues for: the premises assumed rather than
    // written into the statement. What comes back names them in its own sequent, which is what lets
    // somebody disagree with the model instead of with the system.
    val assumed = premises.map(text => force(Kernel.assume(read(text))))
    val subject = Term.variable("p", shipment)

    val instantiated = assumed.map(premise => force(domain.rules.spec(subject, premise)))

    val derived = force(
      for {
        carries <- Right(instantiated(0))
        split <- Right(instantiated(1))
        byList <- Right(instantiated(2))
        bySignature <- Right(instantiated(3))
        subjectIsHazardous <- LogicError.lift(Kernel.assume(at("hazardous", subject)))
        manifested <- domain.rules.mp(carries, subjectIsHazardous)
        cases <- domain.rules.mp(split, manifested)
        left <- LogicError.lift(Kernel.assume(at("itemised", subject)))
        right <- LogicError.lift(Kernel.assume(at("countersigned", subject)))
        fromList <- domain.rules.mp(byList, left)
        fromSignature <- domain.rules.mp(bySignature, right)
        result <- domain.rules.disjElim(cases, fromList, fromSignature)
      } yield result
    )

    // Four premises and the assumption that the subject is hazardous, and nothing else. That
    // list is the model.
    derived.hypotheses.size shouldBe 5
    Derivation.axiomsOf(derived) shouldBe empty

    info(derived.hypotheses.map(Show.show(Notation.standard, _)).mkString("assumes: ", "; ", ""))
  }

  "A domain argument that needs a negation" should "be refused by name rather than attempted" in {
    // The boundary, and it is where a reader has to stop and derive by hand. `~(waived r)` is the
    // shape a real consignment rule takes and it is outside the fragment that costs nothing.
    val withNegation = read("!p:shipment. ~(manifested p) ==> ~(hazardous p)")

    Minimal(domain).prove(withNegation) match {
      case Right(theorem) => fail(s"the fragment must not reach $theorem")
      case Left(refusal) => refusal.message should include("negation")
    }
  }

  "A declared domain type" should "be sayable to have something in it, on no axiom" in {
    // Run rather than reasoned about, and the answer is the opposite of what `proving.md` said
    // until 2026-09-11. The guide claimed `?x:agent. T` was not derivable and that asserting it
    // would cost an axiom. It is derivable and it costs none: a free variable of the type IS a term
    // of the type, and HOL's semantics require every type to be non-empty anyway, so existential
    // introduction at that variable is an ordinary step.
    //
    // What is actually unreachable is **cardinality**. Nothing here says a declared type has two
    // elements, or infinitely many, and that is what the old paragraph was reaching for.
    val witness = Term.variable("p", shipment)
    val predicate = force(Term.abs(witness, domain.truth))
    val trivial = force(domain.rules.truth)

    val inhabited = force(domain.rules.existsIntro(predicate, witness, trivial))

    inhabited.conclusion shouldBe read("?p:shipment. T")
    inhabited.hypotheses shouldBe empty
    Derivation.axiomsOf(inhabited) shouldBe empty
  }

  it should "still be outside the fragment this file's procedure decides" in {
    // `Minimal` is propositional: it has no rule for an existential and says so rather than
    // searching. The two facts above and here are different and a reader must not merge them.
    Minimal(domain).prove(read("?p:shipment. T")).isLeft shouldBe true
  }
}
