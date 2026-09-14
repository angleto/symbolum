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
 * This is one, and the domain is the one nearest to hand: the tiering rule of the engineering
 * handbook that governs this repository. A tier-two project has a gate; a gate means a review or a
 * signature; either of those is auditable. Therefore a tier-two project is auditable.
 *
 * == What the reader should take from it, in order ==
 *
 * **The conclusion costs zero axioms.** Not "few". The premises are hypotheses, so they are visible
 * in the sequent and a reader can argue with the model; the derivation uses connectives that are
 * definitional extensions; and nothing here reaches the sixteen, the choice operator or infinity.
 * `Derivation.axiomsOf` is empty and the test says so.
 *
 * **The case split is done by the machine.** *A gate means a review or a signature* is a
 * disjunction, and the argument has to go both ways round it. That is `Minimal`, on the fragment
 * with no negation in it, and it is why this is automation on a domain and not only bookkeeping.
 *
 * **The declared constants are conservative.** `project`, `tierTwo`, `gated`, `reviewed`, `signed`
 * and `auditable` are declared and never defined, so they prove exactly what their absence proves.
 * The theory holds no axiom of its own and the argument is entirely in what was assumed.
 *
 * == The limits, which are the interesting half ==
 *
 * **Nothing checks that the premises are consistent.** `h |- c` holds vacuously when the hypotheses
 * contradict each other, and a domain model is exactly where that happens. `Refutation.satisfying`
 * is the untrusted answer and it is not run here.
 *
 * **A declared type cannot be said to be inhabited.** As far as the theory knows there may be no
 * projects at all, and `?p:project. T` is not derivable. Asserting it would be an axiom.
 *
 * **The fragment is propositional.** An argument whose premises quantify over something other than
 * the subject, or that needs a negation, is outside what `Minimal` reaches, and is a hand
 * derivation with `Rules` or nothing. That is stated rather than worked around.
 */
class DomainSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private val project: Type = TyApp("project", Nil)
  private val predicate: Type = Type.fun(project, Type.Bool)

  /** The domain: one type and five predicates on it, declared and never defined. */
  private val theory: Theory = force(
    Vector("tierTwo", "gated", "reviewed", "signed", "auditable")
      .foldLeft(Logic.standard.theory.declareTypeOperator("project", 0)) { (acc, name) =>
        acc.flatMap(_.declareConstant(name, predicate))
      }
  )

  /**
   * The connectives over the domain, which is the step a domain theory cannot skip.
   *
   * `Logic.standard` has never heard of `project`, and quantifying over it means asking the theory
   * for the quantifier constant at that type. `Divisibility` documents the same widening for the
   * reals and the reason is identical.
   */
  private val domain: Logic = force(Logic.standard.over(theory))

  private def at(name: String, subject: Term): Term =
    force(Term.app(force(theory.constant(name, predicate)), subject))

  private def read(text: String): Term = force(Parser.proposition(theory, Notation.standard, text))

  private val premises = Vector(
    "!p:project. tierTwo p ==> gated p",
    "!p:project. gated p ==> reviewed p \\/ signed p",
    "!p:project. reviewed p ==> auditable p",
    "!p:project. signed p ==> auditable p"
  )

  private val claim = "!p:project. tierTwo p ==> auditable p"

  "An argument from a domain nobody has axiomatised" should "be proved, and cost no axiom at all" in {
    // The premises are stated at the subject rather than assumed for every project, which is what
    // makes this one statement of the fragment: the universals come off, the argument is about one
    // `p`, and the quantifier goes back on at the end.
    val stated =
      s"!p:project. (tierTwo p ==> gated p) /\\ (gated p ==> reviewed p \\/ signed p) /\\ " +
        "(reviewed p ==> auditable p) /\\ (signed p ==> auditable p) ==> (tierTwo p ==> auditable p)"

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
    val subject = Term.variable("p", project)

    val instantiated = assumed.map(premise => force(domain.rules.spec(subject, premise)))

    val derived = force(
      for {
        gate <- Right(instantiated(0))
        split <- Right(instantiated(1))
        byReview <- Right(instantiated(2))
        bySignature <- Right(instantiated(3))
        tier <- LogicError.lift(Kernel.assume(at("tierTwo", subject)))
        gated <- domain.rules.mp(gate, tier)
        cases <- domain.rules.mp(split, gated)
        left <- LogicError.lift(Kernel.assume(at("reviewed", subject)))
        right <- LogicError.lift(Kernel.assume(at("signed", subject)))
        fromReview <- domain.rules.mp(byReview, left)
        fromSignature <- domain.rules.mp(bySignature, right)
        result <- domain.rules.disjElim(cases, fromReview, fromSignature)
      } yield result
    )

    // Four premises and the tiering assumption, and nothing else. That list is the model.
    derived.hypotheses.size shouldBe 5
    Derivation.axiomsOf(derived) shouldBe empty

    info(derived.hypotheses.map(Show.show(Notation.standard, _)).mkString("assumes: ", "; ", ""))
  }

  "A domain argument that needs a negation" should "be refused by name rather than attempted" in {
    // The boundary, and it is where a reader has to stop and derive by hand. `~(waived r)` is the
    // shape a real handbook rule takes and it is outside the fragment that costs nothing.
    val withNegation = read("!p:project. ~(gated p) ==> ~(tierTwo p)")

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
    val witness = Term.variable("p", project)
    val predicate = force(Term.abs(witness, domain.truth))
    val trivial = force(domain.rules.truth)

    val inhabited = force(domain.rules.existsIntro(predicate, witness, trivial))

    inhabited.conclusion shouldBe read("?p:project. T")
    inhabited.hypotheses shouldBe empty
    Derivation.axiomsOf(inhabited) shouldBe empty
  }

  it should "still be outside the fragment this file's procedure decides" in {
    // `Minimal` is propositional: it has no rule for an existential and says so rather than
    // searching. The two facts above and here are different and a reader must not merge them.
    Minimal(domain).prove(read("?p:project. T")).isLeft shouldBe true
  }
}
