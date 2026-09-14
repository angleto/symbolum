package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What the strong form of infinity would cost if it were derived instead of asserted.
 *
 * `Natural.scala` asserts infinity in the form the construction uses, rather than HOL Light's weak
 * form `?f. ONE_ONE f /\ ~(ONTO f)` with the strong one derived from it. The reason written beside
 * that choice was that the derivation turns `~(!y. ?x. …)` into `?y. ~(?x. …)`, which is the
 * excluded middle, **"which this logic does not have"** — so the alternative was two axioms where
 * this is one.
 *
 * **That reason stopped being true on 2026-09-10.** The excluded middle is derived here now, from
 * choice and eta, and costs no axiom of its own. The comparison is one axiom and a derivation
 * either way, and the argument written next to the choice is no longer the argument.
 *
 * So this file measures the other half, which nobody had: the derivation is written out, from the
 * weak form **assumed** rather than asserted, and its size is the number the decision wants. The
 * trusted base is not touched by it — what comes back carries the weak form on its left.
 */
class InfinitySpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val naturals = Natural.standard
  private val classical = naturals.classical
  private val logic = naturals.logic
  private val rules = logic.rules

  private val ind: Type = TyApp(Natural.Individuals, Nil)
  private val map: Type = Type.fun(ind, ind)

  private def read(text: String): Term =
    force(Parser.proposition(naturals.theory, naturals.notation, text))

  private val weak = read(
    "?f:ind->ind. (!x:ind. !y:ind. f x = f y ==> x = y) /\\ ~(!y:ind. ?x:ind. f x = y)"
  )

  private val strong = force(naturals.axiom(Natural.Infinity)).conclusion

  /** `?x. P x` from `|- P a`, with the predicate written out. */
  private def exists(variable: FVar, body: Term, witness: Term, theorem: Kernel.Thm): Kernel.Thm = {
    val predicate = force(LogicError.lift(Term.abs(variable, body)))
    force(rules.existsIntro(predicate, witness, theorem))
  }

  "The strong form of infinity" should "follow from the weak one, at a cost worth knowing" in {
    val assumed = force(LogicError.lift(Kernel.assume(weak)))

    val f = Term.variable("f", map)
    val onto = read("!y:ind. ?x:ind. (f:ind->ind) x = y")
    val injective = read("!x:ind. !y:ind. (f:ind->ind) x = (f:ind->ind) y ==> x = y")
    val notOnto = force(logic.mkNot(onto))
    val body = force(logic.mkConj(injective, notOnto))

    val fromWitness = {
      val assumedBody = force(LogicError.lift(Kernel.assume(body)))
      val one = force(rules.conjElim1(assumedBody))
      val missing = force(rules.conjElim2(assumedBody))

      // `?y. ~(?x. f x = y)` from `~(!y. ?x. f x = y)`. This is the step the old note called the
      // excluded middle, and it is: the proof is by contradiction twice over.
      val y = Term.variable("y", ind)
      val reached = read("?x:ind. (f:ind->ind) x = (y:ind)")
      val notReached = force(logic.mkNot(reached))
      val someMissed = force(logic.mkExists(y, notReached))

      val everyReached = {
        val denied = force(LogicError.lift(Kernel.assume(force(logic.mkNot(someMissed)))))
        val perPoint = {
          val nq = force(LogicError.lift(Kernel.assume(notReached)))
          val witnessed = exists(y, notReached, y, nq)
          val absurd = force(rules.notElim(denied, witnessed))
          force(classical.contradiction(reached, absurd))
        }
        val everywhere = force(rules.gen(y, perPoint))
        val absurd = force(rules.notElim(missing, everywhere))
        force(classical.contradiction(someMissed, absurd))
      }

      // And out of that existential, the pair the strong form wants.
      val z = Term.variable("z", ind)
      val missedAtZ = force(logic.mkNot(read("?x:ind. (f:ind->ind) x = (z:ind)")))
      val perZ = {
        val assumedMiss = force(LogicError.lift(Kernel.assume(missedAtZ)))
        val x = Term.variable("x", ind)
        val hit = read("(f:ind->ind) (x:ind) = (z:ind)")
        val perX = {
          val assumedHit = force(LogicError.lift(Kernel.assume(hit)))
          val witnessed = exists(x, hit, x, assumedHit)
          val absurd = force(rules.notElim(assumedMiss, witnessed))
          force(rules.notIntro(hit, absurd))
        }
        val never = force(rules.gen(x, perX))
        val paired = force(rules.conjIntro(one, never))
        val atZ = exists(z, force(logic.mkConj(injective, never.conclusion)), z, paired)
        exists(f, atZ.conclusion, f, atZ)
      }

      force(rules.existsElim(everyReached, z, perZ))
    }

    val result = force(rules.existsElim(assumed, f, fromWitness))

    result.conclusion shouldBe strong
    result.hypotheses shouldBe List(weak)

    info(
      s"the strong form follows from the weak one in ${Derivation.size(result)} inferences, " +
        s"reaching ${Derivation.axiomsOf(result).size} axioms"
    )
  }
}
