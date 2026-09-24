package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * The arithmetic of `num` builds over a theory that does not declare `real`.
 *
 * `docs/adr/0016`'s phase 0, asserted rather than described. The record's own guard says why this
 * shape and not the obvious one: a test saying these facts do not reach the sixteen axioms of the
 * reals **passes today**, and would go on passing if the reals crept back in through a lemma that
 * happens to cost no axiom. What cannot go vacuous is that the development builds at all over a
 * theory in which the type operator is not declared, because there is then nothing to creep in.
 */
final class ArithmeticBelowTheRealsSpec extends AnyFlatSpec with Matchers {

  private def force[E, T](result: Either[E, T]): T =
    result.fold(error => fail(s"unexpected refusal: $error"), identity)

  private val realType: Type = TyApp(Real.TypeName, Nil)
  private val naturals = Chain.standard.naturals
  private lazy val built = force(Peano.arithmetic(naturals))
  private def theory: Theory = built._1
  private def facts: Map[String, Kernel.Thm] = built._4

  /** Does a type mention `real` anywhere inside it? */
  private def typeTouchesReal(ty: Type): Boolean = ty match {
    case TyVar(_) => false
    case TyApp(operator, arguments) =>
      operator == Real.TypeName || arguments.exists(typeTouchesReal)
  }

  /** Does a term mention `real`, in the type of a leaf or in a constant it names? */
  private def touchesReal(term: Term): Boolean = term match {
    case BVar(_) => false
    case FVar(_, ty) => typeTouchesReal(ty)
    case Const(_, ty) => typeTouchesReal(ty)
    case App(fn, arg) => touchesReal(fn) || touchesReal(arg)
    case Abs(binderType, body) => typeTouchesReal(binderType) || touchesReal(body)
  }

  "The theory the arithmetic is built over" should "not declare the type of a real number" in {
    // The assertion the whole file is for. `checkType` is the theory saying whether it knows a
    // type, and a Left here is the development being genuinely below the reals rather than merely
    // not using them.
    naturals.theory.checkType(realType).isLeft shouldBe true
  }

  it should "still not declare it after seven stages have extended it" in {
    theory.checkType(realType).isLeft shouldBe true
  }

  "The arithmetic" should "hold every fact of the chain's Peano that names no real" in {
    val chainFacts = Chain.standard.peano.facts
    val pure = chainFacts.filterNot { case (_, theorem) => touchesReal(theorem.conclusion) }

    // Counted rather than written: the split is 74 against 17 on 2026-09-15 and the number is not
    // what is being asserted. What is asserted is that the two sets are the same set of names, so
    // a fact that moves from one side to the other fails this rather than passing quietly.
    facts.keySet shouldBe pure.keySet
    withClue(s"facts below the reals: ${facts.size}\n") {
      facts.size should be >= 70
    }
  }

  it should "prove each of them without a real appearing anywhere in the derivation" in {
    // The stronger reading, and the one that says the closer never reached for the reals. A
    // derivation that spent an axiom of the reals would carry that axiom as a node, and its
    // conclusion names a real, so this catches what `Derivation.axiomsOf` would and more.
    val leaking = facts.toVector.collect {
      case (name, theorem) if walk(theorem).exists(sequentTouchesReal) => name
    }
    leaking shouldBe empty
  }

  it should "be believed on exactly what the naturals are believed on" in {
    // Nothing beyond what the naturals' induction and recursion spend. A ceiling and not an
    // equality: it refuses a fact that starts spending something new, and it lets through one that
    // quietly stops spending one of them, which is the half the equality `CodingSpec` uses covers.
    val expected = Derivation.axiomsOf(force(naturals.fact(Natural.Induction)))
      .union(Derivation.axiomsOf(force(naturals.recursion)))

    facts.values.foreach { theorem =>
      Derivation.axiomsOf(theorem).diff(expected) shouldBe empty
    }
  }

  private def sequentTouchesReal(theorem: Kernel.Thm): Boolean =
    touchesReal(theorem.conclusion) || theorem.hypotheses.exists(touchesReal)

  /** Every node of a proof, reached once, by identity, as `Derivation.walk` does. */
  private def walk(theorem: Kernel.Thm): Vector[Kernel.Thm] = {
    val seen = java.util.Collections.newSetFromMap(
      new java.util.IdentityHashMap[Kernel.Thm, java.lang.Boolean])
    val out = Vector.newBuilder[Kernel.Thm]
    var pending: List[Kernel.Thm] = List(theorem)
    while (pending.nonEmpty) {
      val current = pending.head
      pending = pending.tail
      if (seen.add(current)) {
        out += current
        pending = Derivation.premises(current.derivation) ++ pending
      }
    }
    out.result()
  }
}
