package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * FRACTRAN as a relation, and runs of it certified by the kernel.
 *
 * The facts are checked against the text they are published as. What matters more is that the
 * certification runs, and refuses: a definition of a step that nobody computes with reads exactly
 * like a wrong one, and a certifier that has only been seen agreeing could be agreeing with
 * anything. So every run below has a refusal beside it, at the case that separates.
 */
class FractranSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private lazy val fractran = force(Fractran.construct(chain))

  private def fact(name: String): Kernel.Thm = force(fractran.fact(name))
  private def fractions(pairs: (Int, Int)*): Vector[(BigInt, BigInt)] =
    pairs.toVector.map { case (p, q) => BigInt(p) -> BigInt(q) }
  private def states(values: Int*): Vector[BigInt] = values.toVector.map(BigInt(_))

  /** The claim as a person would write it, with the program spelled out and typed where it must be. */
  private def claim(text: String): Term = force(fractran.proposition(text))

  private val Addition = fractions(3 -> 2)
  private val AdditionText = "(LIST_CONS (PAIR (3:num) (2:num)) (WORD_EMPTY:word(prod(num,num))))"

  "Every fact of the development" should "prove the statement it is published as" in {
    Fractran.Statements.foreach { case (name, text) =>
      withClue(s"$name: ") {
        fact(name).conclusion shouldBe force(fractran.proposition(text))
        fact(name).hypotheses shouldBe empty
      }
    }
  }

  it should "be listed, so that a fact nobody published cannot hide in the map" in {
    fractran.facts.keySet shouldBe Fractran.Statements.map(_._1).toSet
  }

  /**
   * Choice, infinity and eta, which is what `Folding` rests on and so what any statement about a
   * fold over a list costs; measured on 2026-09-26 as exactly those three, over the facts and over
   * the two certified runs below. `FRACTRAN_REACHES_START` rests on none of them, and that is a
   * reading of `REACH_START` rather than a defect: the empty run needs nothing about lists.
   */
  it should "cost what the lists cost, and add no axiom of its own" in {
    val expected = Set(
      force(chain.classical.axiom(Classical.Choice)).conclusion,
      force(chain.classical.axiom(Classical.Eta)).conclusion,
      force(chain.naturals.axiom(Natural.Infinity)).conclusion
    )
    val spent = (Fractran.Statements.map { case (name, _) => fact(name) } ++ Vector(
      force(fractran.certify(Fractran.PrimeGame, 2, 19)),
      force(fractran.halts(Addition, 243))
    )).map(Derivation.axiomsOf).reduce(_ ++ _)
    spent shouldBe expected
    fractran.theory.axioms shouldBe chain.widest.theory.axioms
  }

  "A run" should "be certified along the trace the interpreter proposes" in {
    Fractran.trace(Addition, 72, 10) shouldBe states(72, 108, 162, 243)
    val run = force(fractran.certify(Addition, 72, 10))
    run.hypotheses shouldBe empty
    run.conclusion shouldBe claim(s"FRACTRAN_REACHES $AdditionText 72 3 243")
  }

  it should "end where the program halts, and a state some fraction applies to is not a halt" in {
    val halted = force(fractran.halts(Addition, 243))
    halted.hypotheses shouldBe empty
    halted.conclusion shouldBe claim(s"FRACTRAN_HALTS $AdditionText 243")
    fractran.halts(Addition, 72).isLeft shouldBe true
  }

  /**
   * Conway's PRIMEGAME from `2` first reaches a power of two again at `4`, after 19 steps, which is
   * where OEIS A007547 puts it. The count is the source's and the kernel's agreement with it is
   * the assertion; `docs/adr/0054` says how the fractions were taken.
   */
  it should "carry PRIMEGAME from 2 to 4 in the nineteen steps the sequence records" in {
    val run = force(fractran.certify(Fractran.PrimeGame, 2, 19))
    run.hypotheses shouldBe empty
    val game = Fractran.PrimeGame.foldRight("(WORD_EMPTY:word(prod(num,num)))") { case ((p, q), rest) =>
      s"(LIST_CONS (PAIR ($p:num) ($q:num)) $rest)"
    }
    run.conclusion shouldBe claim(s"FRACTRAN_REACHES $game 2 19 4")
  }

  /**
   * "First" is the whole of the order, and this is the case that separates it from "some": at `6`
   * both `5/3` and `3/2` apply, and a reading of the step as any applicable fraction would accept
   * `9`. The control beside it is the trace the program does produce, so a certifier that refused
   * everything would fail here rather than pass.
   */
  "The certifier" should "refuse a step through a fraction that is not the first to apply" in {
    val program = fractions(5 -> 3, 3 -> 2)
    fractran.certifyTrace(program, states(6, 9)).isLeft shouldBe true
    force(fractran.certifyTrace(program, states(6, 10))).conclusion shouldBe
      claim("FRACTRAN_REACHES (LIST_CONS (PAIR (5:num) (3:num)) (LIST_CONS (PAIR (3:num) (2:num)) (WORD_EMPTY:word(prod(num,num))))) 6 1 10")
  }

  it should "refuse a trace that keeps going past a halt, and one that starts nowhere" in {
    fractran.certifyTrace(Addition, states(243, 243)).isLeft shouldBe true
    fractran.certifyTrace(Addition, Vector.empty).isLeft shouldBe true
  }

  /**
   * A denominator of zero is outside the language and the definition passes over it, so a
   * program of nothing else halts everywhere and one with a fraction after it reaches that
   * fraction. The second is the control: a definition that treated `1/0` as applying would send
   * `5` somewhere `NUM_DIV` does not determine, and would not produce `15`.
   */
  "A fraction with denominator zero" should "never apply" in {
    force(fractran.halts(fractions(1 -> 0), 5)).conclusion shouldBe
      claim("FRACTRAN_HALTS (LIST_CONS (PAIR (1:num) (0:num)) (WORD_EMPTY:word(prod(num,num)))) 5")
    force(fractran.certifyTrace(fractions(1 -> 0, 3 -> 1), states(5, 15))).hypotheses shouldBe empty
  }

  /**
   * `docs/adr/0054` says a fraction need not be reduced, because `gp/gq` applies exactly where
   * `p/q` does and gives the same value. That is argued there and not proved here; what is
   * asserted is agreement in numbers, on PRIMEGAME with every fraction scaled by six, over the
   * 8102 steps that reach `2^17` (OEIS A007547). Agreement is not a proof of the equivalence.
   */
  "An unreduced program" should "run as its reduced form does, in numbers" in {
    val scaled = Fractran.PrimeGame.map { case (p, q) => (p * 6, q * 6) }
    val reduced = Fractran.trace(Fractran.PrimeGame, 2, 8102)
    Fractran.trace(scaled, 2, 8102) shouldBe reduced
    reduced.last shouldBe BigInt(2).pow(17)
  }
}
