package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * FRACTRAN's semantics, read from outside the development that states it: the verification of card
 * `f1c1bb41`.
 *
 * `FractranSpec` certifies the traces `Fractran.trace` proposes, so its PRIMEGAME run agrees with the
 * kernel and with the interpreter at once, and both come from one file. Here the trace is the one
 * OEIS A007542 lists, reproduced on 2026-09-27 by an evaluation over exact rationals written apart
 * from this repository, and it is handed to the kernel without the interpreter proposing it.
 *
 * And "first" is asserted as a theorem rather than as a refusal. A refusal cannot say whose it was,
 * which is what `tools/verify/perturb-fractran.sh` exists for; `|- ~FRACTRAN_STEP P 6 9` is the
 * definition itself saying that the second applicable fraction is not a step, derived from the
 * certified step and `FRACTRAN_STEP_FUNCTIONAL` with no Scala walk deciding anything.
 */
class FractranSemanticsSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private lazy val fractran = force(Fractran.construct(chain))
  private lazy val digits = force(Value.construct(chain)).digits
  private def rules: Rules = fractran.logic.rules

  private def fractions(pairs: (Int, Int)*): Vector[(BigInt, BigInt)] =
    pairs.toVector.map { case (p, q) => BigInt(p) -> BigInt(q) }
  private def states(values: Int*): Vector[BigInt] = values.toVector.map(BigInt(_))
  private def claim(text: String): Term = force(fractran.proposition(text))

  private def text(program: Vector[(BigInt, BigInt)]): String =
    program.foldRight("(WORD_EMPTY:word(prod(num,num)))") { case ((p, q), rest) =>
      s"(LIST_CONS (PAIR ($p:num) ($q:num)) $rest)"
    }

  private val ThreeAxioms = Set(
    force(chain.classical.axiom(Classical.Choice)).conclusion,
    force(chain.classical.axiom(Classical.Eta)).conclusion,
    force(chain.naturals.axiom(Natural.Infinity)).conclusion
  )

  /** At `6` both fractions apply and `5/3` is first; at `4` only `3/2` does; at `7` neither. */
  private val Both = fractions(5 -> 3, 3 -> 2)

  /** OEIS A007542, a(0) to a(19): PRIMEGAME from `2` to the first power of two after it. */
  private val PrimeGameFromTwo = states(
    2, 15, 825, 725, 1925, 2275, 425, 390, 330, 290, 770, 910, 170, 156, 132, 116, 308, 364, 68, 4
  )

  "PRIMEGAME's trajectory as OEIS lists it" should "be certified without the interpreter proposing it" in {
    val run = force(fractran.certifyTrace(Fractran.PrimeGame, PrimeGameFromTwo))
    run.hypotheses shouldBe empty
    run.conclusion shouldBe claim(s"FRACTRAN_REACHES ${text(Fractran.PrimeGame)} 2 19 4")
    Derivation.axiomsOf(run) shouldBe ThreeAxioms
  }

  it should "be refused with one state altered, and with one state left out" in {
    fractran.certifyTrace(Fractran.PrimeGame, PrimeGameFromTwo.updated(2, BigInt(826))).isLeft shouldBe true
    fractran.certifyTrace(Fractran.PrimeGame, PrimeGameFromTwo.patch(2, Nil, 1)).isLeft shouldBe true
  }

  it should "be what the interpreter proposes too, so the two readings are the same run" in {
    Fractran.trace(Fractran.PrimeGame, 2, 19) shouldBe PrimeGameFromTwo
  }

  "The step" should "exclude, as a theorem, the second fraction where the first applies" in {
    val program = force(fractran.program(Both))
    val six = force(digits.numeral(6))
    val nine = force(digits.numeral(9))
    val ten = force(digits.numeral(10))

    val stepped = force(fractran.step(Both, 6))
    stepped.conclusion shouldBe claim(s"FRACTRAN_STEP ${text(Both)} 6 10")

    val wrong = claim(s"FRACTRAN_STEP ${text(Both)} 6 9")
    val assumed = force(LogicError.lift(Kernel.assume(wrong)))
    val functional = force(fractran.fact(Fractran.StepFunctional))
    val same = force(
      rules.specAll(functional, List(program, six, nine, ten))
        .flatMap(instance => rules.conjIntro(assumed, stepped).flatMap(rules.mp(instance, _)))
    )
    val below = force(digits.below(9, 10))
    val tenBelowTen = force(Limit.rewriteInProposition(same, below))
    val irreflexive = force(chain.peano.fact("NUM_LT_IRREFL").flatMap(rules.specAll(_, List(ten))))
    val refused = force(rules.notElim(irreflexive, tenBelowTen).flatMap(rules.notIntro(wrong, _)))

    refused.hypotheses shouldBe empty
    refused.conclusion shouldBe claim(s"~FRACTRAN_STEP ${text(Both)} 6 9")
    Derivation.axiomsOf(refused) shouldBe ThreeAxioms
  }

  it should "pass over a fraction that does not apply and take the next one" in {
    force(fractran.step(Both, 4)).conclusion shouldBe claim(s"FRACTRAN_STEP ${text(Both)} 4 6")
    fractran.halts(Both, 4).isLeft shouldBe true
  }

  "Halting" should "be proved where no fraction applies and refused where any does" in {
    val halted = force(fractran.halts(Both, 7))
    halted.hypotheses shouldBe empty
    halted.conclusion shouldBe claim(s"FRACTRAN_HALTS ${text(Both)} 7")
    fractran.halts(Both, 6).isLeft shouldBe true
    fractran.step(Both, 7).isLeft shouldBe true
  }

  /** `3/2` from `2^4 * 3^2 = 144` to `3^6 = 729`, the states from the same rational evaluation. */
  "The adder" should "take 2^a 3^b to 3^(a+b) and halt there" in {
    val adder = fractions(3 -> 2)
    val run = force(fractran.certifyTrace(adder, states(144, 216, 324, 486, 729)))
    run.conclusion shouldBe claim(s"FRACTRAN_REACHES ${text(adder)} 144 4 729")
    val halted = force(fractran.halts(adder, 729))
    halted.conclusion shouldBe claim(s"FRACTRAN_HALTS ${text(adder)} 729")
    (Derivation.axiomsOf(run) ++ Derivation.axiomsOf(halted)) shouldBe ThreeAxioms
  }
}
