package garden.xeno.symbolum.theories

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * FRACTRAN read as a register machine, `FRACTRAN_STEP_REGISTERS`.
 *
 * `FractranSpec` already compares every published statement with its text. What is asserted here is
 * what it cannot see: that the simulation turns a step the kernel certified on numbers into a step
 * on registers with nothing left assumed; and that each of its two hypotheses is there because the
 * equation is false without it, refuted in the kernel at a program and a state where the other one
 * holds. A theorem proved with a hypothesis it did not need would pass every other test here.
 */
class FractranRegistersSpec extends AnyFlatSpec with Matchers {

  private def force[T](result: Either[LogicError, T]): T =
    result.fold(error => fail(s"unexpected refusal: ${error.message}"), identity)

  private val chain = Chain.standard
  private lazy val fractran = force(Fractran.construct(chain))
  private lazy val digits = force(Value.construct(chain)).digits
  private lazy val logic = fractran.logic
  private lazy val rules = logic.rules
  private lazy val library = Library.of(chain)

  private def lemma(name: String): Kernel.Thm =
    library.entries.find(_.name == name).map(_.theorem).getOrElse(fail(s"no lemma $name"))
  private def fact(name: String): Kernel.Thm = force(fractran.fact(name))
  private def fractions(pairs: (Int, Int)*): Vector[(BigInt, BigInt)] =
    pairs.toVector.map { case (p, q) => BigInt(p) -> BigInt(q) }
  private def numeral(n: Int): Term = force(digits.numeral(BigInt(n)))

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Pairs: Type = TyApp(Product.TypeName, List(Num, Num))

  private def normal(thm: Kernel.Thm): Kernel.Thm =
    force(Conv.betaNormalise(thm.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, thm))))

  private def at(theorem: Kernel.Thm, values: Type): Kernel.Thm =
    Kernel.instType(Map(Classical.TypeVariable -> Pairs, Classical.CodomainVariable -> values), theorem)

  /** `FRACTRAN_REGISTER_STEP [p/q] n m` unfolded one fraction: `COND test lands (LIST_FOLD g F [])`. */
  private def unfoldedOnce(program: Term, n: Term, m: Term): (Kernel.Thm, Term, Term, Term) = {
    val definition = force(fractran.definition(Fractran.RegisterStepName))
    val unfolded = force(Conv.unfold(definition, List(program, n, m)))
    val (g, start, head, tail) = force(Limit.rightOf(unfolded)) match {
      case App(App(App(_, g), start), App(App(_, head), tail)) => (g, start, head, tail)
      case other => fail(s"not a fold over a cons: $other")
    }
    val cons = normal(force(rules.specAll(at(lemma("LIST_FOLD_CONS"), Type.Bool), List(g, start, head, tail))))
    val opened = force(Conv.trans(unfolded, cons))
    force(Limit.rightOf(opened)) match {
      case App(App(App(_, test), lands), rest) => (opened, test, lands, rest)
      case other => fail(s"not a conditional: $other")
    }
  }

  /**
   * `~FRACTRAN_REGISTER_STEP [p/q] n 0`, whatever the fraction: the register machine never lands on
   * nought, because landing says `0 < m`, and past the one fraction there is nothing.
   */
  private def neverNought(program: Term, n: Term): Kernel.Thm = {
    val zero = numeral(0)
    val (opened, test, lands, rest) = unfoldedOnce(program, n, zero)
    val stepTerm = Term.destEq(opened.conclusion).map(_._1).getOrElse(fail("no equation"))
    val condTrue = Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), lemma(Classical.CondTrue))
    val condFalse = Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), lemma(Classical.CondFalse))
    val irreflexive = force(rules.spec(zero, lemma("NUM_LT_IRREFL")))
    val assumed = force(LogicError.lift(Kernel.assume(stepTerm)))
    val asCond = force(LogicError.lift(Kernel.eqMp(opened, assumed)))
    val middle = force(rules.spec(test, lemma("EXCLUDED_MIDDLE")))
    val whenHolds = {
      val h = force(LogicError.lift(Kernel.assume(test)))
      val chosen = force(rules.specAll(condTrue, List(test, lands, rest)).flatMap(rules.mp(_, h)))
      val landed = force(LogicError.lift(Kernel.eqMp(chosen, asCond)))
      force(rules.conjElim1(landed).flatMap(rules.notElim(irreflexive, _)))
    }
    val whenFails = {
      val h = force(LogicError.lift(Kernel.assume(force(logic.mkNot(test)))))
      val chosen = force(rules.specAll(condFalse, List(test, lands, rest)).flatMap(rules.mp(_, h)))
      val passed = force(LogicError.lift(Kernel.eqMp(chosen, asCond)))
      val emptyFold = rest match {
        case App(App(App(_, g), start), _) =>
          force(rules.specAll(at(lemma("LIST_FOLD_EMPTY"), Type.Bool), List(g, start)))
        case other => fail(s"not a fold: $other")
      }
      force(LogicError.lift(Kernel.eqMp(emptyFold, passed)))
    }
    force(rules.disjElim(middle, whenHolds, whenFails).flatMap(rules.notIntro(stepTerm, _)))
  }

  /** The simulation's equation at a program and two states, refuted by a certified step to nought. */
  private def refutedAt(pairs: Vector[(BigInt, BigInt)], n: Int): Kernel.Thm = {
    val program = force(fractran.program(pairs))
    val stepped = force(fractran.step(pairs, BigInt(n)))
    val registerStep = Term.destEq(unfoldedOnce(program, numeral(n), numeral(0))._1.conclusion).map(_._1).getOrElse(fail("no equation"))
    val claimText = force(LogicError.lift(Term.eq(stepped.conclusion, registerStep)))
    val assumed = force(LogicError.lift(Kernel.assume(claimText)))
    val registers = force(LogicError.lift(Kernel.eqMp(assumed, stepped)))
    force(rules.notElim(neverNought(program, numeral(n)), registers).flatMap(rules.notIntro(claimText, _)))
  }

  /**
   * `3/2` at `72 = 2^3 * 3^2`: the kernel certifies the step to `108` on numbers, and the
   * simulation turns it into a step on registers with nothing assumed. The two hypotheses are
   * discharged here, positivity of the state by the digits and of the numerator by the fold. What
   * comes out is read down to the sentence the peer card could not state: at every prime, the
   * register of `108` plus that of `2` is the register of `72` plus that of `3`.
   */
  "The simulation" should "turn a certified step on numbers into a step on registers" in {
    val pairs = fractions(3 -> 2)
    val program = force(fractran.program(pairs))
    val stepped = force(fractran.step(pairs, BigInt(72)))
    val statePositive = force(digits.below(BigInt(0), BigInt(72)))
    val every = force(fractran.term("\\f:prod(num,num). \\r:bool. NUM_LT 0 (FST f) /\\ r", Type.fun(Pairs, Type.fun(Type.Bool, Type.Bool))))
    val truth = force(fractran.term("T", Type.Bool))
    val (head, tail) = program match {
      case App(App(_, head), tail) => (head, tail)
      case other => fail(s"not a cons: $other")
    }
    val cons = normal(force(rules.specAll(at(lemma("LIST_FOLD_CONS"), Type.Bool), List(every, truth, head, tail))))
    val atEmpty = force(rules.specAll(at(lemma("LIST_FOLD_EMPTY"), Type.Bool), List(every, truth)))
    val first = force(rules.specAll(
      Kernel.instType(Map(Classical.TypeVariable -> Num, Classical.CodomainVariable -> Num), lemma("FST_PAIR")),
      List(numeral(3), numeral(2))))
    val below = force(fractran.term("\\x:num. NUM_LT 0 x", Type.fun(Num, Type.Bool)))
    val numeratorPositive = force(
      Conv.apTerm(below, force(Conv.sym(first))).flatMap(Conv.betaSides)
        .flatMap(e => LogicError.lift(Kernel.eqMp(e, force(digits.below(BigInt(0), BigInt(3)))))))
    val truthHolds = force(rules.truth)
    val restHolds = force(Conv.sym(atEmpty).flatMap(e => LogicError.lift(Kernel.eqMp(e, truthHolds))))
    val positives = force(rules.conjIntro(numeratorPositive, restHolds)
      .flatMap(both => Conv.sym(cons).flatMap(e => LogicError.lift(Kernel.eqMp(e, both)))))

    val simulation = force(rules.specAll(fact(Fractran.StepRegisters), List(program, numeral(72), numeral(108)))
      .flatMap(rules.mp(_, statePositive)).flatMap(rules.mp(_, positives)))
    val onRegisters = force(LogicError.lift(Kernel.eqMp(simulation, stepped)))
    onRegisters.hypotheses shouldBe empty
    onRegisters.conclusion shouldBe force(fractran.proposition(
      "FRACTRAN_REGISTER_STEP (LIST_CONS (PAIR (3:num) (2:num)) (WORD_EMPTY:word(prod(num,num)))) 72 108"))

    // Read it down: the fraction's test cannot fail, since past it the fold is F, so it lands.
    val (opened, test, lands, rest) = unfoldedOnce(program, numeral(72), numeral(108))
    val asCond = force(LogicError.lift(Kernel.eqMp(opened, onRegisters)))
    val condTrue = Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), lemma(Classical.CondTrue))
    val condFalse = Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), lemma(Classical.CondFalse))
    val middle = force(rules.spec(test, lemma("EXCLUDED_MIDDLE")))
    val whenHolds = {
      val h = force(LogicError.lift(Kernel.assume(test)))
      val chosen = force(rules.specAll(condTrue, List(test, lands, rest)).flatMap(rules.mp(_, h)))
      force(LogicError.lift(Kernel.eqMp(chosen, asCond)))
    }
    val whenFails = {
      val h = force(LogicError.lift(Kernel.assume(force(logic.mkNot(test)))))
      val chosen = force(rules.specAll(condFalse, List(test, lands, rest)).flatMap(rules.mp(_, h)))
      val passed = force(LogicError.lift(Kernel.eqMp(chosen, asCond)))
      val emptyFold = rest match {
        case App(App(App(_, g), start), _) =>
          force(rules.specAll(at(lemma("LIST_FOLD_EMPTY"), Type.Bool), List(g, start)))
        case other => fail(s"not a fold: $other")
      }
      force(LogicError.lift(Kernel.eqMp(emptyFold, passed)).flatMap(rules.falsityElim(lands, _)))
    }
    val landed = force(rules.disjElim(middle, whenHolds, whenFails))
    val registers = normal(force(rules.conjElim2(landed)))
    registers.hypotheses shouldBe empty
    registers.conclusion shouldBe force(fractran.proposition(
      "!p:num. NUM_PRIME p ==> NUM_VALUATION p 108 + NUM_VALUATION p (SND (PAIR (3:num) (2:num))) = " +
        "NUM_VALUATION p 72 + NUM_VALUATION p (FST (PAIR (3:num) (2:num)))"))
  }

  it should "need a positive state: at nought, 1/1 steps to nought and the registers cannot" in {
    val refuted = refutedAt(fractions(1 -> 1), 0)
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe force(fractran.proposition(
      "~(FRACTRAN_STEP (LIST_CONS (PAIR (1:num) (1:num)) (WORD_EMPTY:word(prod(num,num)))) 0 0 = FRACTRAN_REGISTER_STEP (LIST_CONS (PAIR (1:num) (1:num)) (WORD_EMPTY:word(prod(num,num)))) 0 0)"))
  }

  it should "need positive numerators: 0/1 sends one to nought and the registers cannot follow" in {
    val refuted = refutedAt(fractions(0 -> 1), 1)
    refuted.hypotheses shouldBe empty
    refuted.conclusion shouldBe force(fractran.proposition(
      "~(FRACTRAN_STEP (LIST_CONS (PAIR (0:num) (1:num)) (WORD_EMPTY:word(prod(num,num)))) 1 0 = FRACTRAN_REGISTER_STEP (LIST_CONS (PAIR (0:num) (1:num)) (WORD_EMPTY:word(prod(num,num)))) 1 0)"))
  }
}
