package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Identities of the commutative semiring on `num`, decided here rather than over the reals.
 *
 * `Ring` decides identities of a ring and there was no counterpart for the naturals, so every
 * development over `num` that needed one went through `Modular.identity`, which embeds both sides
 * with `real_of_num`, asks `Ring`, and brings the equation back through injectivity. That is sound
 * and its own docstring argues for it. What it costs is **the sixteen axioms of the reals**,
 * charged to every theorem that reaches it, and on 2026-09-13 twenty-eight of `Modular`'s
 * thirty-eight published lemmas were paying it for arithmetic that is entirely about `num`.
 *
 * The price is not a detail of bookkeeping in this repository. What a conclusion actually rests on
 * is the question `Derivation.axiomsOf` exists to answer and the one the Goedel work in
 * `docs/adr/0013` is **for**: a statement about the incompleteness of arithmetic that rests on the
 * axioms of the real numbers is formally correct and says something false about what was needed.
 *
 * == It is smaller than it sounds, and three readings of the code made it smaller each time ==
 *
 * The first estimate was "a normaliser", the second "the engine is reusable but the order must be
 * redesigned". `Rewrite` is generic and the strategy is now `Rewrite.normaliser`, shared with the
 * reals, so the engine half of that was right.
 *
 * **The order half was wrong, and the way it was wrong is worth the paragraph.** `ringOrder`'s
 * negation-aware part strips `Real.Negation` and nothing else, so on a `num` term it returns the
 * term at depth zero and the comparison degenerates to the structural recursion underneath. That
 * much was measured and is true, and the conclusion drawn from it, that `ringOrder` is therefore
 * reusable here, does not follow and is false.
 *
 * Associativity is an **ordered** rule: `(A + B) + C` becomes `A + (B + C)` only where that makes
 * the term smaller. Under a structural comparison that reduces to whether `A + B` is bigger than
 * `A`, which reduces to comparing the head constants, and `Term.ordering` compares constants by
 * **name**. Over the reals the heads are `*` and `+`, and `*` precedes `+` in ASCII, so a sum
 * counts as bigger than the product at its left and the rule fires. Over `num` the heads are
 * `NUM_ADD` and `NUM_MUL`, and `NUM_ADD` precedes `NUM_MUL`, so the comparison comes out the other
 * way and **associativity stops firing wherever the left summand is a product**.
 *
 * Nothing about that is visible in either order's definition. What it produces is not a wrong
 * theorem but a refusal: two sums with the same monomials reach two different left-nested normal
 * forms and `Rewrite.proveEquation` reports that they are not equal. The measurement that found it
 * was printing both normal forms after one call refused, and the first version of this file
 * asserted the opposite of it in a docstring.
 *
 * [[Semiring.order]] is what replaces it: **size first, at every level of the recursion**, then the
 * same structural comparison. Under it `A + B` is bigger than `A` because it has more nodes,
 * whatever the constants are called, which is the property associativity needs and the only one it
 * needs. The size test has to be inside the recursion rather than wrapped around it: `(A + B) + C`
 * and `A + (B + C)` have the **same** total size, and what separates them is the size of the two
 * function parts one level down.
 *
 * So what was new was a table of rules and an order, and eleven of the fourteen rules were already
 * proved in `Peano`. Since 2026-09-25 both are `CommutativeRing`'s, of which this is the `num`
 * instance, and the three rules `Peano` did not hold are derived there from its laws.
 *
 * == The fragment, stated so a caller knows when to expect a refusal ==
 *
 * Decided: terms built from `NUM_ADD`, `NUM_MUL`, `ZERO`, `SUC ZERO` and the numerals, over
 * anything else as atoms. A numeral is opened by [[Peano.NumeralOneIsSuccessorOfZero]] and the two
 * bit lemmas, so `2` becomes `SUC ZERO + SUC ZERO` and `x * 2` normalises to `x + x`.
 *
 * **`SUC t` for anything but `ZERO` is an atom**, deliberately and not yet. Opening it would mean
 * rewriting `SUC t` to `t + SUC ZERO`, which turns every successor in the goal into a sum and makes
 * a statement about `SUC (SUC (SUC ZERO))` into a term with three sums in it; `Successor` already
 * exists for callers who want that, aimed rather than turned loose, and its own docstring gives the
 * reason. The consequence to know is that `NUM_MUL (SUC x) y = NUM_ADD (NUM_MUL x y) y` is **not**
 * decided here, though it is `Peano.SuccessorTimes` and is one specialisation away.
 *
 * `NUM_SUB`, `PRE`, `NUM_DIV`, `NUM_MOD` and `NUM_GCD` are atoms, which is the same treatment
 * `Modular.identity` gives them and for the same reason: a truncated difference is not the
 * difference of a ring, and no rule here pretends otherwise. An identity that is true only because
 * a subtraction truncates is outside this fragment and is refused rather than decided.
 */
final class Semiring private (
  val peano: NaturalArithmetic,
  val normalisation: Rewrite.Conversion
) {

  /** `|- left = right` for an identity of the semiring, or a refusal naming what stopped. */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    Rewrite.proveEquation(peano.logic, normalisation, goal)

  /** The same, for an equation written in the development's notation. */
  def prove(text: String): Either[LogicError, Kernel.Thm] =
    peano.proposition(text).flatMap(prove)

  /** The same, for two terms rather than an equation. */
  def prove(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    LogicError.lift(Term.eq(left, right)).flatMap(prove)

  /** The normal form of a term, as a theorem saying the two are equal. */
  def normalise(term: Term): Either[LogicError, Kernel.Thm] = normalisation(term)
}

object Semiring {

  /**
   * The order the sorting rules use: more nodes is bigger, and ties go to the structure.
   *
   * It is `CommutativeRing.order` with no negation, which is what it was generalised into on
   * 2026-09-25 and why that order compares by size inside the recursion. Why not
   * `Arithmetic.ringOrder`, which is the order the reals sort with and which is inert on `num`
   * terms: see the class comment. In one line, it compares head constants by name and `NUM_ADD`
   * precedes `NUM_MUL`, so associativity refuses to flatten `(a * p + b * q) + a * q` and two equal
   * sums reach two different normal forms.
   */
  val order: Ordering[Term] = CommutativeRing.order(None)

  /**
   * `|- !x y z. NUM_MUL (NUM_ADD x y) z = NUM_ADD (NUM_MUL x z) (NUM_MUL y z)`
   *
   * `Peano.Distributive` distributes over the **right** factor and the rewriting needs both. Not in
   * `Peano` because nothing there needed it; derived by `CommutativeRing` in three commutations.
   */
  val RightDistributive: String = "NUM_DISTRIBUTE_RIGHT"

  /** `|- !x. NUM_MUL (SUC 0) x = x`, the unit on the left, which `Peano.TimesOne` has on the right. */
  val OneTimes: String = "NUM_ONE_MUL"

  /**
   * `|- !x y z. NUM_MUL x (NUM_MUL y z) = NUM_MUL y (NUM_MUL x z)`
   *
   * The multiplicative twin of `Peano.AddExchange`, and what lets the sorting move a factor past
   * its neighbour without re-associating the whole product first.
   */
  val MulExchange: String = "NUM_MUL_EXCHANGE"

  /** The three `Peano` does not hold and the generic builder derives, as text. */
  val Statements: Vector[(String, String)] = Vector(
    RightDistributive ->
      "!x:num y:num z:num. NUM_MUL (NUM_ADD x y) z = NUM_ADD (NUM_MUL x z) (NUM_MUL y z)",
    OneTimes -> "!x:num. NUM_MUL (SUC ZERO) x = x",
    MulExchange ->
      "!x:num y:num z:num. NUM_MUL x (NUM_MUL y z) = NUM_MUL y (NUM_MUL x z)"
  )

  /**
   * Build it over an arithmetic on the naturals, as the `num` instance of `CommutativeRing`.
   *
   * The laws are `Peano`'s, and so are three of the derived rules, passed as supplied so that the
   * rules hold the theorems `Peano` publishes: its exchange and its two zeros on the left. The rest
   * is derived there. What is `num`'s alone is the extra rules: the numerals opened into successor
   * sums, and a successor opened **under a product** and only there. `x * SUC y` becomes `x * y + x`,
   * which strictly reduces the successor depth beneath a `*` and so leaves the termination argument
   * alone; added on 2026-09-13 when the conversion of `Modular` was measured, where of eighty
   * identities that development decides through the reals seventy-four were already in this
   * fragment and the six that were not were all this one shape. `SUC t` stays an atom
   * **additively**, which is the line the class comment draws.
   */
  def construct(peano: NaturalArithmetic): Either[LogicError, Semiring] = {
    val numbers = TyApp(Natural.TypeName, Nil)
    val binary = Type.fun(numbers, Type.fun(numbers, numbers))
    for {
      add <- LogicError.lift(peano.theory.constant(Peano.Addition, binary))
      multiply <- LogicError.lift(peano.theory.constant(Peano.Multiplication, binary))
      zero <- LogicError.lift(peano.theory.constant(Natural.NumberZero, numbers))
      successor <- LogicError.lift(peano.theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers)))
      one <- LogicError.lift(Term.app(successor, zero))
      laws <- for {
        addAssociative <- peano.fact(Peano.AddAssociative)
        addCommutative <- peano.fact(Peano.AddCommutative)
        addZero <- peano.fact(Peano.AddAtZero)
        multiplyAssociative <- peano.fact(Peano.MulAssociative)
        multiplyCommutative <- peano.fact(Peano.MulCommutative)
        multiplyOne <- peano.fact(Peano.TimesOne)
        distributive <- peano.fact(Peano.Distributive)
        multiplyZero <- peano.fact(Peano.MulAtZero)
      } yield CommutativeRing.Laws(
        addAssociative, addCommutative, addZero, multiplyAssociative, multiplyCommutative,
        multiplyOne, distributive, Some(multiplyZero), None
      )
      supplied <- for {
        exchange <- peano.fact(Peano.AddExchange)
        zeroPlus <- peano.fact(Peano.ZeroPlus)
        zeroTimes <- peano.fact(Peano.ZeroTimes)
      } yield Map(
        CommutativeRing.AddExchange -> exchange,
        CommutativeRing.ZeroPlus -> zeroPlus,
        CommutativeRing.ZeroTimes -> zeroTimes
      )
      extra <- Vector(
        Peano.NumeralOneIsSuccessorOfZero,
        Peano.NumeralBit0Doubles,
        Peano.NumeralBit1Doubles,
        Peano.MulAtSuccessor,
        Peano.SuccessorTimes
      ).foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty))((acc, name) =>
        acc.flatMap(found => peano.fact(name).map(found :+ _)))
      built <- CommutativeRing.semiring(
        peano.logic,
        CommutativeRing.Operations(numbers, add, multiply, zero, one, None),
        laws,
        extra,
        supplied
      )
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { case (acc, (name, text)) =>
        val generic = name match {
          case RightDistributive => CommutativeRing.RightDistributive
          case OneTimes => CommutativeRing.OneTimes
          case _ => CommutativeRing.MultiplyExchange
        }
        for {
          _ <- acc
          expected <- Parser.proposition(peano.theory, peano.notation, text)
          theorem <- built.fact(generic)
          _ <-
            if (theorem.conclusion == expected && theorem.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"the statement published for $name", theorem.conclusion))
        } yield ()
      }
    } yield new Semiring(peano, built.normalisation)
  }
}
