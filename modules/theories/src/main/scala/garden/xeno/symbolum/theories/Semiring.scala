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
 * So what is actually new is a table of rules and an order, and eleven of the fourteen rules were
 * already proved in `Peano`.
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
  val peano: Peano,
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
   * Why not `Arithmetic.ringOrder`, which is the order the reals sort with and which is inert on
   * `num` terms: see the class comment. In one line, it compares head constants by name and
   * `NUM_ADD` precedes `NUM_MUL`, so associativity refuses to flatten `(a * p + b * q) + a * q` and
   * two equal sums reach two different normal forms.
   *
   * Any total order makes the sorting terminate and canonical, which is `ringOrder`'s own docstring
   * and is as true here; what an order is chosen **for** is what it puts where. This one is chosen
   * so that a sum always outranks either of its summands, which is exactly the direction
   * associativity has to travel.
   */
  val order: Ordering[Term] = new Ordering[Term] {

    def compare(left: Term, right: Term): Int = {
      val bySize = size(left).compare(size(right))
      if (bySize != 0) bySize else structurally(left, right)
    }

    /**
     * The same comparison one level down, and the reason the size test is not simply wrapped
     * around a structural order: `(A + B) + C` and `A + (B + C)` hold the same nodes, so size says
     * nothing about them at the top and everything about their function parts.
     */
    private def structurally(left: Term, right: Term): Int = (left, right) match {
      case (App(leftFn, leftArgument), App(rightFn, rightArgument)) =>
        val byFunction = compare(leftFn, rightFn)
        if (byFunction != 0) byFunction else compare(leftArgument, rightArgument)

      case (Abs(leftType, leftBody), Abs(rightType, rightBody)) =>
        val byBinder = Type.ordering.compare(leftType, rightType)
        if (byBinder != 0) byBinder else compare(leftBody, rightBody)

      case _ => Term.ordering.compare(left, right)
    }

    private def size(term: Term): Int = term match {
      case App(fn, argument) => size(fn) + size(argument)
      case Abs(_, body) => 1 + size(body)
      case _ => 1
    }
  }

  /**
   * `|- !x y z. NUM_MUL (NUM_ADD x y) z = NUM_ADD (NUM_MUL x z) (NUM_MUL y z)`
   *
   * `Peano.Distributive` distributes over the **right** factor and the rewriting needs both. Not in
   * `Peano` because nothing there needed it; derived here in three commutations.
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

  /** The three this file proves before it can build its own rule set, as text. */
  val Statements: Vector[(String, String)] = Vector(
    RightDistributive ->
      "!x:num y:num z:num. NUM_MUL (NUM_ADD x y) z = NUM_ADD (NUM_MUL x z) (NUM_MUL y z)",
    OneTimes -> "!x:num. NUM_MUL (SUC ZERO) x = x",
    MulExchange ->
      "!x:num y:num z:num. NUM_MUL x (NUM_MUL y z) = NUM_MUL y (NUM_MUL x z)"
  )

  /** Build it over an arithmetic on the naturals. */
  def construct(peano: Peano): Either[LogicError, Semiring] =
    for {
      derived <- missingLemmas(peano)
      conversion <- conversionFrom(peano, derived)
    } yield new Semiring(peano, conversion)

  /**
   * The three rules `Peano` does not hold, derived by hand rather than by bootstrapping.
   *
   * `Arithmetic` proves its own auxiliaries with a partial normalisation and then rebuilds, which
   * is elegant and is not used here: each of these is three or four specialisations of lemmas that
   * are already proved, and a hand derivation that either works or names the step it failed at is
   * worth more than a bootstrap whose failure is a normal form that did not close.
   */
  private def missingLemmas(peano: Peano): Either[LogicError, Map[String, Kernel.Thm]] = {
    val logic = peano.logic
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val x = Term.variable("x", numbers)
    val y = Term.variable("y", numbers)
    val z = Term.variable("z", numbers)

    for {
      commutative <- peano.fact(Peano.MulCommutative)
      associative <- peano.fact(Peano.MulAssociative)
      distributive <- peano.fact(Peano.Distributive)
      successorTimes <- peano.fact(Peano.SuccessorTimes)
      zeroTimes <- peano.fact(Peano.ZeroTimes)
      zeroPlus <- peano.fact(Peano.ZeroPlus)
      times <- LogicError.lift(
        peano.theory.constant(Peano.Multiplication, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      plus <- LogicError.lift(
        peano.theory.constant(Peano.Addition, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      zero <- LogicError.lift(peano.theory.constant(Natural.NumberZero, numbers))

      // `(x + y) * z = z * (x + y) = z * x + z * y = x * z + y * z`.
      rightDistributive <- for {
        sum <- LogicError.lift(Term.appAll(plus, List(x, y)))
        swapped <- rules.specAll(commutative, List(sum, z))
        opened <- rules.specAll(distributive, List(z, x, y))
        chained <- Conv.trans(swapped, opened)
        leftFactor <- rules.specAll(commutative, List(z, x))
        rightFactor <- rules.specAll(commutative, List(z, y))
        bothSides <- Conv.apTerm(plus, leftFactor).flatMap(step => LogicError.lift(Kernel.mkComb(step, rightFactor)))
        whole <- Conv.trans(chained, bothSides)
        general <- rules.genAll(whole, List(x, y, z))
      } yield general

      // `SUC 0 * x = 0 * x + x = 0 + x = x`.
      oneTimes <- for {
        stepped <- rules.specAll(successorTimes, List(zero, x))
        vanishes <- rules.spec(x, zeroTimes)
        onTheLeft <- Conv.apTerm(plus, vanishes).flatMap(step => LogicError.lift(Kernel.mkComb(step, Conv.refl(x))))
        collapsed <- Conv.trans(stepped, onTheLeft)
        unit <- rules.spec(x, zeroPlus)
        whole <- Conv.trans(collapsed, unit)
        general <- rules.gen(x, whole)
      } yield general

      // `x * (y * z) = (x * y) * z = (y * x) * z = y * (x * z)`.
      mulExchange <- for {
        regrouped <- rules.specAll(associative, List(x, y, z)).flatMap(Conv.sym)
        swapped <- rules.specAll(commutative, List(x, y))
        onTheLeft <- Conv.apTerm(times, swapped).flatMap(Conv.apThm(_, z))
        chained <- Conv.trans(regrouped, onTheLeft)
        opened <- rules.specAll(associative, List(y, x, z))
        whole <- Conv.trans(chained, opened)
        general <- rules.genAll(whole, List(x, y, z))
      } yield general

      derived = Map(
        RightDistributive -> rightDistributive,
        OneTimes -> oneTimes,
        MulExchange -> mulExchange
      )
      checked <- Statements.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(derived)) {
        case (acc, (name, text)) =>
          for {
            found <- acc
            expected <- Parser.proposition(peano.theory, peano.notation, text)
            theorem <- found.get(name).toRight(MissingDefinition(name))
            _ <-
              if (theorem.conclusion == expected && theorem.hypotheses.isEmpty) Right(())
              else Left(NotOfForm(s"the statement published for $name", theorem.conclusion))
          } yield found
      }
    } yield checked
  }

  /**
   * The rule set, split the way `Rewrite.normaliser` wants it.
   *
   * Unconditional: open a numeral, distribute a product over a sum, and remove a unit or a zero.
   * Every one of these makes the term smaller in a measure that does not depend on the order.
   *
   * Ordered: the six associativity, commutativity and exchange rules, which fire only where they
   * decrease `Arithmetic.ringOrder` and would otherwise apply to their own output forever.
   */
  private def conversionFrom(
    peano: Peano,
    derived: Map[String, Kernel.Thm]
  ): Either[LogicError, Rewrite.Conversion] = {
    def named(names: Vector[String]): Either[LogicError, Vector[Kernel.Thm]] =
      names.foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (acc, name) =>
        for {
          found <- acc
          theorem <- derived.get(name).map(Right(_)).getOrElse(peano.fact(name))
        } yield found :+ theorem
      }

    for {
      unconditionalFacts <- named(
        Vector(
          Peano.NumeralOneIsSuccessorOfZero,
          Peano.NumeralBit0Doubles,
          Peano.NumeralBit1Doubles,
          Peano.Distributive,
          RightDistributive,
          // A successor **under a product** is opened, and only there. `x * SUC y` becomes
          // `x * y + x`, which strictly reduces the successor depth beneath a `*` and so leaves the
          // termination argument alone. Added on 2026-09-13 when the conversion of `Modular` was
          // measured: of eighty identities that development decides through the reals, seventy-four
          // were already in this fragment and the six that were not were all this one shape.
          //
          // `SUC t` stays an atom **additively**, which is the line the class comment draws and
          // still draws: nothing here turns `SUC (SUC ZERO)` into a sum, and a claim about a
          // written bound is still `Successor`'s business.
          Peano.MulAtSuccessor,
          Peano.SuccessorTimes,
          Peano.TimesOne,
          OneTimes,
          Peano.MulAtZero,
          Peano.ZeroTimes,
          Peano.AddAtZero,
          Peano.ZeroPlus
        )
      )
      orderedFacts <- named(
        Vector(
          Peano.AddAssociative,
          Peano.AddCommutative,
          Peano.AddExchange,
          Peano.MulAssociative,
          Peano.MulCommutative,
          MulExchange
        )
      )
      unconditional <- Rewrite.Rule.all(peano.logic, unconditionalFacts)
      ordered <- Rewrite.Rule.all(peano.logic, orderedFacts)
    } yield Rewrite.normaliser(unconditional, ordered, order)
  }
}
