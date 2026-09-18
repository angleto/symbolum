package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Arithmetic on the numerals of `num`, at the two axioms the naturals cost.
 *
 * `Arithmetic` computes with the numerals of the reals and `Ring` decides identities there;
 * `Semiring` decides identities over `num` and there was no counterpart for this half, so until
 * 2026-09-18 **nothing anywhere proved `2 + 3 = 5` about the naturals**. Measured that day, before
 * this file: `Semiring.prove` refuses it, `Modular.identity` refuses it, and `12 * 12 = 144` is a
 * theorem over the reals at eight axioms and is not a theorem at all over `num`.
 *
 * == Why not the route that already works ==
 *
 * `Modular.identity` embeds both sides with `real_of_num`, pushes the embedding through `ZERO`,
 * `SUC`, `NUM_ADD` and `NUM_MUL`, asks `Ring` and brings the answer back through injectivity. It
 * refuses a numeral only because the embedding is not pushed through the **bit encoding**, and
 * `Peano` already publishes the three lemmas that would do it. Adding them was tried and works:
 * `17 = 5 * 3 + 2` comes out at 20097 inferences.
 *
 * It comes out at **sixteen axioms**, which is what the route costs and why this file exists
 * instead. Every characterisation lemma a consumer of numeral arithmetic would spend costs **two**:
 * `NUM_DIV_MOD_UNIQUE`, `NUM_MOD_LT`, `NUM_GCD_DIVIDES_LEFT` and `NUM_BEZOUT` were all measured at
 * two the same day, and `NUM_REAL_INJECTIVE`, the bridge that route goes through, at sixteen. A
 * value for `NUM_DIV 17 5` obtained through the reals would therefore rest on the completeness of
 * the real numbers, which is the defect `Semiring`'s own docstring is an argument against and which
 * `docs/adr/0013` makes the reason the Goedel work cares at all.
 *
 * == The table, and which half of it `Semiring` already decides ==
 *
 * The sixteen lemmas are the reals' sixteen with `NUM_` in front, and the split between them is
 * measured rather than assumed: **nine are decided by `Semiring`** exactly as written, and the
 * other **seven** are the ones where a carry produces a `SUC`. That is the line `Semiring` draws
 * about itself — a successor is an atom additively, and its docstring gives the reason — so the
 * seven are proved here, through [[Digits.throughSuccessor]], which is the only thing in this file
 * that is not a table.
 *
 * == What it does not do ==
 *
 * It computes a sum, a product and a strict comparison of two numerals, and nothing else. There is
 * no subtraction and no defined function: `NUM_SUB` truncates and is not the difference of a ring,
 * and `NUM_DIV` is chosen rather than computed, so both belong to the procedure above this one
 * rather than to the table. What this is for is to be that procedure's arithmetic, and the
 * comparison is in it because `NUM_DIV_MOD_UNIQUE` asks for a sum **and** an order in one breath.
 */
final class Digits private (
  val semiring: Semiring,
  /** Every lemma of the table, by name, as proved when this was built. */
  val lemmas: Map[String, Kernel.Thm],
  private val additionRules: Vector[Rewrite.Rule],
  private val multiplicationRules: Vector[Rewrite.Rule]
) {

  val peano: Peano = semiring.peano

  /** The lemma named, as proved when this was built. */
  def lemma(name: String): Either[LogicError, Kernel.Thm] =
    lemmas.get(name).toRight(MissingDefinition(name))

  /** `|- m + n = m+n`, for numerals of `num`. */
  def add(
    left: BigInt,
    right: BigInt,
    limit: Int = Digits.Limit
  ): Either[LogicError, Kernel.Thm] =
    compute(additionRules, Peano.Addition, left, right, left + right, limit)

  /** `|- m * n = m*n`, for numerals of `num`. */
  def multiply(
    left: BigInt,
    right: BigInt,
    limit: Int = Digits.Limit
  ): Either[LogicError, Kernel.Thm] =
    compute(multiplicationRules, Peano.Multiplication, left, right, left * right, limit)

  /**
   * `|- SUC m = m+1`, for a numeral `m`.
   *
   * The bridge between the two spellings of a number this theory has, and it goes the direction
   * `Successor` does not: `Successor.spell` opens a numeral into successors, so that a recurrence
   * stated at `SUC n` has something to hook, and this closes one successor back into a numeral, so
   * that the arithmetic above carries on in digits. Neither is the other reversed and the cost says
   * so: spelling five is 4887 inferences and produces five successors, where this is a sum.
   */
  def successor(value: BigInt): Either[LogicError, Kernel.Thm] = {
    val rules = peano.logic.rules

    for {
      term <- numeral(value)
      zero <- LogicError.lift(peano.theory.constant(Natural.NumberZero, Digits.Numbers))
      successorOf <- LogicError.lift(
        peano.theory.constant(Natural.NumberSuccessor, Type.fun(Digits.Numbers, Digits.Numbers))
      )
      addition <- LogicError.lift(peano.theory.constant(Peano.Addition, Digits.Binary))
      inFront <- LogicError.lift(Term.app(addition, term))

      oneIsSuccessor <- peano.fact(Peano.NumeralOneIsSuccessorOfZero)
      atSuccessor <- peano.fact(Peano.AddAtSuccessor)
      atZero <- peano.fact(Peano.AddAtZero)

      opened <- Conv.apTerm(inFront, oneIsSuccessor)
      stepped <- rules.specAll(atSuccessor, List(term, zero))
      inside <- rules.spec(term, atZero)
      lifted <- Conv.apTerm(successorOf, inside)
      chained <- Conv.trans(opened, stepped).flatMap(Conv.trans(_, lifted))
      sum <- add(value, 1)
      back <- Conv.sym(chained)
      result <- Conv.trans(back, sum)
    } yield result
  }

  /**
   * `|- m < n`, for numerals, and a refusal naming the pair where the first is not below the second.
   *
   * The order of `num` is `NUM_LE m n = ?d. m + d = n` with `NUM_LT m n = NUM_LE (SUC m) n`, so a
   * strict comparison between two numerals is a **witness** rather than a search: the difference
   * less one is the `d`, and what has to be proved about it is a sum, which is what this file is.
   * Nothing walks from one number to the other, which is the whole difference between this and the
   * successor-by-successor comparisons written by hand in `Collatz`: the cost follows the digits.
   *
   * It is here and not beside the table because it is the second half of what a procedure over a
   * defined constant needs. `NUM_DIV_MOD_UNIQUE` asks for `m = n * q + r` **and** `r < n`, and a
   * caller that had to get the two from two places would be the caller this file exists to spare.
   */
  def below(left: BigInt, right: BigInt): Either[LogicError, Kernel.Thm] = {
    val logic = peano.logic
    val rules = logic.rules

    for {
      leftTerm <- numeral(left)
      rightTerm <- numeral(right)
      _ <-
        if (left < right) Right(())
        else Left(NotOfForm(s"a value below $right, and $left is not one", leftTerm))

      step <- successor(left)
      witness <- numeral(right - left - 1)
      sum <- add(left + 1, right - left - 1)
      addition <- LogicError.lift(peano.theory.constant(Peano.Addition, Digits.Binary))
      congruent <- Conv.apTerm(addition, step).flatMap(Conv.apThm(_, witness))
      obligation <- Conv.trans(congruent, sum)

      successorOf <- LogicError.lift(
        peano.theory.constant(Natural.NumberSuccessor, Type.fun(Digits.Numbers, Digits.Numbers))
      )
      above <- LogicError.lift(Term.app(successorOf, leftTerm))
      atMostDefinition <- peano.definition(Peano.NonStrictOrder)
      unfolded <- Conv.unfold(atMostDefinition, List(above, rightTerm))
      existential <- Digits.rightOf(unfolded)
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, witness, obligation)
      atMost <- Conv.sym(unfolded).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, witnessed)))

      belowDefinition <- peano.definition(Peano.StrictOrder)
      strict <- Conv.unfold(belowDefinition, List(leftTerm, rightTerm))
      result <- Conv.sym(strict).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atMost)))
    } yield result
  }

  /**
   * The numeral for a value, said at `num` out loud.
   *
   * The annotation is `Numeral.of`'s and for its reason one type over: a digit string put to a
   * signature that reads numerals at two types is ambiguous and is refused, and this function's
   * name says which of the two it means.
   */
  def numeral(value: BigInt): Either[LogicError, Term] =
    if (value < 0) Left(TypeError(s"$value is not a numeral of num: these are non-negative"))
    else peano.term(s"$value:${Natural.TypeName}")

  /**
   * The statement built out of the two numerals rather than written and parsed again.
   *
   * Assembled and not spelled, which is what makes the refusal this file's own: a negative value
   * spelled into a text is a `-` the elaborator has to give a type to, and what comes back names
   * two types rather than the value that cannot be a numeral of `num`.
   */
  private def compute(
    rules: Vector[Rewrite.Rule],
    operator: String,
    left: BigInt,
    right: BigInt,
    expected: BigInt,
    limit: Int
  ): Either[LogicError, Kernel.Thm] =
    for {
      leftTerm <- numeral(left)
      rightTerm <- numeral(right)
      answer <- numeral(expected)
      operation <- LogicError.lift(peano.theory.constant(operator, Digits.Binary))
      statement <- LogicError.lift(Term.appAll(operation, List(leftTerm, rightTerm)))
      theorem <- Rewrite.prove(rules, statement, answer, limit)
    } yield theorem
}

object Digits {

  /**
   * Passes of rewriting a numeral computation is allowed.
   *
   * `Arithmetic.NumeralLimit`'s figure, and taking it is a measurement rather than a convenience:
   * the two rule sets are the same algorithm over two encodings, so a pass here should cost what a
   * pass costs there, and it does. Measured on 2026-09-18 by bisecting on the limit, the way that
   * file's own figure was found: a product needs **3** passes at one digit, **14** at two and
   * **40** at six, against 6, 14 and 40 over the reals; a sum needs 3, 7 and 18, against 4, 20 and
   * 40. So the product agrees exactly where both were measured and the sum is cheaper here, which
   * is `ZERO` closing a carry that the reals close with a numeral.
   *
   * The bound is therefore four hundred for that file's reason, which is that it is a guard against
   * a rule set that does not terminate rather than a budget anybody approaches.
   */
  val Limit: Int = Arithmetic.NumeralLimit

  /**
   * Addition on the bits, which is the schoolbook algorithm as nine equations.
   *
   * `Arithmetic.AdditionLemmas` with `NUM_` in front of every constant. The four that carry a `1`
   * carry `NUM_ONE` rather than a digit string, because a digit string is read by the elaborator
   * and `NUM_ONE` is the encoding's own unit: writing `1` here would be a numeral whose type the
   * surrounding equation has to determine, and these equations determine nothing.
   */
  val AdditionLemmas: Vector[(String, String)] = Vector(
    "NUM_ADD_BIT0_BIT0" -> "NUM_BIT0 (x:num) + NUM_BIT0 (y:num) = NUM_BIT0 (x + y)",
    "NUM_ADD_BIT0_BIT1" -> "NUM_BIT0 (x:num) + NUM_BIT1 (y:num) = NUM_BIT1 (x + y)",
    "NUM_ADD_BIT1_BIT0" -> "NUM_BIT1 (x:num) + NUM_BIT0 (y:num) = NUM_BIT1 (x + y)",
    "NUM_ADD_BIT1_BIT1" -> "NUM_BIT1 (x:num) + NUM_BIT1 (y:num) = NUM_BIT0 ((x + y) + NUM_ONE)",
    "NUM_ADD_BIT0_ONE" -> "NUM_BIT0 (x:num) + NUM_ONE = NUM_BIT1 x",
    "NUM_ADD_BIT1_ONE" -> "NUM_BIT1 (x:num) + NUM_ONE = NUM_BIT0 (x + NUM_ONE)",
    "NUM_ADD_ONE_BIT0" -> "NUM_ONE + NUM_BIT0 (y:num) = NUM_BIT1 y",
    "NUM_ADD_ONE_BIT1" -> "NUM_ONE + NUM_BIT1 (y:num) = NUM_BIT0 (y + NUM_ONE)",
    "NUM_ADD_ONE_ONE" -> "NUM_ONE + NUM_ONE = NUM_BIT0 NUM_ONE"
  )

  /** Multiplication, recursing on the left factor only, which is `Arithmetic`'s own halving. */
  val MultiplicationLemmas: Vector[(String, String)] = Vector(
    "NUM_MUL_BIT0" -> "NUM_BIT0 (x:num) * (y:num) = NUM_BIT0 (x * y)",
    "NUM_MUL_BIT1" -> "NUM_BIT1 (x:num) * (y:num) = NUM_BIT0 (x * y) + y"
  )

  /**
   * What closes the recursion, and `ZERO` is in it because `num`'s encoding has no zero digit.
   *
   * A numeral of `num` is built from `NUM_ONE`, `NUM_BIT0` and `NUM_BIT1`, and `0` is `ZERO`, which
   * is not one of the three. So `NUM_BIT0 ZERO = ZERO` is not the reals' `BIT0_ZERO` under another
   * name: there it keeps a normal form canonical, and here it is what lets a product with zero in
   * it reduce at all.
   */
  val ClosingLemmas: Vector[(String, String)] = Vector(
    "NUM_ADD_ZERO_LEFT" -> "ZERO + (y:num) = y",
    "NUM_ADD_ZERO_RIGHT" -> "(x:num) + ZERO = x",
    "NUM_BIT0_ZERO" -> "NUM_BIT0 ZERO = ZERO",
    "NUM_MUL_ONE_LEFT" -> "NUM_ONE * (y:num) = y",
    "NUM_MUL_ZERO_LEFT" -> "ZERO * (y:num) = ZERO"
  )

  /** Every lemma this file proves, in one place, for the reader and for the spec. */
  val Lemmas: Vector[(String, String)] = AdditionLemmas ++ MultiplicationLemmas ++ ClosingLemmas

  private val AdditionOrder: Vector[String] =
    (AdditionLemmas ++ ClosingLemmas).map { case (name, _) => name }

  private val MultiplicationOrder: Vector[String] =
    (MultiplicationLemmas ++ ClosingLemmas).map { case (name, _) => name } ++
      AdditionLemmas.map { case (name, _) => name }

  /** Over a semiring of one's own, which is where the nine that need no carry are decided. */
  def construct(semiring: Semiring): Either[LogicError, Digits] =
    for {
      proved <- Lemmas.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
        (accumulated, entry) =>
          val (name, text) = entry
          for {
            held <- accumulated
            theorem <- prove(semiring, text)
            // Quantified before it becomes a rewrite rule, and this is not tidiness: `Rewrite.Rule`
            // takes its pattern variables from the quantifiers it strips, so an open equation makes
            // a rule whose `x` matches the letter `x` and nothing else. Proved open here because
            // both routes work on the equation a reader writes.
            closed <- semiring.peano.logic.rules.genAll(
              theorem,
              Term.freeVariables(theorem.conclusion).toList.sortBy(_.name)
            )
          } yield held + (name -> closed)
      }
      addition <- Rewrite.Rule.all(semiring.peano.logic, AdditionOrder.map(proved))
      multiplication <- Rewrite.Rule.all(semiring.peano.logic, MultiplicationOrder.map(proved))
    } yield new Digits(semiring, proved, addition, multiplication)

  /**
   * One lemma, by whichever of the two routes settles it.
   *
   * `Semiring` is asked first and answers nine of the sixteen; what it refuses is not a failure of
   * the goal but the line that file draws about successors, so the refusal is not reported and the
   * second route is taken. A goal neither settles comes back with **the second** refusal, which is
   * the rule this repository keeps at its own propositional address and for the same reason: the
   * first names a fragment that is no longer the only one being tried.
   */
  private def prove(semiring: Semiring, text: String): Either[LogicError, Kernel.Thm] =
    semiring.prove(text) match {
      case Right(theorem) => Right(theorem)
      case Left(_) => throughSuccessor(semiring, text)
    }

  /**
   * A lemma whose two sides differ by where the carries sit, proved by lifting the successors out.
   *
   * Seven of the sixteen are this shape and they are exactly the ones with a carry in them.
   * `NUM_BIT1 n` is `SUC (NUM_ADD n n)`, so a sum of two odd digits has a successor **inside** a
   * sum on the left of the equation and **inside a numeral** on the right, and `Semiring` treats a
   * successor as an atom additively, so its two normal forms are different arrangements of the same
   * successors and it refuses.
   *
   * Lifting them out is four rewrite rules: the three that open a numeral, and the two halves of
   * "a successor moves out of a sum", `NUM_ADD_SUC` and `NUM_SUC_ADD`. What is left under the
   * successors is a pure sum, which is `Semiring`'s fragment, and the successors go back on by
   * congruence. The two sides must produce the **same number** of them, which is what the check
   * below is: a goal where they differ is a goal this is not about, and it is refused rather than
   * closed by some other route.
   */
  private def throughSuccessor(semiring: Semiring, text: String): Either[LogicError, Kernel.Thm] = {
    val peano = semiring.peano
    val logic = peano.logic

    for {
      goal <- peano.proposition(text)
      sides <- Term.destEq(goal).toRight(NotOfForm("an equation", goal))
      (left, right) = sides

      rules <- lifting(peano)
      leftLifted <- Rewrite.rewrite(rules, left)
      rightLifted <- Rewrite.rewrite(rules, right)
      leftForm <- rightOf(leftLifted)
      rightForm <- rightOf(rightLifted)

      successor <- LogicError.lift(
        peano.theory.constant(Natural.NumberSuccessor, Type.fun(Digits.Numbers, Digits.Numbers))
      )
      leftCore = beneath(successor, leftForm)
      rightCore = beneath(successor, rightForm)
      _ <-
        if (leftCore._2 == rightCore._2) Right(())
        else
          Left(
            NotOfForm(
              s"an equation whose sides carry the same number of successors, " +
                s"and these carry ${leftCore._2} and ${rightCore._2}",
              goal
            )
          )

      cores <- semiring.prove(leftCore._1, rightCore._1)
      rebuilt = (0 until leftCore._2).foldLeft[Either[LogicError, Kernel.Thm]](Right(cores)) {
        (accumulated, _) =>
          accumulated.flatMap(Conv.apTerm(successor, _))
      }
      carried <- rebuilt
      back <- Conv.sym(rightLifted)
      result <- Conv.trans(leftLifted, carried).flatMap(Conv.trans(_, back))
    } yield result
  }

  /** The four rules that open a numeral and move a successor out of a sum. */
  private def lifting(peano: Peano): Either[LogicError, Vector[Rewrite.Rule]] =
    for {
      one <- peano.fact(Peano.NumeralOneIsSuccessorOfZero)
      bit0 <- peano.fact(Peano.NumeralBit0Doubles)
      bit1 <- peano.fact(Peano.NumeralBit1Doubles)
      onTheRight <- peano.fact(Peano.AddAtSuccessor)
      onTheLeft <- peano.fact(Peano.SuccessorPlus)
      rules <- Rewrite.Rule.all(peano.logic, Vector(one, bit0, bit1, onTheRight, onTheLeft))
    } yield rules

  /** A term under its leading successors, with how many there were. */
  private def beneath(successor: Term, term: Term): (Term, Int) = term match {
    case App(head, body) if head == successor =>
      val (core, depth) = beneath(successor, body)
      (core, depth + 1)
    case other => (other, 0)
  }

  private[theories] def rightOf(equation: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  private val Binary: Type = Type.fun(Numbers, Type.fun(Numbers, Numbers))
}
