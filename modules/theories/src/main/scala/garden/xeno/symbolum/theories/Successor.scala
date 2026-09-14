package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A number written as a numeral, opened into successors, so that a recurrence can fire on it.
 *
 * `num` has had numerals since 2026-09-12: `2:num` is a term, and it is `NUM_BIT0 NUM_ONE`. Every
 * recurrence over `num` is stated at `SUC n`, and `NUM_BIT0 NUM_ONE` is not `SUC` applied to
 * anything, so no recurrence in this repository has ever been able to fire on a written number.
 * The consequences were met one at a time and read as separate limitations:
 *
 *  - `Power x 2 = x * x` is not provable. `Ring` normalises over atoms and `Power x 2` is an atom
 *    to it; the only thing that could open it is `POWER_SUC`, stated over `SUC y`. So `Algebraic`
 *    states a degree-eight polynomial over a three-term sum with **twenty copies** of `(x + y + z)`
 *    written out, and a reader comparing that with "the minimal polynomial is x^8 - 40x^6 + ..."
 *    is counting copies rather than reading the claim.
 *  - `Bounded.prove` refuses a bound written as `4` and takes one written as `SUC (SUC (SUC (SUC
 *    ZERO)))`, and its refusal says so.
 *  - Eleven comments across `modules/theories` and `modules/tactics` say `num` has no numerals,
 *    which stopped being true on 2026-09-12 and was still the practical truth, because what the
 *    parser produced could not reach any lemma.
 *
 * == Nothing here is new mathematics, and that is the finding ==
 *
 * The five facts this needs were all in the library already: `NUM_ONE_SUC`, `NUM_BIT0_ADD`,
 * `NUM_BIT1_SUC` for the encoding, and addition's two recurrences to collect what the digits
 * produce. `2` unfolds to `NUM_ADD NUM_ONE NUM_ONE`, then to `NUM_ADD (SUC ZERO) (SUC ZERO)`, and
 * addition walks it down to `SUC (SUC ZERO)`. The rule set terminates and is confluent because
 * every rule strictly reduces the encoding, so the whole conversion is `Rewrite.rewrite` with five
 * rules and no bespoke recursion at all. What was missing was the assembly, not a lemma, and the
 * card that recorded the gap had assumed otherwise.
 *
 * == Why the rewriting is aimed and not turned loose ==
 *
 * The five rules applied to a whole goal would open **every** numeral of `num` in it, and a
 * congruence modulo a written modulus, or a bound of ten thousand a translator produced without
 * anyone intending it, becomes a term with ten thousand nodes in it. So [[expand]] matches
 * `Power b k` at the root and is driven by `Rewrite.depthConv`, and a numeral anywhere else in the
 * goal is left exactly as it was written. [[spell]] is the same conversion pointed at one term by a
 * caller who has decided that is what it wants.
 *
 * Aiming it at `Power b k` is not by itself enough, and the case that says so is `Power
 * (real_of_num 7) 2`: rules that open a numeral, run over the whole of that term, open the `7` in
 * the **base** as well. So the expansion is derived over a variable base and the caller's base is
 * put in afterwards by `Kernel.inst`, which is a primitive rule and cannot reach inside it.
 *
 * == What it does not do ==
 *
 * It does not expand `Power b n` at a variable exponent, which would be wrong rather than
 * expensive: `!n. Power x n = ...` is a claim about every exponent and there is nothing to open.
 * It does not touch `NUM_POW`, whose two recurrences have the same shape and whose consumers are
 * currently none; the day one exists, this file is where it goes and the rules are two lines.
 * And it computes nothing: every numeral it produces is built from `ZERO` and `SUC` by inference,
 * which is what `docs/adr/0010` leaves as the only way.
 */
final class Successor private (
  val peano: Peano,
  val series: Series,
  /**
   * The largest written exponent this will open, beyond which it refuses by name.
   *
   * A field rather than a constant read from the companion, for the reason `Bounded` gives: a limit
   * is calibrated by building the same driver on the other side of it and asking the same claim,
   * which is what `SuccessorSpec` does. [[Successor.Exponent]] is what a caller gets who does not
   * choose.
   */
  val limit: Int,
  /**
   * How much more than [[limit]] the rewriter is allowed, which is a second line and not a detail.
   *
   * A field for the reason [[limit]] is one and `Bounded.limit` is one: the only way to find out
   * what a line cuts is to build the same procedure with the line somewhere else and ask the same
   * claim. Without it the two `NotNormalised` refusals below are unreachable by construction, since
   * the longer of the two walks costs `k + 2` and this is sixteen, and a guard nothing can point at
   * is a guard nobody has seen work. It is signed, and `SuccessorSpec` builds one below zero: the
   * two walks cost differently, so cutting both at once needs a ceiling under the cheaper one.
   */
  val slack: Int,
  private val numeralRules: Vector[Rewrite.Rule],
  private val powerRules: Vector[Rewrite.Rule],
  private val power: Term
) {

  private val logic: Logic = series.logic

  /** The rewriter's ceiling, which follows [[limit]] rather than standing beside it. */
  private val steps: Int = limit + slack

  /**
   * `|- k = SUC (SUC ... ZERO)`, for a `k` written as a numeral of `num`.
   *
   * The equation, not the term: a caller that wanted the term alone would be building a numeral
   * rather than proving anything about the one it was given, and `Bounded.numeral` is where that
   * lives. What this is for is carrying a statement across, which is `Kernel.eqMp` over the result.
   *
   * `0` comes back as `|- 0 = 0`, which is right and not a special case: `ZERO` **is** the
   * encoding's zero, so the numeral and the successor form are the same term and the reflexivity is
   * the honest answer rather than a missing one.
   */
  def spell(numeral: Term): Either[LogicError, Kernel.Thm] =
    for {
      value <- valueOf(numeral).toRight(
        NotOfForm(s"a numeral of ${Natural.TypeName}", numeral)
      )
      _ <- withinLimit(value, numeral)
      equation <- Rewrite.rewrite(numeralRules, numeral, steps)

      // The rewriter hands back what it had built when the step limit ran out, and that theorem is
      // true, so a caller cannot tell a finished spelling from an abandoned one by looking at it.
      // Asked after the fact and only here, which is the discipline `Rewrite.finished` documents.
      right <- rightOf(equation)
      done <- Rewrite.finished(numeralRules, right)
      result <-
        if (done) Right(equation)
        else Left(NotNormalised(right))
    } yield result

  /**
   * `|- ~(a = b)` for two numerals of `num` with different values.
   *
   * The companion [[spell]] has needed since 2026-09-14 and did not have. A numeral of `num` is a
   * bit encoding, so two of them differing is not a fact any procedure here decides: `Semiring`
   * settles identities and says nothing about their negations, and the order lemmas are about
   * variables. What settles it is the successor form, which is what this file exists to produce.
   *
   * Both numerals are spelled, the shorter run of successors is stripped from both by
   * `NUM_SUC_INJECTIVE`, and what is left is a successor equal to zero, which `NUM_SUC_NOT_ZERO`
   * denies. The cost is linear in the smaller value and the refusal for equal values is by name.
   *
   * **What wanted it is a predicate over tagged codes.** `Language.NUM_TERM` reads a tag and
   * selects a clause by it, and the claim that a code with an unrecognised tag is **not** a term is
   * the one assertion that says the predicate discriminates rather than merely being non-constant.
   * That claim is a handful of numeral disequalities and nothing else.
   */
  def distinct(left: Term, right: Term): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    def successors(term: Term): Int = term match {
      case App(Const(Natural.NumberSuccessor, _), argument) => 1 + successors(argument)
      case _ => 0
    }

    for {
      leftValue <- valueOf(left).toRight(NotOfForm(s"a numeral of ${Natural.TypeName}", left))
      rightValue <- valueOf(right).toRight(NotOfForm(s"a numeral of ${Natural.TypeName}", right))
      _ <-
        if (leftValue != rightValue) Right(())
        else Left(NotOfForm(s"two numerals with different values, and both are $leftValue", left))

      leftSpelled <- spell(left)
      rightSpelled <- spell(right)
      leftForm <- rightOf(leftSpelled)
      rightForm <- rightOf(rightSpelled)

      equal <- LogicError.lift(Term.eq(left, right))
      assumed <- LogicError.lift(Kernel.assume(equal))
      inSuccessors <- Conv
        .sym(leftSpelled)
        .flatMap(Conv.trans(_, assumed))
        .flatMap(Conv.trans(_, rightSpelled))

      injective <- peano.naturals.fact(Natural.SuccessorInjective)
      stripped <- (0 until successors(leftForm).min(successors(rightForm)))
        .foldLeft[Either[LogicError, Kernel.Thm]](Right(inSuccessors)) { (carried, _) =>
          for {
            equation <- carried
            sides <- Term
              .destEq(equation.conclusion)
              .toRight(NotOfForm("an equation", equation.conclusion))
            inner <- (sides._1, sides._2) match {
              case (App(_, first), App(_, second)) => Right((first, second))
              case _ => Left(NotOfForm("two successors", equation.conclusion))
            }
            result <- rules
              .specAll(injective, List(inner._1, inner._2))
              .flatMap(rules.mp(_, equation))
          } yield result
        }

      // One side is now `ZERO` and the other is a successor, whichever way round the values fell.
      sides <- Term
        .destEq(stripped.conclusion)
        .toRight(NotOfForm("an equation", stripped.conclusion))
      oriented <-
        if (leftValue > rightValue) Right(stripped)
        else Conv.sym(stripped)
      orientedSides <- Term
        .destEq(oriented.conclusion)
        .toRight(NotOfForm("an equation", oriented.conclusion))
      inside <- orientedSides._1 match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("a successor", other))
      }
      never <- peano.naturals
        .fact(Natural.SuccessorNotZero)
        .flatMap(rules.spec(inside, _))
      contradiction <- rules.notElim(never, oriented)
      result <- rules.notIntro(equal, contradiction)
      _ = sides
    } yield result
  }

  /**
   * `|- t = t'`, with every `Power b k` at a written `k` opened into `b * (b * ... * 1)`.
   *
   * The `1` at the end is `POWER_ZERO` and is not tidied away: tidying it would need the ring's
   * unit law, which is a second procedure's business, and every caller that goes on to `Ring` gets
   * it removed for free. A caller that wants the equation for its own sake gets the form the
   * recurrences produce.
   *
   * A term with no written power in it comes back `|- t = t`, which is what every conversion here
   * does with nothing to do.
   */
  def expand(term: Term): Either[LogicError, Kernel.Thm] =
    Rewrite.depthConv(atPower)(term)

  /**
   * The equation, with its written powers opened and the rest left to `Ring`.
   *
   * The two halves are separate on purpose and the separation is the whole design: this file knows
   * that a power at a written exponent is a repeated product, and `Ring` knows what holds in every
   * commutative ring. Neither could be given the other's half without moving it in the chain, since
   * `Ring` is built four stages below `Series` and cannot name `Power` at all.
   *
   * A refusal from `Ring` comes through as it stands, carrying its own standing: an identity that
   * is false after expansion is [[NotEqualTo]] and decided, and it is decided about the goal as
   * written because the expansion is an equation.
   */
  def prove(goal: Term): Either[LogicError, Kernel.Thm] =
    for {
      equation <- expand(goal)
      opened <- rightOf(equation)
      proved <- series.ring.prove(opened)
      reversed <- Conv.sym(equation)
      result <- LogicError.lift(Kernel.eqMp(reversed, proved))
    } yield result

  /* ------------------------------------------------------------------------ the aimed step */

  /**
   * `Power b k` at the root, and `|- t = t` anywhere else.
   *
   * Total, because that is what the combinators in `Rewrite` are built on: a conversion with
   * nothing to do returns reflexivity rather than failing, so `depthConv` over it visits every
   * subterm and changes only the ones this reads.
   *
   * The one place it does fail is a written exponent past [[limit]], and failing there rather than
   * declining to open it is deliberate: a caller that asked for `Power x 100000` and got the term
   * back unchanged would meet the refusal later, from `Ring`, as a statement about the identity.
   */
  private val atPower: Rewrite.Conversion = term =>
    term match {
      case App(App(head, base), exponent) if head == power =>
        valueOf(exponent) match {
          case None => Right(Conv.refl(term))
          case Some(value) =>
            for {
              _ <- withinLimit(value, term)

              // Over a VARIABLE base, and then instantiated. The rules include the encoding, so
              // running them over the caller's own base would open every numeral of `num` inside
              // it as well, which is the blanket behaviour this conversion is aimed to avoid and
              // which `real_of_num 7` is enough to reach. A variable cannot contain one, so the
              // rewriting has nothing to find but the exponent, and the instance at the end is a
              // primitive rule. It is also cheaper: what is rewritten is three nodes however large
              // the base is.
              stand <- LogicError.lift(Term.appAll(power, List(Successor.Stand, exponent)))
              equation <- Rewrite.rewrite(powerRules, stand, steps)
              right <- rightOf(equation)
              done <- Rewrite.finished(powerRules, right)
              settled <-
                if (done) Right(equation)
                else Left(NotNormalised(right))
              result <- LogicError.lift(Kernel.inst(Map(Successor.Stand -> base), settled))
            } yield result
        }

      case other => Right(Conv.refl(other))
    }

  private def valueOf(term: Term): Option[BigInt] =
    if (Term.typeOf(term) == Successor.Numbers) series.notation.valueOfNumeral(term)
    else None

  /**
   * The line, and the one thing its refusal rounds.
   *
   * `BoundReached` carries what was reached as an `Int` and a numeral is a `BigInt`, so a value
   * past `Int.MaxValue` is reported as `Int.MaxValue`. That is a stated limit rather than a hidden
   * one: the field would otherwise wrap and name a number that is not the one in the term, and
   * nothing a caller does differs between an exponent of two billion and one of ten to the thirty.
   */
  private def withinLimit(value: BigInt, where: Term): Either[LogicError, Unit] =
    if (value <= limit) Right(())
    else Left(BoundReached(Successor.LimitName, value.min(Successor.Reportable).toInt, limit, where))

  private def rightOf(equation: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(equation.conclusion).map(_._2).toRight(NotOfForm("an equation", equation.conclusion))
}

object Successor {

  /** The type the numerals this opens belong to. */
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  /**
   * The base the expansion is derived over before the caller's own is put in.
   *
   * Its name is not chosen for freshness and does not need to be: it is bound nowhere and the
   * instance substitutes it for the caller's base, so a base that happens to mention a variable of
   * this name and type is left exactly as it was written. What the name is for is a reader of a
   * derivation who meets it.
   */
  private val Stand: FVar = Term.variable("base", TyApp(Real.TypeName, Nil))

  /** The name the refusal carries, so that a reader of it knows which line was reached. */
  val LimitName: String = "Successor.Exponent"

  /**
   * How much more than the exponent the rewriter is allowed, measured rather than guessed.
   *
   * The smallest step limit at which each walk finishes was read directly, by asking it at every
   * limit from one upwards until it did, on 2026-09-13:
   *
   * {{{
   *   k                    2   4   8   16   32   64
   *   Power b k            4   6   10  18   34   66
   *   the numeral alone    3   4   6   10   18   34
   * }}}
   *
   * The power walk is `k + 2` at every one of them and the numeral walk is about half that, which
   * is not a surprise once looked at: `depthConv` makes a whole pass per step and the encoding's
   * digits open several successors in one. So the binding walk is the power one and the ceiling is
   * the exponent's own limit plus this.
   *
   * A first version of this file wrote 100000 here and a sentence saying `Rewrite.DefaultLimit`
   * was too small for 64; the sentence was written without the measurement and 66 is not more than
   * 200.
   *
   * The slack is eight times the constant term rather than the constant term, because what it
   * absorbs is a change to the rule set and not a change to the exponent. Running out of it is a
   * `NotNormalised`, which is a refusal and not a wrong answer.
   */
  val Slack: Int = 16

  /** The largest value the refusal can name, since `BoundReached` counts in `Int`. */
  private val Reportable: BigInt = BigInt(Int.MaxValue)

  /**
   * The largest written exponent [[Successor.expand]] opens, for a caller that does not choose.
   *
   * **What this line is about is not what a reader expects, and the measurement is why.** The
   * driver's own cost is nearly flat: spelling a numeral is 4810 inferences at 2 and 6258 at 64,
   * because almost all of it is the five lemmas the rules rest on and every call shares them. So
   * there is no turn in this file's cost to put a line at.
   *
   * The price is the caller's, and it is the polynomial rather than the exponent. Read on
   * 2026-09-13, through [[prove]], on two shapes:
   *
   * {{{
   *   (x + y)^k      k    2      4      8      16     24      32      40      48
   *                  inf  7760   9401   15007  43497  112365  248682  484580  861231
   *
   *   x^k            k    16     32     64     128
   *                  inf  8823   12750  25349  69448
   * }}}
   *
   * The same exponent costs 43497 over a binomial and 8823 over one variable, and at 48 the
   * binomial is 861231 while 128 over one variable is 69448. So a line drawn on the exponent
   * cannot bound what a caller pays: what it bounds is **the term this builds**, which is `k`
   * copies of the base, and that is what it is documented as.
   *
   * 32 is where it is put, and the argument is the binomial ladder because that is the expensive
   * shape of the two: it is the last exponent at which a claim of that shape is settled in one
   * round of thinking, and 40 is twice the price for a quarter more range. A base with three
   * variables in it turns sooner than that and this file cannot see it; a caller meeting that
   * meets it as a slow `Ring` and not as a refusal from here, which is the half this line does
   * not cover.
   *
   * **Measured in both directions**, because a limit calibrated against nothing is calibrated on
   * nothing, and `SuccessorSpec` holds both: what it cuts, by building the driver at 4 and getting
   * `Power x 8` refused by name where this line proves it; and what it buys, which is that
   * `Power x 100000`, a term a translator produces without anybody intending it, is a refusal
   * naming the limit rather than a walk nobody watches finish.
   *
   * A caller who means a larger exponent passes one to [[construct]], which is a change a caller
   * can make and waiting is not.
   */
  val Exponent: Int = 32

  /** The driver over a development that has both the numerals and the powers. */
  def construct(
    peano: Peano,
    series: Series,
    limit: Int = Exponent,
    slack: Int = Slack
  ): Either[LogicError, Successor] =
    for {
      oneIsSuccessor <- peano.fact(Peano.NumeralOneIsSuccessorOfZero)
      evenDigit <- peano.fact(Peano.NumeralBit0Doubles)
      oddDigit <- peano.fact(Peano.NumeralBit1Doubles)
      addAtZero <- peano.fact(Peano.AddAtZero)
      addAtSuccessor <- peano.fact(Peano.AddAtSuccessor)
      powerAtZero <- series.fact(Series.PowerAtZero)
      powerAtSuccessor <- series.fact(Series.PowerAtSuccessor)

      encoding = Vector(oneIsSuccessor, evenDigit, oddDigit, addAtZero, addAtSuccessor)
      numeralRules <- Rewrite.Rule.all(series.logic, encoding)
      powerRules <- Rewrite.Rule.all(series.logic, encoding :+ powerAtZero :+ powerAtSuccessor)

      power <- LogicError.lift(
        series.theory.constant(
          Series.PowerName,
          Type.fun(TyApp(Real.TypeName, Nil), Type.fun(Numbers, TyApp(Real.TypeName, Nil)))
        )
      )
    } yield new Successor(peano, series, limit, slack, numeralRules, powerRules, power)
}
