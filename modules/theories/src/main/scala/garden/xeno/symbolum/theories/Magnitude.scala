package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The larger of two reals, the smaller, the distance from zero, and the sign.
 *
 * `max`, `min`, `abs` and `sgn`, with the facts that characterise each one, and the whole file
 * exists to make one cost visible: **this is the choice axiom's first use outside the foundation.**
 *
 * == Why `max` cannot be written down without it ==
 *
 * The usual definition is a conditional, `if x <= y then y else x`, and when this file was written
 * this logic had no conditional expression at all. **It has one since 2026-09-12** and this
 * paragraph predicted what it would be: `Classical.COND` is
 * `select (\v. (p ==> v = a) /\ (~p ==> v = b))`, the same appeal to choice one level of
 * indirection away. So the conditional was never a route around the cost this file is about and is
 * not one now. `max` could be spelled the usual way today; the bill would be `select` either way,
 * and what is below goes to it directly rather than through a constant that goes to it for it.
 *
 * **A definition by cases is not a route around it either, and the reason is not the one this file
 * used to give.** What stood here said the excluded middle is out of reach, `Logic`'s connectives
 * being intuitionistic and Diaconescu's argument wanting extensionality as well. **That was
 * wrong**, and `docs/adr/0009` is the correction: `Classical.EXCLUDED_MIDDLE` is a theorem resting
 * on the choice axiom and nothing else, so `x <= y \/ ~(x <= y)` has been *reachable* since
 * `select` landed, and `Classical.cases` is the rule that now hands it over.
 *
 * What that gives is a case **analysis**: two branches, each proving the same proposition, and a
 * proposition proved at the end of it. What defining a constant needs is a case **expression**: one
 * closed term. Those are different things, and the second of them is `COND`, which the paragraph
 * above reduces to `select` whether or not anybody has defined it. So the correction moves the
 * argument and does not weaken it: the reason a case split is not a definition is the difference
 * between proving and naming, not the absence of something to split on.
 *
 * `LT_TOTAL` is what this file actually splits on, an axiom of the reals giving the three-way
 * `x < y \/ x = y \/ y < x` for the order **specifically**, and the excluded middle at `x <= y` is
 * now a second route to the same place: both prove that a greatest of the two *exists*, and neither
 * says which term it is. Between a proof that something exists and a term naming it stands the
 * choice operator, and nothing else: `Kernel.defineConstant` wants a closed term, and a witness
 * pulled out by eliminating an existential is a variable. `Classical.witness` is the operation that
 * closes that gap, and it is what `Natural` uses to name the successor on `ind` and `Series` to
 * name a function defined by recursion.
 *
 * **So a development that does not want the choice axiom cannot have `max`**, and that has not
 * changed. It is not a limitation of this file, it is what the sentence "the reals are a complete
 * ordered field" does and does not entail: the sixteen axioms give a greatest of two numbers as a
 * theorem about existence and give no way to name it. What did change is the size of the bill. A
 * development that takes `max` takes the whole classical extension, which has held two axioms
 * since eta landed on 2026-09-10, so the price is choice **and** eta whether or not anything here
 * uses the second. `MagnitudeSpec` asserts it in the only form that cannot go stale, by counting
 * the axioms of both theories rather than naming a number.
 *
 * == Two of the four constants are named by choice, and two are definitions ==
 *
 * `min` and `abs` are abbreviations for combinations of `max`:
 *
 * {{{
 *   min x y = x + y - max x y
 *   abs x   = max x (-x)
 * }}}
 *
 * The first is the identity `min x y + max x y = x + y` read as a definition, which works because
 * the two of them are the same pair of numbers in the other order. It is worth preferring over a
 * second appeal to choice for two reasons and neither is economy of typing: a second `select` would
 * be a second existence proof to keep in agreement with the first, and every fact about `min` here
 * comes out of the corresponding fact about `max` by one ring identity, so `min` cannot drift away
 * from being the other one.
 *
 * `abs x = max x (-x)` is the same trade. It is the reflection that makes it work, not an accident:
 * exactly one of `x` and `-x` is at least zero, so the greater of them is the distance from zero.
 *
 * `sgn` is the one that cannot be had that way, and this is worth stating because it is the natural
 * next thing to try: three answers are not a combination of a two-way operation, so it has an
 * existence proof of its own over a three-way split of `LT_TOTAL`. **It costs no further axiom.**
 * Choice is already in the theory once `max` is there, and a second use of an axiom already
 * believed adds nothing to what has to be believed, which is why the count below does not move for
 * it: `MagnitudeSpec` asserts the sixteen of the field plus the logic's own, whether or not `sgn`
 * exists. What `sgn` does add is a second existence proof, and that is the price it pays.
 *
 * Its three facts are implications and not one equation, because `sgn x` is a single term and which
 * numeral it equals is decided by where `x` sits: an unconditional statement would need a case
 * expression on the right. There has been one since 2026-09-12, `Classical.COND`, so that statement
 * is now writable and is still not written. It would be a different theorem with a different proof
 * and nothing has asked for it; what is here is what was proved.
 *
 * == What is not here ==
 *
 * **`floor` and `ceiling`, deliberately, and they are not a budget casualty.** Both need something
 * this tree does not have. The characterising fact for `floor x` is that it is an *integer* with
 * `floor x <= x < floor x + 1`, and there are no integers here: `Natural` builds `num` and nothing
 * embeds it in the reals, so "an integer below `x`" cannot even be stated. Reaching it another way,
 * as the greatest element of a set that is bounded above, wants a least-element principle over the
 * naturals and then the embedding anyway. A definition could be written today by choice, over a
 * predicate nothing can be proved to satisfy, and every characterising theorem about it would be
 * out of reach: that is worse than the absence, because it would look like progress.
 *
 * What `sgn` does not come with is `sgn x * abs x = x`, which is the identity that makes it worth
 * having and is not derived here. It wants `abs x = x` under `0 <= x` and `abs x = -x` under `x <=
 * 0`, neither of which is in this file: those are two more case analyses on [[Magnitude.AbsCases]]
 * against antisymmetry, and they were not reached rather than being out of reach.
 *
 * The triangle inequality **is** here, and it is the fact that makes `abs` worth having: it is
 * `Order.ADD_LE` twice and then `ABS_CASES` on the sum.
 */
final class Magnitude private (
  val order: Order,
  val classical: Classical,
  val theory: Theory,
  val notation: Notation,
  /**
   * The connectives read against **this** theory rather than against the bare one.
   *
   * A rule that has to build a quantifier at `real` asks a theory for the quantifier constant at
   * that type, so a development that proves anything here needs the logic over the widest
   * signature. `Logic.over` checks the extension rather than assuming it.
   */
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm],
  /**
   * How each of these facts was derived, at the size it was written in.
   *
   * All seventeen since 2026-09-13, and each account is **self-contained**: it opens at the axioms
   * and the definitions and ends at the fact, referring to nothing a reader has not been shown.
   * That is what makes them compose. The three facts about `abs` are the three about `max` at `x`
   * and `-x`, so the account of the triangle inequality replays the account of `ABS_CASES`, which
   * replays the account of `MAX_CASES`, which opens at the existence proof; `Script.tidy` is what
   * keeps a line that several of them share from being printed several times.
   *
   * Held here rather than on the theorem because a theorem has no account: the same sequent is
   * reachable by several routes and `Kernel.Thm` compares by the sequent, so an account attached to
   * one would be claimed by all of them.
   */
  val scripts: Map[String, Script]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  val reals: RealTheory = order.reals

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** The fact named, as a theorem with no hypotheses. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** `|- !x y. max x y = x \/ max x y = y` */
  def maxCases: Either[LogicError, Kernel.Thm] = fact(Magnitude.MaxCases)

  /** `|- !x y. x <= max x y` */
  def maxAboveLeft: Either[LogicError, Kernel.Thm] = fact(Magnitude.MaxAboveLeft)

  /** `|- !x y. y <= max x y` */
  def maxAboveRight: Either[LogicError, Kernel.Thm] = fact(Magnitude.MaxAboveRight)

  /** `|- !x y z. x <= z ==> y <= z ==> max x y <= z` */
  def maxLeast: Either[LogicError, Kernel.Thm] = fact(Magnitude.MaxLeast)

  /** `|- !x y. min x y = x \/ min x y = y` */
  def minCases: Either[LogicError, Kernel.Thm] = fact(Magnitude.MinCases)

  /** `|- !x y. min x y <= x` */
  def minBelowLeft: Either[LogicError, Kernel.Thm] = fact(Magnitude.MinBelowLeft)

  /** `|- !x y. min x y <= y` */
  def minBelowRight: Either[LogicError, Kernel.Thm] = fact(Magnitude.MinBelowRight)

  /** `|- !x y. min x y + max x y = x + y` */
  def minPlusMax: Either[LogicError, Kernel.Thm] = fact(Magnitude.MinPlusMax)

  /** `|- !x. abs x = x \/ abs x = -x` */
  def absCases: Either[LogicError, Kernel.Thm] = fact(Magnitude.AbsCases)

  /** `|- !x. x <= abs x` */
  def absAbove: Either[LogicError, Kernel.Thm] = fact(Magnitude.AbsAbove)

  /** `|- !x. -x <= abs x` */
  def absAboveNegation: Either[LogicError, Kernel.Thm] = fact(Magnitude.AbsAboveNegation)

  /** `|- !x. 0 <= abs x` */
  def absNonNegative: Either[LogicError, Kernel.Thm] = fact(Magnitude.AbsNonNegative)

  /** `|- !x. abs x = 0 ==> x = 0` */
  def absZero: Either[LogicError, Kernel.Thm] = fact(Magnitude.AbsZero)

  /** `|- !x y. abs (x + y) <= abs x + abs y` */
  def triangle: Either[LogicError, Kernel.Thm] = fact(Magnitude.Triangle)

  /** `|- !x. x < 0 ==> sgn x = -1` */
  def signNegative: Either[LogicError, Kernel.Thm] = fact(Magnitude.SignNegative)

  /** `|- !x. x = 0 ==> sgn x = 0` */
  def signZero: Either[LogicError, Kernel.Thm] = fact(Magnitude.SignZero)

  /** `|- !x. 0 < x ==> sgn x = 1` */
  def signPositive: Either[LogicError, Kernel.Thm] = fact(Magnitude.SignPositive)

  // `proposition`, `term` and `show` were written out here and are `Signature`'s since 2026-09-13,
  // when this development joined the chain and needed to be one. The three bodies were identical
  // to the trait's, which is what made deleting them rather than overriding them the right move.
}

object Magnitude {

  /** The greater of two reals, the one constant here that costs the choice axiom. */
  val MaxName: String = "max"

  /** The lesser of two reals, defined as `x + y - max x y`. */
  val MinName: String = "min"

  /** The distance from zero, defined as `max x (-x)`. */
  val AbsName: String = "abs"

  /** `|- !x y. max x y = x \/ max x y = y` */
  val MaxCases: String = "MAX_CASES"

  /** `|- !x y. x <= max x y` */
  val MaxAboveLeft: String = "MAX_ABOVE_LEFT"

  /** `|- !x y. y <= max x y` */
  val MaxAboveRight: String = "MAX_ABOVE_RIGHT"

  /**
   * `|- !x y z. x <= z ==> y <= z ==> max x y <= z`.
   *
   * The half of the characterisation that says `max` is the *least* upper bound of the two and not
   * merely one. Without it the two facts above are satisfied by anything large enough, so this is
   * what makes `max x y` pinned rather than bounded, and it is what a caller eliminating a `max`
   * from a goal actually uses.
   */
  val MaxLeast: String = "MAX_LEAST"

  /** `|- !x y. min x y = x \/ min x y = y` */
  val MinCases: String = "MIN_CASES"

  /** `|- !x y. min x y <= x` */
  val MinBelowLeft: String = "MIN_BELOW_LEFT"

  /** `|- !x y. min x y <= y` */
  val MinBelowRight: String = "MIN_BELOW_RIGHT"

  /**
   * `|- !x y. min x y + max x y = x + y`.
   *
   * The definition of `min` read back as a fact, and the reason it is worth naming is that it is
   * the whole justification for defining `min` that way rather than by a second appeal to choice:
   * the two of them are the same pair of numbers, so their sum does not depend on which is which.
   */
  val MinPlusMax: String = "MIN_PLUS_MAX"

  /** `|- !x. abs x = x \/ abs x = -x` */
  val AbsCases: String = "ABS_CASES"

  /** `|- !x. x <= abs x` */
  val AbsAbove: String = "ABS_ABOVE"

  /** `|- !x. -x <= abs x` */
  val AbsAboveNegation: String = "ABS_ABOVE_NEG"

  /** `|- !x. 0 <= abs x` */
  val AbsNonNegative: String = "ABS_NONNEG"

  /**
   * `|- !x. abs x = 0 ==> x = 0`.
   *
   * Stated as an implication and not as an equivalence, because the converse is a rewrite rather
   * than a theorem worth a name: `abs 0 = 0` follows from [[AbsCases]] at zero either way round.
   * This direction is the one a limit argument uses, and it is antisymmetry: `x <= abs x` gives
   * `x <= 0`, `-x <= abs x` gives `0 <= x`, and the two bounds meet.
   */
  val AbsZero: String = "ABS_ZERO"

  /** `|- !x y. abs (x + y) <= abs x + abs y` */
  val Triangle: String = "ABS_TRIANGLE"

  /**
   * `|- !x. 0 <= x ==> abs x = x`
   *
   * One of the two this file's own opening named as *not reached rather than out of reach*, and
   * the reason they are worth reaching is that they turn `abs` into a term of the ring: with the
   * sign known, every occurrence of `abs` disappears and what is left is arithmetic.
   */
  val OfNonNegative: String = "ABS_OF_NONNEG"

  /** `|- !x. x <= 0 ==> abs x = -x`, the other of the two. */
  val OfNonPositive: String = "ABS_OF_NONPOS"

  /**
   * `|- !x y. abs (x * y) = abs x * abs y`
   *
   * What an estimate over a product needs, and what the two facts above were the obstacle to. It
   * is four cases on the signs, and once the two facts above have removed the `abs` from each
   * factor, every one of the four is a ring identity. `ABS_TRIANGLE` is the additive half of the
   * same question and was here from the start; this is the multiplicative one.
   */
  val Multiplicative: String = "ABS_MUL"

  /** The sign of a real: `-1`, `0` or `1`. */
  val SignName: String = "sgn"

  /** `|- !x. x < 0 ==> sgn x = -1` */
  val SignNegative: String = "SGN_NEGATIVE"

  /** `|- !x. x = 0 ==> sgn x = 0` */
  val SignZero: String = "SGN_ZERO"

  /** `|- !x. 0 < x ==> sgn x = 1` */
  val SignPositive: String = "SGN_POSITIVE"

  /**
   * The predicate a greatest of two numbers satisfies, as the text a person checks it by.
   *
   * Written out in the concrete syntax rather than built, for the reason `docs/adr/0004` gives for
   * the sixteen: what a reader has to check here is that this says "one of the two, and above both
   * of them", and a reader checks a sentence and not a sequence of builder calls. Everything about
   * `max` below is this predicate and nothing else, since choice constrains `select P` only where
   * something satisfies `P`.
   */
  val Greatest: String =
    "?m:real. (m = x:real \\/ m = y:real) /\\ (x:real <= m /\\ y:real <= m)"

  /**
   * The predicate the sign of a real satisfies, as the text a person checks it by.
   *
   * A three-way split rather than the two-way one [[Greatest]] is, which is the whole difference
   * between `sgn` and the rest of this file: it cannot be assembled out of `max`, so it is the
   * second and only other appeal to choice here.
   */
  val Sign: String =
    "?s:real. (x:real < 0 /\\ s = -1) \\/ ((x:real = 0 /\\ s = 0) \\/ (0 < x:real /\\ s = 1))"

  /**
   * What the three facts about `sgn` share, so that each of them can be accounted for on its own.
   *
   * A record rather than a tuple because there are twenty-one of them and a positional read of that
   * is how a proof gets assembled out of the wrong pieces. It exists only between [[signFacts]]'s
   * shared prefix and its three endings.
   */
  private final case class SignPieces(
    characterisation: Kernel.Thm,
    transitive: Kernel.Thm,
    zero: Term,
    neverAtPoint: Kernel.Thm,
    neverAtZero: Kernel.Thm,
    rest: Term,
    below: Term,
    valueBelow: Term,
    equated: Term,
    valueEquated: Term,
    above: Term,
    valueAbove: Term,
    inNegative: Kernel.Thm,
    inZero: Kernel.Thm,
    inPositive: Kernel.Thm,
    answerNegative: Kernel.Thm,
    answerZero: Kernel.Thm,
    answerPositive: Kernel.Thm,
    belowAssumed: Kernel.Thm,
    equatedAssumed: Kernel.Thm,
    aboveAssumed: Kernel.Thm
  )

  private val real: Type = TyApp(Real.TypeName, Nil)

  /** The type the choice operator has to be available at: a predicate on reals, to a real. */
  private val chooser: Type = Type.fun(Type.fun(real, Type.Bool), real)

  /**
   * Built once, over the shortest chain that can hold it.
   *
   * `Classical` first and the reals over it, which is the order `Chain` explains and this needs for
   * a narrower reason: the choice operator has to be in the *same* signature as `<`, or `select`
   * cannot be applied to a predicate about reals at all.
   *
   * **It is not `Order.standard` and cannot be.** That one is built over `Real.standard`, which
   * sits over the axiom-free `Logic.standard` deliberately, so that a development about the reals is
   * not asked to believe choice, or eta either. This is the other configuration, and having both is
   * the point: the sixteen of the field plus the logic's two here against the sixteen alone there,
   * and the difference is one line of this file.
   */
  lazy val standard: Magnitude =
    chain(Classical.standard).fold(
      error => throw new IllegalStateException(s"the magnitude facts do not build: ${error.message}"),
      identity
    )

  /**
   * The whole chain over a classical logic of one's own, in the order that works.
   *
   * Written as one comprehension for the same reason `Chain.construct` is: the order is the content
   * of the function, and a reader checking it should not have to follow a call to see it.
   */
  def chain(classical: Classical): Either[LogicError, Magnitude] =
    for {
      naturals <- Natural.construct(classical)
      built <- Real.construction(classical, naturals)
      arithmetic <- Arithmetic.construct(built.reals)
      ring <- Ring.construct(arithmetic)
      order <- Order.construct(ring)
      magnitude <- construct(classical, order)
    } yield magnitude

  /**
   * Define the three constants over an order whose signature already holds the choice operator.
   *
   * The order is passed in rather than built, so a development that has assembled its own chain,
   * `Chain` being the one that also carries the naturals, gets these facts over *its* signature
   * instead of a second one beside it.
   *
   * The first thing this does is check that `select` is in that signature at the type it is wanted
   * at, and refuse by name if it is not. Without the check the failure is a parse error deep inside
   * an existence proof, which reads as this file being broken rather than as the caller having
   * passed an order built over a logic with no choice in it.
   */
  def construct(classical: Classical, order: Order): Either[LogicError, Magnitude] =
    construct(classical, order, order.reals.theory, order.reals.notation)

  /**
   * The same, over a theory that already holds something else, which is the chain entry point.
   *
   * The overload the five developments moved into `Chain` on 2026-09-12 all have, and this one was
   * missed. What being outside costs is not inconvenience: `Library.of` collects the chain's
   * developments, so these seventeen facts reached no library and `docs/lemmas.md` did not list
   * them; and `max`, `min`, `abs` and `sgn` were not constants of the widest signature, so a goal
   * naming `abs` did not fail. It **parsed**, as a claim about a free variable of that name, which
   * is the trap `Chain`'s own comment records for `NUM_LE ZERO n` and which was still live here on
   * 2026-09-13.
   *
   * Last in the chain's order rather than anywhere earlier, and the position is free for the reason
   * `Matrix`'s field comment gives: nothing below needs `max`, so a development with no dependent
   * belongs where adding it moves nothing.
   */
  def construct(
    classical: Classical,
    order: Order,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Magnitude] = {
    val ring = order.ring
    val reals = order.reals
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      _ <- base
        .constant(Classical.Select, chooser)
        .left
        .map[LogicError](_ =>
          TypeError(
            s"this order is stated over a theory with no ${Classical.Select} in it, so " +
              s"$MaxName cannot be named; build the reals over a Classical logic"
          )
        )
      logic <- classical.logic.over(base)
      rules = logic.rules
      // The spike of 2026-09-13: three of this file's fourteen derivations take their operations
      // from here instead of from `rules` and `Conv`, and each one hands back an account of itself
      // beside the theorem. Nothing else changes about them; see `scripts` on the class.
      record = new Recorder(rules, notation)

      ofLt <- order.leOfLt
      ofEq <- order.leOfEq
      toZero <- order.leToZero
      fromZero <- order.leFromZero
      addNonNegatives <- order.addNonNegatives
      cancelNonNegative <- order.cancelNonNegative
      antisymmetric <- order.antisymmetric
      addBounds <- order.addLe

      /* --------------------------------------------------------------- max */

      // Everything from the existence proof to the theorem that characterises `max`, as one
      // account. The four facts below each replay it, which is what makes each of them readable
      // on its own without citing a theorem nobody has been shown.
      maxNamed = for {
        existence <- greatestExists(record, logic, reals, ofLt, ofEq)
        chosen <- record.step("name it by choice", Some(MaxName), Vector(existence))(
          classical.witness(existence)
        )
        beta <- record.step("beta reduce", None, Vector.empty)(Conv.betaRoot(chosen.conclusion))
        reduced <- record.replace(beta, chosen)
        selected <- Recorded.quiet(chosen.conclusion match {
          case App(_, term) => Right(term)
          case other => Left(NotOfForm("a predicate applied to what was chosen", other))
        })
        maxBody <- Recorded.quiet(LogicError.lift(Term.absAll(List(x, y), selected)))
        defined <- Recorded.quiet(LogicError.lift(Kernel.defineConstant(base, MaxName, maxBody)))
        maxUnfolded <- Recorded.quiet(Conv.unfold(defined._2, List(x, y)))
        maxFolded <- Recorded.quiet(Conv.sym(maxUnfolded))
        characterisation <- record.rewriteIn(
          s"the definition of $MaxName",
          Vector(maxFolded),
          reduced
        )
      } yield (defined._1, defined._2, characterisation)
      named <- maxNamed.value
      (withMax, maxDefinition, _) = named

      characterised = maxNamed.map(_._3)
      isOneOfThemRecorded = characterised.flatMap(record.firstHalf)
      isOneOfThem <- isOneOfThemRecorded.value
      boundsRecorded = characterised.flatMap(record.secondHalf)

      maxCasesRecorded = isOneOfThemRecorded.flatMap(record.generalise(_, List(x, y)))
      maxCases <- maxCasesRecorded.value
      maxAboveLeftRecorded =
        boundsRecorded.flatMap(record.firstHalf).flatMap(record.generalise(_, List(x, y)))
      maxAboveLeft <- maxAboveLeftRecorded.value
      maxAboveRightRecorded =
        boundsRecorded.flatMap(record.secondHalf).flatMap(record.generalise(_, List(x, y)))
      maxAboveRight <- maxAboveRightRecorded.value
      maxLeastRecorded =
        isOneOfThemRecorded.flatMap(greatestIsLeast(record, logic, withMax, notation, _))
      maxLeast <- maxLeastRecorded.value

      /* --------------------------------------------------------------- min */

      minBody <- Parser.term(withMax, notation, s"\\x:real. \\y:real. x + y - $MaxName x y")
      minDefined <- LogicError.lift(Kernel.defineConstant(withMax, MinName, minBody))
      (withMin, minDefinition) = minDefined
      minUnfolded <- Conv.unfold(minDefinition, List(x, y))

      minCasesRecorded = isOneOfThemRecorded.flatMap(
        lesserCases(record, logic, ring, withMin, notation, _, minUnfolded)
      )
      minCases <- minCasesRecorded.value
      minBelowLeftRecorded = maxAboveRightRecorded.flatMap(
        lesserBelow(record, logic, ring, withMin, notation, toZero, fromZero, minUnfolded, _, x, y)
      )
      minBelowLeft <- minBelowLeftRecorded.value
      minBelowRightRecorded = maxAboveLeftRecorded.flatMap(
        lesserBelow(record, logic, ring, withMin, notation, toZero, fromZero, minUnfolded, _, y, x)
      )
      minBelowRight <- minBelowRightRecorded.value
      minPlusMaxRecorded = sumOfBoth(record, logic, ring, withMin, notation, minUnfolded)
      minPlusMax <- minPlusMaxRecorded.value

      /* --------------------------------------------------------------- abs */

      absBody <- Parser.term(withMin, notation, s"\\x:real. $MaxName x (-x)")
      absDefined <- LogicError.lift(Kernel.defineConstant(withMin, AbsName, absBody))
      (withAbs, absDefinition) = absDefined
      absUnfolded <- Conv.unfold(absDefinition, List(x))
      absFolded <- Conv.sym(absUnfolded)

      negated <- Parser.term(withAbs, notation, "-x:real")
      // The three facts about `abs` are the three about `max` at `x` and `-x`, with the definition
      // folded back in. One shape, written once and applied to each.
      atNegation = (about: Recorded[Kernel.Thm]) =>
        about.flatMap(fact =>
          for {
            instance <- record.specialise(fact, List(x, negated))
            folded <- record.rewriteIn(s"the definition of $AbsName", Vector(absFolded), instance)
            general <- record.generalise(folded, List(x))
          } yield general
        )
      absCasesRecorded = atNegation(maxCasesRecorded)
      absCases <- absCasesRecorded.value
      absAboveRecorded = atNegation(maxAboveLeftRecorded)
      absAbove <- absAboveRecorded.value
      absAboveNegationRecorded = atNegation(maxAboveRightRecorded)
      absAboveNegation <- absAboveNegationRecorded.value

      absNonNegativeRecorded = absAboveRecorded.flatMap(above =>
        absAboveNegationRecorded.flatMap(negation =>
          distanceNonNegative(
            record,
            ring,
            order,
            withAbs,
            notation,
            toZero,
            addNonNegatives,
            cancelNonNegative,
            above,
            negation
          )
        )
      )
      absNonNegative <- absNonNegativeRecorded.value
      absZeroRecorded = absAboveRecorded.flatMap(above =>
        absAboveNegationRecorded.flatMap(negation =>
          distanceZero(record, ring, withAbs, notation, toZero, antisymmetric, above, negation)
        )
      )
      absZero <- absZeroRecorded.value
      triangleRecorded = absCasesRecorded.flatMap(cases =>
        absAboveRecorded.flatMap(above =>
          absAboveNegationRecorded.flatMap(negation =>
            triangleInequality(
              record,
              logic,
              ring,
              withAbs,
              notation,
              addBounds,
              cases,
              above,
              negation
            )
          )
        )
      )
      triangle <- triangleRecorded.value

      /* ------------------------------------------------- the sign of abs, and what it unlocks */

      multiplyNonNegatives <- order.fact(Order.MultiplyNonNegatives)
      ltOfNotLe <- order.fact(Order.LtOfNotLe)

      ofNonNegativeRecorded = absCasesRecorded.flatMap(cases =>
        absNonNegativeRecorded.flatMap(nonNegative =>
          distanceOfNonNegative(
            record, logic, ring, withAbs, notation, cases, nonNegative, antisymmetric, fromZero)
        )
      )
      ofNonNegative <- ofNonNegativeRecorded.value
      ofNonPositiveRecorded = absCasesRecorded.flatMap(cases =>
        absNonNegativeRecorded.flatMap(nonNegative =>
          distanceOfNonPositive(record, logic, ring, withAbs, notation, cases, nonNegative, antisymmetric)
        )
      )
      ofNonPositive <- ofNonPositiveRecorded.value
      multiplicativeRecorded = ofNonNegativeRecorded.flatMap(positive =>
        ofNonPositiveRecorded.flatMap(negative =>
          distanceOfProduct(
            record, logic, classical, ring, withAbs, notation, positive, negative,
            multiplyNonNegatives, toZero, fromZero, ltOfNotLe, ofLt)
        )
      )
      multiplicative <- multiplicativeRecorded.value

      /* --------------------------------------------------------------- sgn */

      signNamed = for {
        existence <- signExists(record, logic, reals, withAbs, notation)
        chosen <- record.step("name it by choice", Some(SignName), Vector(existence))(
          classical.witness(existence)
        )
        beta <- record.step("beta reduce", None, Vector.empty)(Conv.betaRoot(chosen.conclusion))
        reduced <- record.replace(beta, chosen)
        selected <- Recorded.quiet(chosen.conclusion match {
          case App(_, term) => Right(term)
          case other => Left(NotOfForm("a predicate applied to what was chosen", other))
        })
        signBody <- Recorded.quiet(LogicError.lift(Term.abs(x, selected)))
        defined <- Recorded.quiet(
          LogicError.lift(Kernel.defineConstant(withAbs, SignName, signBody))
        )
        signUnfolded <- Recorded.quiet(Conv.unfold(defined._2, List(x)))
        signFolded <- Recorded.quiet(Conv.sym(signUnfolded))
        characterisation <- record.rewriteIn(
          s"the definition of $SignName",
          Vector(signFolded),
          reduced
        )
      } yield (defined._1, defined._2, characterisation)
      signNames <- signNamed.value
      (withSign, signDefinition, _) = signNames

      signRecorded = signFacts(record, logic, reals, withSign, notation, signNamed.map(_._3))
      signNegativeValue <- signRecorded._1.value
      signZeroValue <- signRecorded._2.value
      signPositiveValue <- signRecorded._3.value
    } yield new Magnitude(
      order,
      classical,
      withSign,
      notation,
      logic,
      Map(
        MaxName -> maxDefinition,
        MinName -> minDefinition,
        AbsName -> absDefinition,
        SignName -> signDefinition
      ),
      Map(
        MaxCases -> maxCases,
        MaxAboveLeft -> maxAboveLeft,
        MaxAboveRight -> maxAboveRight,
        MaxLeast -> maxLeast,
        MinCases -> minCases,
        MinBelowLeft -> minBelowLeft,
        MinBelowRight -> minBelowRight,
        MinPlusMax -> minPlusMax,
        AbsCases -> absCases,
        AbsAbove -> absAbove,
        AbsAboveNegation -> absAboveNegation,
        AbsNonNegative -> absNonNegative,
        AbsZero -> absZero,
        Triangle -> triangle,
        OfNonNegative -> ofNonNegative,
        OfNonPositive -> ofNonPositive,
        Multiplicative -> multiplicative,
        SignNegative -> signNegativeValue,
        SignZero -> signZeroValue,
        SignPositive -> signPositiveValue
      ),
      Map(
        MaxCases -> maxCasesRecorded.script.tidy,
        MaxAboveLeft -> maxAboveLeftRecorded.script.tidy,
        MaxAboveRight -> maxAboveRightRecorded.script.tidy,
        MaxLeast -> maxLeastRecorded.script.tidy,
        MinCases -> minCasesRecorded.script.tidy,
        MinBelowLeft -> minBelowLeftRecorded.script.tidy,
        MinBelowRight -> minBelowRightRecorded.script.tidy,
        MinPlusMax -> minPlusMaxRecorded.script.tidy,
        AbsCases -> absCasesRecorded.script.tidy,
        AbsAbove -> absAboveRecorded.script.tidy,
        AbsAboveNegation -> absAboveNegationRecorded.script.tidy,
        AbsNonNegative -> absNonNegativeRecorded.script.tidy,
        AbsZero -> absZeroRecorded.script.tidy,
        Triangle -> triangleRecorded.script.tidy,
        OfNonNegative -> ofNonNegativeRecorded.script.tidy,
        OfNonPositive -> ofNonPositiveRecorded.script.tidy,
        Multiplicative -> multiplicativeRecorded.script.tidy,
        SignNegative -> signRecorded._1.script.tidy,
        SignZero -> signRecorded._2.script.tidy,
        SignPositive -> signRecorded._3.script.tidy
      )
    )
  }

  /* ------------------------------------------------------------- existence */

  /**
   * `|- ?m. (m = x \/ m = y) /\ (x <= m /\ y <= m)`, over free `x` and `y`.
   *
   * The one thing the sixteen axioms do say about a greatest of two numbers, and the whole of what
   * the definition of `max` rests on. `LT_TOTAL` splits three ways and every branch hands over the
   * larger of the two as the witness, so each of the three is the same three obligations at a
   * different term: that the witness is one of the pair, which is reflexivity on one side of the
   * disjunction; that it is above itself, which is reflexivity again through `LE_OF_EQ`; and that it
   * is above the other one, which is the branch's own hypothesis through `LE_OF_LT` or `LE_OF_EQ`.
   *
   * The disjuncts are read off the trichotomy instance rather than parsed a second time. A
   * re-parsed disjunct that differed from the axiom's by a single node would make `disjElim` refuse,
   * and the refusal would say nothing about which of the two spellings was wrong.
   */
  private def greatestExists(
    record: Recorder,
    logic: Logic,
    reals: RealTheory,
    ofLt: Kernel.Thm,
    ofEq: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)
    val sameX = record.reflexivity(x)
    val sameY = record.reflexivity(y)

    /** The three obligations at one witness, packed the way the predicate wants them. */
    def body(
      isOneOfThem: Kernel.Thm,
      aboveLeft: Kernel.Thm,
      aboveRight: Kernel.Thm
    ): Recorded[Kernel.Thm] =
      record.both(aboveLeft, aboveRight).flatMap(record.both(isOneOfThem, _))

    for {
      trichotomy <- record.quoted("the order is total")(reals.axiom("LT_TOTAL"))
      statement <- Recorded.quiet(reals.proposition(Greatest))
      predicate <- Recorded.quiet(
        logic
          .destExistsPredicate(statement)
          .toRight(NotOfForm("an existential quantification", statement))
      )

      cases <- record.specialise(trichotomy, List(x, y))
      firstSplit <- Recorded.quiet(
        logic
          .destDisj(cases.conclusion)
          .toRight(NotOfForm("a three-way trichotomy", cases.conclusion))
      )
      (below, rest) = firstSplit
      secondSplit <- Recorded.quiet(
        logic.destDisj(rest).toRight(NotOfForm("a two-way disjunction", rest))
      )
      (equated, above) = secondSplit

      isY <- Recorded.quiet(reals.proposition("y:real = x:real \\/ y:real = y"))
      rightParts <- Recorded.quiet(
        logic.destDisj(isY).toRight(NotOfForm("a disjunction", isY))
      )
      onTheRight <- record.orElseBefore(rightParts._1, sameY)
      isX <- Recorded.quiet(reals.proposition("x:real = x \\/ x:real = y:real"))
      leftParts <- Recorded.quiet(
        logic.destDisj(isX).toRight(NotOfForm("a disjunction", isX))
      )
      onTheLeft <- record.orElse(leftParts._2, sameX)

      reflexiveX <- record.specialise(ofEq, List(x, x)).flatMap(record.modusPonens(_, sameX))
      reflexiveY <- record.specialise(ofEq, List(y, y)).flatMap(record.modusPonens(_, sameY))

      // `x < y`: the witness is `y`, and the hypothesis is what puts `x` below it.
      belowAssumed <- record.assume(below)
      belowGives <- record.specialise(ofLt, List(x, y)).flatMap(record.modusPonens(_, belowAssumed))
      first <- body(onTheRight, belowGives, reflexiveY)
        .flatMap(record.witnessed(predicate, y, _))

      // `x = y`: the witness is `y` again, and the hypothesis is an equality this time.
      equatedAssumed <- record.assume(equated)
      equatedGives <- record
        .specialise(ofEq, List(x, y))
        .flatMap(record.modusPonens(_, equatedAssumed))
      second <- body(onTheRight, equatedGives, reflexiveY)
        .flatMap(record.witnessed(predicate, y, _))

      // `y < x`: the witness is `x`, and the two bounds swap places.
      aboveAssumed <- record.assume(above)
      aboveGives <- record.specialise(ofLt, List(y, x)).flatMap(record.modusPonens(_, aboveAssumed))
      third <- body(onTheLeft, reflexiveX, aboveGives)
        .flatMap(record.witnessed(predicate, x, _))

      tail <- record.assume(rest)
      fromTail <- record.caseSplit(tail, second, third)
      result <- record.caseSplit(cases, first, fromTail)
    } yield result
  }

  /**
   * `|- ?s. (x < 0 /\ s = -1) \/ ((x = 0 /\ s = 0) \/ (0 < x /\ s = 1))`, over free `x`.
   *
   * The same shape as [[greatestExists]] one case wider, and the reason `sgn` cannot be assembled
   * out of `max` the way `min` and `abs` are: three answers cannot be a combination of a two-way
   * operation, so this is a second existence proof and a second use of the choice operator. It
   * costs no further axiom, choice already being in the theory, and it is the second use rather
   * than the first, which is the honest way to describe it.
   *
   * Each branch of `LT_TOTAL` at `x` and `0` hands over the numeral its case names and proves the
   * conjunction it belongs to; the disjuncts the branch does *not* prove are read off the predicate
   * applied to that numeral, so the disjunction assembled is the one the predicate wants to the
   * node rather than a re-parsed spelling of it.
   */
  private def signExists(
    record: Recorder,
    logic: Logic,
    reals: RealTheory,
    theory: Theory,
    notation: Notation
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)

    /** The three disjuncts of the predicate at one witness, as terms. */
    def disjunctsAt(predicate: Term, witness: Term): Either[LogicError, (Term, Term, Term)] =
      for {
        applied <- LogicError.lift(Term.app(predicate, witness))
        reduced <- Term.betaReduce(applied).toRight(NotOfForm("a redex", applied))
        outer <- logic.destDisj(reduced).toRight(NotOfForm("a three-way disjunction", reduced))
        inner <- logic
          .destDisj(outer._2)
          .toRight(NotOfForm("a two-way disjunction", outer._2))
      } yield (outer._1, inner._1, inner._2)

    for {
      trichotomy <- record.quoted("the order is total")(reals.axiom("LT_TOTAL"))
      statement <- Recorded.quiet(Parser.proposition(theory, notation, Sign))
      predicate <- Recorded.quiet(
        logic
          .destExistsPredicate(statement)
          .toRight(NotOfForm("an existential quantification", statement))
      )

      zero <- Recorded.quiet(Parser.term(theory, notation, "0", real))
      one <- Recorded.quiet(Parser.term(theory, notation, "1", real))
      minusOne <- Recorded.quiet(Parser.term(theory, notation, "-1", real))

      cases <- record.specialise(trichotomy, List(x, zero))
      firstSplit <- Recorded.quiet(
        logic
          .destDisj(cases.conclusion)
          .toRight(NotOfForm("a three-way trichotomy", cases.conclusion))
      )
      (below, rest) = firstSplit
      secondSplit <- Recorded.quiet(
        logic.destDisj(rest).toRight(NotOfForm("a two-way disjunction", rest))
      )
      (equated, above) = secondSplit

      // `x < 0`: the answer is `-1`, and it is the first of the three disjuncts.
      belowAssumed <- record.assume(below)
      atMinusOne <- Recorded.quiet(disjunctsAt(predicate, minusOne))
      belowTail <- Recorded.quiet(logic.mkDisj(atMinusOne._2, atMinusOne._3))
      first <- record
        .both(belowAssumed, record.reflexivity(minusOne))
        .flatMap(record.orElse(belowTail, _))
        .flatMap(record.witnessed(predicate, minusOne, _))

      // `x = 0`: the answer is `0`, and it is the second, so it goes into the tail first.
      equatedAssumed <- record.assume(equated)
      atZero <- Recorded.quiet(disjunctsAt(predicate, zero))
      second <- record
        .both(equatedAssumed, record.reflexivity(zero))
        .flatMap(record.orElse(atZero._3, _))
        .flatMap(record.orElseBefore(atZero._1, _))
        .flatMap(record.witnessed(predicate, zero, _))

      // `0 < x`: the answer is `1`, the last of the three.
      aboveAssumed <- record.assume(above)
      atOne <- Recorded.quiet(disjunctsAt(predicate, one))
      third <- record
        .both(aboveAssumed, record.reflexivity(one))
        .flatMap(record.orElseBefore(atOne._2, _))
        .flatMap(record.orElseBefore(atOne._1, _))
        .flatMap(record.witnessed(predicate, one, _))

      tail <- record.assume(rest)
      fromTail <- record.caseSplit(tail, second, third)
      result <- record.caseSplit(cases, first, fromTail)
    } yield result
  }

  /* -------------------------------------------------------------- the facts */

  /**
   * `|- !x y z. x <= z ==> y <= z ==> max x y <= z`.
   *
   * The least of the upper bounds, from the fact that `max x y` is one of the two: whichever of
   * them it is, that one is already below `z` by hypothesis, so the conclusion is the hypothesis
   * transported along an equation. No order reasoning happens at all, which is worth noticing:
   * being *least* among the upper bounds is a consequence of being one of the pair, and the two
   * bounding facts play no part in it.
   */
  private def greatestIsLeast(
    record: Recorder,
    logic: Logic,
    theory: Theory,
    notation: Notation,
    isOneOfThem: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)
    val z = Term.variable("z", real)

    for {
      first <- Recorded.quiet(Parser.proposition(theory, notation, "x:real <= z:real"))
      firstAssumed <- record.assume(first)
      second <- Recorded.quiet(Parser.proposition(theory, notation, "y:real <= z:real"))
      secondAssumed <- record.assume(second)

      split <- Recorded.quiet(
        logic
          .destDisj(isOneOfThem.conclusion)
          .toRight(NotOfForm("a disjunction", isOneOfThem.conclusion))
      )
      (isLeft, isRight) = split

      // In each branch the equation says what `max x y` is, and the bound on that term is already
      // assumed, so the step is congruence on `<=` and nothing more.
      leftAssumed <- record.assume(isLeft)
      whenLeft <- record
        .symmetry(leftAssumed)
        .flatMap(equation =>
          record.rewriteSides(equation, record.reflexivity(z), firstAssumed)
        )
      rightAssumed <- record.assume(isRight)
      whenRight <- record
        .symmetry(rightAssumed)
        .flatMap(equation =>
          record.rewriteSides(equation, record.reflexivity(z), secondAssumed)
        )

      result <- record.caseSplit(isOneOfThem, whenLeft, whenRight)
      innerDischarged <- record.discharge(second, result)
      outerDischarged <- record.discharge(first, innerDischarged)
      general <- record.generalise(outerDischarged, List(x, y, z))
    } yield general
  }

  /**
   * `|- !x y. min x y = x \/ min x y = y`.
   *
   * The mirror of [[MaxCases]], and it needs no second case analysis of its own: `min x y` is
   * `x + y - max x y` by definition, so in the branch where `max x y` is `x` the definition
   * collapses to `y` and in the other to `x`, each by one ring identity. The disjuncts come out in
   * the other order, which is why the two `disjIntro` calls are the way round they are.
   */
  private def lesserCases(
    record: Recorder,
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    isOneOfThem: Kernel.Thm,
    minUnfolded: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      split <- Recorded.quiet(
        logic
          .destDisj(isOneOfThem.conclusion)
          .toRight(NotOfForm("a disjunction", isOneOfThem.conclusion))
      )
      (isLeft, isRight) = split

      isEitherX <- Recorded.quiet(
        Parser.proposition(theory, notation, s"$MinName (x:real) (y:real) = x")
      )
      isEitherY <- Recorded.quiet(
        Parser.proposition(theory, notation, s"$MinName (x:real) (y:real) = y")
      )

      // The definition read at these two arguments, said once so that the two branches below can
      // point at it instead of printing it as a sequent nobody introduced.
      unfolded <- record.quoted(s"the definition of $MinName at x and y")(Right(minUnfolded))

      leftAssumed <- record.assume(isLeft)
      atLeft <- record.rewriteIn("what this branch says", Vector(leftAssumed), unfolded)
      leftCollapses <- record.procedure("RING", "x + y - x = y")(
        ring.prove("x:real + y:real - x = y")
      )
      whenLeft <- record
        .chain(atLeft, leftCollapses)
        .flatMap(record.orElseBefore(isEitherX, _))

      rightAssumed <- record.assume(isRight)
      atRight <- record.rewriteIn("what this branch says", Vector(rightAssumed), unfolded)
      rightCollapses <- record.procedure("RING", "x + y - y = x")(
        ring.prove("x:real + y:real - y = x")
      )
      whenRight <- record
        .chain(atRight, rightCollapses)
        .flatMap(record.orElse(isEitherY, _))

      result <- record.caseSplit(isOneOfThem, whenLeft, whenRight)
      general <- record.generalise(result, List(x, y))
    } yield general
  }

  /**
   * `|- !x y. min x y <= near`, where `near` is whichever of the two the bound is about.
   *
   * One derivation for both halves, because the two differ only in which argument the bound is
   * stated about and which of the two `max` facts it comes from. The chain is: the *other* argument
   * is below `max x y`, so `max x y - far` is at least zero, and that difference is `near - min x y`
   * by ring reasoning once `min x y` is unfolded. Then the non-strict order comes back out of the
   * form `0 <= e`.
   *
   * The ring step is the interesting one and it is where the definition of `min` earns its keep:
   * `near - (x + y - max x y) = max x y - far` is an identity of a commutative ring in three atoms,
   * one of which is `max x y`. [[Ring]] has never heard of `max` and does not need to, an
   * application it cannot take apart being an atom, which is the same reading `Series` relies on for
   * `Sum`. Note that the unfolded body stays `x + y - max x y` whichever way round `near` and `far`
   * are: what the two halves differ in is the side of the identity they are read from.
   */
  private def lesserBelow(
    record: Recorder,
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    toZero: Kernel.Thm,
    fromZero: Kernel.Thm,
    minUnfolded: Kernel.Thm,
    otherIsBelowGreatest: Kernel.Thm,
    near: FVar,
    far: FVar
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      below <- record.specialise(otherIsBelowGreatest, List(x, y))
      greater <- Recorded.quiet(Parser.term(theory, notation, s"$MaxName (x:real) (y:real)"))
      lesser <- Recorded.quiet(Parser.term(theory, notation, s"$MinName (x:real) (y:real)"))

      gap <- record.specialise(toZero, List(far, greater)).flatMap(record.modusPonens(_, below))

      difference <- Recorded.quiet(
        Parser.term(theory, notation, s"${near.name} - $MinName (x:real) (y:real)")
      )
      rule <- Recorded.quiet(Rewrite.Rule.of(logic, minUnfolded))
      unfoldedDifference <- record.rewrite(s"the definition of $MinName", rule, difference)
      claim <- Recorded.quiet(
        Parser.proposition(
          theory,
          notation,
          s"${near.name} - (x:real + y:real - $MaxName x y) = $MaxName x y - ${far.name}"
        )
      )
      rearranged <- record.procedure("RING", Show.show(notation, claim))(ring.prove(claim))
      asGap <- record.chain(unfoldedDifference, rearranged)
      backwards <- record.symmetry(asGap)
      onGoal <- record.rewriteRight(gap, backwards)

      result <- record
        .specialise(fromZero, List(lesser, near))
        .flatMap(record.modusPonens(_, onGoal))
      general <- record.generalise(result, List(x, y))
    } yield general
  }

  /**
   * `|- !x y. min x y + max x y = x + y`.
   *
   * The definition of `min` said as a fact about the pair, which is a single ring identity once
   * `min x y` is unfolded: `(x + y - max x y) + max x y = x + y` in the two atoms `x`, `y` and the
   * atom `max x y`.
   */
  private def sumOfBoth(
    record: Recorder,
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    minUnfolded: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      sum <- Recorded.quiet(
        Parser.term(theory, notation, s"$MinName (x:real) (y:real) + $MaxName x y")
      )
      rule <- Recorded.quiet(Rewrite.Rule.of(logic, minUnfolded))
      unfolded <- record.rewrite(s"the definition of $MinName", rule, sum)
      claim <- Recorded.quiet(
        Parser.proposition(
          theory,
          notation,
          s"(x:real + y:real - $MaxName x y) + $MaxName x y = x + y"
        )
      )
      collapses <- record.procedure("RING", Show.show(notation, claim))(ring.prove(claim))
      result <- record.chain(unfolded, collapses)
      general <- record.generalise(result, List(x, y))
    } yield general
  }

  /**
   * `|- !x. 0 <= abs x`.
   *
   * Not a case analysis, which is worth saying because the obvious proof is one. Both bounds are
   * already there, `x <= abs x` and `-x <= abs x`, so moving each to the form `0 <= e` and adding
   * them gives `0 <= 2 * abs x` in one ring step, and cancelling a positive numeral is
   * `CANCEL_NONNEG` with `0 < 2` from the numerals. The two branches of `ABS_CASES` never appear,
   * so nothing here has to know which of `x` and `-x` the value is.
   */
  private def distanceNonNegative(
    record: Recorder,
    ring: Ring,
    order: Order,
    theory: Theory,
    notation: Notation,
    toZero: Kernel.Thm,
    addNonNegatives: Kernel.Thm,
    cancelNonNegative: Kernel.Thm,
    absAbove: Kernel.Thm,
    absAboveNegation: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)

    for {
      distance <- Recorded.quiet(Parser.term(theory, notation, s"$AbsName (x:real)"))
      negated <- Recorded.quiet(Parser.term(theory, notation, "-x:real"))
      two <- Recorded.quiet(Parser.term(theory, notation, "2", real))

      fromAbove <- record.specialise(absAbove, List(x))
      firstGap <- record
        .specialise(toZero, List(x, distance))
        .flatMap(record.modusPonens(_, fromAbove))
      fromBelow <- record.specialise(absAboveNegation, List(x))
      secondGap <- record
        .specialise(toZero, List(negated, distance))
        .flatMap(record.modusPonens(_, fromBelow))

      firstDifference <- Recorded.quiet(Parser.term(theory, notation, s"$AbsName (x:real) - x"))
      secondDifference <- Recorded.quiet(Parser.term(theory, notation, s"$AbsName (x:real) - -x"))
      summed <- record
        .specialise(addNonNegatives, List(firstDifference, secondDifference))
        .flatMap(record.modusPonens(_, firstGap))
        .flatMap(record.modusPonens(_, secondGap))

      claim <- Recorded.quiet(
        Parser.proposition(
          theory,
          notation,
          s"($AbsName (x:real) - x) + ($AbsName x - -x) = 2 * $AbsName x"
        )
      )
      doubled <- record.procedure("RING", Show.show(notation, claim))(ring.prove(claim))
      onGoal <- record.rewriteRight(summed, doubled)

      positiveTwo <- record.quoted("the numerals give 0 < 2")(order.positive(2))
      result <- record
        .specialise(cancelNonNegative, List(two, distance))
        .flatMap(record.modusPonens(_, positiveTwo))
        .flatMap(record.modusPonens(_, onGoal))
      general <- record.generalise(result, List(x))
    } yield general
  }

  /**
   * `|- !x. abs x = 0 ==> x = 0`.
   *
   * Antisymmetry on the two bounds, with the hypothesis rewriting `abs x` away in both of them:
   * `x <= abs x` becomes `x <= 0`, and `-x <= abs x` becomes `-x <= 0`, which is `0 <= x` after one
   * ring identity through the form `0 <= e`. Two bounds meeting is `LE_ANTISYMMETRIC` and that is
   * the whole proof.
   */
  private def distanceZero(
    record: Recorder,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    toZero: Kernel.Thm,
    antisymmetric: Kernel.Thm,
    absAbove: Kernel.Thm,
    absAboveNegation: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)

    for {
      premise <- Recorded.quiet(Parser.proposition(theory, notation, s"$AbsName (x:real) = 0"))
      assumed <- record.assume(premise)

      zero <- Recorded.quiet(Parser.term(theory, notation, "0", real))
      negated <- Recorded.quiet(Parser.term(theory, notation, "-x:real"))

      belowZero <- record
        .specialise(absAbove, List(x))
        .flatMap(record.rewriteIn("the hypothesis", Vector(assumed), _))
      negationBelow <- record
        .specialise(absAboveNegation, List(x))
        .flatMap(record.rewriteIn("the hypothesis", Vector(assumed), _))

      gap <- record
        .specialise(toZero, List(negated, zero))
        .flatMap(record.modusPonens(_, negationBelow))
      restores <- record.procedure("RING", "0 - -x = x")(ring.prove("0 - -x:real = x"))
      aboveZero <- record.rewriteRight(gap, restores)

      result <- record
        .specialise(antisymmetric, List(x, zero))
        .flatMap(record.modusPonens(_, belowZero))
        .flatMap(record.modusPonens(_, aboveZero))
      discharged <- record.discharge(premise, result)
      general <- record.generalise(discharged, List(x))
    } yield general
  }

  /**
   * `|- F`, from a term said to be equal to zero and on one side of it.
   *
   * Both halves of the same refusal: `x = 0` rewrites `x < 0` and `0 < x` alike into `0 < 0`, which
   * `LT_IRREFLEXIVE` at zero refuses. Written once because the two case pairs it settles, the
   * negative against the zero and the positive against the zero, differ only in which inequality is
   * handed in.
   */
  private def notBesideZero(
    record: Recorder,
    neverAtZero: Kernel.Thm,
    inequality: Kernel.Thm,
    equated: Kernel.Thm
  ): Recorded[Kernel.Thm] =
    for {
      absurd <- record.rewriteIn("what this branch says", Vector(equated), inequality)
      result <- record.contradiction(neverAtZero, absurd)
    } yield result

  /**
   * `|- F`, from a term said to be both below and above zero.
   *
   * Transitivity through zero gives `x < x`, which `LT_IRREFLEXIVE` at `x` refuses. It is the third
   * of the three pairs a three-way split has to rule out, and the only one that is not a rewrite.
   */
  private def notOnBothSides(
    record: Recorder,
    transitive: Kernel.Thm,
    neverAtPoint: Kernel.Thm,
    point: Term,
    zero: Term,
    below: Kernel.Thm,
    above: Kernel.Thm
  ): Recorded[Kernel.Thm] =
    for {
      cycle <- record.specialise(transitive, List(point, zero, point))
      pair <- record.both(below, above)
      absurd <- record.modusPonens(cycle, pair)
      result <- record.contradiction(neverAtPoint, absurd)
    } yield result

  /**
   * The three values of `sgn`, from the disjunction that characterises it.
   *
   * One case analysis per fact, and in every one of them exactly one branch proves the goal while
   * the other two are impossible: the branch's own case and the fact's hypothesis cannot both hold,
   * so the goal follows from falsity. That is why there are nine pieces below and only three of
   * them are the answer. It is also why the three facts are stated as implications rather than as
   * one equation: `sgn x` is a single term, and which numeral it equals is decided by where `x`
   * sits, so a statement without a hypothesis would have to be an equation between `sgn x` and a
   * case expression. `Classical.COND` is one since 2026-09-12 and this file has not been restated
   * around it, which is a decision about scope and not a limit any more.
   *
   * The six impossible branches use three arguments between them, each twice, which is what
   * [[notBesideZero]] and [[notOnBothSides]] are.
   */
  private def signFacts(
    record: Recorder,
    logic: Logic,
    reals: RealTheory,
    theory: Theory,
    notation: Notation,
    characterised: Recorded[Kernel.Thm]
  ): (Recorded[Kernel.Thm], Recorded[Kernel.Thm], Recorded[Kernel.Thm]) = {
    val x = Term.variable("x", real)

    /**
     * Everything the three facts share, derived once and replayed into each account.
     *
     * The three are one case analysis read three ways, so a single `Recorded` prefix is the honest
     * shape: each of the accounts below opens with these lines and then diverges, and none of them
     * refers to a theorem it has not shown the reader.
     */
    val shared: Recorded[SignPieces] = for {
      characterisation <- characterised
      irreflexive <- record.quoted("nothing is below itself")(reals.axiom("LT_IRREFLEXIVE"))
      transitive <- record.quoted("the order is transitive")(reals.axiom("LT_TRANSITIVE"))
      zero <- Recorded.quiet(Parser.term(theory, notation, "0", real))
      neverAtPoint <- record.specialiseOne(x, irreflexive)
      neverAtZero <- record.specialiseOne(zero, irreflexive)

      outer <- Recorded.quiet(
        logic
          .destDisj(characterisation.conclusion)
          .toRight(NotOfForm("a three-way disjunction", characterisation.conclusion))
      )
      (isNegative, rest) = outer
      inner <- Recorded.quiet(
        logic.destDisj(rest).toRight(NotOfForm("a two-way disjunction", rest))
      )
      (isZero, isPositive) = inner

      negativeParts <- Recorded.quiet(
        logic.destConj(isNegative).toRight(NotOfForm("a conjunction", isNegative))
      )
      zeroParts <- Recorded.quiet(
        logic.destConj(isZero).toRight(NotOfForm("a conjunction", isZero))
      )
      positiveParts <- Recorded.quiet(
        logic.destConj(isPositive).toRight(NotOfForm("a conjunction", isPositive))
      )

      // The branch each case of the disjunction is, and what it says on its own.
      negativeBranch <- record.assume(isNegative)
      zeroBranch <- record.assume(isZero)
      positiveBranch <- record.assume(isPositive)
      inNegative <- record.firstHalf(negativeBranch)
      inZero <- record.firstHalf(zeroBranch)
      inPositive <- record.firstHalf(positiveBranch)
      answerNegative <- record.secondHalf(negativeBranch)
      answerZero <- record.secondHalf(zeroBranch)
      answerPositive <- record.secondHalf(positiveBranch)

      // The three hypotheses, assumed once and used in whichever fact is theirs.
      belowAssumed <- record.assume(negativeParts._1)
      equatedAssumed <- record.assume(zeroParts._1)
      aboveAssumed <- record.assume(positiveParts._1)
    } yield SignPieces(
      characterisation = characterisation,
      transitive = transitive,
      zero = zero,
      neverAtPoint = neverAtPoint,
      neverAtZero = neverAtZero,
      rest = rest,
      below = negativeParts._1,
      valueBelow = negativeParts._2,
      equated = zeroParts._1,
      valueEquated = zeroParts._2,
      above = positiveParts._1,
      valueAbove = positiveParts._2,
      inNegative = inNegative,
      inZero = inZero,
      inPositive = inPositive,
      answerNegative = answerNegative,
      answerZero = answerZero,
      answerPositive = answerPositive,
      belowAssumed = belowAssumed,
      equatedAssumed = equatedAssumed,
      aboveAssumed = aboveAssumed
    )

    // `x < 0 ==> sgn x = -1`
    val negative = shared.flatMap { held =>
      for {
        againstZero <- notBesideZero(record, held.neverAtZero, held.belowAssumed, held.inZero)
          .flatMap(record.fromFalsity(held.valueBelow, _))
        againstPositive <- notOnBothSides(
          record,
          held.transitive,
          held.neverAtPoint,
          x,
          held.zero,
          held.belowAssumed,
          held.inPositive
        ).flatMap(record.fromFalsity(held.valueBelow, _))
        tail <- record
          .assume(held.rest)
          .flatMap(record.caseSplit(_, againstZero, againstPositive))
        result <- record
          .caseSplit(held.characterisation, held.answerNegative, tail)
          .flatMap(record.discharge(held.below, _))
          .flatMap(record.generalise(_, List(x)))
      } yield result
    }

    // `x = 0 ==> sgn x = 0`
    val atZero = shared.flatMap { held =>
      for {
        againstNegative <- notBesideZero(record, held.neverAtZero, held.inNegative, held.equatedAssumed)
          .flatMap(record.fromFalsity(held.valueEquated, _))
        againstPositive <- notBesideZero(record, held.neverAtZero, held.inPositive, held.equatedAssumed)
          .flatMap(record.fromFalsity(held.valueEquated, _))
        tail <- record
          .assume(held.rest)
          .flatMap(record.caseSplit(_, held.answerZero, againstPositive))
        result <- record
          .caseSplit(held.characterisation, againstNegative, tail)
          .flatMap(record.discharge(held.equated, _))
          .flatMap(record.generalise(_, List(x)))
      } yield result
    }

    // `0 < x ==> sgn x = 1`
    val positive = shared.flatMap { held =>
      for {
        againstNegative <- notOnBothSides(
          record,
          held.transitive,
          held.neverAtPoint,
          x,
          held.zero,
          held.inNegative,
          held.aboveAssumed
        ).flatMap(record.fromFalsity(held.valueAbove, _))
        againstZero <- notBesideZero(record, held.neverAtZero, held.aboveAssumed, held.inZero)
          .flatMap(record.fromFalsity(held.valueAbove, _))
        tail <- record
          .assume(held.rest)
          .flatMap(record.caseSplit(_, againstZero, held.answerPositive))
        result <- record
          .caseSplit(held.characterisation, againstNegative, tail)
          .flatMap(record.discharge(held.above, _))
          .flatMap(record.generalise(_, List(x)))
      } yield result
    }

    (negative, atZero, positive)
  }

  /**
   * `|- !x. 0 <= x ==> abs x = x`, the first of the two facts this file's own docstring named as
   * missing rather than out of reach.
   *
   * [[AbsCases]] says `abs x` is one of the two and does not say which, so the sign is what
   * chooses. One branch is the conclusion already. The other assumes `abs x = -x`, which turns
   * [[AbsNonNegative]] into `0 <= -x`, and that against the hypothesis is antisymmetry: `x` is
   * zero, so both sides of the goal are zero and the branch closes by rewriting rather than by a
   * second argument about `abs`.
   */
  private def distanceOfNonNegative(
    record: Recorder,
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    absCases: Kernel.Thm,
    absNonNegative: Kernel.Thm,
    antisymmetric: Kernel.Thm,
    fromZero: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)

    for {
      premise <- Recorded.quiet(Parser.proposition(theory, notation, "0 <= x:real"))
      assumed <- record.assume(premise)
      zero <- Recorded.quiet(Parser.term(theory, notation, "0", real))

      split <- record.specialise(absCases, List(x))
      disjuncts <- Recorded.quiet(
        logic.destDisj(split.conclusion).toRight(NotOfForm("a disjunction", split.conclusion))
      )
      (isItself, isNegated) = disjuncts

      whenItself <- record.assume(isItself)

      negatedAssumed <- record.assume(isNegated)
      negationNonNegative <- record
        .specialise(absNonNegative, List(x))
        .flatMap(record.rewriteIn("the case", Vector(negatedAssumed), _))
      restores <- record.procedure("RING", "0 - x = -x")(ring.prove("0 - x:real = -x"))
      backwards <- record.symmetry(restores)
      asDifference <- record.rewriteIn("the difference", Vector(backwards), negationNonNegative)
      belowZero <- record
        .specialise(fromZero, List(x, zero))
        .flatMap(record.modusPonens(_, asDifference))
      isZero <- record
        .specialise(antisymmetric, List(x, zero))
        .flatMap(record.modusPonens(_, belowZero))
        .flatMap(record.modusPonens(_, assumed))
      atZero <- record.rewriteIn("x is zero", Vector(isZero), negatedAssumed)
      folded <- record.procedure("RING", "-0 = 0")(ring.prove("-(0:real) = 0"))
      collapsed <- record.rewriteRight(atZero, folded)
      whenNegated <- record
        .symmetry(isZero)
        .flatMap(back => record.rewriteIn("zero is x", Vector(back), collapsed))

      result <- record.caseSplit(split, whenItself, whenNegated)
      discharged <- record.discharge(premise, result)
      general <- record.generalise(discharged, List(x))
    } yield general
  }

  /**
   * `|- !x. x <= 0 ==> abs x = -x`, the other one, and the same argument with the branches
   * swapped.
   *
   * The branch that is the conclusion is the second disjunct here, and the one that has to work
   * is the first: `abs x = x` with [[AbsNonNegative]] gives `0 <= x`, which against the hypothesis
   * puts `x` at zero again. What differs from the fact above is only which of the two ring
   * identities is needed at the end, and they are `-0 = 0` in both cases because both sides
   * collapse to zero.
   */
  private def distanceOfNonPositive(
    record: Recorder,
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    absCases: Kernel.Thm,
    absNonNegative: Kernel.Thm,
    antisymmetric: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)

    for {
      premise <- Recorded.quiet(Parser.proposition(theory, notation, "x:real <= 0"))
      assumed <- record.assume(premise)
      zero <- Recorded.quiet(Parser.term(theory, notation, "0", real))

      split <- record.specialise(absCases, List(x))
      disjuncts <- Recorded.quiet(
        logic.destDisj(split.conclusion).toRight(NotOfForm("a disjunction", split.conclusion))
      )
      (isItself, isNegated) = disjuncts

      itselfAssumed <- record.assume(isItself)
      aboveZero <- record
        .specialise(absNonNegative, List(x))
        .flatMap(record.rewriteIn("the case", Vector(itselfAssumed), _))
      isZero <- record
        .specialise(antisymmetric, List(x, zero))
        .flatMap(record.modusPonens(_, assumed))
        .flatMap(record.modusPonens(_, aboveZero))
      atZero <- record.rewriteIn("x is zero", Vector(isZero), itselfAssumed)
      folded <- record.procedure("RING", "-0 = 0")(ring.prove("-(0:real) = 0"))
      negatedZero <- record.symmetry(folded)
      asNegation <- record.rewriteRight(atZero, negatedZero)
      whenItself <- record
        .symmetry(isZero)
        .flatMap(back => record.rewriteIn("zero is x", Vector(back), asNegation))

      whenNegated <- record.assume(isNegated)

      result <- record.caseSplit(split, whenItself, whenNegated)
      discharged <- record.discharge(premise, result)
      general <- record.generalise(discharged, List(x))
    } yield general
  }

  /**
   * `|- !x y. abs (x * y) = abs x * abs y`, which is what an estimate over a product wants and
   * what the two facts above were the obstacle to.
   *
   * Four cases, on the sign of each argument, and each one is the same three steps: the sign of
   * the product, the two distances rewritten by the facts above, and one ring identity to see
   * that the signed product is the product of the signed factors. Nothing here reasons about
   * `abs` at all once the signs are known, which is the point of having the two facts: they turn
   * every occurrence into a term of the ring.
   *
   * The split is `Classical.cases` on `0 <= x` and again on `0 <= y`, so it costs the choice
   * axiom, and the negative side of each is `LT_OF_NOT_LE` followed by `LE_OF_LT`. The order's own
   * trichotomy would give the same three cases at the same price and one more branch to write.
   *
   * `MUL_NONNEG_BOTH` is the only fact about products of signs this needs, and it is asked for at
   * the negated arguments where a factor is negative: `0 <= -x` and `0 <= -y` give `0 <= -x * -y`,
   * which is `0 <= x * y` by the ring, and that is how each of the four signs of the product is
   * reached without a lemma of its own.
   */
  private def distanceOfProduct(
    record: Recorder,
    logic: Logic,
    classical: Classical,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    ofNonNegative: Kernel.Thm,
    ofNonPositive: Kernel.Thm,
    multiplyNonNegatives: Kernel.Thm,
    toZero: Kernel.Thm,
    fromZero: Kernel.Thm,
    ltOfNotLe: Kernel.Thm,
    leOfLt: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    /** `0 <= -t` from `t <= 0`, which is `LE_TO_ZERO` and the ring folding `0 - t`. */
    def negationIsNonNegative(subject: Term, below: Kernel.Thm): Recorded[Kernel.Thm] =
      for {
        zero <- Recorded.quiet(Parser.term(theory, notation, "0", real))
        gap <- record.specialise(toZero, List(subject, zero)).flatMap(record.modusPonens(_, below))
        claim <- Recorded.quiet(
          Parser.proposition(theory, notation, s"0 - ${Show.show(notation, subject)} = -${Show.show(notation, subject)}")
        )
        folded <- record.procedure("RING", Show.show(notation, claim))(ring.prove(claim))
        result <- record.rewriteRight(gap, folded)
      } yield result

    /** `t <= 0` from `~(0 <= t)`, which is the negated side of each of the two splits. */
    def belowZeroFromRefusal(subject: Term, refused: Kernel.Thm): Recorded[Kernel.Thm] =
      for {
        zero <- Recorded.quiet(Parser.term(theory, notation, "0", real))
        strict <- record
          .specialise(ltOfNotLe, List(zero, subject))
          .flatMap(record.modusPonens(_, refused))
        result <- record
          .specialise(leOfLt, List(subject, zero))
          .flatMap(record.modusPonens(_, strict))
      } yield result

    /** `abs x * abs y = left * right` from the two distances, by congruence and not by rewriting. */
    def distancesAre(absX: Kernel.Thm, absY: Kernel.Thm): Recorded[Kernel.Thm] =
      for {
        times <- Recorded.quiet(
          Parser.term(theory, notation, "real_mul", Type.fun(real, Type.fun(real, real)))
        )
        distanceOfY <- Recorded.quiet(
          Term.destEq(absY.conclusion).map(_._1).toRight(NotOfForm("an equation", absY.conclusion))
        )
        headOfX <- Recorded.quiet(
          Term.destEq(absX.conclusion).map(_._2).toRight(NotOfForm("an equation", absX.conclusion))
        )
        onTheLeft <- record.step("congruence on the left factor", None, Vector(absX))(
          Conv.apTerm(times, absX).flatMap(Conv.apThm(_, distanceOfY))
        )
        applied <- Recorded.quiet(LogicError.lift(Term.app(times, headOfX)))
        onTheRight <- record.step("congruence on the right factor", None, Vector(absY))(
          Conv.apTerm(applied, absY)
        )
        result <- record.step("transitivity", None, Vector(onTheLeft, onTheRight))(
          Conv.trans(onTheLeft, onTheRight)
        )
      } yield result

    /**
     * One of the four cases: the sign of the product, the two distances, and the ring identity
     * between the signed product and the product of the signed factors.
     */
    def caseOf(
      productSign: Kernel.Thm,
      productIsNonNegative: Boolean,
      absX: Kernel.Thm,
      absY: Kernel.Thm,
      identity: String
    ): Recorded[Kernel.Thm] =
      for {
        product <- Recorded.quiet(Parser.term(theory, notation, "x:real * y:real", real))
        distanceOfTheProduct <-
          if (productIsNonNegative)
            record.specialise(ofNonNegative, List(product)).flatMap(record.modusPonens(_, productSign))
          else
            record.specialise(ofNonPositive, List(product)).flatMap(record.modusPonens(_, productSign))
        rearranged <- record.procedure("RING", identity)(ring.prove(identity))
        asProduct <- record.step("transitivity", None, Vector(distanceOfTheProduct, rearranged))(
          Conv.trans(distanceOfTheProduct, rearranged)
        )
        distances <- distancesAre(absX, absY)
        result <- record
          .symmetry(distances)
          .flatMap(back =>
            record.step("transitivity", None, Vector(asProduct, back))(Conv.trans(asProduct, back))
          )
      } yield result

    for {
      nonNegativeX <- Recorded.quiet(Parser.proposition(theory, notation, "0 <= x:real"))
      nonNegativeY <- Recorded.quiet(Parser.proposition(theory, notation, "0 <= y:real"))
      product <- Recorded.quiet(Parser.term(theory, notation, "x:real * y:real", real))
      negatedX <- Recorded.quiet(Parser.term(theory, notation, "-x:real", real))
      negatedY <- Recorded.quiet(Parser.term(theory, notation, "-y:real", real))
      zero <- Recorded.quiet(Parser.term(theory, notation, "0", real))

      assumedX <- record.assume(nonNegativeX)
      negatedGoalX <- Recorded.quiet(logic.mkNot(nonNegativeX))
      refusedX <- record.assume(negatedGoalX)
      belowX <- belowZeroFromRefusal(x, refusedX)
      assumedY <- record.assume(nonNegativeY)
      negatedGoalY <- Recorded.quiet(logic.mkNot(nonNegativeY))
      refusedY <- record.assume(negatedGoalY)
      belowY <- belowZeroFromRefusal(y, refusedY)

      absXPositive <- record.specialise(ofNonNegative, List(x)).flatMap(record.modusPonens(_, assumedX))
      absXNegative <- record.specialise(ofNonPositive, List(x)).flatMap(record.modusPonens(_, belowX))
      absYPositive <- record.specialise(ofNonNegative, List(y)).flatMap(record.modusPonens(_, assumedY))
      absYNegative <- record.specialise(ofNonPositive, List(y)).flatMap(record.modusPonens(_, belowY))

      negationOfX <- negationIsNonNegative(x, belowX)
      negationOfY <- negationIsNonNegative(y, belowY)

      // The four signs of the product, each `MUL_NONNEG_BOTH` at the arguments made non-negative
      // and then one ring identity to put the negations back where the goal has them.
      bothPositive <- record
        .specialise(multiplyNonNegatives, List(x, y))
        .flatMap(record.modusPonens(_, assumedX))
        .flatMap(record.modusPonens(_, assumedY))
      positiveTimesNegative <- for {
        raw <- record
          .specialise(multiplyNonNegatives, List(x, negatedY))
          .flatMap(record.modusPonens(_, assumedX))
          .flatMap(record.modusPonens(_, negationOfY))
        folded <- record.procedure("RING", "x * (-y) = 0 - x * y")(ring.prove("x:real * (-y:real) = 0 - x * y"))
        asGap <- record.rewriteRight(raw, folded)
        result <- record.specialise(fromZero, List(product, zero)).flatMap(record.modusPonens(_, asGap))
      } yield result
      negativeTimesPositive <- for {
        raw <- record
          .specialise(multiplyNonNegatives, List(negatedX, y))
          .flatMap(record.modusPonens(_, negationOfX))
          .flatMap(record.modusPonens(_, assumedY))
        folded <- record.procedure("RING", "(-x) * y = 0 - x * y")(ring.prove("(-x:real) * y:real = 0 - x * y"))
        asGap <- record.rewriteRight(raw, folded)
        result <- record.specialise(fromZero, List(product, zero)).flatMap(record.modusPonens(_, asGap))
      } yield result
      bothNegative <- for {
        raw <- record
          .specialise(multiplyNonNegatives, List(negatedX, negatedY))
          .flatMap(record.modusPonens(_, negationOfX))
          .flatMap(record.modusPonens(_, negationOfY))
        folded <- record.procedure("RING", "(-x) * (-y) = x * y")(ring.prove("(-x:real) * (-y:real) = x:real * y"))
        result <- record.rewriteRight(raw, folded)
      } yield result

      whenBothPositive <- caseOf(bothPositive, true, absXPositive, absYPositive, "x:real * y:real = x * y")
      whenPositiveNegative <- caseOf(
        positiveTimesNegative, false, absXPositive, absYNegative, "-(x:real * y:real) = x * (-y)")
      whenNegativePositive <- caseOf(
        negativeTimesPositive, false, absXNegative, absYPositive, "-(x:real * y:real) = (-x) * y")
      whenBothNegative <- caseOf(
        bothNegative, true, absXNegative, absYNegative, "x:real * y:real = (-x) * (-y)")

      withPositiveX <- record.step("cases on the sign of y", None, Vector(whenBothPositive, whenPositiveNegative))(
        classical.cases(nonNegativeY, whenBothPositive, whenPositiveNegative)
      )
      withNegativeX <- record.step("cases on the sign of y", None, Vector(whenNegativePositive, whenBothNegative))(
        classical.cases(nonNegativeY, whenNegativePositive, whenBothNegative)
      )
      result <- record.step("cases on the sign of x", None, Vector(withPositiveX, withNegativeX))(
        classical.cases(nonNegativeX, withPositiveX, withNegativeX)
      )
      general <- record.generalise(result, List(x, y))
    } yield general
  }

  /**
   * `|- !x y. abs (x + y) <= abs x + abs y`.
   *
   * The fact that makes `abs` worth having, and it is two applications of `Order.ADD_LE` and then
   * `ABS_CASES` on the sum. Both `x + y` and `-(x + y)` are below `abs x + abs y`: the first by
   * adding `x <= abs x` to `y <= abs y`, the second by adding the two negated bounds and one ring
   * identity to see that `-x + -y` is `-(x + y)`. Whichever of the two `abs (x + y)` turns out to
   * be, the bound for it is already proved, so the case analysis transports a bound rather than
   * proving two of them.
   *
   * That is why `ADD_LE` had to exist first. `LT_ADD` adds the same term to both sides of one
   * inequality and there is no way to reach "the sum of two bounds bounds the sum" from it in a
   * single step, which is the shape both halves of this proof are.
   */
  private def triangleInequality(
    record: Recorder,
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    addBounds: Kernel.Thm,
    absCases: Kernel.Thm,
    absAbove: Kernel.Thm,
    absAboveNegation: Kernel.Thm
  ): Recorded[Kernel.Thm] = {
    val x = Term.variable("x", real)
    val y = Term.variable("y", real)

    for {
      sum <- Recorded.quiet(Parser.term(theory, notation, "x:real + y:real"))
      distanceOfX <- Recorded.quiet(Parser.term(theory, notation, s"$AbsName (x:real)"))
      distanceOfY <- Recorded.quiet(Parser.term(theory, notation, s"$AbsName (y:real)"))
      bound <- Recorded.quiet(
        Parser.term(theory, notation, s"$AbsName (x:real) + $AbsName (y:real)")
      )
      negatedX <- Recorded.quiet(Parser.term(theory, notation, "-x:real"))
      negatedY <- Recorded.quiet(Parser.term(theory, notation, "-y:real"))

      aboveX <- record.specialise(absAbove, List(x))
      aboveY <- record.specialise(absAbove, List(y))
      aboveNegatedX <- record.specialise(absAboveNegation, List(x))
      aboveNegatedY <- record.specialise(absAboveNegation, List(y))

      // `x + y <= abs x + abs y`, which is one of the two disjuncts already.
      onTheSum <- record
        .specialise(addBounds, List(x, distanceOfX, y, distanceOfY))
        .flatMap(record.modusPonens(_, aboveX))
        .flatMap(record.modusPonens(_, aboveY))

      // `-(x + y) <= abs x + abs y`, which is the other, after the ring folds the two negations.
      onTheNegations <- record
        .specialise(addBounds, List(negatedX, distanceOfX, negatedY, distanceOfY))
        .flatMap(record.modusPonens(_, aboveNegatedX))
        .flatMap(record.modusPonens(_, aboveNegatedY))
      folded <- record.procedure("RING", "-x + -y = -(x + y)")(
        ring.prove("-x:real + -y:real = -(x + y)")
      )
      onTheNegatedSum <- record.rewriteSides(folded, record.reflexivity(bound), onTheNegations)

      split <- record.specialise(absCases, List(sum))
      disjuncts <- Recorded.quiet(
        logic
          .destDisj(split.conclusion)
          .toRight(NotOfForm("a disjunction", split.conclusion))
      )
      (isSum, isNegatedSum) = disjuncts

      sumAssumed <- record.assume(isSum)
      whenSum <- record
        .symmetry(sumAssumed)
        .flatMap(equation => record.rewriteSides(equation, record.reflexivity(bound), onTheSum))
      negatedAssumed <- record.assume(isNegatedSum)
      whenNegated <- record
        .symmetry(negatedAssumed)
        .flatMap(equation =>
          record.rewriteSides(equation, record.reflexivity(bound), onTheNegatedSum)
        )

      result <- record.caseSplit(split, whenSum, whenNegated)
      general <- record.generalise(result, List(x, y))
    } yield general
  }
}
