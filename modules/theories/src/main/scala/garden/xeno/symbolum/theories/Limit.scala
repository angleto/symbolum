package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What a sequence of reals converges to, which is the first analysis this repository has.
 *
 * `converges s l` is the epsilon-N statement and nothing more: past some index every term of `s` is
 * within every positive distance of `l`. `lim s` is the value, named by choice the way `NUM_GCD`
 * and `max` are, and pinned by [[Limit.Unique]]: where a sequence converges at all, `lim` is what
 * it converges to, and where it does not the term denotes and nothing here says what.
 *
 * == Why this is the missing piece and not one of several ==
 *
 * The reals have carried `COMPLETENESS` since the beginning and until 2026-09-13 nothing read it;
 * `Peano.NUM_ARCHIMEDES` was the first thing to spend it. What the axiom is **for** is convergence,
 * and convergence could not be said here at all: `docs/proving.md` has listed the transcendental
 * functions as the fourth thing to add since it was written, and the reason given each time is that
 * they need sequences. This is the sequences.
 *
 * [[Transcendental]] is the consumer it was written for and the two landed together, which is
 * `docs/adr/0007`'s rule about an axiom arriving in the commit whose derivation needs it, read for
 * a definition instead: a limit operator with no limit taken is a constant nobody has checked.
 *
 * == It costs no axiom, and one thing it does not do ==
 *
 * Both constants are definitions. `lim` reaches `select`, which the chain already pays for, so what
 * a development over this must believe is what it was before; `LimitSpec` asserts that as an
 * equality rather than as a ceiling, the way `CodingSpec` does.
 *
 * **Three facts here obtain a convergence and the rest move one.** [[Limit.MonotoneConverges]] is
 * the general instrument, an increasing sequence under a bound, and it is where `COMPLETENESS` is
 * spent a second time; [[Limit.Comparison]] is that theorem spent on the partial sums of a series;
 * [[Limit.Constant]] settles the sequence that does not move at all. Everything else takes a
 * convergence as a hypothesis and carries it somewhere, which is the vocabulary and the
 * bookkeeping.
 *
 * This paragraph said **nothing** here proved a convergence, and it said so for the day between
 * `MONOTONE_CONVERGES` landing and this sentence being written, with the next line naming that
 * theorem as what was still to come. A file's own summary of what it cannot do is the sentence
 * least likely to be reread when the file changes, and no test fails for it.
 *
 * That pair, [[Limit.Constant]] with [[Limit.Eventually]], is more than it looks: it settles every
 * sequence that stops moving, which is what a power series at zero is, and it is the whole of what
 * [[Transcendental]] can reach today. What [[Limit.Comparison]] adds is not reached from
 * [[Transcendental]] at all: the exponential's series wants a dominating one, and building it wants
 * `2^i <= 2 * i!`, which no development holds. What else it wanted and what has since landed are in
 * [[Limit.Comparison]], which is the one place here that carries them.
 *
 * == The epsilon principle is here rather than in `Order`, and that is an argument worth making ==
 *
 * [[Limit.BelowEveryPositive]] is a fact about the order on the reals and mentions neither constant
 * of this file, so `Order` is where a reader would look for it. It is here because it is what a
 * limit argument spends and nothing below has ever wanted it: three links down it would sit where
 * nothing cites it. If a second consumer appears below this, it moves, and the citation moves with
 * it.
 */
final class Limit private (
  val magnitude: Magnitude,
  val peano: Peano,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = magnitude.classical.logic
    .over(theory)
    .fold(
      error => throw new IllegalStateException(s"the logic does not extend: ${error.message}"),
      identity
    )

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /** `|- !x. 0 <= x ==> (!e. 0 < e ==> x < e) ==> x = 0`, the epsilon principle. */
  def belowEveryPositive: Either[LogicError, Kernel.Thm] = fact(Limit.BelowEveryPositive)

  /** `|- !c. converges (\n. c) c` */
  def constantSequence: Either[LogicError, Kernel.Thm] = fact(Limit.Constant)

  /** `|- !s a b. converges s a ==> converges s b ==> a = b` */
  def unique: Either[LogicError, Kernel.Thm] = fact(Limit.Unique)

  /** `|- !s l. converges s l ==> lim s = l` */
  def valueOfConverges: Either[LogicError, Kernel.Thm] = fact(Limit.ValueOfConverges)

  /** `|- !s t l N. (!n. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l` */
  def eventually: Either[LogicError, Kernel.Thm] = fact(Limit.Eventually)

  /** `|- !s. (!n. s n <= s (SUC n)) ==> !m n. NUM_LE m n ==> s m <= s n` */
  def monotoneBelow: Either[LogicError, Kernel.Thm] = fact(Limit.MonotoneBelow)

  /** `|- !s. (!n. s n <= s (SUC n)) ==> (?b. !n. s n <= b) ==> ?l. converges s l` */
  def monotoneConverges: Either[LogicError, Kernel.Thm] = fact(Limit.MonotoneConverges)

  /**
   * `|- !f g. (!n. 0 <= f n) ==> (!n. f n <= g n) ==> (?b. !n. Sum g n <= b)
   * ==> ?l. converges (Sum f) l`
   */
  def comparison: Either[LogicError, Kernel.Thm] = fact(Limit.Comparison)

  /** `|- !s l b N. converges s l ==> (!n. NUM_LE N n ==> s n <= b) ==> l <= b` */
  def belowBound: Either[LogicError, Kernel.Thm] = fact(Limit.BelowBound)

  /** `|- !s l b N. converges s l ==> (!n. NUM_LE N n ==> b <= s n) ==> b <= l` */
  def aboveBound: Either[LogicError, Kernel.Thm] = fact(Limit.AboveBound)

  /** `|- !s t a b. converges s a ==> converges t b ==> converges (\n. s n + t n) (a + b)` */
  def added: Either[LogicError, Kernel.Thm] = fact(Limit.Added)

  /** `|- !s a. converges s a ==> converges (\n. -(s n)) (-a)` */
  def negated: Either[LogicError, Kernel.Thm] = fact(Limit.Negated)

  /**
   * `|- !s t a b. converges s a ==> converges t b ==> converges (\n. s n * t n) (a * b)`
   */
  def multiplied: Either[LogicError, Kernel.Thm] = fact(Limit.Multiplied)

  /** `|- !f l. converges (Sum (\i. abs (f i))) l ==> ?m. converges (Sum f) m` */
  def absolute: Either[LogicError, Kernel.Thm] = fact(Limit.Absolute)

  /** `|- !f l. (!i. 0 <= f i) ==> converges (Sum f) l ==> !n. Sum f n <= l` */
  def belowLimit: Either[LogicError, Kernel.Thm] = fact(Limit.BelowLimit)

  /** `|- !f. (!i. 0 <= f i) ==> !m n. NUM_LE m n ==> Sum f m <= Sum f n` */
  def grows: Either[LogicError, Kernel.Thm] = fact(Limit.Grows)

  /** The `n`th partial Cauchy sum under the product of the two `n`th partial sums. */
  def cauchyBelowSquare: Either[LogicError, Kernel.Thm] = fact(Limit.CauchyBelowSquare)

  /** The product of the two `n`th partial sums under the partial Cauchy sum at `n + n`. */
  def squareBelowCauchy: Either[LogicError, Kernel.Thm] = fact(Limit.SquareBelowCauchy)

  /** [[Limit.CauchyNonNegative]], the Cauchy product where both series have non-negative terms. */
  def cauchyNonNegative: Either[LogicError, Kernel.Thm] = fact(Limit.CauchyNonNegative)

  /** [[Limit.SumOfMagnitudes]], the triangle inequality at a finite sum. */
  def sumOfMagnitudes: Either[LogicError, Kernel.Thm] = fact(Limit.SumOfMagnitudes)

  /** [[Limit.Squeezed]], a sequence under a vanishing one. */
  def squeezed: Either[LogicError, Kernel.Thm] = fact(Limit.Squeezed)

  /** [[Limit.StretchOfMagnitudes]], the triangle inequality on a stretch of a series. */
  def stretchOfMagnitudes: Either[LogicError, Kernel.Thm] = fact(Limit.StretchOfMagnitudes)

  /** [[Limit.Cauchy]], the Cauchy product for absolutely convergent series. */
  def cauchy: Either[LogicError, Kernel.Thm] = fact(Limit.Cauchy)

  /** `|- !f l. converges (Sum f) l ==> converges (\n. l - Sum f n) 0` */
  def tail: Either[LogicError, Kernel.Thm] = fact(Limit.Tail)
}

object Limit {

  /** `converges s l` says the sequence `s` converges to `l`. */
  val Converges: String = "converges"

  /** `lim s` is what `s` converges to, where it converges to anything. */
  val Value: String = "lim"

  /**
   * The epsilon-N definition, as the text a person checks it by.
   *
   * Written out in the concrete syntax rather than assembled, for the reason `docs/adr/0004` gives
   * for the sixteen axioms: what a reader has to check is that this says "past some index, within
   * every positive distance", and a reader checks a sentence rather than a sequence of builder
   * calls.
   *
   * `NUM_LE N n` rather than `NUM_LT`, and the distance is strict. Both are the usual conventions
   * and neither is load-bearing: the same sequences converge either way, since an index can be
   * stepped and a tolerance can be halved. What **is** load-bearing is that the tolerance is a real
   * and not a natural, which is what makes this convergence in the reals.
   */
  val ConvergesBody: String =
    "\\s:num -> real. \\l:real. !e:real. 0 < e ==> ?N:num. !n:num. NUM_LE N n ==> abs (s n - l) < e"

  /**
   * The value, which is choice applied to the predicate above and nothing else.
   *
   * The same construction as `NUM_GCD`, `NUM_FLOOR` and `max`: a term that denotes at every
   * argument and about which nothing is provable except where something satisfies the predicate.
   * [[Unique]] is what makes that exception the whole of the interesting case: a sequence has at
   * most one limit, so `lim s` is not merely *a* limit of `s` but *the* one.
   */
  val ValueBody: String = "\\s:num -> real. select (\\l:real. converges s l)"

  /** `|- !x. 0 <= x ==> (!e. 0 < e ==> x < e) ==> x = 0` */
  val BelowEveryPositive: String = "LE_BELOW_EVERY_POSITIVE"

  /** `|- !c. converges (\n. c) c` */
  val Constant: String = "CONVERGES_CONSTANT"

  /** `|- !s a b. converges s a ==> converges s b ==> a = b` */
  val Unique: String = "CONVERGES_UNIQUE"

  /** `|- !s l. converges s l ==> lim s = l` */
  val ValueOfConverges: String = "LIM_OF_CONVERGES"

  /** `|- !s t l N. (!n. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l` */
  val Eventually: String = "CONVERGES_EVENTUALLY"

  /**
   * `|- !s. (!n. s n <= s (SUC n)) ==> !m n. NUM_LE m n ==> s m <= s n`
   *
   * A step at a time gives a step to anywhere, which is the induction nobody states and everybody
   * uses. It is published beside the theorem below rather than folded into it because it is about
   * the order and not about convergence: a caller with an increasing sequence and no interest in
   * its limit wants this one.
   */
  val MonotoneBelow: String = "MONOTONE_LE"

  /**
   * `|- !s. (!n. s n <= s (SUC n)) ==> (?b. !n. s n <= b) ==> ?l. converges s l`
   *
   * The monotone convergence theorem, and the first thing in this repository to **prove** that a
   * sequence converges rather than to take a convergence as a hypothesis. It is where
   * `COMPLETENESS` is spent the second time, `Peano.NUM_ARCHIMEDES` having been the first.
   */
  val MonotoneConverges: String = "MONOTONE_CONVERGES"

  /**
   * The comparison test: a non-negative series under a bounded one converges.
   *
   * The first thing here that obtains the convergence of a **series** rather than of a sequence,
   * and it is [[MonotoneConverges]] spent on the one sequence a series always has. `docs/adr/0017`
   * and `docs/proving.md` both put it first among what the analysis owed.
   *
   * **It did not buy `exp 1 > 2`, which this docstring said it would buy immediately**, and both
   * records were corrected in place rather than left to be believed. What that claim wanted
   * besides this theorem was a dominating series for the exponential: `1 / i!` under
   * `2 * (1/2)^i` asks for `2^i <= 2 * i!` and then an order fact about a quotient. The second
   * landed on 2026-09-18, `Order.INV_ANTITONE` with `Order.LE_MUL_BOTH` under it, and the first
   * on 2026-09-20 as `Coding.NUM_POW_LE_FACT`, so `Transcendental.EXP_ONE_ABOVE_TWO` is a theorem
   * and this test is what obtains the limit it is about. **Four days between the theorem and its
   * first real consumer, and what stood in between was arithmetic on `num`**: the geometric
   * series at one half asked for neither fact and `LimitSpec` obtained it the same day, which is
   * how this went from unspent to spent on an example that proved nothing about the gap.
   */
  val Comparison: String = "SUM_COMPARISON"

  /**
   * `|- !s l b N. converges s l ==> (!n. NUM_LE N n ==> s n <= b) ==> l <= b`
   *
   * A bound the terms respect from some index on is a bound the limit respects, and until this
   * landed nothing here could say anything at all about **where** a limit is. [[MonotoneConverges]]
   * and [[Comparison]] hand back `?l. converges s l` and stop; a caller who wanted to know that the
   * limit it had just obtained sits under two, or over one, had the existential and no way to say
   * it. So this pair is not an ornament on the convergence theorems, it is what makes their output
   * usable in an inequality.
   *
   * == Why the hypothesis is eventual and not everywhere ==
   *
   * `!n. s n <= b` would be the shorter statement and it is the weaker lemma, by exactly the
   * distance that matters to the consumer this was written for. An increasing sequence is under no
   * bound its own terms respect at every index, and the useful lower bound on an increasing
   * sequence is one of its own terms: `!n. NUM_LE m n ==> s m <= s n` is [[MonotoneBelow]] read at
   * a fixed `m`, and it is **false** at `n` below `m`. With the everywhere form, that argument
   * cannot be made at all; with this one it is [[AboveBound]] at `N := m`.
   *
   * The index costs the derivation one step and not a case analysis: the tolerance's own witness
   * and `N` are put together by `Peano.NUM_LE_ADD`, which is the same "above both" [[Unique]] uses
   * and for the same reason, `num` having no maximum.
   *
   * == It is classical, and the file's other bound facts are not ==
   *
   * The argument is a contradiction: if the limit passed the bound the distance between them would
   * be a tolerance no term could be inside, and one is. `Order.LT_OF_NOT_LE` turns the negated
   * conclusion into the strict inequality the tolerance is built from, and `Classical.NOT_NOT`
   * closes it. [[BelowEveryPositive]] is the contrast worth reading beside this one: it reaches the
   * same kind of conclusion through `Order.LE_CASES` and spends nothing classical, and there is no
   * such route here, because what has to be produced is a **number**, the gap, and a disjunction
   * over the three cases of the order gives the gap in one case only.
   */
  val BelowBound: String = "CONVERGES_LE"

  /**
   * `|- !s l b N. converges s l ==> (!n. NUM_LE N n ==> b <= s n) ==> b <= l`
   *
   * [[BelowBound]] at the other side, and it is a second derivation rather than the first one with
   * a sign moved: what the two spend of `abs` are the two different halves of it,
   * `Magnitude.ABS_ABOVE` here and `Magnitude.ABS_ABOVE_NEG` there, because the term that has to be
   * shown to break the bound sits on the other side of the limit.
   *
   * Both are published rather than one, and the reason is the one `Series.POWER_NEG_DOUBLE` states
   * for the half-law it does **not** have: a reader who finds one side of an order fact and not the
   * other cannot tell whether the missing side is false or merely unwritten. Here both are true,
   * both are consumed by the same kind of argument, and the second costs forty lines.
   */
  val AboveBound: String = "CONVERGES_GE"

  /**
   * `|- !s t a b. converges s a ==> converges t b ==> converges (\n. s n + t n) (a + b)`
   *
   * The limit of a sum is the sum of the limits, and it is the first fact in this development that
   * relates **two** convergent sequences to each other. Everything above it takes one sequence and
   * says something about it alone: that a constant converges, that a limit is unique, that an
   * increasing bounded sequence has one. A development that cannot add two limits cannot state the
   * Cauchy product, so this is the piece the analysis was actually short of, and `docs/adr/0017`
   * does not name it because the thing it names, `SUM_SWAP`, is a different gap.
   *
   * The proof is the epsilon argument [[Unique]] already contains, run forwards instead of into a
   * contradiction: halve the tolerance, take the two indices the halves give, and answer at a
   * single index above both. `Peano.NUM_LE_ADD` is what "above both" is here and a maximum is not,
   * for the reason [[Unique]] gives: `num` has no maximum, and the sum of two indices is above each
   * of them for nothing.
   *
   * == Why the triangle inequality is not used, although this is where a reader expects it ==
   *
   * `Magnitude.ABS_TRIANGLE` says `abs (x + y) <= abs x + abs y`, and the textbook step is that
   * inequality applied to `(s n - a) + (t n - b)`. Using it would mean first rewriting
   * `s n + t n - (a + b)` into that sum **under `abs`**, which is a rewrite of a subterm the
   * congruence here reaches only through [[rewriteInProposition]], and then a second step to put
   * the two halves together. What replaces it costs one `Order.ABS_CASES` split and two `Linarith`
   * calls: in each branch `abs` is gone, and what is left is linear over the eight atoms. The
   * inequality is not avoided, it is **decided**, which is what having a fragment decider is for.
   */
  val Added: String = "CONVERGES_ADD"

  /**
   * `|- !s a. converges s a ==> converges (\n. -(s n)) (-a)`
   *
   * Negation of a sequence, and it is here rather than as the scalar multiple `c = -1` for a reason
   * that is about the proof and not about generality. Proved from the definition,
   * `converges (\n. c * s n) (c * a)` divides the tolerance by `abs c` and therefore has to split on
   * `c = 0` before it can divide at all; the negation divides by nothing, keeps the same index, and
   * is three lines of `Linarith` over the same two bounds [[Added]] uses.
   *
   * **The scalar multiple is not missing and never needed that split**, which this paragraph said
   * it did until [[Multiplied]] landed. It is that fact at the constant sequence, and the split
   * does not arise because nothing in that derivation divides by `c`: what it divides by is
   * `(abs c + 1) + (abs a + 1)`, positive whatever `c` is. `LimitSpec` derives it and asserts that
   * what comes out owes the convergence of `s` and owes nothing about `c`, which is the half of the
   * claim a conclusion alone would not carry.
   */
  val Negated: String = "CONVERGES_NEG"

  /**
   * `|- !s t a b. converges s a ==> converges t b ==> converges (\n. s n * t n) (a * b)`
   *
   * The limit of a product, which is what the Cauchy product has to be able to say and what
   * [[Added]] is one operation below. It is the last of the four arithmetic operations this
   * development can carry across a limit that does not need a case split on a zero: the quotient
   * does, and is not here.
   *
   * **It is not [[Added]] with a symbol changed**, and the two places it differs are where the
   * work is. The tolerance is asked for **three** times rather than two, because one factor of the
   * estimate is `abs (s n)`, which the hypotheses bound at no fixed number until the convergence of
   * `s` is spent once at the tolerance `1`. And nothing is halved: the two summands come out
   * bounded by the tolerance times `abs a + 1` and by the tolerance times `abs b + 1`, so the
   * tolerance is chosen to make that sum `e` exactly, which is `e * inv ((abs a + 1) + (abs b + 1))`
   * and the one place a reciprocal enters this file.
   */
  val Multiplied: String = "CONVERGES_MUL"

  /**
   * `|- !f l. converges (Sum (\i. abs (f i))) l ==> ?m. converges (Sum f) m`
   *
   * An absolutely convergent series converges. It is the first theorem here that obtains a
   * convergence from another convergence rather than from a bound, and it is what every argument
   * that rearranges a series has to have in front of it.
   *
   * **It does not go through a Cauchy criterion**, which this repository has not got. See
   * [[absolutelyConvergent]] for the route, which spends completeness exactly once and through
   * [[Comparison]], and for the one lemma it deliberately does not publish beside itself.
   */
  val Absolute: String = "CONVERGES_ABSOLUTE"

  /**
   * `|- !f l. (!i. 0 <= f i) ==> converges (Sum f) l ==> !n. Sum f n <= l`
   *
   * A series of non-negative terms never passes its own limit. It is what turns the **hypothesis**
   * of a convergence into the **bound** a comparison argument needs, and it is the one shape of
   * that move this development has: `CONVERGES_LE` goes the other way, from a bound on the terms
   * to a bound on the limit.
   *
   * It was derived inside [[Absolute]] and is published because a second consumer arrived. That
   * one discharges the non-negativity from `Magnitude.ABS_NONNEG` and is otherwise unchanged, so
   * what this removes is a copy rather than adding a name: the derivation lived in one function
   * and the next argument that wanted it would have written it again.
   *
   * The route is worth a line. The partial sums increase, by `Series.SUM_SUC` and the
   * hypothesis; [[MonotoneBelow]] carries that to every pair of indices; and [[AboveBound]] at
   * **one of the sequence's own terms** turns "increasing and convergent to `l`" into "at most
   * `l`". That last step is what [[AboveBound]] was published for, and it is false below that
   * term's index.
   */
  val BelowLimit: String = "SUM_BELOW_LIMIT"

  /**
   * `|- !f. (!i. 0 <= f i) ==> !m n. NUM_LE m n ==> Sum f m <= Sum f n`
   *
   * The partial sums of a series of non-negative terms grow with the length. It is two lines —
   * `Series.SUM_SUC` with the hypothesis makes the sequence increasing, and [[MonotoneBelow]]
   * carries that to every pair of indices — and it is published because those two lines had been
   * written **three times** by the time anything asked for them: inside [[BelowLimit]], and twice
   * more in the arguments that wanted a partial sum at a shorter length under one at a longer.
   *
   * The third copy is what settled it. A fact derived twice is a coincidence of two authors; a
   * fact derived three times is the library missing an entry, and the rule in `ARC` that a
   * business rule has one implementation site reads the same way about a lemma.
   */
  val Grows: String = "SUM_GROWS"

  /**
   * `|- !a b n. (!i. 0 <= a i) ==> (!i. 0 <= b i) ==>
   * Sum (\k. Sum (\i. a i * b (k - i)) (SUC k)) n <= Sum a n * Sum b n`
   *
   * The triangle is inside the square: for non-negative terms the `n`th partial sum of a Cauchy
   * product never passes the product of the two `n`th partial sums. It is the first half of the
   * sandwich the Cauchy product's convergence rests on, and it is what makes the **split at `n/2`
   * unnecessary** — the measurement that decided the route is written in the card.
   *
   * It costs nothing but `Series.SUM_CAUCHY_GAP` read as a sign. That fact says the difference is
   * `Sum (\i. a i * (Sum b n - Sum b (n - i))) n`, every term of which is a non-negative number
   * times a **tail** of `b`, and a tail of a non-negative series is non-negative because
   * [[Grows]] says the shorter partial sum is the smaller one. `NUM_SUB_LE` is what puts
   * `n - i` under `n`, and it holds with no side condition because the difference is truncated.
   */
  val CauchyBelowSquare: String = "SUM_CAUCHY_BELOW_SQUARE"

  /**
   * `|- !a b n. (!i. 0 <= a i) ==> (!i. 0 <= b i) ==>
   * Sum a n * Sum b n <= Sum (\k. Sum (\i. a i * b (k - i)) (SUC k)) (n + n)`
   *
   * The square is inside the double triangle: every pair `(i, j)` with `i < n` and `j < n` has
   * `i + j < n + n`. It is the second half of the sandwich, and with [[CauchyBelowSquare]] it is
   * what makes the Cauchy product's convergence reachable **without a split at `n / 2`**: the
   * bound `A * B <= D` comes from this at every `n` rather than from cutting a sum in two.
   *
   * `n + n` and not `2 * n`, which is not a spelling. Written with the doubling there is no
   * division anywhere in the argument and `NUM_DIV` never enters; written with `2 * n` the
   * arithmetic under it is the same but a reader is invited to look for the halving that is not
   * there.
   */
  val SquareBelowCauchy: String = "SUM_SQUARE_BELOW_CAUCHY"

  /**
   * `|- !f l. converges (Sum f) l ==> converges (\n. l - Sum f n) 0`
   *
   * What a series has left to add goes to zero. With [[BelowLimit]] it is the tail estimate every
   * rearrangement argument needs, and the pair is **not** a Cauchy criterion: for a series of
   * non-negative terms the tail from `N` on is at most `l - Sum f N`, so the criterion's content
   * is available without the criterion. This repository still has none, and this is the second
   * place where the route around it is monotone convergence rather than completeness twice.
   *
   * It costs four facts and no analysis: the constant sequence converges, [[Negated]] turns the
   * partial sums around, [[Added]] puts the two together at `l + -l`, and the value is `0` by the
   * ring. The sequence is then `\n. l + -(Sum f n)` where a reader writes `\n. l - Sum f n`, and
   * the two are equal at every index without being the same term, which is [[Eventually]] at
   * index zero for the reason `Transcendental.EXP_ONE_ABOVE_TWO` gives.
   */
  val Tail: String = "CONVERGES_TAIL"

  /**
   * `|- !a b A B. (!i. 0 <= a i) ==> (!i. 0 <= b i) ==> converges (Sum a) A ==> converges (Sum b) B
   * ==> converges (Sum (\k. Sum (\i. a i * b (k - i)) (SUC k))) (A * B)`
   *
   * The Cauchy product, for series of non-negative terms, and **there is no epsilon in it**.
   *
   * The two halves of the sandwich do the whole of the work. Write `D` for the partial sums of
   * the convolution and `P n` for `Sum a n * Sum b n`. [[CauchyBelowSquare]] gives `D n <= P n`
   * and [[SquareBelowCauchy]] gives `P n <= D (n + n)`, so `D` is bounded by `A * B` and
   * [[Comparison]] hands back a limit `l`; then `l <= A * B` by [[BelowBound]] on `D`, and
   * `A * B <= l` by [[BelowBound]] on `P`, whose bound is `P n <= D (n + n) <= l`. Antisymmetry
   * closes it.
   *
   * That the epsilon is absent is the return on the sandwich rather than a coincidence. A bracket
   * holding at every index between two sequences whose limits are known is an **order** argument,
   * and the only analysis anywhere under it is the one [[Comparison]] already did. The textbook
   * proof of this theorem is an epsilon argument with a split at `n / 2` inside it; what replaced
   * the split is `n + n`, and what replaced the epsilon is the bracket.
   *
   * Non-negative and not absolutely convergent, which is the honest scope and not a step on the
   * way: the general case needs the triangle inequality at a finite sum, which this repository
   * does not publish, and a squeeze this file does not have. [[Absolute]] is the other half of
   * that pair and is equally unspent here.
   */
  val CauchyNonNegative: String = "SUM_CAUCHY_PRODUCT_NONNEG"

  /**
   * `|- !f n. abs (Sum f n) <= Sum (\i. abs (f i)) n`
   *
   * The triangle inequality at a finite sum. `ABS_TRIANGLE` is the two-term case and this is the
   * induction over it, so it costs no axiom the order did not already cost.
   *
   * It is in this development rather than in `Magnitude` or `Series` because those two cannot
   * write it: `abs` belongs to the first, `Sum` to the second, `Magnitude` is built above
   * `Series` and is handed none of it, and this is the lowest link that holds both names.
   */
  val SumOfMagnitudes: String = "SUM_ABS"

  /**
   * `|- !s u. (!n. abs (s n) <= u n) ==> converges u 0 ==> converges s 0`
   *
   * The squeeze at zero. A sequence whose magnitude is under one that vanishes vanishes, which is
   * the one shape of squeeze the general Cauchy product needs and the cheapest one to state: at a
   * general limit the hypothesis reads `abs (s n - l) <= u n`, which is this statement with the
   * subtraction done by the caller, and both callers here already hold the difference.
   *
   * It costs one asking of `u`'s convergence and no halving, because there is no second sequence
   * to put an index together with.
   */
  val Squeezed: String = "CONVERGES_TO_ZERO"

  /**
   * `|- !f m n. NUM_LE m n ==> abs (Sum f n - Sum f m) <= Sum (\i. abs (f i)) n - Sum (\i. abs (f i)) m`
   *
   * [[SumOfMagnitudes]] on a stretch rather than on a prefix. `SUM_REINDEX` turns each difference
   * into a sum over the stretch and back, so it costs three facts and no induction.
   *
   * The order is a hypothesis rather than the difference being written with `NUM_SUB`, and the
   * derivation says why: at the one call site the guard is then `Peano.NUM_SUB_LE`, which holds
   * with nothing assumed, where the additive form would make the consumer owe `i <= n` at every
   * index.
   */
  val StretchOfMagnitudes: String = "SUM_TAIL_ABS"

  /**
   * `|- !a b A B P Q. converges (Sum (\i. abs (a i))) P ==> converges (Sum (\i. abs (b i))) Q ==>
   * converges (Sum a) A ==> converges (Sum b) B ==>
   * converges (Sum (\k. Sum (\i. a i * b (k - i)) (SUC k))) (A * B)`
   *
   * The Cauchy product, for series whose terms have signs, which is what
   * `Transcendental.EXP_ADD` and the Pythagorean identity were waiting for:
   * [[CauchyNonNegative]] reaches neither, since `sin` alternates and the exponential is wanted
   * at every real rather than at the positives.
   *
   * Both series absolutely convergent, which is the honest hypothesis and not the weakest one:
   * Mertens' theorem asks it of one of the two and this asks it of both. What that buys is that
   * the whole argument runs on one instance of the non-negative theorem and one squeeze.
   *
   * == The identity that does the work carries no hypothesis ==
   *
   * `Series.SUM_CAUCHY_GAP` says `A_n * B_n - D_n = Sum (\i. a i * (B_n - B (n - i))) n` and asks
   * **nothing** of the terms, so it holds of signed series exactly as it holds of non-negative
   * ones. Written at `a, b` and again at the magnitudes it gives two sums that compare termwise,
   * and the comparison is `ABS_MUL` with [[StretchOfMagnitudes]] under it. So the signed gap is
   * under the magnitudes' gap at every index, the magnitudes' gap vanishes because
   * [[Multiplied]] and [[CauchyNonNegative]] send its two halves to the same number, and
   * [[Squeezed]] carries that across.
   *
   * **There is no epsilon in this one either**, and for a reason one step removed from the
   * non-negative theorem's: the only epsilon anywhere under it is the one [[Squeezed]] spends,
   * and [[Squeezed]] spends exactly one.
   */
  val Cauchy: String = "SUM_CAUCHY_PRODUCT"

  /** Everything this development proves, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    BelowEveryPositive -> "!x:real. 0 <= x ==> (!e:real. 0 < e ==> x < e) ==> x = 0",
    Constant -> "!c:real. converges (\\n:num. c) c",
    Unique -> "!s:num -> real. !a:real. !b:real. converges s a ==> converges s b ==> a = b",
    ValueOfConverges -> "!s:num -> real. !l:real. converges s l ==> lim s = l",
    Eventually ->
      ("!s:num -> real. !t:num -> real. !l:real. !N:num. " +
        "(!n:num. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l"),
    MonotoneBelow ->
      ("!s:num -> real. (!n:num. s n <= s (SUC n)) ==> " +
        "!m:num. !n:num. NUM_LE m n ==> s m <= s n"),
    MonotoneConverges ->
      ("!s:num -> real. (!n:num. s n <= s (SUC n)) ==> (?b:real. !n:num. s n <= b) ==> " +
        "?l:real. converges s l"),
    Comparison ->
      ("!f:num -> real. !g:num -> real. (!n:num. 0 <= f n) ==> (!n:num. f n <= g n) ==> " +
        "(?b:real. !n:num. Sum g n <= b) ==> ?l:real. converges (Sum f) l"),
    BelowBound ->
      ("!s:num -> real. !l:real. !b:real. !N:num. converges s l ==> " +
        "(!n:num. NUM_LE N n ==> s n <= b) ==> l <= b"),
    AboveBound ->
      ("!s:num -> real. !l:real. !b:real. !N:num. converges s l ==> " +
        "(!n:num. NUM_LE N n ==> b <= s n) ==> b <= l"),
    Added ->
      ("!s:num -> real. !t:num -> real. !a:real. !b:real. " +
        "converges s a ==> converges t b ==> converges (\\n:num. s n + t n) (a + b)"),
    Negated ->
      "!s:num -> real. !a:real. converges s a ==> converges (\\n:num. -(s n)) (-a)",
    Multiplied ->
      ("!s:num -> real. !t:num -> real. !a:real. !b:real. " +
        "converges s a ==> converges t b ==> converges (\\n:num. s n * t n) (a * b)"),
    Absolute ->
      ("!f:num -> real. !l:real. converges (Sum (\\i:num. abs (f i))) l ==> " +
        "?m:real. converges (Sum f) m"),
    BelowLimit ->
      ("!f:num -> real. !l:real. (!i:num. 0 <= f i) ==> converges (Sum f) l ==> " +
        "!n:num. Sum f n <= l"),
    Grows ->
      ("!f:num -> real. (!i:num. 0 <= f i) ==> " +
        "!m:num. !n:num. NUM_LE m n ==> Sum f m <= Sum f n"),
    CauchyBelowSquare ->
      ("!a:num -> real. !b:num -> real. !n:num. (!i:num. 0 <= a i) ==> (!i:num. 0 <= b i) ==> " +
        "Sum (\\k:num. Sum (\\i:num. a i * b (NUM_SUB k i)) (SUC k)) n <= Sum a n * Sum b n"),
    SquareBelowCauchy ->
      ("!a:num -> real. !b:num -> real. !n:num. (!i:num. 0 <= a i) ==> (!i:num. 0 <= b i) ==> " +
        "Sum a n * Sum b n <= " +
        "Sum (\\k:num. Sum (\\i:num. a i * b (NUM_SUB k i)) (SUC k)) (NUM_ADD n n)"),
    Tail ->
      ("!f:num -> real. !l:real. converges (Sum f) l ==> " +
        "converges (\\n:num. l - Sum f n) 0"),
    CauchyNonNegative ->
      ("!a:num -> real. !b:num -> real. !A:real. !B:real. " +
        "(!i:num. 0 <= a i) ==> (!i:num. 0 <= b i) ==> " +
        "converges (Sum a) A ==> converges (Sum b) B ==> " +
        "converges (Sum (\\k:num. Sum (\\i:num. a i * b (NUM_SUB k i)) (SUC k))) (A * B)"),
    SumOfMagnitudes ->
      "!f:num -> real. !n:num. abs (Sum f n) <= Sum (\\i:num. abs (f i)) n",
    Squeezed ->
      ("!s:num -> real. !u:num -> real. (!n:num. abs (s n) <= u n) ==> " +
        "converges u 0 ==> converges s 0"),
    StretchOfMagnitudes ->
      ("!f:num -> real. !m:num. !n:num. NUM_LE m n ==> " +
        "abs (Sum f n - Sum f m) <= Sum (\\i:num. abs (f i)) n - Sum (\\i:num. abs (f i)) m"),
    Cauchy ->
      ("!a:num -> real. !b:num -> real. !A:real. !B:real. !P:real. !Q:real. " +
        "converges (Sum (\\i:num. abs (a i))) P ==> " +
        "converges (Sum (\\i:num. abs (b i))) Q ==> " +
        "converges (Sum a) A ==> converges (Sum b) B ==> " +
        "converges (Sum (\\k:num. Sum (\\i:num. a i * b (NUM_SUB k i)) (SUC k))) (A * B)")
  )

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val sequences: Type = Type.fun(numbers, values)

  /** The standard development, which is the chain's own and not a second one beside it. */
  lazy val standard: Limit = Chain.standard.limit

  /**
   * The development over a magnitude and a Peano arithmetic that are in one signature.
   *
   * `base` is the theory to extend rather than `magnitude.theory`, for the reason `Rotation` gives:
   * a constant declared into a side branch is unreachable from every link above it, so what this
   * extends is whatever the chain has reached by the time it gets here.
   */
  def construct(
    magnitude: Magnitude,
    peano: Peano,
    series: Series,
    reals: RealTheory,
    induct: Induct,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Limit] = {
    val classical = magnitude.classical

    for {
      convergesBody <- Parser.term(base, notation, ConvergesBody)
      definedConverges <- LogicError.lift(Kernel.defineConstant(base, Converges, convergesBody))
      (afterConverges, convergesDefinition) = definedConverges

      valueBody <- Parser.term(afterConverges, notation, ValueBody)
      definedValue <- LogicError.lift(Kernel.defineConstant(afterConverges, Value, valueBody))
      (theory, valueDefinition) = definedValue

      logic <- classical.logic.over(theory)
      linarith <- Linarith.construct(magnitude.order)

      irreflexive <- reals.axiom("LT_IRREFLEXIVE")
      completeness <- reals.axiom("COMPLETENESS")
      leCases <- magnitude.order.leCases
      leOfEq <- magnitude.order.leOfEq
      notForall <- classical.fact(Classical.NotForall)
      doubleNegation <- classical.fact(Classical.DoubleNegation)
      weakFromNegated <- magnitude.order.fact(Order.LeOfNotLt)
      strictFromNegated <- magnitude.order.fact(Order.LtOfNotLe)
      addAtZero <- peano.fact(Peano.AddAtZero)
      addAtSuccessor <- peano.fact(Peano.AddAtSuccessor)
      orderDefinition <- peano.definition(Peano.NonStrictOrder)
      absCases <- magnitude.absCases
      absAbove <- magnitude.absAbove
      absAboveNegation <- magnitude.absAboveNegation
      absNonNegative <- magnitude.absNonNegative
      absZero <- magnitude.absZero
      atMostSum <- peano.fact(Peano.AtMostSum)
      transitive <- peano.fact(Peano.Transitive)
      addCommutative <- peano.fact(Peano.AddCommutative)

      // `Series` is a link of `Chain` below this one, so the dependency runs the way the chain
      // already runs and costs a parameter rather than a reordering. The comparison test is
      // here and not in `Transcendental`, which has both halves already: that file's first sentence
      // says it is the transcendental functions, and a general fact about series under it would
      // make that sentence false.
      sumAtSuccessor <- series.fact(Series.AtSuccessor)
      sumMonotone <- series.fact(Series.Monotone)
      sumAdditive <- series.fact(Series.Additive)

      absTriangle <- magnitude.triangle
      absMultiplicative <- magnitude.fact(Magnitude.Multiplicative)
      mulSymmetric <- reals.axiom("MUL_SYM")
      mulUnit <- reals.axiom("MUL_ONE")
      mulInverse <- reals.axiom("MUL_INVERSE")
      mulPositive <- reals.axiom("LT_MUL")
      zeroLessOne <- magnitude.order.fact(Order.ZeroLessOne)
      positiveNotZero <- magnitude.order.fact(Order.NonZero)
      inversePositive <- magnitude.order.fact(Order.InversePositive)
      multiplyLe <- magnitude.order.fact(Order.MultiplyLe)
      multiplyLt <- magnitude.order.fact(Order.MultiplyBoth)

      bounds = Bounds(absCases, absAbove, absAboveNegation, absNonNegative, absZero)
      indices = Indices(atMostSum, transitive, addCommutative)
      products = Products(
        absTriangle, absMultiplicative, mulSymmetric, mulUnit, zeroLessOne, positiveNotZero,
        mulInverse, inversePositive, mulPositive, multiplyLe, multiplyLt)

      epsilon <- belowEveryPositive(logic, linarith, theory, notation, irreflexive, leCases)
      constant <- constantSequence(logic, linarith, theory, notation, convergesDefinition, absCases)
      unique <- uniqueLimit(
        logic, linarith, theory, notation, convergesDefinition, bounds, indices, epsilon)
      value <- valueOfConverges(logic, classical, theory, notation, valueDefinition, unique)
      eventually <- eventuallyEqual(
        logic, theory, notation, convergesDefinition, indices)

      monotoneBelow <- monotoneOrder(
        logic, linarith, theory, notation, induct, leOfEq, orderDefinition, addAtZero,
        addAtSuccessor)

      monotoneConverges <- monotoneConvergence(
        logic, linarith, theory, notation, convergesDefinition, completeness, notForall,
        doubleNegation, irreflexive, weakFromNegated, bounds, monotoneBelow)

      comparisonTest <- comparison(
        logic, linarith, theory, notation, sumAtSuccessor, sumMonotone, monotoneConverges)

      below <- boundsTheLimit(
        logic, linarith, theory, notation, convergesDefinition, bounds, indices,
        strictFromNegated, doubleNegation, irreflexive)
      above <- limitBoundsBelow(
        logic, linarith, theory, notation, convergesDefinition, bounds, indices,
        strictFromNegated, doubleNegation, irreflexive)

      addedLimits <- convergesAdd(
        logic, linarith, theory, notation, convergesDefinition, bounds, indices)
      negatedLimit <- convergesNegated(
        logic, linarith, theory, notation, convergesDefinition, bounds)
      partialSumsGrow <- sumsGrow(
        logic, linarith, theory, notation, sumAtSuccessor, monotoneBelow)
      sumCauchyGap <- series.fact(Series.CauchyGap)
      sumNonNegative <- series.fact(Series.NonNegative)
      productNonNegative <- magnitude.order.fact(Order.MultiplyNonNegatives)
      differenceBelow <- peano.fact(Peano.SubBelow)
      sumCauchy <- series.fact(Series.Cauchy)
      sumHalves <- series.fact(Series.Halves)
      sumMonotoneBelow <- series.fact(Series.MonotoneBelow)
      sumScaledRight <- series.fact(Series.ScaledRight)
      atMostFromBelow <- peano.fact(Peano.AtMostFromBelow)
      atMostDouble <- peano.fact(Peano.AtMostDoubleMinus)
      multiplyLe <- magnitude.order.fact(Order.MultiplyLe)
      mulSymmetric <- reals.axiom("MUL_SYM")
      squareUnderTriangle <- squareUnderCauchy(
        logic,
        linarith,
        theory,
        notation,
        Squares(
          sumCauchy, sumHalves, sumMonotoneBelow, sumScaledRight, sumNonNegative,
          productNonNegative, partialSumsGrow, atMostFromBelow, atMostDouble, multiplyLe,
          mulSymmetric)
      )

      triangleUnderSquare <- cauchyUnderSquare(
        logic, linarith, theory, notation, sumCauchyGap, partialSumsGrow, sumNonNegative,
        productNonNegative, differenceBelow)
      belowItsOwnLimit <- belowItsLimit(logic, theory, notation, partialSumsGrow, above)
      tailToZero <- tailVanishes(
        logic, magnitude.order.ring, theory, notation, constant, negatedLimit, addedLimits,
        eventually)

      absoluteSeries <- absolutelyConvergent(
        logic,
        linarith,
        theory,
        notation,
        Absolutes(
          sumAdditive, comparisonTest, belowItsOwnLimit, addedLimits, negatedLimit, eventually),
        bounds
      )

      multipliedLimits <- convergesMultiplied(
        logic, linarith, magnitude.order.ring, theory, notation, convergesDefinition, bounds,
        indices, products)

      vanishingDominates <- dominatedByAVanishing(
        logic, linarith, theory, notation, convergesDefinition, bounds)

      absTriangle <- magnitude.fact(Magnitude.Triangle)
      absOfNonNegative <- magnitude.fact(Magnitude.OfNonNegative)
      sumAtSuccessorFact <- series.fact(Series.AtSuccessor)
      sumAtZero <- series.fact(Series.AtZero)
      magnitudesOfASum <- sumUnderMagnitudes(
        logic, linarith, theory, notation, induct,
        Magnitudes(absTriangle, absOfNonNegative, sumAtSuccessorFact, sumAtZero))

      sumReindex <- series.fact(Series.Reindex)
      magnitudesOfAStretch <- stretchUnderMagnitudes(
        logic, theory, notation, orderDefinition, sumReindex, magnitudesOfASum)

      antisymmetry <- magnitude.order.antisymmetric
      cauchyProduct <- cauchyOfNonNegative(
        logic,
        linarith,
        theory,
        notation,
        Cauchys(
          comparisonTest, below, belowItsOwnLimit, triangleUnderSquare, squareUnderTriangle,
          multipliedLimits, sumNonNegative, productNonNegative, multiplyLe, mulSymmetric,
          antisymmetry)
      )
      absNonNegative <- magnitude.fact(Magnitude.AbsNonNegative)
      absMul <- magnitude.fact(Magnitude.Multiplicative)
      sumMonotone <- series.fact(Series.Monotone)
      signedCauchyProduct <- cauchyOfSigned(
        logic,
        linarith,
        theory,
        notation,
        Generals(
          magnitude.order.ring, absNonNegative, absMul, cauchyProduct, multipliedLimits,
          addedLimits, negatedLimit, eventually, vanishingDominates, sumCauchyGap, sumMonotone,
          magnitudesOfASum, magnitudesOfAStretch, multiplyLe, mulSymmetric, differenceBelow)
      )
    } yield new Limit(
      magnitude,
      peano,
      theory,
      notation,
      Map(Converges -> convergesDefinition, Value -> valueDefinition),
      Map(
        BelowEveryPositive -> epsilon,
        Constant -> constant,
        Unique -> unique,
        ValueOfConverges -> value,
        Eventually -> eventually,
        MonotoneBelow -> monotoneBelow,
        MonotoneConverges -> monotoneConverges,
        Comparison -> comparisonTest,
        BelowBound -> below,
        AboveBound -> above,
        Added -> addedLimits,
        Negated -> negatedLimit,
        Multiplied -> multipliedLimits,
        Absolute -> absoluteSeries,
        BelowLimit -> belowItsOwnLimit,
        Grows -> partialSumsGrow,
        CauchyBelowSquare -> triangleUnderSquare,
        SquareBelowCauchy -> squareUnderTriangle,
        Tail -> tailToZero,
        CauchyNonNegative -> cauchyProduct,
        SumOfMagnitudes -> magnitudesOfASum,
        Squeezed -> vanishingDominates,
        StretchOfMagnitudes -> magnitudesOfAStretch,
        Cauchy -> signedCauchyProduct
      )
    )
  }

  /**
   * The comparison test, from the three facts it is made of and nothing else.
   *
   * == Why it is short ==
   *
   * Every piece was already published and the work is putting them in one order. `SUM_SUC` says a
   * partial sum grows by the term just added, so non-negative terms make the partial sums an
   * increasing sequence; `SUM_MONOTONE` says termwise domination carries to the partial sums; and
   * [[MonotoneConverges]] closes an increasing sequence bounded above. The series is never
   * mentioned as a series: what converges is the sequence `Sum f`, which is what a series **is**
   * here, and that is why no new constant and no axiom are needed.
   *
   * == The hypothesis is stronger than the argument strictly needs, and that is deliberate ==
   *
   * `!n. 0 <= f n` asks for non-negativity at **every** index, where the mathematics needs it only
   * from the point the tail starts. The reason is [[MonotoneConverges]]: it asks for
   * `!n. s n <= s (SUC n)` everywhere, so a weaker hypothesis here would need a convergence rule
   * for an eventually increasing sequence, which this development has not got. [[Eventually]] is
   * not that rule: it carries a limit across two sequences that agree past an index, which is
   * eventual **equality** and not eventual monotonicity.
   *
   * So the weaker form is a piece of work rather than a better phrasing of this one, and it is
   * named here so that a reader meeting the strong hypothesis knows it was measured against the
   * rule above rather than written down without looking.
   */
  private def comparison(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    sumAtSuccessor: Kernel.Thm,
    sumMonotone: Kernel.Thm,
    monotoneConverges: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val f = Term.variable("f", sequences)
    val g = Term.variable("g", sequences)
    val n = Term.variable("n", numbers)
    val b = Term.variable("b", values)

    def proposition(text: String): Either[LogicError, Term] =
      Parser.proposition(theory, notation, text)

    for {
      nonNegative <- proposition("!n:num. 0 <= (f:num -> real) n")
      dominated <- proposition("!n:num. (f:num -> real) n <= (g:num -> real) n")
      boundedAbove <- proposition("?b:real. !n:num. Sum (g:num -> real) n <= b")

      assumedNonNegative <- LogicError.lift(Kernel.assume(nonNegative))
      assumedDominated <- LogicError.lift(Kernel.assume(dominated))
      assumedBounded <- LogicError.lift(Kernel.assume(boundedAbove))

      /* ---- the partial sums increase, which is `SUM_SUC` read with a non-negative term ---- */

      sumF <- Parser.term(theory, notation, "Sum (f:num -> real)")
      atSuccessor <- rules.specAll(sumAtSuccessor, List(f, n))
      termNonNegative <- rules.spec(n, assumedNonNegative)

      // `Sum f n <= Sum f n + f n` is a linear consequence of `0 <= f n`, and the equation above
      // turns the right side into `Sum f (SUC n)`. Linarith decides the first and the rewriting
      // does the second, which is why neither half is a hand derivation.
      growsBody <- proposition(
        "0 <= (f:num -> real) n:num ==> Sum f n <= Sum f n + f n")
      grows <- linarith.prove(growsBody)
      growsAt <- rules.mp(grows, termNonNegative)
      // Reversed, because `SUM_SUC` reads `Sum f (SUC n) = Sum f n + f n` and what has to move is
      // the right side into the left: the linear step above produces `Sum f n + f n` and
      // `MONOTONE_CONVERGES` asks for `Sum f (SUC n)`.
      folded <- Conv.sym(atSuccessor)
      increasingAt <- Rewrite.Rule
        .of(logic, folded)
        .flatMap(rule => Rewrite.inTheorem(Vector(rule), growsAt))
      increasing <- rules.gen(n, increasingAt)

      /* ---- and they are bounded, because they lie under `g`'s ---- */

      belowG <- rules.specAll(sumMonotone, List(f, g))
      dominatedSums <- rules.mp(belowG, assumedDominated)

      bound <- proposition("!n:num. Sum (g:num -> real) n <= b:real")
      assumedBound <- LogicError.lift(Kernel.assume(bound))

      // A CONJUNCTION and not two arrows, because of the `conjIntro` below and for no other
      // reason. This comment said the conjunction was the shape `Linarith.prove` documents and
      // that a curried goal comes back wrong, and **that is false**: `Linarith.split` peels every
      // antecedent, not one, and `CurriedGoalSpec` has pinned the two forms as the same goal since
      // the day a version that peeled exactly one was repaired. What refused the curried attempt
      // was `Rules.mp`, downstream, against an antecedent this assembly does not build -- a
      // constraint of the three lines below rather than of the prover. The distinction is worth
      // the paragraph: a wrong figure gets rechecked by whoever trips on it, and a wrong
      // constraint gets **obeyed**, so nobody ever discovers it was unnecessary.
      transitivityGoal <- proposition(
        "Sum (f:num -> real) n:num <= Sum (g:num -> real) n /\\ Sum g n <= b:real ==> " +
          "Sum f n <= b")
      transitivity <- linarith.prove(transitivityGoal)
      underG <- rules.spec(n, dominatedSums)
      underB <- rules.spec(n, assumedBound)
      both <- rules.conjIntro(underG, underB)
      belowBoundAt <- rules.mp(transitivity, both)
      belowBound <- rules.gen(n, belowBoundAt)

      // The witness is discharged here rather than carried: what `MONOTONE_CONVERGES` wants is the
      // existential, and rebuilding it after the case keeps `b` out of the conclusion.
      boundedF <- proposition("?b:real. !n:num. Sum (f:num -> real) n <= b")
      witnessed <- logic
        .destExistsPredicate(boundedF)
        .toRight(NotOfForm("an existential quantification", boundedF))
      packed <- rules.existsIntro(witnessed, b, belowBound)
      existsBound <- rules.existsElim(assumedBounded, b, packed)

      /* ---- and that is exactly what the monotone rule asks for ---- */

      atSums <- rules.spec(sumF, monotoneConverges)
      converging <- rules.mp(atSums, increasing).flatMap(rules.mp(_, existsBound))

      dischargedBounded <- rules.disch(boundedAbove, converging)
      dischargedDominated <- rules.disch(dominated, dischargedBounded)
      dischargedNonNegative <- rules.disch(nonNegative, dischargedDominated)
      result <- rules.genAll(dischargedNonNegative, List(f, g))
    } yield result
  }

  /**
   * `|- !s l b N. converges s l ==> (!n. NUM_LE N n ==> s n <= b) ==> l <= b`
   *
   * Suppose the limit passed the bound. Then the distance between them is a positive tolerance, so
   * some index answers it, and from that index on every term is within the gap of the limit and
   * therefore **above** the bound, which the hypothesis forbids from `N` on. The two indices are put
   * together the way [[Unique]] puts its two together, by `Peano.NUM_LE_ADD`, and the contradiction
   * is a single linear step over four atoms.
   *
   * == The one step that is not obvious ==
   *
   * The tolerance is `l - b` itself rather than a fraction of it. Halving buys nothing here: what
   * has to be contradicted is a **non-strict** bound, and a term within `l - b` of `l` is already
   * strictly above `b`. Every other epsilon argument in this file halves, so the absence is worth
   * the sentence: the reader who expects `e / 2` is expecting the shape of [[Unique]], where two
   * distances have to fit inside one tolerance and here there is one.
   */
  private def boundsTheLimit(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds,
    indices: Indices,
    strictFromNegated: Kernel.Thm,
    doubleNegation: Kernel.Thm,
    irreflexive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val l = Term.variable("l", values)
    val b = Term.variable("b", values)
    val from = Term.variable("N", numbers)
    val m = Term.variable("m", numbers)

    for {
      converging <- Parser.proposition(theory, notation, "converges (s:num -> real) (l:real)")
      assumedConverging <- LogicError.lift(Kernel.assume(converging))
      unfolded <- Conv.unfold(convergesDefinition, List(s, l)).flatMap(normaliseRight)
      body <- LogicError.lift(Kernel.eqMp(unfolded, assumedConverging))

      eventual <- Parser.proposition(
        theory, notation, "!n:num. NUM_LE N:num n ==> (s:num -> real) n <= b:real")
      assumedEventual <- LogicError.lift(Kernel.assume(eventual))

      target <- Parser.proposition(theory, notation, "l:real <= b:real")
      refused <- Parser.proposition(theory, notation, "~(l:real <= b:real)")
      assumedRefused <- LogicError.lift(Kernel.assume(refused))
      strict <- rules.specAll(strictFromNegated, List(l, b)).flatMap(rules.mp(_, assumedRefused))

      tolerance <- Parser.term(theory, notation, "l:real - b:real", values)
      positive <- linarith
        .prove("!x:real. !y:real. y < x ==> 0 < x - y")
        .flatMap(rules.specAll(_, List(l, b)))
        .flatMap(rules.mp(_, strict))
      near <- rules.spec(tolerance, body).flatMap(rules.mp(_, positive))

      inside <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (l:real)) < (l:real) - (b:real)"
      )
      assumedInside <- LogicError.lift(Kernel.assume(inside))

      index <- Parser.term(theory, notation, "NUM_ADD N:num m:num", numbers)
      pastFrom <- rules.specAll(indices.atMostSum, List(from, m))
      pastWitness <- for {
        other <- rules.specAll(indices.atMostSum, List(m, from))
        swap <- rules.specAll(indices.commutative, List(m, from))
        carried <- rewriteWith(swap, other)
      } yield carried

      close <- rules.spec(index, assumedInside).flatMap(rules.mp(_, pastWitness))
      under <- rules.spec(index, assumedEventual).flatMap(rules.mp(_, pastFrom))

      atIndex <- Parser.term(theory, notation, "(s:num -> real) (NUM_ADD N:num m:num)", values)
      gap <- Parser.term(
        theory, notation, "(s:num -> real) (NUM_ADD N:num m:num) - (l:real)", values)
      distance <- Parser.term(
        theory, notation, "abs ((s:num -> real) (NUM_ADD N:num m:num) - (l:real))", values)
      aboveNegation <- rules.spec(gap, bounds.aboveNegation)

      // Infeasible rather than merely false: the three hypotheses put the term strictly above the
      // bound and at most the bound, so `l < l` is a linear consequence and irreflexivity is what
      // turns it into the refutation. The conclusion is about `l` and not about `b` so that the
      // clash is with the axiom this file already reads.
      absurd <- linarith
        .prove(
          "!x:real. !p:real. !q:real. !d:real. " +
            "-(x - p) <= d ==> d < p - q ==> x <= q ==> p < p")
        .flatMap(rules.specAll(_, List(atIndex, l, b, distance)))
        .flatMap(rules.mp(_, aboveNegation))
        .flatMap(rules.mp(_, close))
        .flatMap(rules.mp(_, under))
      clash <- rules.spec(l, irreflexive).flatMap(rules.notElim(_, absurd))
      eliminated <- rules.existsElim(near, m, clash)

      doubled <- rules.notIntro(refused, eliminated)
      settled <- rules.spec(target, doubleNegation).flatMap(rules.mp(_, doubled))

      result <- rules
        .disch(eventual, settled)
        .flatMap(rules.disch(converging, _))
        .flatMap(rules.genAll(_, List(s, l, b, from)))
    } yield result
  }

  /**
   * `|- !s l b N. converges s l ==> (!n. NUM_LE N n ==> b <= s n) ==> b <= l`
   *
   * [[boundsTheLimit]] with the limit on the other side of the bound, and the derivation differs in
   * three places rather than in a sign: the tolerance is `b - l`, the half of `abs` that is spent is
   * `ABS_ABOVE` instead of `ABS_ABOVE_NEG`, and the linear step contradicts a term sitting strictly
   * **below** a bound it is supposed to be above.
   */
  private def limitBoundsBelow(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds,
    indices: Indices,
    strictFromNegated: Kernel.Thm,
    doubleNegation: Kernel.Thm,
    irreflexive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val l = Term.variable("l", values)
    val b = Term.variable("b", values)
    val from = Term.variable("N", numbers)
    val m = Term.variable("m", numbers)

    for {
      converging <- Parser.proposition(theory, notation, "converges (s:num -> real) (l:real)")
      assumedConverging <- LogicError.lift(Kernel.assume(converging))
      unfolded <- Conv.unfold(convergesDefinition, List(s, l)).flatMap(normaliseRight)
      body <- LogicError.lift(Kernel.eqMp(unfolded, assumedConverging))

      eventual <- Parser.proposition(
        theory, notation, "!n:num. NUM_LE N:num n ==> b:real <= (s:num -> real) n")
      assumedEventual <- LogicError.lift(Kernel.assume(eventual))

      target <- Parser.proposition(theory, notation, "b:real <= l:real")
      refused <- Parser.proposition(theory, notation, "~(b:real <= l:real)")
      assumedRefused <- LogicError.lift(Kernel.assume(refused))
      strict <- rules.specAll(strictFromNegated, List(b, l)).flatMap(rules.mp(_, assumedRefused))

      tolerance <- Parser.term(theory, notation, "b:real - l:real", values)
      positive <- linarith
        .prove("!x:real. !y:real. y < x ==> 0 < x - y")
        .flatMap(rules.specAll(_, List(b, l)))
        .flatMap(rules.mp(_, strict))
      near <- rules.spec(tolerance, body).flatMap(rules.mp(_, positive))

      inside <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (l:real)) < (b:real) - (l:real)"
      )
      assumedInside <- LogicError.lift(Kernel.assume(inside))

      index <- Parser.term(theory, notation, "NUM_ADD N:num m:num", numbers)
      pastFrom <- rules.specAll(indices.atMostSum, List(from, m))
      pastWitness <- for {
        other <- rules.specAll(indices.atMostSum, List(m, from))
        swap <- rules.specAll(indices.commutative, List(m, from))
        carried <- rewriteWith(swap, other)
      } yield carried

      close <- rules.spec(index, assumedInside).flatMap(rules.mp(_, pastWitness))
      over <- rules.spec(index, assumedEventual).flatMap(rules.mp(_, pastFrom))

      atIndex <- Parser.term(theory, notation, "(s:num -> real) (NUM_ADD N:num m:num)", values)
      gap <- Parser.term(
        theory, notation, "(s:num -> real) (NUM_ADD N:num m:num) - (l:real)", values)
      distance <- Parser.term(
        theory, notation, "abs ((s:num -> real) (NUM_ADD N:num m:num) - (l:real))", values)
      above <- rules.spec(gap, bounds.above)

      absurd <- linarith
        .prove(
          "!x:real. !p:real. !q:real. !d:real. " +
            "x - p <= d ==> d < q - p ==> q <= x ==> p < p")
        .flatMap(rules.specAll(_, List(atIndex, l, b, distance)))
        .flatMap(rules.mp(_, above))
        .flatMap(rules.mp(_, close))
        .flatMap(rules.mp(_, over))
      clash <- rules.spec(l, irreflexive).flatMap(rules.notElim(_, absurd))
      eliminated <- rules.existsElim(near, m, clash)

      doubled <- rules.notIntro(refused, eliminated)
      settled <- rules.spec(target, doubleNegation).flatMap(rules.mp(_, doubled))

      result <- rules
        .disch(eventual, settled)
        .flatMap(rules.disch(converging, _))
        .flatMap(rules.genAll(_, List(s, l, b, from)))
    } yield result
  }

  /**
   * What a derivation about `abs` needs, so that each one names what it uses.
   *
   * A record rather than a tuple for the reason `Magnitude.SignPieces` gives: a positional read of
   * five theorems of the same type is how a derivation gets assembled out of the wrong pieces.
   */
  private final case class Bounds(
    cases: Kernel.Thm,
    above: Kernel.Thm,
    aboveNegation: Kernel.Thm,
    nonNegative: Kernel.Thm,
    zero: Kernel.Thm
  )

  /** What a derivation that puts two indices together needs: a sum is above each summand. */
  private final case class Indices(
    atMostSum: Kernel.Thm,
    transitive: Kernel.Thm,
    commutative: Kernel.Thm
  )

  /** What the square-inside-the-double-triangle argument takes from the three files under it. */
  private final case class Squares(
    cauchy: Kernel.Thm,
    halves: Kernel.Thm,
    monotoneBelow: Kernel.Thm,
    scaledRight: Kernel.Thm,
    nonNegativeSum: Kernel.Thm,
    productNonNegative: Kernel.Thm,
    grows: Kernel.Thm,
    atMostFromBelow: Kernel.Thm,
    atMostDouble: Kernel.Thm,
    multiplyLe: Kernel.Thm,
    symmetric: Kernel.Thm
  )

  /**
   * What the triangle inequality at a finite sum takes, which is three facts and an induction.
   *
   * A bundle for [[Bounds]]'s reason, and the smallest one here. Two are `Magnitude`'s and one is
   * `Series`', which is the whole of why the lemma cannot live in either of those files.
   */
  private final case class Magnitudes(
    triangle: Kernel.Thm,
    ofNonNegative: Kernel.Thm,
    atSuccessor: Kernel.Thm,
    atZero: Kernel.Thm
  )

  /**
   * What the general Cauchy product takes, which is fifteen facts and is the whole argument.
   *
   * A bundle for [[Bounds]]'s reason, and the largest here. Four of the fifteen are this file's
   * own and were proved for this consumer — the non-negative product, the squeeze, and the
   * triangle inequality at a prefix and at a stretch — and the rest are the order's, the ring's
   * and `Series`'. `SUM_CAUCHY_GAP` is the one to read first: it carries no hypothesis, which is
   * why an argument about non-negative terms and an argument about signed ones can share it.
   */
  private final case class Generals(
    ring: Ring,
    absNonNegative: Kernel.Thm,
    absMul: Kernel.Thm,
    nonNegativeProduct: Kernel.Thm,
    multiplied: Kernel.Thm,
    added: Kernel.Thm,
    negated: Kernel.Thm,
    eventually: Kernel.Thm,
    squeezed: Kernel.Thm,
    gap: Kernel.Thm,
    monotone: Kernel.Thm,
    prefix: Kernel.Thm,
    stretch: Kernel.Thm,
    multiplyLe: Kernel.Thm,
    symmetric: Kernel.Thm,
    subBelow: Kernel.Thm
  )

  /**
   * What the Cauchy product takes, which is eleven facts and not one procedure.
   *
   * A bundle for [[Bounds]]'s reason. It is worth reading as a list, because it is the whole
   * argument: five of the eleven are this file's own and were proved for this consumer, and the
   * other six are the order's. Nothing in it is an analysis fact that the two sandwich halves did
   * not already buy.
   */
  private final case class Cauchys(
    comparison: Kernel.Thm,
    belowBound: Kernel.Thm,
    belowLimit: Kernel.Thm,
    cauchyBelowSquare: Kernel.Thm,
    squareBelowCauchy: Kernel.Thm,
    multiplied: Kernel.Thm,
    nonNegativeSum: Kernel.Thm,
    productNonNegative: Kernel.Thm,
    multiplyLe: Kernel.Thm,
    symmetric: Kernel.Thm,
    antisymmetric: Kernel.Thm
  )

  /**
   * What the absolute convergence theorem takes from the two developments under this one.
   *
   * A bundle for [[Bounds]]'s reason: one derivation wants all eight and no other wants any of
   * them. Two are `Series`' and six are this file's own, which is the shape of the argument — the
   * work is putting facts that already exist in one order, and the only thing it adds is the
   * observation that the bracket is non-negative.
   */
  private final case class Absolutes(
    additive: Kernel.Thm,
    comparison: Kernel.Thm,
    belowLimit: Kernel.Thm,
    added: Kernel.Thm,
    negated: Kernel.Thm,
    eventually: Kernel.Thm
  )

  /**
   * What an estimate over a **product** needs, which is everything an estimate over a sum does not.
   *
   * It is a bundle for the reason [[Bounds]] is: one derivation wants all of it and no other wants
   * any of it, so the alternative is eleven parameters on one signature. Three of them are the
   * reciprocal's, and they are here rather than in a `Field` call because what this derivation
   * needs of a denominator is one equation at a value already known positive, not a tactic that
   * carries a side condition.
   */
  private final case class Products(
    triangle: Kernel.Thm,
    multiplicative: Kernel.Thm,
    symmetric: Kernel.Thm,
    unit: Kernel.Thm,
    zeroLessOne: Kernel.Thm,
    nonZero: Kernel.Thm,
    inverse: Kernel.Thm,
    inversePositive: Kernel.Thm,
    productPositive: Kernel.Thm,
    multiplyLe: Kernel.Thm,
    multiplyLt: Kernel.Thm
  )

  /**
   * `|- !x. 0 <= x ==> (!e. 0 < e ==> x < e) ==> x = 0`, and it is classical in nothing.
   *
   * The textbook proof argues by contradiction from the excluded middle. That is not needed and the
   * route here says why: `Order.LE_CASES` turns `0 <= x` into `0 < x \/ 0 = x`, and the first
   * disjunct is refuted **directly** by instantiating the hypothesis at `e := x`, which gives
   * `x < x` against the irreflexivity axiom. What comes out is a disjunction elimination rather
   * than a contradiction, so **this derivation** reaches no classical axiom, which `LimitSpec`
   * asserts rather than this sentence claiming it.
   *
   * It is the only one in the file of which that is true, and the reason is worth knowing before
   * reading the rest: everything else here touches `abs`, which is defined through `select`, so the
   * choice axiom arrives with the first `Magnitude` fact whatever route the proof takes. What the
   * route buys is not a cheaper foundation, it is that nothing here **decides** anything by the
   * excluded middle.
   *
   * The instantiation at `e := x` is the whole content, and it is the step somebody rediscovers
   * every time they meet this lemma: the hypothesis is about **every** positive tolerance, so it is
   * about the number itself.
   */
  private def belowEveryPositive(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    irreflexive: Kernel.Thm,
    leCases: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val x = Term.variable("x", values)

    for {
      nonNegative <- Parser.proposition(theory, notation, "0 <= x:real")
      assumedNonNegative <- LogicError.lift(Kernel.assume(nonNegative))

      everyPositive <- Parser.proposition(theory, notation, "!e:real. 0 < e ==> x:real < e")
      assumedEvery <- LogicError.lift(Kernel.assume(everyPositive))

      target <- Parser.proposition(theory, notation, "x:real = 0")
      zero <- Parser.term(theory, notation, "0:real", values)

      split <- rules.specAll(leCases, List(zero, x)).flatMap(rules.mp(_, assumedNonNegative))

      strict <- Parser.proposition(theory, notation, "0 < x:real")
      fromStrict <- for {
        assumed <- LogicError.lift(Kernel.assume(strict))
        atItself <- rules.spec(x, assumedEvery).flatMap(rules.mp(_, assumed))
        never <- rules.spec(x, irreflexive)
        clash <- rules.notElim(never, atItself)
        anything <- rules.falsityElim(target, clash)
      } yield anything

      equated <- Parser.proposition(theory, notation, "0 = x:real")
      fromEquated <- for {
        assumed <- LogicError.lift(Kernel.assume(equated))
        turn <- linarith.prove("!a:real. 0 = a ==> a = 0")
        applied <- rules.spec(x, turn).flatMap(rules.mp(_, assumed))
      } yield applied

      settled <- rules.disjElim(split, fromStrict, fromEquated)
      result <- rules
        .disch(everyPositive, settled)
        .flatMap(rules.disch(nonNegative, _))
        .flatMap(rules.gen(x, _))
    } yield result
  }

  /**
   * `|- !c. converges (\n. c) c`, the one sequence whose limit needs no analysis.
   *
   * Every index answers, so the witness is `0` and the distance is `abs (c - c)`. That the distance
   * is zero is `Magnitude.ABS_CASES` and one linear step in each branch, which is cheaper than it
   * looks: the two branches differ only in the sign of a difference that vanishes either way.
   *
   * It is not decoration. [[Eventually]] turns it into every sequence that is eventually constant,
   * and that pair is what [[Transcendental]] evaluates a power series at zero with, without any
   * convergence theorem at all.
   */
  private def constantSequence(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    absCases: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val c = Term.variable("c", values)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)

    for {
      sequence <- Parser.term(theory, notation, "\\n:num. c:real", sequences)
      unfolded <- Conv.unfold(convergesDefinition, List(sequence, c))
      opened <- normaliseRight(unfolded)
      body <- rightOf(opened)

      difference <- Parser.term(theory, notation, "c:real - c:real", values)
      distance <- Parser.term(theory, notation, "abs (c:real - c:real)", values)
      split <- rules.spec(difference, absCases)

      plain <- Parser.proposition(theory, notation, "abs (c:real - c:real) = c - c")
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        cancels <- linarith.prove("!a:real. a - a = 0")
        result <- rules.spec(c, cancels).flatMap(Conv.trans(assumed, _))
      } yield result

      negated <- Parser.proposition(theory, notation, "abs (c:real - c:real) = -(c - c)")
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negated))
        cancels <- linarith.prove("!a:real. -(a - a) = 0")
        result <- rules.spec(c, cancels).flatMap(Conv.trans(assumed, _))
      } yield result

      vanishes <- rules.disjElim(split, fromPlain, fromNegated)

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      small <- linarith.prove("!a:real. !e:real. a = 0 ==> 0 < e ==> a < e")
      close <- rules
        .specAll(small, List(distance, e))
        .flatMap(rules.mp(_, vanishes))
        .flatMap(rules.mp(_, assumedPositive))

      guard <- Parser.proposition(theory, notation, "NUM_LE 0 n:num")
      guarded <- rules.disch(guard, close).flatMap(rules.gen(n, _))

      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> abs (c:real - c:real) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      first <- Parser.term(theory, notation, "0:num", numbers)
      witnessed <- rules.existsIntro(predicate, first, guarded)

      whole <- rules.disch(positive, witnessed).flatMap(rules.gen(e, _))
      _ <- sameStatement(notation, whole, body)

      folded <- Conv.sym(opened).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))
      result <- rules.gen(c, folded)
    } yield result
  }

  /**
   * `|- !s a b. converges s a ==> converges s b ==> a = b`: a sequence has at most one limit.
   *
   * The argument is the standard one, and the two places it could have been harder are both closed
   * by something this chain already has. Halving the tolerance is `Linarith`'s, since a numeral
   * denominator is a rational coefficient to it and `0 < e ==> 0 < e / 2` is inside the fragment it
   * decides. Putting the two indices together is `Peano.NUM_LE_ADD`: their sum is above each of
   * them, so no maximum on `num` is needed, and there is none.
   *
   * What is left is one case split on the sign of `a - b`, because the distance between the two
   * limits has to be compared with the tolerance and `abs` is not linear. Each branch is a single
   * `Linarith` step over five hypotheses, which is the triangle inequality written out rather than
   * `Magnitude.ABS_TRIANGLE` applied: the two bounds it would be assembled from are already in
   * hand, and putting them together with the case hypothesis is what the procedure is for.
   *
   * The conclusion is reached through [[BelowEveryPositive]] rather than by contradiction, and what
   * that is worth is stated where that lemma is: not a cheaper foundation, since `abs` costs choice
   * either way, but no step that decides a question by the excluded middle.
   */
  private def uniqueLimit(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds,
    indices: Indices,
    epsilon: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val a = Term.variable("a", values)
    val b = Term.variable("b", values)
    val e = Term.variable("e", values)
    val m = Term.variable("m", numbers)
    val k = Term.variable("k", numbers)

    for {
      toA <- Parser.proposition(theory, notation, "converges (s:num -> real) (a:real)")
      toB <- Parser.proposition(theory, notation, "converges (s:num -> real) (b:real)")
      assumedA <- LogicError.lift(Kernel.assume(toA))
      assumedB <- LogicError.lift(Kernel.assume(toB))

      unfoldedA <- Conv.unfold(convergesDefinition, List(s, a)).flatMap(normaliseRight)
      unfoldedB <- Conv.unfold(convergesDefinition, List(s, b)).flatMap(normaliseRight)
      bodyA <- LogicError.lift(Kernel.eqMp(unfoldedA, assumedA))
      bodyB <- LogicError.lift(Kernel.eqMp(unfoldedB, assumedB))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      half <- Parser.term(theory, notation, "e:real / 2", values)
      halfPositive <- linarith
        .prove("!e:real. 0 < e ==> 0 < e / 2")
        .flatMap(rules.spec(e, _))
        .flatMap(rules.mp(_, assumedPositive))

      nearA <- rules.spec(half, bodyA).flatMap(rules.mp(_, halfPositive))
      nearB <- rules.spec(half, bodyB).flatMap(rules.mp(_, halfPositive))

      // Inside the two witnesses, at the one index that answers both.
      insideA <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (a:real)) < e:real / 2"
      )
      insideB <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE k:num n ==> abs ((s:num -> real) n - (b:real)) < e:real / 2"
      )
      assumedInsideA <- LogicError.lift(Kernel.assume(insideA))
      assumedInsideB <- LogicError.lift(Kernel.assume(insideB))

      index <- Parser.term(theory, notation, "NUM_ADD m:num k:num", numbers)
      aboveM <- rules.specAll(indices.atMostSum, List(m, k))
      aboveK <- for {
        other <- rules.specAll(indices.atMostSum, List(k, m))
        swap <- rules.specAll(indices.commutative, List(k, m))
        carried <- rewriteWith(swap, other)
      } yield carried

      closeA <- rules.spec(index, assumedInsideA).flatMap(rules.mp(_, aboveM))
      closeB <- rules.spec(index, assumedInsideB).flatMap(rules.mp(_, aboveK))

      // The term at the index that answers both, and the two distances, read rather than built:
      // what a reader checks against the case split below is a sentence.
      atIndex <- Parser.term(theory, notation, "(s:num -> real) (NUM_ADD m:num k:num)", values)
      gapA <- Parser.term(
        theory, notation, "(s:num -> real) (NUM_ADD m:num k:num) - (a:real)", values)
      gapB <- Parser.term(
        theory, notation, "(s:num -> real) (NUM_ADD m:num k:num) - (b:real)", values)
      distanceA <- Parser.term(
        theory, notation, "abs ((s:num -> real) (NUM_ADD m:num k:num) - (a:real))", values)
      distanceB <- Parser.term(
        theory, notation, "abs ((s:num -> real) (NUM_ADD m:num k:num) - (b:real))", values)
      distance <- Parser.term(theory, notation, "abs (a:real - b:real)", values)
      difference <- Parser.term(theory, notation, "a:real - b:real", values)

      // The four bounds the triangle inequality is made of, two per limit.
      aboveA <- rules.spec(gapA, bounds.above)
      aboveNegA <- rules.spec(gapA, bounds.aboveNegation)
      aboveB <- rules.spec(gapB, bounds.above)
      aboveNegB <- rules.spec(gapB, bounds.aboveNegation)

      split <- rules.spec(difference, bounds.cases)

      plain <- Parser.proposition(theory, notation, "abs (a:real - b:real) = a - b")
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !u:real. !v:real. !g:real. !e:real. " +
            "-(x - p) <= u ==> x - q <= v ==> u < e / 2 ==> v < e / 2 ==> g = p - q ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atIndex, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveNegA))
          .flatMap(rules.mp(_, aboveB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      negated <- Parser.proposition(theory, notation, "abs (a:real - b:real) = -(a - b)")
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negated))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !u:real. !v:real. !g:real. !e:real. " +
            "x - p <= u ==> -(x - q) <= v ==> u < e / 2 ==> v < e / 2 ==> g = -(p - q) ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atIndex, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveA))
          .flatMap(rules.mp(_, aboveNegB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      closeGap <- rules.disjElim(split, fromPlain, fromNegated)

      withoutB <- rules.existsElim(nearB, k, closeGap)
      withoutA <- rules.existsElim(nearA, m, withoutB)

      everyPositive <- rules.disch(positive, withoutA).flatMap(rules.gen(e, _))
      nonNegative <- rules.spec(difference, bounds.nonNegative)
      vanishes <- rules
        .spec(distance, epsilon)
        .flatMap(rules.mp(_, nonNegative))
        .flatMap(rules.mp(_, everyPositive))
      differenceZero <- rules.spec(difference, bounds.zero).flatMap(rules.mp(_, vanishes))
      equal <- linarith
        .prove("!p:real. !q:real. p - q = 0 ==> p = q")
        .flatMap(rules.specAll(_, List(a, b)))
        .flatMap(rules.mp(_, differenceZero))

      result <- rules
        .disch(toB, equal)
        .flatMap(rules.disch(toA, _))
        .flatMap(rules.gen(b, _))
        .flatMap(rules.gen(a, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s t a b. converges s a ==> converges t b ==> converges (\n. s n + t n) (a + b)`
   *
   * The epsilon argument [[uniqueLimit]] runs into a contradiction, run forwards instead. Both
   * sequences are put inside half the tolerance, the two witnesses are taken out with
   * `existsElim`, and the index that answers the goal is their **sum**, which is above each of them
   * by `Peano.NUM_LE_ADD` and needs no maximum that `num` has not got.
   *
   * The distance is settled by [[Bounds]] and `Linarith` rather than by the triangle inequality,
   * and [[Added]]'s note says why at length: inside each branch of `ABS_CASES` the `abs` is gone
   * and what remains is linear over eight atoms, which is inside the fragment `Linarith` decides.
   */
  private def convergesAdd(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds,
    indices: Indices
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val t = Term.variable("t", sequences)
    val a = Term.variable("a", values)
    val b = Term.variable("b", values)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)
    val k = Term.variable("k", numbers)

    for {
      toA <- Parser.proposition(theory, notation, "converges (s:num -> real) (a:real)")
      toB <- Parser.proposition(theory, notation, "converges (t:num -> real) (b:real)")
      assumedA <- LogicError.lift(Kernel.assume(toA))
      assumedB <- LogicError.lift(Kernel.assume(toB))

      unfoldedA <- Conv.unfold(convergesDefinition, List(s, a)).flatMap(normaliseRight)
      unfoldedB <- Conv.unfold(convergesDefinition, List(t, b)).flatMap(normaliseRight)
      bodyA <- LogicError.lift(Kernel.eqMp(unfoldedA, assumedA))
      bodyB <- LogicError.lift(Kernel.eqMp(unfoldedB, assumedB))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      half <- Parser.term(theory, notation, "e:real / 2", values)
      halfPositive <- linarith
        .prove("!e:real. 0 < e ==> 0 < e / 2")
        .flatMap(rules.spec(e, _))
        .flatMap(rules.mp(_, assumedPositive))

      nearA <- rules.spec(half, bodyA).flatMap(rules.mp(_, halfPositive))
      nearB <- rules.spec(half, bodyB).flatMap(rules.mp(_, halfPositive))

      insideA <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (a:real)) < e:real / 2"
      )
      insideB <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE k:num n ==> abs ((t:num -> real) n - (b:real)) < e:real / 2"
      )
      assumedInsideA <- LogicError.lift(Kernel.assume(insideA))
      assumedInsideB <- LogicError.lift(Kernel.assume(insideB))

      // One index above both, and it is a sum rather than a maximum because `num` has no maximum.
      index <- Parser.term(theory, notation, "NUM_ADD m:num k:num", numbers)
      guard <- Parser.proposition(theory, notation, "NUM_LE (NUM_ADD m:num k:num) n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))

      aboveM <- rules.specAll(indices.atMostSum, List(m, k))
      pastM <- rules
        .conjIntro(aboveM, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(m, index, n)).flatMap(rules.mp(_, both)))

      aboveK <- for {
        other <- rules.specAll(indices.atMostSum, List(k, m))
        swap <- rules.specAll(indices.commutative, List(k, m))
        carried <- rewriteWith(swap, other)
      } yield carried
      pastK <- rules
        .conjIntro(aboveK, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(k, index, n)).flatMap(rules.mp(_, both)))

      closeA <- rules.spec(n, assumedInsideA).flatMap(rules.mp(_, pastM))
      closeB <- rules.spec(n, assumedInsideB).flatMap(rules.mp(_, pastK))

      // The atoms the two branches below are linear over, read rather than built, for the reason
      // `uniqueLimit` gives: what a reader checks against the case split is a sentence.
      atS <- Parser.term(theory, notation, "(s:num -> real) (n:num)", values)
      atT <- Parser.term(theory, notation, "(t:num -> real) (n:num)", values)
      gapA <- Parser.term(
        theory, notation, "(s:num -> real) (n:num) - (a:real)", values)
      gapB <- Parser.term(
        theory, notation, "(t:num -> real) (n:num) - (b:real)", values)
      distanceA <- Parser.term(
        theory, notation, "abs ((s:num -> real) (n:num) - (a:real))", values)
      distanceB <- Parser.term(
        theory, notation, "abs ((t:num -> real) (n:num) - (b:real))", values)
      total <- Parser.term(
        theory,
        notation,
        "(s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real))",
        values
      )
      distance <- Parser.term(
        theory,
        notation,
        "abs ((s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real)))",
        values
      )

      aboveA <- rules.spec(gapA, bounds.above)
      aboveNegA <- rules.spec(gapA, bounds.aboveNegation)
      aboveB <- rules.spec(gapB, bounds.above)
      aboveNegB <- rules.spec(gapB, bounds.aboveNegation)

      split <- rules.spec(total, bounds.cases)

      plain <- Parser.proposition(
        theory,
        notation,
        "abs ((s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real))) = " +
          "(s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real))"
      )
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !y:real. !u:real. !v:real. !g:real. !e:real. " +
            "x - p <= u ==> y - q <= v ==> u < e / 2 ==> v < e / 2 ==> " +
            "g = x + y - (p + q) ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atS, atT, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveA))
          .flatMap(rules.mp(_, aboveB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      negatedCase <- Parser.proposition(
        theory,
        notation,
        "abs ((s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real))) = " +
          "-((s:num -> real) (n:num) + (t:num -> real) (n:num) - ((a:real) + (b:real)))"
      )
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negatedCase))
        lemma <- linarith.prove(
          "!p:real. !q:real. !x:real. !y:real. !u:real. !v:real. !g:real. !e:real. " +
            "-(x - p) <= u ==> -(y - q) <= v ==> u < e / 2 ==> v < e / 2 ==> " +
            "g = -(x + y - (p + q)) ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, b, atS, atT, distanceA, distanceB, distance, e))
          .flatMap(rules.mp(_, aboveNegA))
          .flatMap(rules.mp(_, aboveNegB))
          .flatMap(rules.mp(_, closeA))
          .flatMap(rules.mp(_, closeB))
          .flatMap(rules.mp(_, assumed))
      } yield result

      closeGap <- rules.disjElim(split, fromPlain, fromNegated)

      guarded <- rules.disch(guard, closeGap).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> " +
          "abs ((s:num -> real) n + (t:num -> real) n - ((a:real) + (b:real))) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, index, guarded)

      withoutB <- rules.existsElim(nearB, k, witnessed)
      withoutA <- rules.existsElim(nearA, m, withoutB)
      whole <- rules.disch(positive, withoutA).flatMap(rules.gen(e, _))

      sequence <- Parser.term(
        theory, notation, "\\n:num. (s:num -> real) n + (t:num -> real) n", sequences)
      limit <- Parser.term(theory, notation, "(a:real) + (b:real)", values)
      unfoldedSum <- Conv.unfold(convergesDefinition, List(sequence, limit)).flatMap(normaliseRight)
      bodySum <- rightOf(unfoldedSum)
      _ <- sameStatement(notation, whole, bodySum)
      folded <- Conv
        .sym(unfoldedSum)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))

      result <- rules
        .disch(toB, folded)
        .flatMap(rules.disch(toA, _))
        .flatMap(rules.gen(b, _))
        .flatMap(rules.gen(a, _))
        .flatMap(rules.gen(t, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s a. converges s a ==> converges (\n. -(s n)) (-a)`
   *
   * The same index answers, and the same tolerance: negating a sequence does not move any distance,
   * so nothing is halved and nothing is put together. What the two branches of `ABS_CASES` need is
   * the two bounds the other derivation also uses, and they arrive the other way round, since the
   * quantity whose sign is split is the negation of the one they bound.
   */
  private def convergesNegated(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val a = Term.variable("a", values)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)

    for {
      toA <- Parser.proposition(theory, notation, "converges (s:num -> real) (a:real)")
      assumedA <- LogicError.lift(Kernel.assume(toA))
      unfoldedA <- Conv.unfold(convergesDefinition, List(s, a)).flatMap(normaliseRight)
      bodyA <- LogicError.lift(Kernel.eqMp(unfoldedA, assumedA))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- rules.spec(e, bodyA).flatMap(rules.mp(_, assumedPositive))

      inside <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (a:real)) < e:real"
      )
      assumedInside <- LogicError.lift(Kernel.assume(inside))

      guard <- Parser.proposition(theory, notation, "NUM_LE m:num n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      close <- rules.spec(n, assumedInside).flatMap(rules.mp(_, assumedGuard))

      atS <- Parser.term(theory, notation, "(s:num -> real) (n:num)", values)
      gap <- Parser.term(theory, notation, "(s:num -> real) (n:num) - (a:real)", values)
      distanceOf <- Parser.term(
        theory, notation, "abs ((s:num -> real) (n:num) - (a:real))", values)
      total <- Parser.term(
        theory, notation, "-((s:num -> real) (n:num)) - -(a:real)", values)
      distance <- Parser.term(
        theory, notation, "abs (-((s:num -> real) (n:num)) - -(a:real))", values)

      above <- rules.spec(gap, bounds.above)
      aboveNegation <- rules.spec(gap, bounds.aboveNegation)
      split <- rules.spec(total, bounds.cases)

      plain <- Parser.proposition(
        theory,
        notation,
        "abs (-((s:num -> real) (n:num)) - -(a:real)) = " +
          "-((s:num -> real) (n:num)) - -(a:real)"
      )
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        lemma <- linarith.prove(
          "!p:real. !x:real. !u:real. !g:real. !e:real. " +
            "-(x - p) <= u ==> u < e ==> g = -x - -p ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, atS, distanceOf, distance, e))
          .flatMap(rules.mp(_, aboveNegation))
          .flatMap(rules.mp(_, close))
          .flatMap(rules.mp(_, assumed))
      } yield result

      negatedCase <- Parser.proposition(
        theory,
        notation,
        "abs (-((s:num -> real) (n:num)) - -(a:real)) = " +
          "-(-((s:num -> real) (n:num)) - -(a:real))"
      )
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negatedCase))
        lemma <- linarith.prove(
          "!p:real. !x:real. !u:real. !g:real. !e:real. " +
            "x - p <= u ==> u < e ==> g = -(-x - -p) ==> g < e"
        )
        result <- rules
          .specAll(lemma, List(a, atS, distanceOf, distance, e))
          .flatMap(rules.mp(_, above))
          .flatMap(rules.mp(_, close))
          .flatMap(rules.mp(_, assumed))
      } yield result

      closeGap <- rules.disjElim(split, fromPlain, fromNegated)

      guarded <- rules.disch(guard, closeGap).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> abs (-((s:num -> real) n) - -(a:real)) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, m, guarded)
      eliminated <- rules.existsElim(near, m, witnessed)
      whole <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))

      sequence <- Parser.term(
        theory, notation, "\\n:num. -((s:num -> real) n)", sequences)
      limit <- Parser.term(theory, notation, "-(a:real)", values)
      unfoldedNeg <- Conv.unfold(convergesDefinition, List(sequence, limit)).flatMap(normaliseRight)
      bodyNeg <- rightOf(unfoldedNeg)
      _ <- sameStatement(notation, whole, bodyNeg)
      folded <- Conv
        .sym(unfoldedNeg)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))

      result <- rules
        .disch(toA, folded)
        .flatMap(rules.gen(a, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }


  /**
   * `|- !s t a b. converges s a ==> converges t b ==> converges (\n. s n * t n) (a * b)`
   *
   * The limit of a product, and it is the fact `docs/adr/0017`'s second point stands on: the Cauchy
   * product rearranges a double series and then has to say what the rearranged thing converges to,
   * which is a statement about a product of two limits. [[Added]] is the same shape one operation
   * down and its note names what it was for; this one is not that derivation with a symbol changed,
   * and the two paragraphs below are the whole of the difference.
   *
   * == Why the tolerance is asked for three times and not two ==
   *
   * `abs (s n * t n - a * b)` is split as `abs (s n) * abs (t n - b) + abs (s n - a) * abs b`, and
   * the first summand carries a factor, `abs (s n)`, that the hypotheses bound at **no** fixed
   * number: the sequence is near `a` past some index, and how near depends on the tolerance the
   * caller picked. So a bound on it has to be bought, and what buys it is the convergence of `s`
   * asked at the tolerance `1`, which gives `abs (s n) <= abs a + 1` from that index on. The other
   * two askings are the tolerance the estimate actually needs, one per sequence. Three indices, and
   * the one that answers is their sum for [[Added]]'s reason: `num` has no maximum.
   *
   * **The textbook halves the tolerance and this one does not**, which is where the two derivations
   * part. Halving works there because the two summands are bounded by the same thing; here they are
   * bounded by `tolerance * (abs a + 1)` and `tolerance * (abs b + 1)`, whose sum is the tolerance
   * times a quantity fixed by `a` and `b` alone. So the tolerance is chosen to make that sum come
   * out at `e` exactly: it is `e * inv ((abs a + 1) + (abs b + 1))`, and the last step of the
   * estimate is an **equation** rather than the sum of two halves.
   *
   * == The reciprocal, which is the one thing here no procedure decides ==
   *
   * `Linarith` refuses a symbolic denominator by name, and `Transcendental.EXP_ONE_ABOVE_TWO` is
   * where the shape that answers it was written down: the reciprocal enters as a term whose only
   * property used is `MUL_INVERSE` at a denominator already known positive, and every arithmetic
   * step is a schematic implication over real **variables**, proved once and specialised afterwards
   * at the terms of this problem. Nothing here is put to a procedure with a quotient in it.
   *
   * What that costs is three ring identities over variables — that `(x - p) + p` is `x`, that
   * `x * y - p * q` splits, and that `(x * v) * p + (x * v) * q` collects — and three uses of
   * `MUL_SYM` to bring two bounds into the same shape. The commutations are not decoration: a
   * bound proved as `p * c <= q * c` and one proved as `c * p < c * q` are two theorems modus
   * ponens cannot join, and rewriting one of them is cheaper than a lemma stated twice.
   */
  private def convergesMultiplied(
    logic: Logic,
    linarith: Linarith,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds,
    indices: Indices,
    products: Products
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val t = Term.variable("t", sequences)
    val a = Term.variable("a", values)
    val b = Term.variable("b", values)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)
    val k = Term.variable("k", numbers)
    val j = Term.variable("j", numbers)
    val x = Term.variable("x", values)
    val y = Term.variable("y", values)
    val p = Term.variable("p", values)
    val q = Term.variable("q", values)
    val v = Term.variable("v", values)

    /** A ring identity over plain variables, closed so that a caller specialises it at terms. */
    def schematic(text: String, binders: List[FVar]): Either[LogicError, Kernel.Thm] =
      binders.foldLeft(ring.prove(text))((theorem, binder) => theorem.flatMap(rules.gen(binder, _)))

    for {
      toA <- Parser.proposition(theory, notation, "converges (s:num -> real) (a:real)")
      toB <- Parser.proposition(theory, notation, "converges (t:num -> real) (b:real)")
      assumedA <- LogicError.lift(Kernel.assume(toA))
      assumedB <- LogicError.lift(Kernel.assume(toB))

      unfoldedA <- Conv.unfold(convergesDefinition, List(s, a)).flatMap(normaliseRight)
      unfoldedB <- Conv.unfold(convergesDefinition, List(t, b)).flatMap(normaliseRight)
      bodyA <- LogicError.lift(Kernel.eqMp(unfoldedA, assumedA))
      bodyB <- LogicError.lift(Kernel.eqMp(unfoldedB, assumedB))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))

      absA <- Parser.term(theory, notation, "abs (a:real)", values)
      absB <- Parser.term(theory, notation, "abs (b:real)", values)
      boundA <- Parser.term(theory, notation, "abs (a:real) + 1", values)
      boundB <- Parser.term(theory, notation, "abs (b:real) + 1", values)
      scale <- Parser.term(
        theory, notation, "(abs (a:real) + 1) + (abs (b:real) + 1)", values)
      tolerance <- Parser.term(
        theory,
        notation,
        "e:real * inv ((abs (a:real) + 1) + (abs (b:real) + 1))",
        values
      )
      inverseTerm <- Parser.term(
        theory, notation, "inv ((abs (a:real) + 1) + (abs (b:real) + 1))", values)
      one <- Parser.term(theory, notation, "(1:real)", values)

      nonNegativeA <- rules.spec(a, bounds.nonNegative)
      nonNegativeB <- rules.spec(b, bounds.nonNegative)
      positiveBoundA <- linarith
        .prove("!x:real. 0 <= x ==> 0 < x + 1")
        .flatMap(rules.spec(absA, _))
        .flatMap(rules.mp(_, nonNegativeA))
      positiveBoundB <- linarith
        .prove("!x:real. 0 <= x ==> 0 < x + 1")
        .flatMap(rules.spec(absB, _))
        .flatMap(rules.mp(_, nonNegativeB))
      positiveScale <- linarith
        .prove("!x:real. !y:real. 0 <= x ==> 0 <= y ==> 0 < (x + 1) + (y + 1)")
        .flatMap(rules.specAll(_, List(absA, absB)))
        .flatMap(rules.mp(_, nonNegativeA))
        .flatMap(rules.mp(_, nonNegativeB))

      // The reciprocal's only property anything here uses, bought where the denominator is already
      // known positive, which is what keeps `Field`'s side condition out of every goal below.
      scaleNotZero <- rules.spec(scale, products.nonZero).flatMap(rules.mp(_, positiveScale))
      inverseEquation <- rules.spec(scale, products.inverse).flatMap(rules.mp(_, scaleNotZero))
      positiveInverse <- rules
        .spec(scale, products.inversePositive)
        .flatMap(rules.mp(_, positiveScale))
      positiveTolerance <- rules
        .conjIntro(assumedPositive, positiveInverse)
        .flatMap(both =>
          rules
            .specAll(products.productPositive, List(e, inverseTerm))
            .flatMap(rules.mp(_, both)))

      // The tolerance times what the two bounds add up to is `e` on the nose, which is what this
      // derivation has instead of halving. Nothing below divides anything.
      collected <- schematic(
        "(x:real * v:real) * p:real + (x:real * v:real) * q:real = x:real * ((p:real + q:real) * v:real)",
        List(q, p, v, x)
      ).flatMap(rules.specAll(_, List(e, inverseTerm, boundA, boundB)))
      cancelled <- rewriteInProposition(inverseEquation, collected)
      toleranceSpends <- rules
        .spec(e, products.unit)
        .flatMap(unit => Conv.trans(cancelled, unit))

      // The three askings. The first is what bounds `abs (s n)` and is the reason there are three.
      withinOne <- rules.spec(one, bodyA).flatMap(rules.mp(_, products.zeroLessOne))
      nearA <- rules.spec(tolerance, bodyA).flatMap(rules.mp(_, positiveTolerance))
      nearB <- rules.spec(tolerance, bodyB).flatMap(rules.mp(_, positiveTolerance))

      insideOne <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (a:real)) < 1"
      )
      insideA <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE k:num n ==> abs ((s:num -> real) n - (a:real)) < " +
          "e:real * inv ((abs (a:real) + 1) + (abs (b:real) + 1))"
      )
      insideB <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE j:num n ==> abs ((t:num -> real) n - (b:real)) < " +
          "e:real * inv ((abs (a:real) + 1) + (abs (b:real) + 1))"
      )
      assumedInsideOne <- LogicError.lift(Kernel.assume(insideOne))
      assumedInsideA <- LogicError.lift(Kernel.assume(insideA))
      assumedInsideB <- LogicError.lift(Kernel.assume(insideB))

      index <- Parser.term(
        theory, notation, "NUM_ADD (NUM_ADD m:num k:num) j:num", numbers)
      firstPair <- Parser.term(theory, notation, "NUM_ADD m:num k:num", numbers)
      guard <- Parser.proposition(
        theory, notation, "NUM_LE (NUM_ADD (NUM_ADD m:num k:num) j:num) n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))

      pairInIndex <- rules.specAll(indices.atMostSum, List(firstPair, j))
      inPair <- rules.specAll(indices.atMostSum, List(m, k))
      kInPair <- for {
        other <- rules.specAll(indices.atMostSum, List(k, m))
        swap <- rules.specAll(indices.commutative, List(k, m))
        carried <- rewriteWith(swap, other)
      } yield carried
      jInIndex <- for {
        other <- rules.specAll(indices.atMostSum, List(j, firstPair))
        swap <- rules.specAll(indices.commutative, List(j, firstPair))
        carried <- rewriteWith(swap, other)
      } yield carried

      mInIndex <- rules
        .conjIntro(inPair, pairInIndex)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(m, firstPair, index)).flatMap(rules.mp(_, both)))
      kInIndex <- rules
        .conjIntro(kInPair, pairInIndex)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(k, firstPair, index)).flatMap(rules.mp(_, both)))

      pastM <- rules
        .conjIntro(mInIndex, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(m, index, n)).flatMap(rules.mp(_, both)))
      pastK <- rules
        .conjIntro(kInIndex, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(k, index, n)).flatMap(rules.mp(_, both)))
      pastJ <- rules
        .conjIntro(jInIndex, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(j, index, n)).flatMap(rules.mp(_, both)))

      withinOneAt <- rules.spec(n, assumedInsideOne).flatMap(rules.mp(_, pastM))
      closeA <- rules.spec(n, assumedInsideA).flatMap(rules.mp(_, pastK))
      closeB <- rules.spec(n, assumedInsideB).flatMap(rules.mp(_, pastJ))

      atS <- Parser.term(theory, notation, "(s:num -> real) (n:num)", values)
      atT <- Parser.term(theory, notation, "(t:num -> real) (n:num)", values)
      gapA <- Parser.term(theory, notation, "(s:num -> real) (n:num) - (a:real)", values)
      gapB <- Parser.term(theory, notation, "(t:num -> real) (n:num) - (b:real)", values)
      distanceA <- Parser.term(
        theory, notation, "abs ((s:num -> real) (n:num) - (a:real))", values)
      distanceB <- Parser.term(
        theory, notation, "abs ((t:num -> real) (n:num) - (b:real))", values)
      sizeOfS <- Parser.term(theory, notation, "abs ((s:num -> real) (n:num))", values)
      leftFactor <- Parser.term(
        theory,
        notation,
        "(s:num -> real) (n:num) * ((t:num -> real) (n:num) - (b:real))",
        values
      )
      rightFactor <- Parser.term(
        theory,
        notation,
        "((s:num -> real) (n:num) - (a:real)) * (b:real)",
        values
      )
      distance <- Parser.term(
        theory,
        notation,
        "abs ((s:num -> real) (n:num) * (t:num -> real) (n:num) - (a:real) * (b:real))",
        values
      )

      // `abs (s n) <= abs a + 1`, which is what the tolerance of one was asked for.
      recomposed <- schematic("(x:real - p:real) + p:real = x:real", List(p, x))
        .flatMap(rules.specAll(_, List(atS, a)))
      sizeSplit <- rules
        .specAll(products.triangle, List(gapA, a))
        .flatMap(rewriteInProposition(recomposed, _))
      sizeBounded <- linarith
        .prove("!x:real. !y:real. !p:real. x <= y + p ==> y < 1 ==> x <= p + 1")
        .flatMap(rules.specAll(_, List(sizeOfS, distanceA, absA)))
        .flatMap(rules.mp(_, sizeSplit))
        .flatMap(rules.mp(_, withinOneAt))

      // The estimate, which is the triangle inequality over a sum nothing wrote and `ABS_MUL` on
      // each half of it.
      rearranged <- schematic(
        "x:real * y:real - p:real * q:real = x:real * (y:real - q:real) + (x:real - p:real) * q:real",
        List(q, p, y, x)
      ).flatMap(rules.specAll(_, List(atS, atT, a, b)))
      estimate <- rules
        .specAll(products.triangle, List(leftFactor, rightFactor))
        .flatMap(theorem =>
          Conv.sym(rearranged).flatMap(rewriteInProposition(_, theorem)))
      leftSize <- rules.specAll(products.multiplicative, List(atS, gapB))
      rightSize <- rules.specAll(products.multiplicative, List(gapA, b))
      split <- rewriteInProposition(leftSize, estimate)
        .flatMap(rewriteInProposition(rightSize, _))

      // Each summand against the tolerance. The two steps of each are a non-strict bound on one
      // factor and a strict one on the other, and `MUL_SYM` is what brings them into one shape: a
      // bound proved as `p * c <= q * c` and one proved as `c * p < c * q` are two theorems modus
      // ponens cannot join.
      leftProduct <- Parser.term(
        theory,
        notation,
        "abs ((s:num -> real) (n:num)) * abs ((t:num -> real) (n:num) - (b:real))",
        values
      )
      leftMiddle <- Parser.term(
        theory,
        notation,
        "abs ((t:num -> real) (n:num) - (b:real)) * (abs (a:real) + 1)",
        values
      )
      leftCeiling <- Parser.term(
        theory,
        notation,
        "(e:real * inv ((abs (a:real) + 1) + (abs (b:real) + 1))) * (abs (a:real) + 1)",
        values
      )
      rightProduct <- Parser.term(
        theory,
        notation,
        "abs ((s:num -> real) (n:num) - (a:real)) * abs (b:real)",
        values
      )
      rightMiddle <- Parser.term(
        theory,
        notation,
        "abs ((s:num -> real) (n:num) - (a:real)) * (abs (b:real) + 1)",
        values
      )
      rightCeiling <- Parser.term(
        theory,
        notation,
        "(e:real * inv ((abs (a:real) + 1) + (abs (b:real) + 1))) * (abs (b:real) + 1)",
        values
      )

      nonNegativeGapA <- rules.spec(gapA, bounds.nonNegative)
      nonNegativeGapB <- rules.spec(gapB, bounds.nonNegative)
      absBelowBound <- linarith.prove("!x:real. x <= x + 1").flatMap(rules.spec(absB, _))

      leftStep <- rules
        .specAll(products.multiplyLe, List(distanceB, sizeOfS, boundA))
        .flatMap(rules.mp(_, nonNegativeGapB))
        .flatMap(rules.mp(_, sizeBounded))
        .flatMap(theorem =>
          rules
            .specAll(products.symmetric, List(boundA, distanceB))
            .flatMap(rewriteInProposition(_, theorem)))
      leftReach <- rules
        .specAll(products.multiplyLt, List(boundA, distanceB, tolerance))
        .flatMap(rules.mp(_, positiveBoundA))
        .flatMap(rules.mp(_, closeB))

      rightStep <- rules
        .specAll(products.multiplyLe, List(distanceA, absB, boundB))
        .flatMap(rules.mp(_, nonNegativeGapA))
        .flatMap(rules.mp(_, absBelowBound))
        .flatMap(theorem =>
          rules
            .specAll(products.symmetric, List(absB, distanceA))
            .flatMap(rewriteInProposition(_, theorem)))
        .flatMap(theorem =>
          rules
            .specAll(products.symmetric, List(boundB, distanceA))
            .flatMap(rewriteInProposition(_, theorem)))
      rightReach <- rules
        .specAll(products.multiplyLt, List(boundB, distanceA, tolerance))
        .flatMap(rules.mp(_, positiveBoundB))
        .flatMap(rules.mp(_, closeA))

      // One schematic implication rather than three, because what the six facts above say is one
      // chain and splitting it would buy three specialisations and the same arithmetic.
      closeGap <- linarith
        .prove(
          "!g:real. !x:real. !y:real. !u:real. !w:real. !v:real. !z:real. !e:real. " +
            "g <= x + y ==> x <= u ==> u < w ==> y <= v ==> v < z ==> w + z = e ==> g < e"
        )
        .flatMap(rules.specAll(
          _,
          List(
            distance, leftProduct, rightProduct, leftMiddle, leftCeiling, rightMiddle,
            rightCeiling, e)))
        .flatMap(rules.mp(_, split))
        .flatMap(rules.mp(_, leftStep))
        .flatMap(rules.mp(_, leftReach))
        .flatMap(rules.mp(_, rightStep))
        .flatMap(rules.mp(_, rightReach))
        .flatMap(rules.mp(_, toleranceSpends))

      guarded <- rules.disch(guard, closeGap).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> " +
          "abs ((s:num -> real) n * (t:num -> real) n - (a:real) * (b:real)) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, index, guarded)

      withoutB <- rules.existsElim(nearB, j, witnessed)
      withoutA <- rules.existsElim(nearA, k, withoutB)
      withoutOne <- rules.existsElim(withinOne, m, withoutA)
      whole <- rules.disch(positive, withoutOne).flatMap(rules.gen(e, _))

      sequence <- Parser.term(
        theory, notation, "\\n:num. (s:num -> real) n * (t:num -> real) n", sequences)
      limit <- Parser.term(theory, notation, "(a:real) * (b:real)", values)
      unfoldedProduct <- Conv
        .unfold(convergesDefinition, List(sequence, limit))
        .flatMap(normaliseRight)
      bodyProduct <- rightOf(unfoldedProduct)
      _ <- sameStatement(notation, whole, bodyProduct)
      folded <- Conv
        .sym(unfoldedProduct)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))

      result <- rules
        .disch(toB, folded)
        .flatMap(rules.disch(toA, _))
        .flatMap(rules.gen(b, _))
        .flatMap(rules.gen(a, _))
        .flatMap(rules.gen(t, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !f l. converges (Sum (\i. abs (f i))) l ==> ?m. converges (Sum f) m`
   *
   * An absolutely convergent series converges, **and without a Cauchy criterion**, which this
   * repository does not have. That is the whole of what is worth reading here rather than the
   * statement: the textbook route shows the partial sums are Cauchy and appeals to completeness
   * through a criterion nothing here states, and building one is a piece of work of its own. This
   * route appeals to completeness exactly once, through [[Comparison]], which is
   * [[MonotoneConverges]] on a series of non-negative terms and was already here.
   *
   * == The trick, which is one line of algebra ==
   *
   * `f i` is `(f i + abs (f i)) - abs (f i)`, and the bracket is **non-negative** and at most
   * `abs (f i) + abs (f i)`: the lower bound is `Magnitude.ABS_ABOVE_NEG` and the upper is
   * `Magnitude.ABS_ABOVE`, one each and nothing else. So the series of brackets has non-negative
   * terms dominated by one whose partial sums are bounded, which is what the comparison test asks
   * for, and what comes back is a convergence. Taking the absolute series off again is
   * [[Negated]] and [[Added]], both of which take a convergence as a hypothesis and neither of
   * which reaches the sixteenth axiom.
   *
   * == Where the hypothesis becomes a bound, which is the half that is not the trick ==
   *
   * The comparison test wants the dominating partial sums **bounded** and the hypothesis gives
   * that they converge. A series of non-negative terms has increasing partial sums, by
   * `Series.SUM_SUC` and `Magnitude.ABS_NONNEG`; [[MonotoneBelow]] carries that to every pair of
   * indices; and [[AboveBound]] at one of its own terms turns "increasing and convergent to `l`"
   * into "at most `l`". That last step is the one to read: the useful lower bound on an increasing
   * sequence is one of its own terms, which is exactly what [[AboveBound]] was published for and
   * is false below that term's index. The bound handed over is `l + l`, the absolute series twice.
   *
   * == The lambda at the end, and a claim about it that was measured and dropped ==
   *
   * The two sequences are identified by [[Eventually]] at index zero: what [[Added]] produces is
   * a lambda over the two and what is wanted is `Sum f`, equal at every index without being the
   * same term. That lambda **does** carry a beta redex, since [[Negated]]'s sequence goes in as
   * a lambda and comes back applied, and `Conv.betaNormalise` moves it, which is the check.
   *
   * Reducing it is nevertheless **not** load-bearing, and this derivation did it for a paragraph
   * on the strength of a sentence rather than a measurement. A perturbation that removed the
   * reduction left the whole suite green, so the call is gone rather than kept with prose beside
   * it. `LimitSpec`'s composition test records the same trap from the other side, where the redex
   * does reach an assertion and the comparison against the written form goes red; the difference
   * is that nothing downstream of this one reads the intermediate sequence.
   *
   * == What is NOT published beside it ==
   *
   * `abs (Sum f n) <= Sum (\i. abs (f i)) n`, the triangle inequality at a finite sum. It is the
   * other basic fact about absolute values and sums, it is three lines from `ABS_TRIANGLE`, and
   * **nothing asks for it today**: this theorem does not, since the trick goes through an
   * inequality between summands rather than between sums. `Series.SUM_CONGRUENCE_BELOW`'s note
   * argues at length against adding library entries nobody has asked for, and this is that
   * argument applied to the first entry that would have been added for symmetry alone.
   */
  /**
   * [[BelowLimit]], lifted out of [[absolutelyConvergent]] when a second consumer arrived.
   *
   * The generalisation is from `abs (f i)` to any non-negative summand, which costs the caller
   * one `Magnitude.ABS_NONNEG` and costs this nothing: the derivation never read anything about
   * `abs` except that it is non-negative.
   */
  /**
   * [[SquareBelowCauchy]], which is where the split at `n / 2` was supposed to be and is not.
   *
   * Every pair `(i, j)` with `i < n` and `j < n` has `i + j < n + n`, so the square of side `n`
   * sits inside the triangle of side `n + n`. As sums: the partial Cauchy sum at `n + n` is
   * `Series.SUM_HALVES` into a first half and a second, the second is non-negative and dropped,
   * and the first dominates `Sum a n * Sum b n` term by term because a row read at `(n + n) - i`
   * is longer than one read at `n` whenever `i <= n`.
   *
   * **That last step wanted two lemmas and neither existed.** The comparison holds only below the
   * bound, which is `Series.SUM_MONOTONE_BELOW`; and the arithmetic under it is
   * `Peano.NUM_LE_DOUBLE_SUB`, which is `2n - i >= n` written with `NUM_ADD n n` so that no
   * division appears anywhere. Both landed for this.
   */
  private def squareUnderCauchy(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    pieces: Squares
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val a = Term.variable("a", sequences)
    val b = Term.variable("b", sequences)
    val n = Term.variable("n", numbers)

    def normalised(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    def sidesOf(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
      Term
        .destEq(theorem.conclusion)
        .toRight(NotOfForm("an equation", theorem.conclusion))

    def summandOf(term: Term): Either[LogicError, Term] = term match {
      case App(App(_, body), _) => Right(body)
      case other                => Left(NotOfForm("a sum", other))
    }

    /** The right of `x <= y`, which is where an order statement keeps the larger side. */
    def largerOf(term: Term): Either[LogicError, Term] = term match {
      case App(App(_, _), larger) => Right(larger)
      case other                  => Left(NotOfForm("an order statement", other))
    }

    /** Open a bounded pointwise obligation and hand its index and guard to the caller. */
    def belowTheBound(
      left: Term,
      right: Term,
      length: Term,
      close: (Term, FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        instance <- rules
          .specAll(pieces.monotoneBelow, List(left, right, length))
          .flatMap(normalised)
        obligation <- logic
          .destImp(instance.conclusion)
          .map(_._1)
          .toRight(NotOfForm("an implication", instance.conclusion))
        stripped <- Logic.stripForall(obligation)
        index <- stripped._1.headOption
          .toRight(NotOfForm("a claim about every index", obligation))
        parts <- logic
          .destImp(stripped._2)
          .toRight(NotOfForm("an implication", stripped._2))
        (guard, body) = parts
        assumed <- LogicError.lift(Kernel.assume(guard))
        proved <- close(body, index, assumed)
        result <- rules
          .disch(guard, proved)
          .flatMap(rules.gen(index, _))
          .flatMap(rules.mp(instance, _))
      } yield result

    /** Open an unbounded pointwise obligation the same way. */
    def everywhere(
      body: Term,
      close: (Term, FVar) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        instance <- rules.spec(body, pieces.nonNegativeSum).flatMap(normalised)
        obligation <- logic
          .destImp(instance.conclusion)
          .map(_._1)
          .toRight(NotOfForm("an implication", instance.conclusion))
        stripped <- Logic.stripForall(obligation)
        index <- stripped._1.headOption
          .toRight(NotOfForm("a claim about every index", obligation))
        proved <- close(stripped._2, index).flatMap(rules.gen(index, _))
        result <- rules.mp(instance, proved)
      } yield result

    for {
      nonNegativeA <- Parser.proposition(theory, notation, "!i:num. 0 <= (a:num -> real) i")
      nonNegativeB <- Parser.proposition(theory, notation, "!i:num. 0 <= (b:num -> real) i")
      assumedA <- LogicError.lift(Kernel.assume(nonNegativeA))
      assumedB <- LogicError.lift(Kernel.assume(nonNegativeB))

      doubled <- Parser.term(theory, notation, "NUM_ADD (n:num) (n:num)", numbers)
      partialB <- Parser.term(theory, notation, "Sum (b:num -> real) (n:num)", values)

      rowsNonNegative <- rules.spec(b, pieces.nonNegativeSum).flatMap(rules.mp(_, assumedB))
      ordered <- rules.spec(b, pieces.grows).flatMap(rules.mp(_, assumedB))

      // The Cauchy partial sum at twice the length, as one sum over rows.
      wideAt <- rules.specAll(pieces.cauchy, List(a, b, doubled))
      wideBody <- sidesOf(wideAt).map(_._2).flatMap(summandOf)

      // Halved, and the second half dropped because every term of it is a product of two
      // non-negative numbers: a term of `a`, and a partial sum of `b`.
      split <- rules.specAll(pieces.halves, List(wideBody, n)).flatMap(normalised)
      secondHalf <- sidesOf(split).map(_._2).flatMap(largerOf)
      shiftedBody <- summandOf(secondHalf)
      secondNonNegative <- everywhere(
        shiftedBody,
        (goal, index) =>
          goal match {
            case App(App(_, _), App(App(_, factor), row)) =>
              for {
                // The factor is `a (n + z)` and not `a z`: the second half is the shifted one,
                // so the non-negativity is asked at the shifted index rather than at the index.
                at <- factor match {
                  case App(_, argument) => Right(argument)
                  case other            => Left(NotOfForm("a term of the sequence", other))
                }
                positive <- rules.spec(at, assumedA)
                length <- row match {
                  case App(_, end) => Right(end)
                  case other       => Left(NotOfForm("a partial sum", other))
                }
                rows <- rules.spec(length, rowsNonNegative)
                product <- rules
                  .specAll(pieces.productNonNegative, List(factor, row))
                  .flatMap(rules.mp(_, positive))
                  .flatMap(rules.mp(_, rows))
              } yield product
            case other => Left(NotOfForm("a product of two", other))
          }
      ).flatMap(rules.spec(n, _))

      // The first half dominates the square, term by term and only below the bound.
      product <- rules.specAll(pieces.scaledRight, List(partialB, a, n)).flatMap(normalised)
      squareBody <- sidesOf(product).map(_._1).flatMap(summandOf)
      dominated <- belowTheBound(
        squareBody,
        wideBody,
        n,
        (goal, index, bound) =>
          for {
            weak <- rules.specAll(pieces.atMostFromBelow, List(index, n)).flatMap(rules.mp(_, bound))
            reaches <- rules.specAll(pieces.atMostDouble, List(n, index)).flatMap(rules.mp(_, weak))
            far <- largerOf(reaches.conclusion)
            longer <- rules.specAll(ordered, List(n, far)).flatMap(rules.mp(_, reaches))
            farSum <- largerOf(longer.conclusion)
            here <- LogicError.lift(Term.app(a, index))
            positive <- rules.spec(index, assumedA)
            scaled <- rules
              .specAll(pieces.multiplyLe, List(here, partialB, farSum))
              .flatMap(rules.mp(_, positive))
              .flatMap(rules.mp(_, longer))
            turnedLeft <- rules.specAll(pieces.symmetric, List(partialB, here))
            turnedRight <- rules.specAll(pieces.symmetric, List(farSum, here))
            settled <- rewriteInProposition(turnedLeft, scaled)
              .flatMap(rewriteInProposition(turnedRight, _))
            _ <- sameStatement(notation, settled, goal)
          } yield settled
      )

      // Six sums, five equations and inequalities between them, and the goal is linear in
      // all six. Nothing here multiplies anything: the two products were made into atoms above.
      square <- sidesOf(product).map(_._2)
      scaledSum <- sidesOf(product).map(_._1)
      firstHalf <- sidesOf(split).map(_._2).flatMap {
        case App(App(_, first), _) => Right(first)
        case other                 => Left(NotOfForm("a sum of two halves", other))
      }
      whole <- sidesOf(split).map(_._1)
      cauchyAt <- sidesOf(wideAt).map(_._1)
      result <- linarith
        .prove(
          "!p:real. !q:real. !r:real. !s:real. !t:real. !c:real. " +
            "q = p ==> q <= r ==> 0 <= s ==> t = r + s ==> c = t ==> p <= c"
        )
        .flatMap(rules.specAll(
          _, List(square, scaledSum, firstHalf, secondHalf, whole, cauchyAt)))
        .flatMap(rules.mp(_, product))
        .flatMap(rules.mp(_, dominated))
        .flatMap(rules.mp(_, secondNonNegative))
        .flatMap(rules.mp(_, split))
        .flatMap(rules.mp(_, wideAt))
        .flatMap(rules.disch(nonNegativeB, _))
        .flatMap(rules.disch(nonNegativeA, _))
        .flatMap(rules.genAll(_, List(a, b, n)))
    } yield result
  }

  /**
   * [[CauchyBelowSquare]], which is `SUM_CAUCHY_GAP` read as a statement about a sign.
   *
   * Nothing here is an induction and nothing is an estimate. The gap is a sum whose every term is
   * `a i` against a tail of `b`; both factors are non-negative, so the sum is, so the thing it is
   * the gap of is the larger. The only fact that is not immediate is that a tail of a
   * non-negative series is non-negative, which is [[Grows]] at `n - i` and `n`.
   */
  private def cauchyUnderSquare(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    cauchyGap: Kernel.Thm,
    grows: Kernel.Thm,
    nonNegativeSum: Kernel.Thm,
    productNonNegative: Kernel.Thm,
    differenceBelow: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val a = Term.variable("a", sequences)
    val b = Term.variable("b", sequences)
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)

    for {
      nonNegativeA <- Parser.proposition(theory, notation, "!i:num. 0 <= (a:num -> real) i")
      nonNegativeB <- Parser.proposition(theory, notation, "!i:num. 0 <= (b:num -> real) i")
      assumedA <- LogicError.lift(Kernel.assume(nonNegativeA))
      assumedB <- LogicError.lift(Kernel.assume(nonNegativeB))

      gap <- rules.specAll(cauchyGap, List(a, b, n))
      corner <- Term
        .destEq(gap.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", gap.conclusion))
      cornerBody <- corner match {
        case App(App(_, body), _) => Right(body)
        case other                => Left(NotOfForm("a sum", other))
      }

      shorter <- Parser.term(theory, notation, "NUM_SUB (n:num) (i:num)", numbers)
      shortSum <- Parser.term(
        theory, notation, "Sum (b:num -> real) (NUM_SUB (n:num) (i:num))", values)
      longSum <- Parser.term(theory, notation, "Sum (b:num -> real) (n:num)", values)
      tail <- Parser.term(
        theory,
        notation,
        "Sum (b:num -> real) (n:num) - Sum (b:num -> real) (NUM_SUB (n:num) (i:num))",
        values
      )
      here <- Parser.term(theory, notation, "(a:num -> real) (i:num)", values)

      // A tail of a non-negative series is non-negative, which is the one fact here that is not
      // immediate. `NUM_SUB_LE` needs no side condition because the difference is truncated.
      ordered <- rules.spec(b, grows).flatMap(rules.mp(_, assumedB))
      below <- rules.specAll(differenceBelow, List(n, i))
      grown <- rules.specAll(ordered, List(shorter, n)).flatMap(rules.mp(_, below))
      tailNonNegative <- linarith
        .prove("!s:real. !t:real. s <= t ==> 0 <= t - s")
        .flatMap(rules.specAll(_, List(shortSum, longSum)))
        .flatMap(rules.mp(_, grown))

      termNonNegative <- rules
        .spec(i, assumedA)
        .flatMap(atI =>
          rules
            .specAll(productNonNegative, List(here, tail))
            .flatMap(rules.mp(_, atI))
            .flatMap(rules.mp(_, tailNonNegative)))
        .flatMap(rules.gen(i, _))
      cornerNonNegative <- rules
        .spec(cornerBody, nonNegativeSum)
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))
        .flatMap(rules.mp(_, termNonNegative))
        .flatMap(rules.spec(n, _))

      pieces <- Term.destEq(gap.conclusion).map(_._1) match {
        case Some(App(App(_, product), cauchy)) => Right((product, cauchy))
        case _ => Left(NotOfForm("a difference of a square and a triangle", gap.conclusion))
      }
      result <- linarith
        .prove("!p:real. !c:real. !g:real. p - c = g ==> 0 <= g ==> c <= p")
        .flatMap(rules.specAll(_, List(pieces._1, pieces._2, corner)))
        .flatMap(rules.mp(_, gap))
        .flatMap(rules.mp(_, cornerNonNegative))
        .flatMap(rules.disch(nonNegativeB, _))
        .flatMap(rules.disch(nonNegativeA, _))
        .flatMap(rules.genAll(_, List(a, b, n)))
    } yield result
  }

  /**
   * [[Grows]], which is the two lines [[belowItsLimit]] used to open with and two other arguments
   * wrote again.
   *
   * `Series.SUM_SUC` with the hypothesis makes the sequence of partial sums increasing, and
   * [[MonotoneBelow]] carries that to every pair of indices. Nothing else is in it, which is why
   * it went unnoticed as a copy for as long as it did: two lines are cheaper to write again than
   * to look for.
   */
  private def sumsGrow(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    atSuccessor: Kernel.Thm,
    monotoneBelow: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val f = Term.variable("f", sequences)
    val n = Term.variable("n", numbers)

    def normalised(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    for {
      pointwise <- Parser.proposition(theory, notation, "!i:num. 0 <= (f:num -> real) i")
      assumedPointwise <- LogicError.lift(Kernel.assume(pointwise))
      partial <- Parser.term(theory, notation, "Sum (f:num -> real)", sequences)
      atN <- Parser.term(theory, notation, "(f:num -> real) (n:num)", values)

      stepped <- rules.specAll(atSuccessor, List(f, n)).flatMap(normalised)
      steppedParts <- Term.destEq(stepped.conclusion) match {
        case Some((whole, App(App(_, short), _))) => Right((whole, short))
        case _ => Left(NotOfForm("a sum peeled at its top", stepped.conclusion))
      }
      increasing <- rules
        .spec(n, assumedPointwise)
        .flatMap(positive =>
          linarith
            .prove("!s:real. !a:real. !t:real. t = s + a ==> 0 <= a ==> s <= t")
            .flatMap(rules.specAll(_, List(steppedParts._2, atN, steppedParts._1)))
            .flatMap(rules.mp(_, stepped))
            .flatMap(rules.mp(_, positive)))
        .flatMap(rules.gen(n, _))
      ordered <- rules.spec(partial, monotoneBelow).flatMap(rules.mp(_, increasing))
      result <- rules.disch(pointwise, ordered).flatMap(rules.gen(f, _))
    } yield result
  }

  private def belowItsLimit(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    grows: Kernel.Thm,
    aboveBound: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val f = Term.variable("f", sequences)
    val l = Term.variable("l", values)
    val n = Term.variable("n", numbers)

    for {
      pointwise <- Parser.proposition(
        theory, notation, "!i:num. 0 <= (f:num -> real) i")
      assumedPointwise <- LogicError.lift(Kernel.assume(pointwise))
      premise <- Parser.proposition(
        theory, notation, "converges (Sum (f:num -> real)) (l:real)")
      assumed <- LogicError.lift(Kernel.assume(premise))

      partial <- Parser.term(theory, notation, "Sum (f:num -> real)", sequences)
      here <- Parser.term(theory, notation, "Sum (f:num -> real) (n:num)", values)
      ordered <- rules.spec(f, grows).flatMap(rules.mp(_, assumedPointwise))
      everywhere <- rules
        .specAll(aboveBound, List(partial, l, here, n))
        .flatMap(rules.mp(_, assumed))
        .flatMap(theorem => rules.spec(n, ordered).flatMap(rules.mp(theorem, _)))
        .flatMap(rules.gen(n, _))
      result <- rules
        .disch(premise, everywhere)
        .flatMap(rules.disch(pointwise, _))
        .flatMap(rules.genAll(_, List(f, l)))
    } yield result
  }

  /**
   * [[Tail]], which is four facts in one order and no analysis at all.
   *
   * The only thing in it that is not a specialisation is the value: [[Added]] hands back
   * `l + -l` and what is wanted is `0`, so the value is rewritten by a congruence on the
   * convergence's second argument. Doing that to the **value** rather than to the sequence is
   * what keeps [[Eventually]] out of it until the end, where it is needed for the sequence and
   * for nothing else.
   */
  private def tailVanishes(
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    constant: Kernel.Thm,
    negated: Kernel.Thm,
    added: Kernel.Thm,
    eventually: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val f = Term.variable("f", sequences)
    val l = Term.variable("l", values)
    val n = Term.variable("n", numbers)

    def normalised(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    def convergenceOf(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
      theorem.conclusion match {
        case App(App(_, sequence), value) => Right((sequence, value))
        case other                        => Left(NotOfForm("a convergence", other))
      }

    for {
      premise <- Parser.proposition(
        theory, notation, "converges (Sum (f:num -> real)) (l:real)")
      assumed <- LogicError.lift(Kernel.assume(premise))
      partial <- Parser.term(theory, notation, "Sum (f:num -> real)", sequences)

      steady <- rules.spec(l, constant)
      steadyParts <- convergenceOf(steady)
      turned <- rules.specAll(negated, List(partial, l)).flatMap(rules.mp(_, assumed))
      turnedParts <- convergenceOf(turned)
      together <- rules
        .specAll(added, List(steadyParts._1, turnedParts._1, l, turnedParts._2))
        .flatMap(rules.mp(_, steady))
        .flatMap(rules.mp(_, turned))
        .flatMap(normalised)

      // The value, by a congruence on the convergence's second argument rather than by anything
      // about the sequence.
      togetherParts <- convergenceOf(together)
      zero <- Parser.term(theory, notation, "(0:real)", values)
      vanishes <- LogicError
        .lift(Term.eq(togetherParts._2, zero))
        .flatMap(ring.prove)
      leading <- together.conclusion match {
        case App(partial, _) => Right(partial)
        case other           => Left(NotOfForm("a convergence", other))
      }
      atZero <- Conv
        .apTerm(leading, vanishes)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, together)))

      // And the sequence, which a reader writes with a subtraction.
      wanted <- Parser.term(
        theory, notation, "\\n:num. (l:real) - Sum (f:num -> real) n", sequences)
      guard <- Parser.proposition(theory, notation, "NUM_LE ZERO (n:num)")
      indexZero <- Parser.term(theory, notation, "ZERO", numbers)
      agreeing <- rules
        .specAll(eventually, List(togetherParts._1, wanted, zero, indexZero))
        .flatMap(normalised)
        .flatMap(instance =>
          logic
            .destImp(instance.conclusion)
            .toRight(NotOfForm("an implication", instance.conclusion))
            .flatMap { parts =>
              Logic
                .stripForall(parts._1)
                .flatMap { stripped =>
                  stripped._1.headOption
                    .toRight(NotOfForm("a claim about every index", parts._1))
                    .flatMap { index =>
                      logic
                        .destImp(stripped._2)
                        .toRight(NotOfForm("an implication", stripped._2))
                        .flatMap { inner =>
                          ring
                            .prove(inner._2)
                            .flatMap(rules.disch(inner._1, _))
                            .flatMap(rules.gen(index, _))
                            .flatMap(rules.mp(instance, _))
                        }
                    }
                }
            })
      carried <- rules.mp(agreeing, atZero)
      result <- rules
        .disch(premise, carried)
        .flatMap(rules.genAll(_, List(f, l)))
      _ = guard
    } yield result
  }

  private def absolutelyConvergent(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    pieces: Absolutes,
    bounds: Bounds
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val f = Term.variable("f", sequences)
    val l = Term.variable("l", values)
    val m = Term.variable("m", values)
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)

    val absolute = "\\i:num. abs ((f:num -> real) i)"
    val bracket = "\\i:num. (f:num -> real) i + abs (f i)"
    val doubled = "\\i:num. abs ((f:num -> real) i) + abs (f i)"

    def normalised(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    /** The sequence and the value of `converges s v`. */
    def convergenceOf(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
      theorem.conclusion match {
        case App(App(_, sequence), value) => Right((sequence, value))
        case other                        => Left(NotOfForm("a convergence", other))
      }

    /** The shorter partial sum on the right of `Sum f (SUC n) = Sum f n + f n`. */
    def shorter(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
      Term.destEq(theorem.conclusion) match {
        case Some((whole, App(App(_, short), _))) => Right((whole, short))
        case _ => Left(NotOfForm("a sum peeled at its top", theorem.conclusion))
      }

    for {
      absSeries <- Parser.term(theory, notation, "Sum (" + absolute + ")", sequences)
      bracketBody <- Parser.term(theory, notation, bracket)
      doubledBody <- Parser.term(theory, notation, doubled)
      absBody <- Parser.term(theory, notation, absolute)
      bracketSeries <- Parser.term(theory, notation, "Sum (" + bracket + ")", sequences)
      sequence <- Parser.term(theory, notation, "Sum (f:num -> real)", sequences)
      atI <- Parser.term(theory, notation, "(f:num -> real) (i:num)", values)
      sizeAtI <- Parser.term(theory, notation, "abs ((f:num -> real) (i:num))", values)
      twice <- Parser.term(theory, notation, "(l:real) + (l:real)", values)

      premise <- Parser.proposition(
        theory, notation, "converges (Sum (" + absolute + ")) (l:real)")
      assumed <- LogicError.lift(Kernel.assume(premise))

      // The bracket is non-negative and at most the absolute term twice. One `abs` fact each.
      nonNegative <- rules
        .spec(atI, bounds.aboveNegation)
        .flatMap(lower =>
          linarith
            .prove("!x:real. !a:real. -x <= a ==> 0 <= x + a")
            .flatMap(rules.specAll(_, List(atI, sizeAtI)))
            .flatMap(rules.mp(_, lower)))
        .flatMap(rules.gen(i, _))
      dominated <- rules
        .spec(atI, bounds.above)
        .flatMap(upper =>
          linarith
            .prove("!x:real. !a:real. x <= a ==> x + a <= a + a")
            .flatMap(rules.specAll(_, List(atI, sizeAtI)))
            .flatMap(rules.mp(_, upper)))
        .flatMap(rules.gen(i, _))

      // The absolute partial sums never pass their limit, which is [[BelowLimit]] and was this
      // derivation's own twelve lines until that fact was published. All it asks of `abs` is
      // that it is non-negative.
      nonNegativeTerms <- rules.spec(atI, bounds.nonNegative).flatMap(rules.gen(i, _))
      atMostLimit <- rules
        .specAll(pieces.belowLimit, List(absBody, l))
        .flatMap(rules.mp(_, nonNegativeTerms))
        .flatMap(rules.mp(_, assumed))

      // So the dominating partial sums are bounded, and the bound is the limit twice.
      split <- rules.specAll(pieces.additive, List(absBody, absBody, n)).flatMap(normalised)
      splitParts <- shorter(split)
      boundedAt <- linarith
        .prove("!t:real. !s:real. !b:real. t = s + s ==> s <= b ==> t <= b + b")
        .flatMap(rules.specAll(_, List(splitParts._1, splitParts._2, l)))
        .flatMap(rules.mp(_, split))
        .flatMap(theorem => rules.spec(n, atMostLimit).flatMap(rules.mp(theorem, _)))
        .flatMap(rules.gen(n, _))
      boundClaim <- Parser.proposition(
        theory, notation, "?b:real. !n:num. Sum (" + doubled + ") n <= b")
      boundPredicate <- logic
        .destExistsPredicate(boundClaim)
        .toRight(NotOfForm("an existential", boundClaim))
      bounded <- rules.existsIntro(boundPredicate, twice, boundedAt)

      // The comparison test, which is the one place completeness is spent.
      brackets <- rules
        .specAll(pieces.comparison, List(bracketBody, doubledBody))
        .flatMap(rules.mp(_, nonNegative))
        .flatMap(rules.mp(_, dominated))
        .flatMap(rules.mp(_, bounded))

      // And back. The bracket series less the absolute one is the series itself, at every index.
      inner <- Parser.proposition(
        theory, notation, "converges (Sum (" + bracket + ")) (m:real)")
      assumedInner <- LogicError.lift(Kernel.assume(inner))
      negatedSeries <- rules
        .specAll(pieces.negated, List(absSeries, l))
        .flatMap(rules.mp(_, assumed))
      negatedParts <- convergenceOf(negatedSeries)
      together <- rules
        .specAll(pieces.added, List(bracketSeries, negatedParts._1, m, negatedParts._2))
        .flatMap(rules.mp(_, assumedInner))
        .flatMap(rules.mp(_, negatedSeries))
      togetherParts <- convergenceOf(together)

      guard <- Parser.proposition(theory, notation, "NUM_LE ZERO (n:num)")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      bracketSplit <- rules.specAll(pieces.additive, List(f, absBody, n)).flatMap(normalised)
      bracketParts <- Term
        .destEq(bracketSplit.conclusion)
        .toRight(NotOfForm("an equation", bracketSplit.conclusion))
      identified <- bracketParts._2 match {
        case App(App(_, plain), tail) =>
          linarith
            .prove("!p:real. !q:real. !r:real. p = q + r ==> p + -r = q")
            .flatMap(rules.specAll(_, List(bracketParts._1, plain, tail)))
            .flatMap(rules.mp(_, bracketSplit))
        case other => Left(NotOfForm("a sum of two", other))
      }
      agreeing <- rules
        .disch(guard, identified)
        .flatMap(rules.gen(n, _))

      zero <- Parser.term(theory, notation, "ZERO", numbers)
      carried <- rules
        .specAll(pieces.eventually, List(togetherParts._1, sequence, togetherParts._2, zero))
        .flatMap(normalised)
        .flatMap(rules.mp(_, agreeing))
        .flatMap(rules.mp(_, together))

      claim <- Parser.proposition(
        theory, notation, "?m:real. converges (Sum (f:num -> real)) m")
      predicate <- logic
        .destExistsPredicate(claim)
        .toRight(NotOfForm("an existential", claim))
      witnessed <- rules.existsIntro(predicate, togetherParts._2, carried)
      withoutWitness <- rules.existsElim(brackets, m, witnessed)
      result <- rules
        .disch(premise, withoutWitness)
        .flatMap(rules.genAll(_, List(f, l)))
    } yield result
  }

  /**
   * `|- !s l. converges s l ==> lim s = l`, which is what makes `lim` more than a term.
   *
   * `select` says that a predicate holds of what it chooses **where something satisfies it**, and
   * the convergence in the hypothesis is that something. So `lim s` is a limit of `s`, and
   * [[Unique]] turns "a limit" into "the limit". Both halves are needed and neither is enough: the
   * choice alone would leave `lim s` an arbitrary limit if a sequence could have two.
   */
  private def valueOfConverges(
    logic: Logic,
    classical: Classical,
    theory: Theory,
    notation: Notation,
    valueDefinition: Kernel.Thm,
    unique: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val l = Term.variable("l", values)

    for {
      converges <- Parser.proposition(theory, notation, "converges (s:num -> real) (l:real)")
      assumed <- LogicError.lift(Kernel.assume(converges))

      existential <- Parser.proposition(theory, notation, "?m:real. converges (s:num -> real) m")
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, l, assumed)
      chosen <- classical.witness(witnessed)
      reduced <- Conv
        .betaNormalise(chosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))

      unfolded <- Conv.unfold(valueDefinition, List(s))
      backwards <- Conv.sym(unfolded)
      atLimit <- rewriteWith(backwards, reduced)

      value <- Parser.term(theory, notation, "lim (s:num -> real)", values)
      result <- rules
        .specAll(unique, List(s, value, l))
        .flatMap(rules.mp(_, atLimit))
        .flatMap(rules.mp(_, assumed))
        .flatMap(rules.disch(converges, _))
        .flatMap(rules.gen(l, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s t l N. (!n. NUM_LE N n ==> s n = t n) ==> converges s l ==> converges t l`
   *
   * Agreement past an index is all a limit sees, and the index where the two hypotheses meet is
   * again a sum rather than a maximum. What the derivation actually spends is one congruence: at an
   * index past both, `s n = t n` turns the distance from `l` into the other sequence's distance
   * from `l`, and the tolerance never moves.
   *
   * Stated with the agreement first because that is the hypothesis a caller has: it knows its
   * sequence settles, and it is asking what that buys.
   */
  private def eventuallyEqual(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    indices: Indices
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val t = Term.variable("t", sequences)
    val l = Term.variable("l", values)
    val bound = Term.variable("N", numbers)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)

    for {
      agreement <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE N:num n ==> (s:num -> real) n = (t:num -> real) n"
      )
      assumedAgreement <- LogicError.lift(Kernel.assume(agreement))

      convergesS <- Parser.proposition(theory, notation, "converges (s:num -> real) (l:real)")
      assumedS <- LogicError.lift(Kernel.assume(convergesS))
      unfoldedS <- Conv.unfold(convergesDefinition, List(s, l)).flatMap(normaliseRight)
      bodyS <- LogicError.lift(Kernel.eqMp(unfoldedS, assumedS))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- rules.spec(e, bodyS).flatMap(rules.mp(_, assumedPositive))

      inside <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((s:num -> real) n - (l:real)) < e:real"
      )
      assumedInside <- LogicError.lift(Kernel.assume(inside))

      index <- Parser.term(theory, notation, "NUM_ADD m:num N:num", numbers)
      guard <- Parser.proposition(theory, notation, "NUM_LE (NUM_ADD m:num N:num) n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))

      aboveM <- rules.specAll(indices.atMostSum, List(m, bound))
      pastM <- rules
        .conjIntro(aboveM, assumedGuard)
        .flatMap(both => rules.specAll(indices.transitive, List(m, index, n)).flatMap(rules.mp(_, both)))

      aboveN <- for {
        other <- rules.specAll(indices.atMostSum, List(bound, m))
        swap <- rules.specAll(indices.commutative, List(bound, m))
        carried <- rewriteWith(swap, other)
      } yield carried
      pastN <- rules
        .conjIntro(aboveN, assumedGuard)
        .flatMap(both =>
          rules.specAll(indices.transitive, List(bound, index, n)).flatMap(rules.mp(_, both)))

      close <- rules.spec(n, assumedInside).flatMap(rules.mp(_, pastM))
      same <- rules.spec(n, assumedAgreement).flatMap(rules.mp(_, pastN))
      moved <- rewriteInProposition(same, close)

      guarded <- rules.disch(guard, moved).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?M:num. !n:num. NUM_LE M n ==> abs ((t:num -> real) n - (l:real)) < e:real"
      )
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(predicate, index, guarded)
      eliminated <- rules.existsElim(near, m, witnessed)

      whole <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))
      unfoldedT <- Conv.unfold(convergesDefinition, List(t, l)).flatMap(normaliseRight)
      bodyT <- rightOf(unfoldedT)
      _ <- sameStatement(notation, whole, bodyT)
      folded <- Conv
        .sym(unfoldedT)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))

      result <- rules
        .disch(convergesS, folded)
        .flatMap(rules.disch(agreement, _))
        .flatMap(rules.gen(bound, _))
        .flatMap(rules.gen(l, _))
        .flatMap(rules.gen(t, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * Rewrite the last argument of an application inside a theorem, by congruence.
   *
   * `equation` is `u = v` and `theorem` proves `P ... u`; what comes back proves `P ... v`. Written
   * once because four derivations here want it, and each of them would otherwise take an
   * application apart by hand, which is where a derivation silently starts being about the wrong
   * argument.
   */
  private def rewriteWith(
    equation: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    theorem.conclusion match {
      case App(partial, _) =>
        for {
          congruence <- Conv.apTerm(partial, equation)
          moved <- LogicError.lift(Kernel.eqMp(congruence, theorem))
        } yield moved
      case other => Left(NotOfForm("an application", other))
    }

  /**
   * [[CauchyNonNegative]], which is the sandwich squeezed.
   *
   * `D` is the partial sums of the convolution and `P n` is `Sum a n * Sum b n`. The argument is
   * four bounds and an antisymmetry, and the reason the docstring on the name is worth reading
   * first is that this one is about where each bound comes from rather than about the shape:
   *
   *  - `D n <= P n <= A * B`, so the Cauchy partial sums are bounded, so they converge, which is
   *    [[Comparison]] at a series dominating **itself**. That gives a limit `l` and says nothing
   *    at all about where it is.
   *  - `l <= A * B`, because `D n <= A * B` at every `n`, which is [[BelowBound]].
   *  - `A * B <= l`, because `P n <= D (n + n) <= l`, the first being [[SquareBelowCauchy]] and
   *    the second [[BelowLimit]] at the convolution. `P` converges to `A * B` by [[Multiplied]],
   *    so it is [[BelowBound]] again, on the other sequence.
   *  - The two meet by `Order.LE_ANTISYMMETRIC`, and the value is rewritten where it stands by a
   *    congruence on the convergence's second argument rather than by a rewriting pass.
   *
   * The dominating series being the dominated one is the step worth pausing on. [[Comparison]]
   * asks for termwise domination and a bound on the **dominator**'s partial sums; here there is
   * only one series and the bound is its own, so what the test is being used for is the
   * monotone convergence under it and nothing else. `!k. D' k <= D' k` is `Linarith`'s, in one
   * line, rather than `Order.LE_OF_EQ` over a reflexivity, which is what `LimitSpec` does two
   * files over and is equally available here: the fragment decides `!x. x <= x` outright, so the
   * alternative is a twelfth field on the bundle to save nothing.
   *
   * Two `NUM_LE ZERO n` guards are introduced and discharged vacuously, because [[BelowBound]]
   * asks for a bound from an index on and what is available here is a bound everywhere. That is
   * the same shape `Transcendental.EXP_ONE_ABOVE_TWO` meets and is not a defect of either: a
   * bound from zero on is a bound, and the alternative is a second form of the theorem nobody
   * would use twice.
   */
  private def cauchyOfNonNegative(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    pieces: Cauchys
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val a = Term.variable("a", sequences)
    val b = Term.variable("b", sequences)
    val bigA = Term.variable("A", values)
    val bigB = Term.variable("B", values)
    val l = Term.variable("l", values)
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)
    val k = Term.variable("k", numbers)

    val convolution =
      "\\k:num. Sum (\\i:num. (a:num -> real) i * (b:num -> real) (NUM_SUB k i)) (SUC k)"
    val inner = "\\i:num. (a:num -> real) i * (b:num -> real) (NUM_SUB (k:num) i)"

    /** A fact specialised at a lambda leaves a redex where the variable was applied. */
    def opened(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    /** Two bounds put end to end, which this derivation does three times. */
    def chain(
      lower: Kernel.Thm,
      upper: Kernel.Thm,
      small: Term,
      middle: Term,
      large: Term
    ): Either[LogicError, Kernel.Thm] =
      linarith
        .prove("!x:real. !y:real. !z:real. x <= y ==> y <= z ==> x <= z")
        .flatMap(rules.specAll(_, List(small, middle, large)))
        .flatMap(rules.mp(_, lower))
        .flatMap(rules.mp(_, upper))

    for {
      nonNegativeA <- Parser.proposition(theory, notation, "!i:num. 0 <= (a:num -> real) i")
      nonNegativeB <- Parser.proposition(theory, notation, "!i:num. 0 <= (b:num -> real) i")
      toA <- Parser.proposition(theory, notation, "converges (Sum (a:num -> real)) (A:real)")
      toB <- Parser.proposition(theory, notation, "converges (Sum (b:num -> real)) (B:real)")
      assumedA <- LogicError.lift(Kernel.assume(nonNegativeA))
      assumedB <- LogicError.lift(Kernel.assume(nonNegativeB))
      convergesA <- LogicError.lift(Kernel.assume(toA))
      convergesB <- LogicError.lift(Kernel.assume(toB))

      convolutionBody <- Parser.term(theory, notation, convolution)
      innerBody <- Parser.term(theory, notation, inner)
      product <- Parser.term(theory, notation, "(A:real) * (B:real)", values)
      zero <- Parser.term(theory, notation, "ZERO", numbers)
      here <- Parser.term(theory, notation, "(a:num -> real) (i:num)", values)
      shifted <- Parser.term(
        theory, notation, "(b:num -> real) (NUM_SUB (k:num) (i:num))", values)
      shiftedIndex <- Parser.term(theory, notation, "NUM_SUB (k:num) (i:num)", numbers)
      successorOfK <- Parser.term(theory, notation, "SUC (k:num)", numbers)
      partialA <- Parser.term(theory, notation, "Sum (a:num -> real) (n:num)", values)
      partialB <- Parser.term(theory, notation, "Sum (b:num -> real) (n:num)", values)
      sumA <- Parser.term(theory, notation, "Sum (a:num -> real)", sequences)
      sumB <- Parser.term(theory, notation, "Sum (b:num -> real)", sequences)
      cauchySums <- Parser.term(theory, notation, "Sum (" + convolution + ")", sequences)
      atZeroA <- Parser.term(theory, notation, "Sum (a:num -> real) ZERO", values)
      squareAt <- Parser.term(
        theory, notation, "Sum (a:num -> real) (n:num) * Sum (b:num -> real) (n:num)", values)
      viaLimitOfA <- Parser.term(
        theory, notation, "(A:real) * Sum (b:num -> real) (n:num)", values)
      cauchyAt <- Parser.term(theory, notation, "Sum (" + convolution + ") (n:num)", values)
      cauchyAtDouble <- Parser.term(
        theory, notation, "Sum (" + convolution + ") (NUM_ADD (n:num) (n:num))", values)
      doubled <- Parser.term(theory, notation, "NUM_ADD (n:num) (n:num)", numbers)
      termAt <- Parser.term(theory, notation, "Sum (" + inner + ") (SUC (k:num))", values)

      /* -------------------------------------------- the convolution is non-negative */

      innerNonNegative <- rules
        .spec(i, assumedA)
        .flatMap(atHere =>
          rules
            .spec(shiftedIndex, assumedB)
            .flatMap(atThere =>
              rules
                .specAll(pieces.productNonNegative, List(here, shifted))
                .flatMap(rules.mp(_, atHere))
                .flatMap(rules.mp(_, atThere))))
        .flatMap(rules.gen(i, _))
      convolutionNonNegative <- rules
        .spec(innerBody, pieces.nonNegativeSum)
        .flatMap(opened)
        .flatMap(rules.mp(_, innerNonNegative))
        .flatMap(rules.spec(successorOfK, _))
        .flatMap(rules.gen(k, _))

      /* -------------------------------- the partial Cauchy sums are under `A * B` */

      belowSquare <- rules
        .specAll(pieces.cauchyBelowSquare, List(a, b, n))
        .flatMap(rules.mp(_, assumedA))
        .flatMap(rules.mp(_, assumedB))
      aBelow <- rules
        .specAll(pieces.belowLimit, List(a, bigA))
        .flatMap(rules.mp(_, assumedA))
        .flatMap(rules.mp(_, convergesA))
      bBelow <- rules
        .specAll(pieces.belowLimit, List(b, bigB))
        .flatMap(rules.mp(_, assumedB))
        .flatMap(rules.mp(_, convergesB))
      aNonNegative <- rules.spec(a, pieces.nonNegativeSum).flatMap(rules.mp(_, assumedA))
      bNonNegative <- rules.spec(b, pieces.nonNegativeSum).flatMap(rules.mp(_, assumedB))

      aNonNegativeAtZero <- rules.spec(zero, aNonNegative)
      aBelowAtZero <- rules.spec(zero, aBelow)
      limitNonNegative <- linarith
        .prove("!s:real. !u:real. 0 <= s ==> s <= u ==> 0 <= u")
        .flatMap(rules.specAll(_, List(atZeroA, bigA)))
        .flatMap(rules.mp(_, aNonNegativeAtZero))
        .flatMap(rules.mp(_, aBelowAtZero))

      bNonNegativeAtN <- rules.spec(n, bNonNegative)
      aBelowAtN <- rules.spec(n, aBelow)
      bBelowAtN <- rules.spec(n, bBelow)
      firstFactor <- rules
        .specAll(pieces.multiplyLe, List(partialB, partialA, bigA))
        .flatMap(rules.mp(_, bNonNegativeAtN))
        .flatMap(rules.mp(_, aBelowAtN))
      secondFactor <- rules
        .specAll(pieces.multiplyLe, List(bigA, partialB, bigB))
        .flatMap(rules.mp(_, limitNonNegative))
        .flatMap(rules.mp(_, bBelowAtN))
      turnedLeft <- rules.specAll(pieces.symmetric, List(partialB, bigA))
      turnedRight <- rules.specAll(pieces.symmetric, List(bigB, bigA))
      secondTurned <- rewriteInProposition(turnedLeft, secondFactor)
        .flatMap(rewriteInProposition(turnedRight, _))

      squareBelowProduct <- chain(firstFactor, secondTurned, squareAt, viaLimitOfA, product)
      cauchyBelowProduct <- chain(belowSquare, squareBelowProduct, cauchyAt, squareAt, product)

      /* ------------------------------------------- bounded, so convergent, so squeezed */

      boundClaim <- Parser.proposition(
        theory, notation, "?z:real. !u:num. Sum (" + convolution + ") u <= z")
      boundPredicate <- logic
        .destExistsPredicate(boundClaim)
        .toRight(NotOfForm("an existential quantification", boundClaim))
      bounded <- rules
        .gen(n, cauchyBelowProduct)
        .flatMap(rules.existsIntro(boundPredicate, product, _))

      // At the series' `k`th **term**, which is a whole inner sum, and not at its `k`th partial
      // sum: the comparison test compares terms, and the two differ by the `Sum` in front.
      dominates <- linarith
        .prove("!x:real. x <= x")
        .flatMap(rules.spec(termAt, _))
        .flatMap(rules.gen(k, _))
      converging <- rules
        .specAll(pieces.comparison, List(convolutionBody, convolutionBody))
        .flatMap(opened)
        .flatMap(rules.mp(_, convolutionNonNegative))
        .flatMap(rules.mp(_, dominates))
        .flatMap(rules.mp(_, bounded))

      guard <- Parser.proposition(theory, notation, "NUM_LE ZERO (n:num)")
      converged <- Parser.proposition(
        theory, notation, "converges (Sum (" + convolution + ")) (l:real)")
      assumedLimit <- LogicError.lift(Kernel.assume(converged))

      everyCauchyIndex <- rules.disch(guard, cauchyBelowProduct).flatMap(rules.gen(n, _))
      limitBelowProduct <- rules
        .specAll(pieces.belowBound, List(cauchySums, l, product, zero))
        .flatMap(rules.mp(_, assumedLimit))
        .flatMap(rules.mp(_, everyCauchyIndex))

      cauchyBelowLimit <- rules
        .specAll(pieces.belowLimit, List(convolutionBody, l))
        .flatMap(opened)
        .flatMap(rules.mp(_, convolutionNonNegative))
        .flatMap(rules.mp(_, assumedLimit))
      squareBelowDouble <- rules
        .specAll(pieces.squareBelowCauchy, List(a, b, n))
        .flatMap(rules.mp(_, assumedA))
        .flatMap(rules.mp(_, assumedB))
      squareBelowLimit <- rules
        .spec(doubled, cauchyBelowLimit)
        .flatMap(chain(squareBelowDouble, _, squareAt, cauchyAtDouble, l))

      productConverges <- rules
        .specAll(pieces.multiplied, List(sumA, sumB, bigA, bigB))
        .flatMap(rules.mp(_, convergesA))
        .flatMap(rules.mp(_, convergesB))
      productSequence <- productConverges.conclusion match {
        case App(App(_, sequence), _) => Right(sequence)
        case other                    => Left(NotOfForm("a convergence", other))
      }
      everySquareIndex <- rules.disch(guard, squareBelowLimit).flatMap(rules.gen(n, _))
      productBelowLimit <- rules
        .specAll(pieces.belowBound, List(productSequence, product, l, zero))
        .flatMap(opened)
        .flatMap(rules.mp(_, productConverges))
        .flatMap(rules.mp(_, everySquareIndex))

      // The two bounds meet, and the value is rewritten where it stands: the congruence reaches
      // the last argument of the application, which is exactly the one that moves.
      equal <- rules
        .specAll(pieces.antisymmetric, List(l, product))
        .flatMap(rules.mp(_, limitBelowProduct))
        .flatMap(rules.mp(_, productBelowLimit))
      carried <- assumedLimit.conclusion match {
        case App(partial, _) =>
          Conv
            .apTerm(partial, equal)
            .flatMap(congruence => LogicError.lift(Kernel.eqMp(congruence, assumedLimit)))
        case other => Left(NotOfForm("a convergence", other))
      }

      result <- rules
        .existsElim(converging, l, carried)
        .flatMap(rules.disch(toB, _))
        .flatMap(rules.disch(toA, _))
        .flatMap(rules.disch(nonNegativeB, _))
        .flatMap(rules.disch(nonNegativeA, _))
        .flatMap(rules.genAll(_, List(a, b, bigA, bigB)))
    } yield result
  }

  /**
   * `|- !f n. abs (Sum f n) <= Sum (\i. abs (f i)) n`
   *
   * The triangle inequality at a finite sum, which is one induction over `ABS_TRIANGLE`.
   *
   * **It lives here and its subject is not limits**, which is the chain's doing rather than a
   * choice: `abs` is `Magnitude`'s and `Sum` is `Series`', `Magnitude` is built **above** `Series`
   * and is handed no `Series` at all, so the lowest development in which the two can be written
   * in one statement is this one. Handing `Magnitude` a `Series` to carry one lemma would add an
   * edge to the dependency graph for a fact about neither of its two subjects, and
   * `CONVERGES_ABSOLUTE` already pairs the two names here, so this is where a reader looking for
   * the pair arrives.
   *
   * **Nothing consumed it until 2026-09-21, which is why it was not written**, and this file said
   * so of itself while it was absent. The consumer is the general Cauchy product: bounding a
   * signed sum by the same sum of magnitudes is what turns the non-negative theorem into a
   * statement about arbitrary terms.
   *
   * The step is put together and then folded back rather than rewritten forwards. What
   * `ABS_TRIANGLE` and the hypothesis give is an order between the **opened** partial sums, and
   * the two recurrences are applied backwards to it by [[rewriteInProposition]], which is the
   * same direction [[rewriteInProposition]]'s other callers use and avoids asking the rewriter to
   * put a `SUC` back where it has just taken one out.
   */
  private def sumUnderMagnitudes(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    induct: Induct,
    pieces: Magnitudes
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val f = Term.variable("f", sequences)

    def opened(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    for {
      zero <- Parser.term(theory, notation, "0:real", values)
      absZero <- rules
        .spec(zero, pieces.ofNonNegative)
        .flatMap(theorem => linarith.prove("(0:real) <= 0").flatMap(rules.mp(theorem, _)))

      vanishing <- Rewrite.Rule.of(logic, pieces.atZero)
      collapse <- Rewrite.Rule.of(logic, absZero)

      magnitudes <- Parser.term(
        theory, notation, "\\i:num. abs ((f:num -> real) i)", sequences)

      statement <- Parser.proposition(
        theory,
        notation,
        "!n:num. abs (Sum (f:num -> real) n) <= Sum (\\i:num. abs ((f:num -> real) i)) n")

      everywhere <- induct.proveBy(
        statement,
        // Both sides collapse to zero, and `abs 0 = 0` is the one rule the sum's own does not give.
        base =>
          Induct.afterRewriting(Vector(vanishing, collapse), base)(goal =>
            linarith.prove(Show.show(notation, goal))),
        step =>
          for {
            atSignedSuccessor <- rules.specAll(pieces.atSuccessor, List(f, step.variable))
            atMagnitudeSuccessor <- rules
              .specAll(pieces.atSuccessor, List(magnitudes, step.variable))
              .flatMap(opened)

            // `Sum f k + f k` and `Sum (\i. abs (f i)) k + abs (f k)`, read off the two
            // recurrences rather than built, so no term here is written twice.
            signedSides <- destructEquation(atSignedSuccessor)
            magnitudeSides <- destructEquation(atMagnitudeSuccessor)
            summands <- signedSides._2 match {
              case App(App(_, partial), here) => Right((partial, here))
              case other => Left(NotOfForm("a partial sum and the term just added", other))
            }
            (partial, here) = summands

            triangle <- rules.specAll(pieces.triangle, List(partial, here))
            bounds <- triangle.conclusion match {
              case App(App(_, whole), App(App(_, left), right)) => Right((whole, left, right))
              case other => Left(NotOfForm("the triangle inequality", other))
            }
            (whole, leftMagnitude, rightMagnitude) = bounds

            partialMagnitudes <- magnitudeSides._2 match {
              case App(App(_, sofar), _) => Right(sofar)
              case other => Left(NotOfForm("a partial sum and the term just added", other))
            }

            // `p <= q + r` with `q <= s` gives `p <= s + r`: the hypothesis replaces the first
            // summand and the second is carried across untouched.
            assembled <- linarith
              .prove("!p:real. !q:real. !r:real. !s:real. p <= q + r ==> q <= s ==> p <= s + r")
              .flatMap(rules.specAll(
                _, List(whole, leftMagnitude, rightMagnitude, partialMagnitudes)))
              .flatMap(rules.mp(_, triangle))
              .flatMap(rules.mp(_, step.hypothesis))

            foldedLeft <- Conv.sym(atSignedSuccessor).flatMap(rewriteInProposition(_, assembled))
            result <- Conv.sym(atMagnitudeSuccessor).flatMap(rewriteInProposition(_, foldedLeft))
          } yield result
      )

      result <- rules.gen(f, everywhere)
    } yield result
  }

  /**
   * `|- !s u. (!n. abs (s n) <= u n) ==> converges u 0 ==> converges s 0`
   *
   * The squeeze, in the only shape this development needs: a sequence dominated in magnitude by
   * one that goes to zero goes to zero. Written at zero rather than at a general limit on purpose,
   * because the two-sided form wants `abs (s n - l) <= u n`, which is the same statement with the
   * shift done by the caller, and every consumer here already has the difference in hand.
   *
   * **One tolerance and no halving.** `u`'s own convergence is asked once, at the tolerance the
   * caller gave, and the index it answers with is the index this sequence answers with: there is
   * no second sequence to put an index together with, which is what makes this shorter than
   * [[Added]] and much shorter than [[Multiplied]]. The whole estimate is
   * `abs (s n - 0) = abs (s n) <= u n <= abs (u n - 0) < e`, four links, and the middle two are
   * the hypothesis and `ABS_ABOVE`.
   *
   * The first link is the one worth naming, because it is not an identity the rewriting produces:
   * `abs (s n - 0)` is what `converges` asks about and `abs (s n)` is what the hypothesis bounds,
   * and they are different terms. What joins them is `s n - 0 = s n` carried under `abs` by
   * congruence, which is the same step [[Tail]] takes for the same reason.
   */
  private def dominatedByAVanishing(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    bounds: Bounds
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val u = Term.variable("u", sequences)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)

    for {
      zero <- Parser.term(theory, notation, "0:real", values)
      dominated <- Parser.proposition(
        theory, notation, "!n:num. abs ((s:num -> real) n) <= (u:num -> real) n")
      assumedDominated <- LogicError.lift(Kernel.assume(dominated))

      toZero <- Parser.proposition(theory, notation, "converges (u:num -> real) 0")
      assumedZero <- LogicError.lift(Kernel.assume(toZero))
      unfoldedU <- Conv.unfold(convergesDefinition, List(u, zero)).flatMap(normaliseRight)
      bodyU <- LogicError.lift(Kernel.eqMp(unfoldedU, assumedZero))

      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      near <- rules.spec(e, bodyU).flatMap(rules.mp(_, assumedPositive))

      inside <- Parser.proposition(
        theory,
        notation,
        "!n:num. NUM_LE m:num n ==> abs ((u:num -> real) n - 0) < e:real")
      assumedInside <- LogicError.lift(Kernel.assume(inside))

      guard <- Parser.proposition(theory, notation, "NUM_LE m:num n:num")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      close <- rules.spec(n, assumedInside).flatMap(rules.mp(_, assumedGuard))

      atHere <- rules.spec(n, assumedDominated)
      atU <- Parser.term(theory, notation, "(u:num -> real) (n:num)", values)
      gapU <- Parser.term(theory, notation, "(u:num -> real) (n:num) - 0", values)
      distanceU <- Parser.term(theory, notation, "abs ((u:num -> real) (n:num) - 0)", values)
      atS <- Parser.term(theory, notation, "abs ((s:num -> real) (n:num))", values)
      distanceS <- Parser.term(theory, notation, "abs ((s:num -> real) (n:num) - 0)", values)
      aboveU <- rules.spec(gapU, bounds.above)

      // `abs (s n - 0)` is what `converges` asks about and `abs (s n)` is what the hypothesis
      // bounds. The shift is carried under `abs` by congruence rather than by a rewriting pass.
      atSPlain <- Parser.term(theory, notation, "(s:num -> real) (n:num)", values)
      magnitude <- distanceS match {
        case App(constant, _) => Right(constant)
        case other            => Left(NotOfForm("a magnitude", other))
      }
      shift <- linarith.prove("!x:real. x - 0 = x")
      carried <- rules.spec(atSPlain, shift).flatMap(Conv.apTerm(magnitude, _))

      closeGap <- linarith
        .prove(
          "!d:real. !q:real. !v:real. !w:real. !t:real. " +
            "d = q ==> q <= v ==> v - 0 <= w ==> w < t ==> d < t")
        .flatMap(rules.specAll(_, List(distanceS, atS, atU, distanceU, e)))
        .flatMap(rules.mp(_, carried))
        .flatMap(rules.mp(_, atHere))
        .flatMap(rules.mp(_, aboveU))
        .flatMap(rules.mp(_, close))

      guarded <- rules.disch(guard, closeGap).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> abs ((s:num -> real) n - 0) < e:real")
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential quantification", existential))
      witnessed <- rules.existsIntro(predicate, m, guarded)
      eliminated <- rules.existsElim(near, m, witnessed)
      whole <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))

      unfoldedS <- Conv.unfold(convergesDefinition, List(s, zero)).flatMap(normaliseRight)
      bodyS <- rightOf(unfoldedS)
      _ <- sameStatement(notation, whole, bodyS)
      folded <- Conv
        .sym(unfoldedS)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, whole)))

      result <- rules
        .disch(toZero, folded)
        .flatMap(rules.disch(dominated, _))
        .flatMap(rules.genAll(_, List(s, u)))
    } yield result
  }

  /**
   * `|- !f m n. NUM_LE m n ==> abs (Sum f n - Sum f m) <= Sum (\i. abs (f i)) n - Sum (\i. abs (f i)) m`
   *
   * The triangle inequality on a **stretch** of a series rather than on a prefix, which is
   * [[SumOfMagnitudes]] with `SUM_REINDEX` on both sides of it and no induction of its own.
   *
   * `SUM_REINDEX` already says that a sum started at `m` and run for `d` terms is the difference
   * of two partial sums, so the whole derivation is three facts in a line: read the difference
   * backwards into a sum over the stretch, put [[SumOfMagnitudes]] to that sum, and read the
   * answer forwards into a difference again with the same fact at the magnitudes. **The lemma
   * that looked missing was in the library**, which is why this costs three lines rather than a
   * second induction over the gap.
   *
   * == Why the order is a hypothesis and not a subtraction ==
   *
   * `SUM_REINDEX` is additive, so the natural statement of this is over `m` and `d` with `m + d`
   * where this one writes `n`. That form is true, shorter to derive, and **unusable at the one
   * call site there is**: the consumer holds `Sum b n - Sum b (NUM_SUB n i)` and would have to
   * produce `NUM_SUB n i + i = n`, which is `Peano.NUM_SUB_ADD` under `i <= n` — a hypothesis it
   * would then owe for every `i`. Written with the order in front, the guard at that site is
   * `NUM_LE (NUM_SUB n i) n`, which is `Peano.NUM_SUB_LE` and holds for **every** `i` with
   * nothing assumed. So the hypothesis here buys the consumer the absence of one there, and the
   * consumer can use `SUM_MONOTONE` where it would otherwise have needed the bounded twin.
   */
  private def stretchUnderMagnitudes(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    orderDefinition: Kernel.Thm,
    reindex: Kernel.Thm,
    prefix: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val f = Term.variable("f", sequences)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val d = Term.variable("d", numbers)

    def opened(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    for {
      magnitudes <- Parser.term(
        theory, notation, "\\i:num. abs ((f:num -> real) i)", sequences)
      shifted <- Parser.term(
        theory, notation, "\\u:num. (f:num -> real) (NUM_ADD (m:num) u)", sequences)

      // The stretch read as a difference, and the same for the magnitudes.
      asDifference <- rules.specAll(reindex, List(f, m, d)).flatMap(opened)
      magnitudesAsDifference <- rules.specAll(reindex, List(magnitudes, m, d)).flatMap(opened)

      overTheStretch <- rules.specAll(prefix, List(shifted, d)).flatMap(opened)

      core <- rewriteInProposition(asDifference, overTheStretch)
        .flatMap(rewriteInProposition(magnitudesAsDifference, _))

      below <- Parser.proposition(theory, notation, "NUM_LE (m:num) (n:num)")
      assumedBelow <- LogicError.lift(Kernel.assume(below))
      unfolded <- Conv.unfold(orderDefinition, List(m, n)).flatMap(normaliseRight)
      witness <- LogicError.lift(Kernel.eqMp(unfolded, assumedBelow))

      inner <- Parser.proposition(theory, notation, "NUM_ADD (m:num) (d:num) = n:num")
      assumedInner <- LogicError.lift(Kernel.assume(inner))
      atIndex <- rewriteInProposition(assumedInner, core)
      eliminated <- rules.existsElim(witness, d, atIndex)

      result <- rules
        .disch(below, eliminated)
        .flatMap(rules.genAll(_, List(f, m, n)))
    } yield result
  }

  /**
   * [[Cauchy]], the Cauchy product where the terms have signs.
   *
   * == What the non-negative theorem does and does not give ==
   *
   * [[CauchyNonNegative]] is this statement at `abs (a i)` and `abs (b i)`, and it is spent here
   * exactly once, on the magnitudes. What that buys is a sequence that is known to vanish; it
   * says nothing at all about the signed convolution, whose partial sums are not monotone and
   * are not bracketed by anything.
   *
   * == The argument, which is one identity and one squeeze ==
   *
   * Write `A_n` for `Sum a n` and `D_n` for the signed convolution's partial sum, and `P_n`,
   * `Q_n`, `E_n` for the same three at the magnitudes. `Series.SUM_CAUCHY_GAP` is an identity
   * carrying **no hypothesis**, so it holds of signed terms as it does of non-negative ones:
   *
   *   `A_n * B_n - D_n = Sum (\i. a i * (B_n - B (n - i))) n`
   *
   * and the same at the magnitudes. The two right-hand sides compare termwise, which is the
   * whole of the work: `abs (a i * (B_n - B (n - i)))` is `abs (a i) * abs (B_n - B (n - i))` by
   * `ABS_MUL`, and the second factor is under `Q_n - Q (n - i)` by [[StretchOfMagnitudes]] with
   * `Peano.NUM_SUB_LE` discharging its guard at every `i` and nothing assumed. So
   * [[SumOfMagnitudes]] and `SUM_MONOTONE` give
   *
   *   `abs (A_n * B_n - D_n) <= P_n * Q_n - E_n`
   *
   * and the right side vanishes, because [[Multiplied]] sends `P_n * Q_n` to `P * Q` and the
   * non-negative theorem sends `E_n` to the same number. [[Squeezed]] carries that to the left
   * side, and then `D_n = A_n * B_n - (A_n * B_n - D_n)` converges to `A * B - 0`.
   *
   * == Two shapes of bookkeeping, named so a reader does not mistake them for the argument ==
   *
   * The difference of two limits is assembled out of [[Negated]] and [[Added]], so what comes
   * back is a sequence spelled `\n. x n + -(y n)` and a limit spelled `l + -(l)`. Neither is the
   * term a reader writes. [[Eventually]] at index zero replaces the sequence, its hypothesis
   * being a pointwise **linear** equation, and a rewrite replaces the limit. That is the same
   * arrangement [[Tail]] uses and is for the same reason.
   */
  private def cauchyOfSigned(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    pieces: Generals
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val a = Term.variable("a", sequences)
    val b = Term.variable("b", sequences)
    val bigA = Term.variable("A", values)
    val bigB = Term.variable("B", values)
    val bigP = Term.variable("P", values)
    val bigQ = Term.variable("Q", values)
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)

    val magnitudesOfA = "\\i:num. abs ((a:num -> real) i)"
    val magnitudesOfB = "\\i:num. abs ((b:num -> real) i)"
    val signedConvolution =
      "\\k:num. Sum (\\i:num. (a:num -> real) i * (b:num -> real) (NUM_SUB k i)) (SUC k)"

    def opened(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    def convergenceOf(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
      theorem.conclusion match {
        case App(App(_, sequence), value) => Right((sequence, value))
        case other                        => Left(NotOfForm("a convergence", other))
      }

    /**
     * The same convergence with the **value** written the way a reader writes it.
     *
     * [[Added]] hands back `l + -l` where what is wanted is `0`, and the repair is a congruence
     * on the convergence's second argument: nothing about the sequence is touched.
     */
    def valued(produced: Kernel.Thm, wanted: Term): Either[LogicError, Kernel.Thm] =
      for {
        parts <- convergenceOf(produced)
        equation <- LogicError.lift(Term.eq(parts._2, wanted)).flatMap(pieces.ring.prove)
        leading <- produced.conclusion match {
          case App(partial, _) => Right(partial)
          case other           => Left(NotOfForm("a convergence", other))
        }
        result <- Conv
          .apTerm(leading, equation)
          .flatMap(congruence => LogicError.lift(Kernel.eqMp(congruence, produced)))
      } yield result

    /**
     * The same convergence with the **sequence** written the way a reader writes it.
     *
     * This one cannot be a congruence, because the two sequences are equal at every index and are
     * not the same function: what says so is [[Eventually]] at index zero, whose hypothesis is a
     * pointwise equation the ring decides. The index is read off the instance rather than written,
     * since the instance is what fixes which variable the hypothesis is about.
     */
    def spelled(produced: Kernel.Thm, wanted: Term): Either[LogicError, Kernel.Thm] =
      for {
        parts <- convergenceOf(produced)
        indexZero <- Parser.term(theory, notation, "ZERO", numbers)
        instance <- rules
          .specAll(pieces.eventually, List(parts._1, wanted, parts._2, indexZero))
          .flatMap(opened)
        premise <- logic
          .destImp(instance.conclusion)
          .toRight(NotOfForm("an implication", instance.conclusion))
        stripped <- Logic.stripForall(premise._1)
        index <- stripped._1.headOption
          .toRight(NotOfForm("a claim about every index", premise._1))
        inner <- logic
          .destImp(stripped._2)
          .toRight(NotOfForm("an implication", stripped._2))
        agreeing <- pieces.ring
          .prove(inner._2)
          .flatMap(rules.disch(inner._1, _))
          .flatMap(rules.gen(index, _))
          .flatMap(rules.mp(instance, _))
        result <- rules.mp(agreeing, produced)
      } yield result

    /** Two bounds put end to end. */
    def chain(
      lower: Kernel.Thm,
      upper: Kernel.Thm,
      small: Term,
      middle: Term,
      large: Term
    ): Either[LogicError, Kernel.Thm] =
      linarith
        .prove("!x:real. !y:real. !z:real. x <= y ==> y <= z ==> x <= z")
        .flatMap(rules.specAll(_, List(small, middle, large)))
        .flatMap(rules.mp(_, lower))
        .flatMap(rules.mp(_, upper))

    for {
      toP <- Parser.proposition(
        theory, notation, "converges (Sum (" + magnitudesOfA + ")) (P:real)")
      toQ <- Parser.proposition(
        theory, notation, "converges (Sum (" + magnitudesOfB + ")) (Q:real)")
      toA <- Parser.proposition(theory, notation, "converges (Sum (a:num -> real)) (A:real)")
      toB <- Parser.proposition(theory, notation, "converges (Sum (b:num -> real)) (B:real)")
      convergesP <- LogicError.lift(Kernel.assume(toP))
      convergesQ <- LogicError.lift(Kernel.assume(toQ))
      convergesA <- LogicError.lift(Kernel.assume(toA))
      convergesB <- LogicError.lift(Kernel.assume(toB))

      absA <- Parser.term(theory, notation, magnitudesOfA, sequences)
      absB <- Parser.term(theory, notation, magnitudesOfB, sequences)
      signed <- Parser.term(theory, notation, signedConvolution, sequences)
      sumA <- Parser.term(theory, notation, "Sum (a:num -> real)", sequences)
      sumB <- Parser.term(theory, notation, "Sum (b:num -> real)", sequences)
      sumAbsA <- Parser.term(theory, notation, "Sum (" + magnitudesOfA + ")", sequences)
      sumAbsB <- Parser.term(theory, notation, "Sum (" + magnitudesOfB + ")", sequences)
      product <- Parser.term(theory, notation, "(A:real) * (B:real)", values)
      magnitudeProduct <- Parser.term(theory, notation, "(P:real) * (Q:real)", values)
      zero <- Parser.term(theory, notation, "0:real", values)

      /* --------------------------------------- the magnitudes, where the old theorem is spent */

      atA <- Parser.term(theory, notation, "(a:num -> real) (i:num)", values)
      atB <- Parser.term(theory, notation, "(b:num -> real) (i:num)", values)
      nonNegativeA <- rules.spec(atA, pieces.absNonNegative).flatMap(rules.gen(i, _))
      nonNegativeB <- rules.spec(atB, pieces.absNonNegative).flatMap(rules.gen(i, _))

      magnitudeCauchy <- rules
        .specAll(pieces.nonNegativeProduct, List(absA, absB, bigP, bigQ))
        .flatMap(opened)
        .flatMap(rules.mp(_, nonNegativeA))
        .flatMap(rules.mp(_, nonNegativeB))
        .flatMap(rules.mp(_, convergesP))
        .flatMap(rules.mp(_, convergesQ))
      // The **sequence**, which is `Sum` applied to the convolution and not the convolution:
      // `CONVERGES_NEG` is about a sequence and the partial sums are what converges.
      magnitudeParts <- convergenceOf(magnitudeCauchy)
      magnitudeConvolution = magnitudeParts._1

      magnitudeSquares <- rules
        .specAll(pieces.multiplied, List(sumAbsA, sumAbsB, bigP, bigQ))
        .flatMap(rules.mp(_, convergesP))
        .flatMap(rules.mp(_, convergesQ))
      signedSquares <- rules
        .specAll(pieces.multiplied, List(sumA, sumB, bigA, bigB))
        .flatMap(rules.mp(_, convergesA))
        .flatMap(rules.mp(_, convergesB))

      /* ---------------------------------------------- the two gaps, and the bound between them */

      signedGap <- rules.specAll(pieces.gap, List(a, b, n))
      magnitudeGap <- rules.specAll(pieces.gap, List(absA, absB, n)).flatMap(opened)
      signedGapSides <- destructEquation(signedGap)
      magnitudeGapSides <- destructEquation(magnitudeGap)
      signedBody <- signedGapSides._2 match {
        case App(App(_, body), _) => Right(body)
        case other => Left(NotOfForm("a sum over the gap", other))
      }
      magnitudeBody <- magnitudeGapSides._2 match {
        case App(App(_, body), _) => Right(body)
        case other => Left(NotOfForm("a sum over the gap", other))
      }

      tailOfB <- Parser.term(
        theory,
        notation,
        "Sum (b:num -> real) (n:num) - Sum (b:num -> real) (NUM_SUB (n:num) (i:num))",
        values)
      tailOfMagnitudes <- Parser.term(
        theory,
        notation,
        "Sum (" + magnitudesOfB + ") (n:num) - Sum (" + magnitudesOfB + ") (NUM_SUB (n:num) (i:num))",
        values)
      hereMagnitude <- Parser.term(theory, notation, "abs ((a:num -> real) (i:num))", values)
      hereTailMagnitude <- Parser.term(
        theory,
        notation,
        "abs (Sum (b:num -> real) (n:num) - Sum (b:num -> real) (NUM_SUB (n:num) (i:num)))",
        values)

      // The stretch bound, at every `i` and with nothing assumed: its guard is `NUM_SUB_LE`.
      difference <- Parser.term(theory, notation, "NUM_SUB (n:num) (i:num)", numbers)
      stretch <- rules
        .specAll(pieces.stretch, List(b, difference, n))
        .flatMap(opened)
        .flatMap(theorem =>
          rules.specAll(pieces.subBelow, List(n, i)).flatMap(rules.mp(theorem, _)))
      hereNonNegative <- rules.spec(atA, pieces.absNonNegative)
      scaled <- rules
        .specAll(pieces.multiplyLe, List(hereMagnitude, hereTailMagnitude, tailOfMagnitudes))
        .flatMap(rules.mp(_, hereNonNegative))
        .flatMap(rules.mp(_, stretch))
      turnedLeft <- rules.specAll(pieces.symmetric, List(hereTailMagnitude, hereMagnitude))
      turnedRight <- rules.specAll(pieces.symmetric, List(tailOfMagnitudes, hereMagnitude))
      commuted <- rewriteInProposition(turnedLeft, scaled)
        .flatMap(rewriteInProposition(turnedRight, _))
      splitMagnitude <- rules.specAll(pieces.absMul, List(atA, tailOfB))
      termwise <- Conv.sym(splitMagnitude).flatMap(rewriteInProposition(_, commuted))
      everyTerm <- rules.gen(i, termwise)

      magnitudesOfSigned <- rules.specAll(pieces.prefix, List(signedBody, n)).flatMap(opened)
      magnitudesSequence <- magnitudesOfSigned.conclusion match {
        case App(App(_, _), App(App(_, sequence), _)) => Right(sequence)
        case other => Left(NotOfForm("a bound on a sum of magnitudes", other))
      }
      dominated <- rules
        .specAll(pieces.monotone, List(magnitudesSequence, magnitudeBody))
        .flatMap(opened)
        .flatMap(rules.mp(_, everyTerm))
        .flatMap(rules.spec(n, _))

      // `Sum` and `abs` are read off terms already built rather than parsed bare.
      partialSums <- sumA match {
        case App(constant, _) => Right(constant)
        case other            => Left(NotOfForm("the partial sums of a series", other))
      }
      magnitudeOf <- hereMagnitude match {
        case App(constant, _) => Right(constant)
        case other            => Left(NotOfForm("a magnitude", other))
      }
      signedSums <- LogicError.lift(Term.app(partialSums, signedBody))
      signedSum <- LogicError.lift(Term.app(signedSums, n))
      magnitudeSums <- LogicError.lift(Term.app(partialSums, magnitudeBody))
      magnitudeSum <- LogicError.lift(Term.app(magnitudeSums, n))
      middleSums <- LogicError.lift(Term.app(partialSums, magnitudesSequence))
      middleSum <- LogicError.lift(Term.app(middleSums, n))
      absOfSignedSum <- LogicError.lift(Term.app(magnitudeOf, signedSum))

      bounded <- chain(magnitudesOfSigned, dominated, absOfSignedSum, middleSum, magnitudeSum)
      foldedLeft <- Conv
        .sym(signedGap)
        .flatMap(equation => rewriteInProposition(equation, bounded))
      pointwise <- Conv
        .sym(magnitudeGap)
        .flatMap(equation => rewriteInProposition(equation, foldedLeft))
      everywhere <- rules.gen(n, pointwise)

      /* ------------------------------------- the bound vanishes, so the gap does, so `D` lands */

      pointwiseSides <- pointwise.conclusion match {
        case App(App(_, left), right) => Right((left, right))
        case other                    => Left(NotOfForm("a comparison", other))
      }
      signedGapAt <- pointwiseSides._1 match {
        case App(_, inner) => Right(inner)
        case other         => Left(NotOfForm("a magnitude", other))
      }
      gapSequence <- LogicError.lift(Term.abs(n, signedGapAt))
      boundSequence <- LogicError.lift(Term.abs(n, pointwiseSides._2))

      magnitudeSquareParts <- convergenceOf(magnitudeSquares)
      turnedMagnitudes <- rules
        .specAll(pieces.negated, List(magnitudeConvolution, magnitudeProduct))
        .flatMap(rules.mp(_, magnitudeCauchy))
      turnedMagnitudeParts <- convergenceOf(turnedMagnitudes)
      boundTogether <- rules
        .specAll(
          pieces.added,
          List(
            magnitudeSquareParts._1,
            turnedMagnitudeParts._1,
            magnitudeProduct,
            turnedMagnitudeParts._2))
        .flatMap(rules.mp(_, magnitudeSquares))
        .flatMap(rules.mp(_, turnedMagnitudes))
        .flatMap(opened)
      boundVanishes <- valued(boundTogether, zero).flatMap(spelled(_, boundSequence))

      gapVanishes <- rules
        .specAll(pieces.squeezed, List(gapSequence, boundSequence))
        .flatMap(opened)
        .flatMap(rules.mp(_, everywhere))
        .flatMap(rules.mp(_, boundVanishes))

      signedSquareParts <- convergenceOf(signedSquares)
      turnedGap <- rules
        .specAll(pieces.negated, List(gapSequence, zero))
        .flatMap(rules.mp(_, gapVanishes))
        .flatMap(opened)
      turnedGapParts <- convergenceOf(turnedGap)
      assembled <- rules
        .specAll(
          pieces.added,
          List(signedSquareParts._1, turnedGapParts._1, product, turnedGapParts._2))
        .flatMap(rules.mp(_, signedSquares))
        .flatMap(rules.mp(_, turnedGap))
        .flatMap(opened)

      convolutionSums <- LogicError.lift(Term.app(partialSums, signed))
      landed <- valued(assembled, product).flatMap(spelled(_, convolutionSums))

      result <- rules
        .disch(toB, landed)
        .flatMap(rules.disch(toA, _))
        .flatMap(rules.disch(toQ, _))
        .flatMap(rules.disch(toP, _))
        .flatMap(rules.genAll(_, List(a, b, bigA, bigB, bigP, bigQ)))
    } yield result
  }

  /**
   * Rewrite one subterm of a proposition with an equation, wherever in it the subterm occurs.
   *
   * The congruence above reaches the last argument of an application and no further, and what this
   * needs is a term buried under `abs` and a subtraction. So the proposition is abstracted over the
   * subterm, the abstraction is applied to each side of the equation, and the two applications are
   * reduced: that is the general rewrite, written here rather than reached for from `Rewrite`
   * because what is wanted is one occurrence of one term and not a normalising pass.
   */
  private def rewriteInProposition(
    equation: Kernel.Thm,
    theorem: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Term.destEq(equation.conclusion) match {
      case None => Left(NotOfForm("an equation", equation.conclusion))
      case Some((left, _)) =>
        val placeholder = Conv.freshVariable(
          "u",
          Term.typeOf(left),
          Term.freeVariables(theorem.conclusion) ++ Term.freeVariables(equation.conclusion)
        )

        for {
          replaced <- LogicError.lift(replace(theorem.conclusion, left, placeholder))

          // A replacement that found nothing would make the congruence below a no-op and hand back
          // the theorem it was given, which is what a rewrite that missed looks like from outside.
          _ <- if (replaced != theorem.conclusion) Right(())
               else Left(NotOfForm(s"a proposition mentioning ${left}", theorem.conclusion))

          template <- LogicError.lift(Term.abs(placeholder, replaced))
          congruence <- Conv.apTerm(template, equation)
          reduced <- Conv.betaSides(congruence)
          moved <- LogicError.lift(Kernel.eqMp(reduced, theorem))
        } yield moved
    }

  /** Every occurrence of `target` inside `term`, replaced by `replacement`. */
  private def replace(term: Term, target: Term, replacement: Term): Either[KernelError, Term] =
    if (term == target) Right(replacement)
    else
      term match {
        case App(fn, argument) =>
          for {
            left <- replace(fn, target, replacement)
            right <- replace(argument, target, replacement)
            joined <- Term.app(left, right)
          } yield joined
        // No descent under a binder: the kernel keeps those constructors to itself, and no
        // caller here rewrites inside one. An occurrence that is only under a binder therefore
        // leaves the term unchanged, which the check above turns into a refusal.
        case other => Right(other)
      }

  /** Refuse with both statements named where a derivation and its target have drifted apart. */
  private def sameStatement(
    notation: Notation,
    theorem: Kernel.Thm,
    target: Term
  ): Either[LogicError, Unit] =
    if (theorem.conclusion == target) Right(())
    else Left(NotOfForm(s"a proof of ${Show.show(notation, target)}", theorem.conclusion))

  /**
   * `|- !s. (!n. s n <= s (SUC n)) ==> !m n. NUM_LE m n ==> s m <= s n`
   *
   * A step at a time gives a step to anywhere. The induction is over the **gap** rather than over
   * either index: `NUM_LE m n` is `?d. NUM_ADD m d = n` by definition, so what an induction can
   * reach is `!m d. s m <= s (NUM_ADD m d)`, and the order statement is that with the witness put
   * back inside the existential.
   *
   * `Induct.proveBy` and not `Induct.prove`, because neither half is a rewrite. The base carries
   * the reflexivity of the order across `NUM_ADD m 0 = m` by congruence, which is `LE_OF_EQ`
   * applied to an equation rather than a normalisation, and the step chains the hypothesis with
   * the assumption at one index, which is transitivity over three atoms.
   */
  private def monotoneOrder(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    induct: Induct,
    ofEq: Kernel.Thm,
    orderDefinition: Kernel.Thm,
    addAtZero: Kernel.Thm,
    addAtSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val d = Term.variable("d", numbers)

    for {
      increasing <- Parser.proposition(theory, notation, "!n:num. (s:num -> real) n <= s (SUC n)")
      assumed <- LogicError.lift(Kernel.assume(increasing))
      transitive <- linarith.prove("!a:real. !b:real. !c:real. a <= b ==> b <= c ==> a <= c")

      statement <- Parser.proposition(
        theory, notation, "!m:num. !d:num. (s:num -> real) m <= s (NUM_ADD m d)")

      // **The variables are read off the goals the driver hands over and never taken from the
      // scope above.** `Induct.proveBy` opens the induction on its own fresh variables and leaves
      // the others free as ITS variables, so a base written with the `m` and `d` of this function
      // proves a statement about two other terms of the same name. What that produces is not a
      // type error: it is a theorem about the wrong thing, and what refuses it is `gen` reporting
      // a variable free in a hypothesis, several steps later and about a term nobody wrote.
      overTheGap <- induct.proveBy(
        statement,
        base =>
          for {
            indices <- comparisonIndices(base)
            collapsed <- rules.spec(indices._1, addAtZero)
            carried <- Conv.sym(collapsed).flatMap(Conv.apTerm(s, _))
            sides <- destructEquation(carried)
            result <- rules.specAll(ofEq, List(sides._1, sides._2)).flatMap(rules.mp(_, carried))
          } yield result,
        step =>
          for {
            indices <- comparisonIndices(step.hypothesis.conclusion)
            (index, gapSum) = indices
            opened <- rules.specAll(addAtSuccessor, List(index, argumentOf(gapSum)))
            sides <- destructEquation(opened)
            (_, successor) = sides
            above <- rules.spec(argumentOf(successor), assumed)
            here <- LogicError.lift(Term.app(s, index))
            middle <- LogicError.lift(Term.app(s, argumentOf(successor)))
            top <- LogicError.lift(Term.app(s, successor))
            chained <- rules
              .specAll(transitive, List(here, middle, top))
              .flatMap(rules.mp(_, step.hypothesis))
              .flatMap(rules.mp(_, above))
            carried <- Conv.sym(opened).flatMap(Conv.apTerm(s, _))
            result <- rewriteWith(carried, chained)
          } yield result
      )

      below <- Parser.proposition(theory, notation, "NUM_LE (m:num) (n:num)")
      assumedBelow <- LogicError.lift(Kernel.assume(below))
      unfolded <- Conv.unfold(orderDefinition, List(m, n)).flatMap(normaliseRight)
      witness <- LogicError.lift(Kernel.eqMp(unfolded, assumedBelow))

      inner <- Parser.proposition(theory, notation, "NUM_ADD (m:num) (d:num) = n:num")
      assumedInner <- LogicError.lift(Kernel.assume(inner))
      atGap <- rules.specAll(overTheGap, List(m, d))
      carriedInner <- Conv.apTerm(s, assumedInner)
      atIndex <- rewriteWith(carriedInner, atGap)
      eliminated <- rules.existsElim(witness, d, atIndex)

      result <- rules
        .disch(below, eliminated)
        .flatMap(rules.gen(n, _))
        .flatMap(rules.gen(m, _))
        .flatMap(rules.disch(increasing, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /**
   * `|- !s. (!n. s n <= s (SUC n)) ==> (?b. !n. s n <= b) ==> ?l. converges s l`
   *
   * The monotone convergence theorem, and the second time `COMPLETENESS` is spent in this
   * repository. The argument is the textbook one and every step of it is here: the image of the
   * sequence is a non-empty set bounded above, so it has a least upper bound; no term passes it;
   * and past any tolerance one term does, because otherwise the supremum would not be least.
   *
   * == The step this logic could not take until today ==
   *
   * "Otherwise the supremum would not be least" is a negated universal turned into a witness, and
   * `Peano.NUM_ARCHIMEDES` records that this logic had no rule for it and that its own derivation
   * was turned around to avoid needing one. There is no turning this one around: the witness IS
   * the index the convergence needs. `Classical.NOT_FORALL` is what landed with this theorem, and
   * the theorem is what paid for it.
   *
   * == What the derivation does NOT need, which is worth knowing before reading it ==
   *
   * No maximum over indices, because monotonicity carries one index to every later one, which is
   * [[MonotoneBelow]]. No second case split on the sign of the distance beyond the one `abs`
   * forces: past the witness the terms sit between the supremum less the tolerance and the
   * supremum, so both branches are a linear step over three comparisons.
   */
  private def monotoneConvergence(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    convergesDefinition: Kernel.Thm,
    completeness: Kernel.Thm,
    notForall: Kernel.Thm,
    doubleNegation: Kernel.Thm,
    irreflexive: Kernel.Thm,
    weakFromNegated: Kernel.Thm,
    bounds: Bounds,
    monotoneBelow: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val s = Term.variable("s", sequences)
    val bound = Term.variable("b", values)
    val supremum = Term.variable("t", values)
    val e = Term.variable("e", values)
    val x = Term.variable("x", values)
    val n = Term.variable("n", numbers)
    val k = Term.variable("k", numbers)

    val memberText = "?n:num. x:real = (s:num -> real) n"

    /** `!x. (?n. x = s n) ==> x <= <ceiling>` from `!n. s n <= <ceiling>`. */
    def upperBoundOf(ceiling: String, everyTerm: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        member <- Parser.proposition(theory, notation, memberText)
        assumedMember <- LogicError.lift(Kernel.assume(member))
        witnessEquation <- Parser.proposition(
          theory, notation, "x:real = (s:num -> real) (k:num)")
        assumedWitness <- LogicError.lift(Kernel.assume(witnessEquation))
        ceilingTerm <- Parser.term(theory, notation, ceiling, values)
        atK <- rules.spec(k, everyTerm)
        applied <- LogicError.lift(Term.app(s, k))
        carry <- linarith.prove("!a:real. !b:real. !c:real. a = b ==> b <= c ==> a <= c")
        atX <- rules
          .specAll(carry, List(x, applied, ceilingTerm))
          .flatMap(rules.mp(_, assumedWitness))
          .flatMap(rules.mp(_, atK))
        eliminated <- rules.existsElim(assumedMember, k, atX)
        result <- rules.disch(member, eliminated).flatMap(rules.gen(x, _))
      } yield result

    for {
      increasing <- Parser.proposition(theory, notation, "!n:num. (s:num -> real) n <= s (SUC n)")
      assumedIncreasing <- LogicError.lift(Kernel.assume(increasing))
      boundedStatement <- Parser.proposition(
        theory, notation, "?b:real. !n:num. (s:num -> real) n <= b")
      assumedBounded <- LogicError.lift(Kernel.assume(boundedStatement))

      // The image is inhabited, by the first term and nothing cleverer.
      inhabitedStatement <- Parser.proposition(
        theory, notation, "?x:real. ?n:num. x = (s:num -> real) n")
      inhabitedPredicate <- logic
        .destExistsPredicate(inhabitedStatement)
        .toRight(NotOfForm("an existential", inhabitedStatement))
      first <- Parser.term(theory, notation, "(s:num -> real) 0", values)
      atFirstStatement <- Parser.proposition(
        theory, notation, "?n:num. (s:num -> real) 0 = s n")
      atFirstPredicate <- logic
        .destExistsPredicate(atFirstStatement)
        .toRight(NotOfForm("an existential", atFirstStatement))
      zeroIndex <- Parser.term(theory, notation, "0:num", numbers)
      atFirst <- rules.existsIntro(atFirstPredicate, zeroIndex, Kernel.refl(first))
      inhabited <- rules.existsIntro(inhabitedPredicate, first, atFirst)

      // And bounded above, which is the hypothesis with the image wrapped round it.
      insideBounded <- Parser.proposition(
        theory, notation, "!n:num. (s:num -> real) n <= b:real")
      assumedInside <- LogicError.lift(Kernel.assume(insideBounded))
      boundsTheImage <- upperBoundOf("b:real", assumedInside)
      boundedAboveStatement <- Parser.proposition(
        theory,
        notation,
        "?y:real. !x:real. (?n:num. x = (s:num -> real) n) ==> x <= y"
      )
      boundedAbovePredicate <- logic
        .destExistsPredicate(boundedAboveStatement)
        .toRight(NotOfForm("an existential", boundedAboveStatement))
      boundedAboveAt <- rules.existsIntro(boundedAbovePredicate, bound, boundsTheImage)
      boundedAbove <- rules.existsElim(assumedBounded, bound, boundedAboveAt)

      // So there is a least upper bound.
      image <- Parser.term(
        theory, notation, "\\x:real. ?n:num. x = (s:num -> real) n", Type.fun(values, Type.Bool))
      atImage <- rules.spec(image, completeness)
      opened <- Conv
        .betaNormalise(atImage.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atImage)))
      premises <- rules.conjIntro(inhabited, boundedAbove)
      supremumExists <- rules.mp(opened, premises)

      supremumStatement <- Parser.proposition(
        theory,
        notation,
        "(!x:real. (?n:num. x = (s:num -> real) n) ==> x <= t:real) /\\ " +
          "(!y:real. (!x:real. (?n:num. x = (s:num -> real) n) ==> x <= y) ==> t <= y)"
      )
      assumedSupremum <- LogicError.lift(Kernel.assume(supremumStatement))
      upper <- rules.conjElim1(assumedSupremum)
      least <- rules.conjElim2(assumedSupremum)

      // No term passes it.
      //
      // **The bound name is `u` and not `n`, and that is not style.** Written `?n. s n = s n` the
      // binder captures the free index this is about, the predicate becomes `\u. s u = s u`, and
      // what comes out is a true theorem about the wrong thing. Nothing refuses it at the point it
      // is built: `Rules.mp` does not compare its antecedent, so the mismatch travels as an extra
      // hypothesis and surfaces several steps later as a variable free in a hypothesis, naming a
      // term nobody wrote. The check below is what turns it back into a refusal where it happens.
      atNStatement <- Parser.proposition(
        theory, notation, "?u:num. (s:num -> real) (n:num) = s u")
      atNPredicate <- logic
        .destExistsPredicate(atNStatement)
        .toRight(NotOfForm("an existential", atNStatement))
      applied <- LogicError.lift(Term.app(s, n))
      isMember <- rules.existsIntro(atNPredicate, n, Kernel.refl(applied))
      _ <- sameStatement(notation, isMember, atNStatement)
      belowSupremumAtN <- rules.spec(applied, upper).flatMap(rules.mp(_, isMember))
      belowSupremum <- rules.gen(n, belowSupremumAtN)

      // The convergence itself, at an arbitrary tolerance.
      positive <- Parser.proposition(theory, notation, "0 < e:real")
      assumedPositive <- LogicError.lift(Kernel.assume(positive))

      // Suppose no term passes the supremum less the tolerance.
      noneStatement <- Parser.proposition(
        theory, notation, "!n:num. ~(t:real - e:real < (s:num -> real) n)")
      assumedNone <- LogicError.lift(Kernel.assume(noneStatement))
      gap <- Parser.term(theory, notation, "t:real - e:real", values)
      belowGapAtN <- rules
        .specAll(weakFromNegated, List(gap, applied))
        .flatMap(rules.mp(_, rules.spec(n, assumedNone).getOrElse(assumedNone)))
      belowGap <- rules.gen(n, belowGapAtN)
      gapBoundsTheImage <- upperBoundOf("t:real - e:real", belowGap)
      leastAtGap <- rules.spec(gap, least).flatMap(rules.mp(_, gapBoundsTheImage))
      absurd <- linarith
        .prove("!a:real. !b:real. 0 < b ==> a <= a - b ==> a < a")
        .flatMap(rules.specAll(_, List(supremum, e)))
        .flatMap(rules.mp(_, assumedPositive))
        .flatMap(rules.mp(_, leastAtGap))
      clash <- rules.spec(supremum, irreflexive).flatMap(rules.notElim(_, absurd))
      notNone <- rules.notIntro(noneStatement, clash)

      // So one does, and that is the index the convergence wants.
      predicate <- Parser.term(
        theory,
        notation,
        "\\n:num. ~(t:real - e:real < (s:num -> real) n)",
        Type.fun(numbers, Type.Bool)
      )
      // **`NOT_FORALL` is polymorphic and has to be instantiated at `num` before it can be
      // specialised**, which is a step a reader of the derivation will not expect because nothing
      // else here is polymorphic. Without it the refusal is a type error about `'a -> bool` against
      // `num -> bool`, which names the symptom rather than the omission.
      atIndices = Kernel.instType(Map(Classical.TypeVariable -> numbers), notForall)
      passes <- rules
        .spec(predicate, atIndices)
        .flatMap(theorem =>
          Conv
            .betaNormalise(theorem.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))
        .flatMap(rules.mp(_, notNone))

      doubledStatement <- Parser.proposition(
        theory, notation, "~(~(t:real - e:real < (s:num -> real) (k:num)))")
      assumedDoubled <- LogicError.lift(Kernel.assume(doubledStatement))
      atWitnessStatement <- Parser.proposition(
        theory, notation, "t:real - e:real < (s:num -> real) (k:num)")
      atWitness <- rules
        .spec(atWitnessStatement, doubleNegation)
        .flatMap(rules.mp(_, assumedDoubled))

      // Past the witness every term sits between the supremum less the tolerance and the supremum.
      guard <- Parser.proposition(theory, notation, "NUM_LE (k:num) (n:num)")
      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      monotone <- rules
        .spec(s, monotoneBelow)
        .flatMap(rules.mp(_, assumedIncreasing))
        .flatMap(rules.specAll(_, List(k, n)))
        .flatMap(rules.mp(_, assumedGuard))

      atK <- LogicError.lift(Term.app(s, k))
      difference <- Parser.term(
        theory, notation, "(s:num -> real) (n:num) - t:real", values)
      distance <- Parser.term(
        theory, notation, "abs ((s:num -> real) (n:num) - t:real)", values)
      split <- rules.spec(difference, bounds.cases)

      plain <- Parser.proposition(
        theory, notation, "abs ((s:num -> real) (n:num) - t:real) = s n - t")
      fromPlain <- for {
        assumed <- LogicError.lift(Kernel.assume(plain))
        lemma <- linarith.prove(
          "!g:real. !a:real. !b:real. !e:real. g = a - b ==> a <= b ==> 0 < e ==> g < e")
        result <- rules
          .specAll(lemma, List(distance, applied, supremum, e))
          .flatMap(rules.mp(_, assumed))
          .flatMap(rules.mp(_, belowSupremumAtN))
          .flatMap(rules.mp(_, assumedPositive))
      } yield result

      negated <- Parser.proposition(
        theory, notation, "abs ((s:num -> real) (n:num) - t:real) = -(s n - t)")
      fromNegated <- for {
        assumed <- LogicError.lift(Kernel.assume(negated))
        lemma <- linarith.prove(
          "!g:real. !a:real. !b:real. !c:real. !e:real. " +
            "g = -(a - b) ==> b - e < c ==> c <= a ==> g < e")
        result <- rules
          .specAll(lemma, List(distance, applied, supremum, atK, e))
          .flatMap(rules.mp(_, assumed))
          .flatMap(rules.mp(_, atWitness))
          .flatMap(rules.mp(_, monotone))
      } yield result

      close <- rules.disjElim(split, fromPlain, fromNegated)

      guarded <- rules.disch(guard, close).flatMap(rules.gen(n, _))
      existential <- Parser.proposition(
        theory,
        notation,
        "?N:num. !n:num. NUM_LE N n ==> abs ((s:num -> real) n - t:real) < e:real"
      )
      existentialPredicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      witnessed <- rules.existsIntro(existentialPredicate, k, guarded)
      atTolerance <- rules.existsElim(passes, k, witnessed)

      body <- rules.disch(positive, atTolerance).flatMap(rules.gen(e, _))
      unfolded <- Conv.unfold(convergesDefinition, List(s, supremum)).flatMap(normaliseRight)
      target <- rightOf(unfolded)
      _ <- sameStatement(notation, body, target)
      converges <- Conv
        .sym(unfolded)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, body)))

      answer <- Parser.proposition(theory, notation, "?l:real. converges (s:num -> real) l")
      answerPredicate <- logic
        .destExistsPredicate(answer)
        .toRight(NotOfForm("an existential", answer))
      someLimit <- rules.existsIntro(answerPredicate, supremum, converges)
      eliminated <- rules.existsElim(supremumExists, supremum, someLimit)

      result <- rules
        .disch(boundedStatement, eliminated)
        .flatMap(rules.disch(increasing, _))
        .flatMap(rules.gen(s, _))
    } yield result
  }

  /** The two sides of an equation a theorem states. */
  private def destructEquation(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
    Term.destEq(theorem.conclusion).toRight(NotOfForm("an equation", theorem.conclusion))

  /**
   * The indices two applications of one sequence are compared at.
   *
   * `s m <= s (NUM_ADD m d)` gives `m` and `NUM_ADD m d`, which is what an induction step needs in
   * order to be about the driver's variables rather than about the caller's.
   */
  private def comparisonIndices(proposition: Term): Either[LogicError, (Term, Term)] =
    proposition match {
      case App(App(_, App(_, left)), App(_, right)) => Right((left, right))
      case other => Left(NotOfForm("a comparison of two terms of one sequence", other))
    }

  /** The argument of an application, which is what a successor wraps. */
  private def argumentOf(term: Term): Term = term match {
    case App(_, argument) => argument
    case other => other
  }

  /** Beta-normalise the right side of an equation, keeping it an equation. */
  private def normaliseRight(equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      right <- rightOf(equation)
      normal <- Conv.betaNormalise(right)
      joined <- Conv.trans(equation, normal)
    } yield joined

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))
}
