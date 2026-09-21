package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Finite sums and finite products over the naturals, with their recurrences and the facts a
 * consumer of them actually asks for.
 *
 * `Sum f n` is `f ZERO + ... + f (n - 1)` and `Prod f n` is `f ZERO * ... * f (n - 1)`, both
 * defined by recursion rather than assumed:
 *
 * {{{
 *   |- !f. Sum f ZERO = 0            |- !f. Prod f ZERO = 1
 *   |- !f n. Sum f (SUC n) = Sum f n + f n
 *   |- !f n. Prod f (SUC n) = Prod f n * f n
 * }}}
 *
 * Point 3 of the card that asked for the sum, which is explicit that Sigma with its recurrence is
 * not enough on its own: what the consumer needs is linearity, the telescoping sum, and **summation
 * by parts**, and without the last one an argument that quantifies over its length stays prose.
 *
 * == Why they are definitions and not hypotheses ==
 *
 * A recurrence can be carried on the left of the turnstile, which is what `RecurrenceSpec` shows
 * and what a development had to do before the recursion theorem existed. It costs every theorem two
 * hypotheses it can never discharge. With recursion the two equations are consequences of a
 * definition, so the theorems below rest on the axioms and on nothing else.
 *
 * == How the equations are proved, which is the same way every time ==
 *
 * One induction, whose step is a rewrite and a ring identity. The recurrences and the induction
 * hypothesis go in as rewrite rules, both sides of the goal are brought to a form whose only
 * unknowns are `Sum f n`, `f n` and their neighbours, and `Ring` closes what is left. `Ring` has
 * never heard of `Sum`, and does not need to: an application it cannot take apart is an atom, which
 * is exactly the right reading of a sum whose length is a variable.
 *
 * == How the bounds are proved, which is not that way ==
 *
 * Not one of the positivity or monotonicity facts is an equation, so `Ring` cannot close their
 * steps and [[Induct.proveWith]] does not apply to them. Each drives the induction with
 * [[Induct.proveBy]] and closes its two halves with [[Series.Bounds]], where the certificate
 * replacing `Ring` is written out: the difference between the two sides is a sum of products of
 * things already known to be at least zero, [[Order]] adds and multiplies those, and `Ring` is
 * asked only for the identity that turns the sum back into the difference. Every step below has a
 * certificate of two terms.
 *
 * == Where this sits, and what that buys ==
 *
 * **Over `Peano`, not beside it**, since 2026-09-11. The two used to extend the theory of the reals
 * each for its own constants, and the consequence was not a choice a caller had to make: it was
 * that `NUM_ADD` could not appear **inside** a `Sum`, because the theory the sum was defined over
 * had never heard of it. `Sum (\i. f (NUM_ADD m i)) n` named no term and the proposition was not a
 * proposition.
 *
 * What that cost was reindexing by an arbitrary offset. [[Series.Shift]] is the offset-one case,
 * which is the whole of what `SUC` alone can say, and its note wrote the general induction out in
 * advance and called it blocked. It is [[Series.Reindex]] now, and the proof is that induction
 * unchanged: what was missing was never the mathematics, it was where the two developments stood
 * relative to each other.
 *
 * Swapping two finite sums was expected to be behind that same door and never was: it is
 * [[Series.Swapped]], it needs no arithmetic on `num`, and what it needed instead was one step the
 * driver cannot take, recorded there. The expectation being wrong is the reason that note is long.
 *
 * The second thing it buys is the laws of exponents, [[Series.PowerOfSum]] and
 * [[Series.PowerOfProduct]], which mention `NUM_ADD` and `NUM_MUL` for the same reason and were
 * unsayable for the same one. They are here rather than in `Peano` because `Peano` has never heard
 * of `Power`: only this development has both.
 */
final class Series private (
  val ring: Ring,
  val logic: Logic,
  val theory: Theory,
  val notation: Notation,
  val definition: Kernel.Thm,
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  val reals: RealTheory = ring.reals

  /** A derived fact of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Series {

  /** The sum's name. */
  val SumName: String = "Sum"

  /** The power's name: `Power b n` is `b` multiplied by itself `n` times. */
  val PowerName: String = "Power"

  /** The product's name: `Prod f n` is `f ZERO * ... * f (n - 1)`. */
  val ProdName: String = "Prod"

  /** `|- !b. Power b ZERO = 1` */
  val PowerAtZero: String = "POWER_ZERO"

  /** `|- !b n. Power b (SUC n) = b * Power b n` */
  val PowerAtSuccessor: String = "POWER_SUC"

  /** `|- !f. Prod f ZERO = 1` */
  val ProdAtZero: String = "PROD_ZERO"

  /** `|- !f n. Prod f (SUC n) = Prod f n * f n` */
  val ProdAtSuccessor: String = "PROD_SUC"

  /** `|- !f. Sum f ZERO = 0` */
  val AtZero: String = "SUM_ZERO"

  /** `|- !f n. Sum f (SUC n) = Sum f n + f n` */
  val AtSuccessor: String = "SUM_SUC"

  /** `|- !a f g n. Sum (\i. a * f i + g i) n = a * Sum f n + Sum g n` */
  val Linear: String = "SUM_LINEAR"

  /** `|- !g n. Sum (\i. g (SUC i) - g i) n = g n - g ZERO` */
  val Telescoping: String = "SUM_TELESCOPES"

  /**
   * `|- !a b n. Sum (\i. a i * (b (SUC i) - b i)) n =
   *             a n * b n - a ZERO * b ZERO - Sum (\i. b (SUC i) * (a (SUC i) - a i)) n`
   *
   * The one the card calls the real consumer. An argument that sums a product against a difference
   * and needs the answer for every length rather than for two of them is this identity or it is
   * prose.
   */
  val ByParts: String = "SUM_BY_PARTS"

  /**
   * `|- !f n. Sum (\i. f (SUC i)) n = Sum f (SUC n) - f ZERO`
   *
   * Reindexing, as far as this theory can state it, and the gap is the point rather than an
   * omission. The lemma the card asks for is `Sum (\i. f (i + m)) n = ...`, and **that statement
   * cannot be written here**: `num` carries `ZERO` and `SUC` and nothing else, so `i + m` names no
   * term and the proposition is not a proposition. What `SUC` alone can express is the offset of
   * one, which is this.
   *
   * == What lands with addition, and what it costs ==
   *
   * Given `+` on `num` with its two recurrences, `!f m n. Sum (\i. f (i + m)) n = Sum f (m + n) -
   * Sum f m` is an induction on `n` of exactly this shape: the base wants `Sum f (m + ZERO) = Sum f
   * m`, which is the right-zero recurrence, and the step wants `m + SUC n = SUC (m + n)`, which is
   * the other one. This lemma is that lemma at `m = SUC ZERO` once `SUC ZERO` and `1` are the same
   * number, and it is stated separately rather than derived from it because it is the case a
   * development can have today.
   *
   * **Swapping two finite sums is not behind this door at all**, which was worth measuring rather
   * than assuming: it needs no arithmetic on `num` and it is [[Swapped]], below.
   */
  val Shift: String = "SUM_SHIFT"

  /**
   * `|- !f m n. Sum (\i. f (NUM_ADD m i)) n = Sum f (NUM_ADD m n) - Sum f m`
   *
   * Reindexing by an arbitrary offset, which [[Shift]]'s note predicted would land the day addition
   * on `num` did and which took a day longer than that. Addition landed on 2026-09-10 in `Peano`;
   * what was missing was that `Sum` was defined over a theory that had never heard of it, so
   * `NUM_ADD m i` under the binder named no term and the proposition was not a proposition. Series
   * over Peano rather than beside it is what makes the statement *writable*, and the proof is then
   * the induction [[Shift]]'s note wrote out in advance, unchanged: the base is `NUM_ADD m ZERO =
   * m`, the step is `NUM_ADD m (SUC n) = SUC (NUM_ADD m n)`, and `Ring` closes what is left over
   * the three atoms `Sum f (NUM_ADD m n)`, `Sum f m` and `f (NUM_ADD m n)`.
   *
   * [[Shift]] stays. It is this lemma at `m = SUC ZERO`, and it is stated separately because its
   * right-hand side is written with `SUC` alone: a development that has the sums and not the
   * arithmetic can still have it, and deriving it from this one would cost a rewrite through
   * `NUM_ADD (SUC ZERO) n = SUC n` to say something the shorter statement already says.
   *
   * The offset is on the **left** of `NUM_ADD`, because `NUM_ADD` recurses on its second argument
   * and the induction here is on `n`. Written the other way round the step would need commutativity
   * before the recurrence could fire, which is a theorem `Peano` has and an extra rewrite this does
   * not need.
   */
  val Reindex: String = "SUM_REINDEX"

  /**
   * `|- !f m n. Sum (\i. Sum (\j. f i j) m) n = Sum (\j. Sum (\i. f i j) n) m`
   *
   * The order of two finite summations does not matter. It was expected to need reindexing and it
   * does not: what it needs is [[Additive]] and [[OfZero]], and one thing the driver cannot do on
   * its own.
   *
   * == The one step the driver cannot take, and it is not the one predicted ==
   *
   * After the recurrences and the induction hypothesis, the step is exactly
   *
   * {{{
   *   Sum (\j. Sum (\i. f i j) k) m + Sum (\j. f k j) m = Sum (\j. Sum (\i. f i j) k + f k j) m
   * }}}
   *
   * which is [[Additive]] read backwards at a particular pair of summands. `Ring` cannot close it,
   * because the three sums are three unrelated atoms to it and the identity is false between
   * atoms. And `Additive` cannot be *handed to the rewriter* to close it either: as a rule its left
   * side is `Sum (\i. F i + G i) n`, and matching that against a summand which is itself a sum
   * would mean binding `F` to a function of the bound variable rather than to a term. That is
   * higher-order matching, and `Matching`'s own comment says it is first order and why.
   *
   * So the step instantiates `Additive` **by hand** at the two summands it reads off the goal, beta
   * normalises the instance, and closes with it. That is the whole of what is special here, and it
   * is why this lemma has a step of its own rather than a line in [[Statements]].
   *
   * == What was measured, against what was predicted ==
   *
   * The prediction, written when only `Sum` existed, was that this needed addition on `num` and was
   * therefore blocked with [[Shift]]. Two measurements say otherwise. The rewriter **does** rewrite
   * a sum sitting under a binder whose summand mentions that binder's variable, which was the
   * doubt: `Sum (\j. Sum (\i. f i j) (SUC k)) m` becomes `Sum (\j. Sum (\i. f i j) k + f k j) m`,
   * because the rewriter opens a binder with a fresh free variable before descending rather than
   * matching under it. `SeriesSpec` pins that, since it is the fact the proof rests on. And the
   * arithmetic never enters: the induction is on the outer length and the inner one is a parameter.
   */
  val Swapped: String = "SUM_SWAP"

  /**
   * `|- !f g n. Sum (\i. f i + g i) n = Sum f n + Sum g n`
   *
   * [[Linear]] without the scalar, and it is not a convenience: `Linear` at `a = 1` gives
   * `Sum (\i. 1 * f i + g i) n`, whose summand is not the summand anybody writes, and a rewrite
   * rule is matched syntactically. This is the shape a sum of two summands actually has.
   *
   * It is also the first half of what swapping two finite sums needs, and the reason that is not
   * here is recorded under [[Shift]].
   */
  val Additive: String = "SUM_ADD"

  /**
   * `|- !a f n. Sum (\i. a * f i) n = a * Sum f n`
   *
   * A constant factor comes out of a finite sum. It is [[Linear]] with the second summand dropped
   * and it is **not** that lemma specialised: `Linear` at `g := \i. 0` gives the summand
   * `a * f i + 0`, which is not the summand anybody writes, and a rewrite rule is matched
   * syntactically. The same argument [[Additive]] already makes about itself, one operation over.
   */
  val Scaled: String = "SUM_SCALE"

  /**
   * `|- !a f n. Sum (\i. f i * a) n = Sum f n * a`
   *
   * [[Scaled]] with the factor on the other side, and both are published for the reason
   * [[NegatedDouble]] gives for the half-law it does not have: a reader who finds one side and not
   * the other cannot tell whether the missing side is false or merely unwritten. Here both are
   * true and both are consumed, by the two ends of [[Product]]: the inner sum of a double sum
   * carries its factor on the left and the outer one carries it on the right, so a development
   * holding one of these would have to commute under a binder to use it.
   */
  val ScaledRight: String = "SUM_SCALE_RIGHT"

  /**
   * `|- !f g m n. Sum (\i. Sum (\j. f i * g j) m) n = Sum f n * Sum g m`
   *
   * Every product of a term of `f` with a term of `g`, added up, is the product of the two sums.
   * It is the **finite** half of what the Cauchy product needs, and it is where a route to
   * `exp (x + y) = exp x * exp y` begins: the product of two partial sums is a sum over a square
   * of indices, and everything after this is about what happens to that square as both sides grow.
   *
   * **It is not about `Prod`**, which is this file's other operator and is a product of terms of
   * one sequence. The name says products in the plural because what is summed is one product per
   * pair, and the two constants cannot be confused in a statement: nothing here mentions `Prod`.
   *
   * == What it costs, which is two lemmas and no induction of its own ==
   *
   * The two lengths are independent and the induction is on the outer one alone, `m` riding through
   * as a parameter exactly as it does in [[Swapped]]. The step needs the inner sum collapsed,
   * `Sum (\j. f n * g j) m = f n * Sum g m`, which is [[Scaled]] **as a rewrite rule**, and that is
   * the whole of why this is not a line in [[Statements]]: it is proved from a rule set the
   * statements above have to exist first to build.
   *
   * And it is the measurement that says the scale lemmas had to be a pair. The inner collapse binds
   * the constant on the **left** and what is left over, `Sum (\i. f i * Sum g m) n`, binds it on
   * the **right**; one lemma would have meant commuting a product under a binder, which is a
   * congruence over the whole summand rather than a rewrite.
   */
  val Product: String = "SUM_OF_PRODUCTS"

  /**
   * `|- !f n. Sum (\k. Sum (\i. f i (k - i)) (SUC k)) n = Sum (\i. Sum (\j. f i j) (n - i)) n`
   *
   * The triangle `{(i, j) : i + j < n}` added up by antidiagonals on the left and by rows on the
   * right. With [[Product]] it is the whole finite content of the Cauchy product: that one says a
   * product of two sums is a sum over a **square**, this one says how a triangle is re-cut, and
   * what is left between the pair and `exp (x + y) = exp x * exp y` is analysis and the binomial
   * theorem, neither of which this file owns.
   *
   * The antidiagonal `k` has `SUC k` entries and the row `i` has `n - i` of them, which is why the
   * two lengths are written the way they are and why neither side can be stated without the
   * truncated difference. See [[summedDiagonal]] for what the step costs, which is a bounded
   * congruence and two facts about `NUM_SUB` that did not exist.
   */
  val Diagonal: String = "SUM_DIAGONAL"

  /**
   * `|- !x y n. Power (x + y) n =
   * Sum (\i. real_of_num (NUM_CHOOSE n i) * (Power x i * Power y (n - i))) (SUC n)`
   *
   * The binomial theorem. It is the one fact in this file whose statement mentions a constant
   * this development does not own: `NUM_CHOOSE` is `Peano`'s, and it is the reason this waited,
   * since nothing anywhere defined a binomial coefficient until 2026-09-20.
   *
   * The sum runs to `SUC n` rather than to `n` because the range of a `Sum` is the indices
   * **below** its bound, so `SUC n` is the `n + 1` entries a reader expects. Everything at or
   * past that is zero anyway, which is `Peano.NUM_CHOOSE_ABOVE` and is spent inside the proof
   * rather than left for a reader to notice.
   *
   * See [[binomialTheorem]] for what the step costs, which is four congruences of which exactly
   * one carries a bound.
   */
  val Binomial: String = "POWER_BINOMIAL"

  /**
   * `|- !a b n. Sum (\k. Sum (\i. a i * b (k - i)) (SUC k)) n = Sum (\i. a i * Sum b (n - i)) n`
   *
   * The `n`th partial sum of a Cauchy product, in closed form. The left side is the definition —
   * add up the first `n` convolutions — and the right side is one sum whose `i`th term is a term
   * of `a` against a **partial sum** of `b`. Everything a convergence argument does to a Cauchy
   * product starts by making that move, and until [[Diagonal]] landed it could not be made.
   *
   * It is [[Diagonal]] at `\i j. a i * b j` with [[Scaled]] inside, and nothing else: the
   * diagonal says the triangle summed by antidiagonals is the triangle summed by rows, and a row
   * of this triangle is `a i` times a partial sum of `b` because `a i` does not depend on the
   * index the row runs over. The congruence is unconditional, since that is true at every `i`.
   */
  val Cauchy: String = "SUM_CAUCHY"

  /**
   * `|- !a b n. Sum a n * Sum b n - Sum (\k. Sum (\i. a i * b (k - i)) (SUC k)) n =
   * Sum (\i. a i * (Sum b n - Sum b (n - i))) n`
   *
   * What a Cauchy product is missing at `n`, as **one sum**. The product of the two partial sums
   * is a sum over a square and the partial Cauchy sum is a sum over the triangle inside it, so
   * the gap is the corner; written this way it is a single sum whose `i`th term is a term of `a`
   * against a **tail** of `b`, `Sum b n - Sum b (n - i)`.
   *
   * That shape is the whole point. The remaining analytic step in the Cauchy product theorem is
   * that this goes to zero, and in this form it is one estimate over one sum rather than an
   * argument about two regions of a square. What it still needs is stated where the work is
   * tracked rather than promised here: tails of an absolutely convergent series going to zero,
   * which this development has not got.
   *
   * == It is derived as a sum and published as a difference ==
   *
   * The derivation gives `gap + cauchy = product`, because [[Additive]] splits a sum and there is
   * no lemma here taking a negation out of one: `Sum (\i. -(f i)) n = -(Sum f n)` is not in the
   * library and is not added for this, since one `Linarith` step over three atoms turns the sum
   * form into the difference a reader wants. The difference is what is published because that is
   * what the word "gap" means.
   */
  val CauchyGap: String = "SUM_CAUCHY_GAP"

  /**
   * `|- !n. Sum (\i. 0) n = 0`
   *
   * A sum of nothing is nothing, at every length, and it does **not** follow from `SUM_ZERO`, which
   * is about a sum of length zero rather than a summand of value zero. The two read alike and are
   * different facts; this is the one an empty inner sum leaves behind.
   */
  val OfZero: String = "SUM_OF_ZERO"

  /**
   * `|- !c n. Sum (\i. c) n = real_of_num n * c`
   *
   * A sum of a constant is the constant times the length, which is the only way this library can
   * say how long a range is. [[OfZero]] is this at `c = 0` and was here first, which is the shape
   * of the gap rather than an accident: the zero case was wanted once, by [[Swapped]]'s base, and
   * generalising it was never forced because nothing until now summed a summand that does not
   * mention the index.
   *
   * The distinction [[OfZero]]'s own note draws is this one a step out. `SUM_ZERO` is a sum of
   * length zero, `SUM_OF_ZERO` a summand of value zero, and this is a summand of any FIXED value:
   * three facts that read alike, and the third is the one that counts a range.
   *
   * Its rules are the sum's recurrences together with the embedding of zero and of the successor,
   * which is a combination no other list here uses: the length crosses from `num` to `real` on the
   * right-hand side and nowhere else, so the step is `real_of_num n * c + c` against
   * `(real_of_num n + 1) * c` and RING closes it.
   *
   * The consumer that asked for it was counting the words of a length: appending a 1 to every word
   * of length t adds `2^t` to each offset, so summing over the upper half leaves a genuinely
   * constant summand over a range of 2^t indices. The alternative was to dress that constant up as
   * a weighted sum so that an existing lemma would reach it, which costs the reader of the formal
   * statement the ability to check it against the informal one.
   */
  val Constant: String = "SUM_CONSTANT"

  /**
   * `|- !f g. (!i. f i = g i) ==> !n. Sum f n = Sum g n`
   *
   * The lemma a binder needs, and the scope of it is narrower than it looks. The rewriter goes
   * **into** the lambda `Sum` binds, so a summand written out is rewritten where it stands:
   *
   * {{{
   *   Sum (\i. ff i) n      becomes  Sum (\i. gg i) n
   *   Sum (\i. 2 * ff i) n  becomes  Sum (\i. 2 * gg i) n
   *   Sum ff n              does not move
   * }}}
   *
   * So this is wanted exactly when the summand is a **bare symbol**, which is what a development
   * that quantifies over its summand rather than writing it out has. There is no redex to go into
   * there, and without extensionality, which is not asserted here and the note in `Natural` says
   * why, a congruence lemma is the only way.
   *
   * **Every future operator that binds a variable will want its own**, products, integrals, maxima.
   * That is a consequence of not having extensionality rather than an oversight in this file, and
   * it is written here because this is the first place it bites.
   *
   * That prediction has now been tested rather than believed. `Prod` is the first such operator to
   * arrive and it wanted [[ProdCongruence]], which is this derivation at a different constant: the
   * prediction held, and what it cost was a parameter on one private function rather than a second
   * proof. [[NonNegative]] and [[Monotone]] are the same shape again for the same reason, a bare
   * summand symbol with a pointwise hypothesis, and they are three more instances of it.
   */
  val Congruence: String = "SUM_CONGRUENCE"

  /**
   * `|- !f g. (!i. f i = g i) ==> !n. Prod f n = Prod g n`
   *
   * [[Congruence]] at `Prod`, and the test of the prediction that file comment makes. It is not
   * derivable from the sum's congruence and it is not a rewrite of it: it is the same induction run
   * over the product's two recurrences.
   */
  val ProdCongruence: String = "PROD_CONGRUENCE"

  /**
   * `|- !b. 0 < b ==> !n. 0 < Power b n`
   *
   * The shortest of the bounds and the one to read first: its step is a product of two positives,
   * which is `LT_MUL` and therefore an axiom of the theory rather than something to derive.
   */
  val PowerPositive: String = "POWER_POSITIVE"

  /**
   * `|- !a b. 0 < a ==> a <= b ==> !n. Power a n <= Power b n`
   *
   * Monotone in the **base** and not in the exponent, which is a choice and not the only statement
   * the name could carry. Monotonicity in the exponent is a different fact, it needs `1 <= b`
   * rather than `0 < a`, and it says nothing about two different bases; this is the one a bound on a
   * measured quantity wants, where the base is what is known imprecisely.
   *
   * `0 < a` and not `0 <= a`: at `n = ZERO` both sides are `1` and the hypothesis is unused, but
   * the step multiplies the induction hypothesis by `a`, and a factor that may be zero turns the
   * strict positivity of `Power b n` into nothing. The certificate says where:
   * `b * Power b n - a * Power a n = (b - a) * Power b n + a * (Power b n - Power a n)`, and the
   * second product needs `0 <= a`, which is all the hypothesis is spent on.
   */
  val PowerMonotone: String = "POWER_MONOTONE"

  /**
   * `|- !b m n. Power b (NUM_ADD m n) = Power b m * Power b n`, the law of exponents.
   *
   * Without it an exponent that is a sum is an **opaque atom**: `Power 2 (NUM_ADD a b)` and
   * `Power 2 a * Power 2 b` are two terms with no relation, and no rewriting brings them together.
   * Every exponent in a development that counts something in stages has that shape, because a stage
   * count is a partial sum, so this is the lemma that decides whether such a development can state
   * anything at all about its exponents.
   *
   * It could not be written before 2026-09-11, and the reason is the one [[Reindex]] gives: it
   * mentions `NUM_ADD`, which belongs to `Peano`, and until this development was built over that one
   * the two constants had no theory in common. The card that asked for it proposed `Peano` as the
   * home for exactly that reason, and that was right about the old order and is wrong about this
   * one: `Peano` has never heard of `Power`, and here both are in scope.
   */
  val PowerOfSum: String = "POWER_ADD"

  /**
   * `|- !m n. real_of_num (NUM_POW m n) = Power (real_of_num m) n`
   *
   * The bridge between the natural-number power and the real one, and the only place it can
   * live: `Peano` defines `NUM_POW` and has never heard of `Power`, and here both are in scope.
   * The same argument that put [[PowerOfSum]] in this file rather than in `Peano`.
   *
   * It is what a development counting things needs. An exponent a proof is still COUNTING with
   * is a `num` and its power is `NUM_POW`; the moment that count is weighed against a real it
   * has to become `Power`, and without this the two are unrelated constants. `2^t` as the number
   * of words of length `t` and `2^t` as a coefficient are the same number on either side of it.
   */
  val EmbedsPower: String = "NUM_REAL_POW"

  /**
   * `|- !f n. Sum f (NUM_ADD n n) = Sum f n + Sum (\i. f (NUM_ADD n i)) n`
   *
   * A sum over a range split down the middle: the first half as it stands, the second half
   * reindexed to start at zero. It is [[Reindex]] with both arguments the same and the
   * subtraction cleared, which is the one instance of it that anything actually uses, because a
   * range that doubles is what a binary enumeration produces at every step.
   *
   * The reason it is worth a name: with `NUM_MUL_TWO` and `NUM_POW_SUC` it reads as the split of
   * the `2^(n+1)` objects of length `n+1` into the `2^n` of length `n` twice over, which is the
   * combinatorial step underneath every recurrence on such a family. A consumer that has this
   * does not have to reason about the enumeration at all.
   *
   * **And it is worth a name rather than an inlining because a rewrite cannot do it.** What
   * separates it from [[Reindex]] is clearing a subtraction, `a = b - c` against `b = c + a`,
   * and NOTHING REARRANGES A SUBTRACTION UNLESS SOMEBODY WRITES A RULE FOR IT. A reader who
   * reaches for a rewrite here finds nothing and concludes the identity is hard; it is not, it
   * is three atoms and the linear reader settles it. That is what this entry is for.
   */
  val Halves: String = "SUM_HALVES"

  /**
   * `|- !f g n. (!i. NUM_LT i n ==> f i = g i) ==> Sum f n = Sum g n`
   *
   * Congruence ON A RANGE, which is the statement a consumer can actually use.
   *
   * [[Congruence]] asks the two summands to agree at EVERY index, and `Sum f n` never evaluates
   * `f` at or above `n`: `SUM_SUC` unfolds it downwards and stops. So the unconditional form is
   * the lazy statement of the fact, and two summands that agree exactly where the sum looks --
   * which is the ordinary case, and is what every argument about a family indexed below a bound
   * produces -- cannot use it at all.
   *
   * The induction is on `n` with the implication inside it, because the hypothesis mentions the
   * induction variable and cannot be lifted out. Its step re-derives the hypothesis at `n` from
   * the one at `SUC n`, which needs `i < n ==> i < SUC n`; that is `Peano.NUM_LT_TRANS` with
   * `NUM_LT_SUC`, and the first of those was missing until this was written.
   *
   * == How many siblings this defect has, counted on 2026-09-12 ==
   *
   * The shape is a hypothesis quantified over the whole type where the conclusion names an object
   * with a BOUND, and the tell is mechanical: compare the hypothesis's quantifiers against the
   * bounds the conclusion writes. Of the seventeen lemmas in the library whose hypothesis carries
   * its own universal, **four** match, and they are the same statement as [[Congruence]] at a
   * different operator or a different relation:
   *
   *   - [[ProdCongruence]], `(!i. f i = g i) ==> Prod f n = Prod g n`
   *   - [[ProdPositive]], `(!i. 0 < f i) ==> 0 < Prod f n`
   *   - [[Monotone]], `(!i. f i <= g i) ==> Sum f n <= Sum g n`
   *   - [[NonNegative]], `(!i. 0 <= f i) ==> 0 <= Sum f n`
   *
   * All four are strictly stronger than they need to be, by the same argument as above: `PROD_SUC`
   * unfolds downwards exactly as `SUM_SUC` does, so neither operator reads its summand at or above
   * the bound.
   *
   * The other thirteen do not match, and three are the instructive ones: `WORD_EXTENSIONALITY`,
   * `WORD_MAKE_LENGTH` and `WORD_MAKE_NTH` all DO carry the bound in the hypothesis, which settles
   * that the omission is not a house style anybody chose: this library writes the bound when the
   * author happened to think about it and drops it when they did not.
   *
   * **And none of the four is demonstrated to be a defect, which is the honest half of this count.**
   * A lemma stated at the wrong scope is invisible from inside: it is true, it is general, and it
   * passes every test written about it. It becomes visible when a consumer holds the hypothesis
   * only on the range, and grep says all four are referenced nowhere but their own assertions in
   * `SeriesSpec`. [[Congruence]]'s defect surfaced only because a development outside this
   * repository used it. So this is a prediction rather than a repair, and it is the kind that can
   * be checked: **the first real consumer of any of those four meets this same wall**, and the fix
   * will again be a bounded twin rather than a correction. Weakening them now would add four
   * library entries nobody has asked for, which is the move this note exists to argue against.
   */
  val CongruenceBelow: String = "SUM_CONGRUENCE_BELOW"

  /**
   * `|- !f g n. (!i. NUM_LT i n ==> f i <= g i) ==> Sum f n <= Sum g n`
   *
   * [[Monotone]] with the bound written into the hypothesis, and **it is the prediction
   * [[CongruenceBelow]]'s note makes, come true.** That note counts four lemmas here stated at the
   * wrong scope, says that none of them is demonstrated to be a defect from inside, and predicts
   * that the first real consumer of any of the four meets the same wall and gets a bounded twin
   * rather than a correction. [[Monotone]] is one of the four, and the Cauchy product is that
   * consumer: the square of side `n` sits inside the triangle of side `n + n`, and the two
   * summands it compares are ordered **only** below the bound.
   *
   * It costs no derivation of its own. [[congruenceOnARange]] was already the induction this
   * wants, and the only thing in it specific to an equation was how the base closes, so that is a
   * parameter now. [[Monotone]] stays, for the reason [[Congruence]] stays beside its own twin.
   *
   * **The parameter is kept for what it refuses, not for what it proves**, and that was measured
   * rather than assumed. `Linarith` settles `0 = 0`, so closing the equation's base with it
   * instead of with `Kernel.refl` leaves the whole suite green: a perturbation says so. What
   * `refl` buys is that it refuses any base the rewriting did not already close, where the
   * decider would accept a true equation it had failed to reduce, and a base that is silently
   * not closed is the shape of defect this induction cannot otherwise report.
   */
  val MonotoneBelow: String = "SUM_MONOTONE_BELOW"

  /**
   * `|- !b m n. Power b (NUM_MUL m n) = Power (Power b m) n`, the second law of exponents.
   *
   * The companion of [[PowerOfSum]] and proved by the same induction one line later, because its
   * step rewrites `NUM_MUL m (SUC n)` to `NUM_ADD (NUM_MUL m n) m` and then wants [[PowerOfSum]] as
   * a rewrite rule. It is here because it was cheap once the first was there, not because anything
   * in the repository asks for it yet: the card that proposed it said in as many words that it was
   * not verified and blocked nothing.
   */
  val PowerOfProduct: String = "POWER_MUL"

  /**
   * `|- !n. Power 1 n = 1`, the unit base, and **nothing asks for it**.
   *
   * It has the label [[PowerOfProduct]] has and for a sharper reason, which is worth the paragraph
   * because the first version of this comment said the opposite. A consumer asked for it on
   * 2026-09-13, to reach `(-1)^(2^t) = 1` through `POWER_MUL`, and it was proved the same hour.
   * That consumer then **withdrew the request**: the route it took induces on the square rather
   * than on the value, since the value is `1` for `t >= 1` and `-1` at `t = 0` and no single
   * equation holds at every length while the square does, and that route needs neither this lemma
   * nor `POWER_MUL`.
   *
   * So it is kept for being cheap and general and not for unblocking anything, and saying so is
   * the point: a comment claiming a consumer would be read a month from now as evidence that
   * something depended on this, which nothing does. The correction is the consumer's, offered
   * before this was committed rather than after.
   *
   * What the episode is worth keeping is its rule, which is theirs: **a consumer sending a request
   * upstream should send the FACT it needs and not the derivation it has in mind**, because the
   * derivation is the half that can be improved on and that one was.
   *
   * Checked absent before it was proved, by name, by constant and by shape. `NUM_POW_ONE` is the
   * same statement over `num` and is a different lemma. Proved by the same induction as the two
   * laws above and from the same two rules, its step being `1 * Power 1 n` against `Power 1 n`,
   * which the driver's RING closes.
   */
  val PowerOfOne: String = "POWER_ONE"

  /**
   * `|- !a b n. Power (a * b) n = Power a n * Power b n`, the power of a product of BASES.
   *
   * Every other power law here names what happens in the EXPONENT: [[PowerOfSum]] is
   * `Power b (NUM_ADD m n)` and [[PowerOfProduct]] is `Power b (NUM_MUL m n)`. This one is the
   * first about the base, which is why it is not called `POWER_PRODUCT` or `POWER_OF_PRODUCT`:
   * the pattern `POWER_<operation>` is taken, so a name of that shape for a law about the base
   * reads as a third law of exponents, and a reader who has seen the two lines above it in
   * `docs/lemmas.md` parses it that way. `MUL` is also the corpus's spelling of multiplication,
   * 33 fact names to `PRODUCT`'s 0 out of 279, and the one-spelling-per-concept rule in
   * `docs/naming.md` says a new lemma may not add a fourth. The adjective follows [[Linear]]:
   * a name for the homomorphism property of the OPERATOR rather than for the operation inside
   * its argument, which is what `SUM_LINEAR` is to `Sum`.
   *
   * **What asked for it, and it is a consumer rather than symmetry.** `Ring` normalises to a sum
   * of monomials over ATOMS, and an atom is a term the procedure has decided not to look inside.
   * A power at a VARIABLE exponent is one, since nothing there expands `Power 2 t`. So
   * `Power 2 t` and `Power 4 t` are two DISTINCT atoms and no ring identity relates them: a term
   * holding both collapses by rewriting or not at all, never by arithmetic. (The first version of
   * this paragraph said the ordered rules compare head constants by name. That is a sentence about
   * where an atom sits in a monomial, which is `Arithmetic.ringOrder`'s business, and it is not
   * why two atoms are unrelated. Correct conclusion, wrong mechanism under it.) A development downstream was paying one full induction per pair of bases
   * (`2^t * 4^t = 8^t` and `2^t * 2^t = 4^t` were two of them) for want of the lemma that relates
   * them. With this, each of those is one specialisation and the next pair costs nothing.
   *
   * A list of its own rather than a fourth line in [[ExponentStatements]], for the reason the
   * third and fourth lists exist: what separates it is the RULE SET. It wants the power's two
   * recurrences and nothing else -- no arithmetic on `num`, no laws of exponents, not even
   * [[PowerOfSum]] -- because its induction is on the exponent and its step is one rewrite and a
   * ring identity. Putting it in the exponent list would have said it rests on `NUM_ADD` and
   * `NUM_MUL`, which it does not.
   */
  val Multiplicative: String = "POWER_MULTIPLICATIVE"

  /**
   * `|- !q n. (q - 1) * Sum (\i. Power q i) n = Power q n - 1`, the geometric sum.
   *
   * Cleared of its denominator, so that `Ring` and not a field closes the algebra and the lemma
   * carries no hypothesis `q != 1` at all. At `q = 1` both sides are zero and the statement is
   * true and empty, which is the right behaviour for a lemma somebody will instantiate without
   * looking: the degenerate case cannot give a wrong answer, only an uninformative one.
   *
   * **It cannot go through the default step, and the reason is the one `Induct`'s own comment
   * gives.** That step uses the induction hypothesis as a REWRITE RULE, so its left side has to
   * be a subterm of the step goal. Here the step goal rewrites to
   * `(q - 1) * (Sum f n + Power q n) = q * Power q n - 1` and the hypothesis's left side is
   * `(q - 1) * Sum f n`, which is not a subterm of it: the scalar multiplies the whole of the
   * extended sum. So the hypothesis is carried as an IMPLICATION and discharged, which is what
   * [[geometricSum]] does, and the same shape as [[CongruenceBelow]] for a different reason.
   *
   * The alternative was to state it at the summand `(q - 1) * Power q i`, where the hypothesis IS
   * a subterm and the default step closes it. Rejected: that is a weighted sum and not the
   * geometric sum, a reader would not recognise it, and the consumer would have to pull the
   * scalar back out through [[Linear]] with a zero second summand, which is the awkward step this
   * lemma exists to spare them.
   */
  val Geometric: String = "SUM_GEOMETRIC"

  /**
   * `|- !x n. Power (0 - x) (NUM_ADD n n) = Power x (NUM_ADD n n)`: a doubled exponent does not
   * see the sign of the base.
   *
   * **The odd half of the sign law is NOT here**, and saying so is the point rather than an
   * apology. `Power (0 - x) (SUC (NUM_ADD n n)) = 0 - Power x (SUC (NUM_ADD n n))` is equally
   * true and nobody has asked for it; a reader who finds half a law and cannot tell whether the
   * other half is FALSE or merely ABSENT is the defect this paragraph prevents. [[PowerOfOne]]
   * carries the same kind of note for its own case.
   *
   * The statement is at `NUM_ADD n n` and not at a parity predicate, which is why it has no
   * exception anywhere: an exponent written as a sum with itself is even by construction, so
   * there is no length at which it fails and no side condition to carry. A name with `EVEN` in
   * it was considered and dropped for exactly that reason -- there is no parity predicate in the
   * statement, and `docs/naming.md` asks that a constant be spelled the way the constant is
   * spelled.
   *
   * **What it does NOT rest on, measured rather than assumed.** A five-rewrite route was proposed
   * for it: `POWER_ADD` to split the doubled exponent, [[Multiplicative]] BACKWARDS to collect
   * `(0-x)(0-x)`, a ring step to `x*x`, then the two forwards again. It does not close, and the
   * reason is mechanical: a rewrite rule fires in one direction, and that route needs
   * [[Multiplicative]] in the other. Put to the kernel, the rule set reduces both sides to
   * `Power (0-x) n * Power (0-x) n` and `Power x n * Power x n`, which `Ring` sees as unrelated
   * atoms, and refuses. The plain induction closes in 9581 inferences and wants neither
   * [[PowerOfSum]] nor [[Multiplicative]]: the power's two recurrences and `NUM_ADD`'s three.
   *
   * `NUM_SUC_ADD` is the third of those and is the one that is easy to leave out. Without it the
   * step peels only the RIGHT successor of `NUM_ADD (SUC n) (SUC n)` and stalls at
   * `NUM_ADD (SUC n) n`, where the induction hypothesis cannot match; the refusal names a term
   * that looks like an algebra failure and is a missing arithmetic rule.
   */
  val NegatedDouble: String = "POWER_NEG_DOUBLE"

  /**
   * `|- !f. (!i. 0 <= f i) ==> !n. 0 <= Sum f n`
   *
   * A summand that is never negative gives a sum that is never negative. Stated over a **bare**
   * summand symbol with a pointwise hypothesis, for the reason [[Congruence]] gives at length: a
   * development that quantifies over its summand has no lambda for the rewriter to go into, so the
   * hypothesis is specialised at the index the induction is at instead.
   */
  val NonNegative: String = "SUM_NONNEGATIVE"

  /**
   * `|- !f g. (!i. f i <= g i) ==> !n. Sum f n <= Sum g n`
   *
   * [[Congruence]] with `<=` in place of `=`, and it exists for the same reason and has the same
   * shape: pointwise hypothesis, bare summand symbols, one induction, discharge and generalise. The
   * step's certificate is
   * `(Sum g n - Sum f n) + (g n - f n) = (Sum g n + g n) - (Sum f n + f n)`, two terms, one from the
   * induction hypothesis and one from the pointwise hypothesis.
   */
  val Monotone: String = "SUM_MONOTONE"

  /**
   * `|- !f. (!i. 0 < f i) ==> !n. 0 < Prod f n`
   *
   * The product's answer to [[PowerPositive]], and the same axiom closes its step. It is what makes
   * `Prod` usable as a denominator or under an inverse, which is the first thing a development asks
   * of a product and the thing `Prod f n = 0` would forbid.
   */
  val ProdPositive: String = "PROD_POSITIVE"

  /**
   * `|- !c f n. Prod (\i. c * f i) n = Power c n * Prod f n`
   *
   * The product's analogue of [[Linear]]: a constant factor pulled out of every position comes out
   * as a power, and it is the structural fact that ties the two definitions in this file together.
   * Its step is a rewrite and a ring identity, so it goes through the driver like the equations do.
   */
  val ProdScales: String = "PROD_SCALES"

  /**
   * The equations the sum's own recurrences prove, as the text a person checks them by.
   *
   * The rules the driver is given for these are `SUM_ZERO` and `SUM_SUC` and nothing else, which is
   * why [[ProdScales]] is not in this list: it mentions three constants and wants the recurrences of
   * two more. [[ProductStatements]] is that list, and the split is the rule set rather than any
   * difference in how the two are proved.
   *
   * [[Swapped]] is an equation and is in neither list, for the different reason that its step is
   * not a ring identity: the note there says what closes it instead.
   */
  val Statements: Vector[(String, String)] = Vector(
    (
      Linear,
      "!a:real. !f:num->real. !g:num->real. !n:num. " +
        "Sum (\\i:num. a * f i + g i) n = a * Sum f n + Sum g n"
    ),
    (
      Telescoping,
      "!g:num->real. !n:num. Sum (\\i:num. g (SUC i) - g i) n = g n - g ZERO"
    ),
    (
      ByParts,
      "!a:num->real. !b:num->real. !n:num. " +
        "Sum (\\i:num. a i * (b (SUC i) - b i)) n = " +
        "a n * b n - a ZERO * b ZERO - Sum (\\i:num. b (SUC i) * (a (SUC i) - a i)) n"
    ),
    (
      Shift,
      "!f:num->real. !n:num. Sum (\\i:num. f (SUC i)) n = Sum f (SUC n) - f ZERO"
    ),
    (
      Additive,
      "!f:num->real. !g:num->real. !n:num. Sum (\\i:num. f i + g i) n = Sum f n + Sum g n"
    ),
    (
      OfZero,
      "!n:num. Sum (\\i:num. 0) n = 0"
    ),
    (
      Scaled,
      "!a:real. !f:num->real. !n:num. Sum (\\i:num. a * f i) n = a * Sum f n"
    ),
    (
      ScaledRight,
      "!a:real. !f:num->real. !n:num. Sum (\\i:num. f i * a) n = Sum f n * a"
    )
  )

  /** The equations that want the product's and the power's recurrences as well. */
  val ProductStatements: Vector[(String, String)] = Vector(
    (
      ProdScales,
      "!c:real. !f:num->real. !n:num. Prod (\\i:num. c * f i) n = Power c n * Prod f n"
    )
  )

  /**
   * The equations that want the arithmetic of the naturals as well, which is why this is a third
   * list and not a line in the first.
   *
   * One entry, and the list exists rather than the entry being inlined because what separates it
   * from [[Statements]] is a fact about the *rules*, not about the statement: these are proved with
   * `NUM_ADD`'s two recurrences added to the sum's, and a reader checking which facts a lemma rests
   * on should not have to read the call to find out.
   */
  val ArithmeticStatements: Vector[(String, String)] = Vector(
    (
      Reindex,
      "!f:num->real. !m:num. !n:num. " +
        "Sum (\\i:num. f (NUM_ADD m i)) n = Sum f (NUM_ADD m n) - Sum f m"
    )
  )

  /**
   * The one equation that wants the sum's recurrences together with the EMBEDDING of the naturals.
   *
   * A fifth list, for the reason the third and fourth exist: what separates it is the rule set and
   * not the statement. Every other induction here stays on one side of the bridge; this one has a
   * `num` on the right of an equation between reals, so it needs `real_of_num`'s two recurrences
   * and nothing else new.
   */
  val EmbeddingStatements: Vector[(String, String)] = Vector(
    (
      Constant,
      "!c:real. !n:num. Sum (\\i:num. c) n = real_of_num n * c"
    )
  )

  /**
   * The one law about the BASE, which is a sixth list because its rules are a sixth set.
   *
   * It wants the power's two recurrences and nothing else. Every other list here adds something
   * -- the sum's recurrences, the product's, the arithmetic of `num`, the embedding -- and
   * [[ExponentStatements]] adds the arithmetic because its members mention `NUM_ADD` and
   * `NUM_MUL`. This one mentions neither, and the list says so where a reader looks, which is
   * the whole reason this file splits by rule set rather than by subject.
   */
  val BaseStatements: Vector[(String, String)] = Vector(
    (
      Multiplicative,
      "!a:real. !b:real. !n:num. Power (a * b) n = Power a n * Power b n"
    )
  )

  /**
   * The one law about the SIGN of the base, a seventh list because its rules are a seventh set.
   *
   * The power's two recurrences and `NUM_ADD`'s three, and nothing else. It is not in
   * [[ExponentStatements]] because it needs neither law of exponents and that list would have
   * said it does; it is not in [[BaseStatements]] because that one carries no arithmetic.
   */
  val SignStatements: Vector[(String, String)] = Vector(
    (
      NegatedDouble,
      "!x:real. !n:num. Power (0 - x) (NUM_ADD n n) = Power x (NUM_ADD n n)"
    )
  )

  /** [[Geometric]], whose step carries the hypothesis as an implication. See [[Geometric]]. */
  val GeometricStatement: String =
    "!q:real. !n:num. (q - 1) * Sum (\\i:num. Power q i) n = Power q n - 1"

  /**
   * The two laws of exponents, which want the power's recurrences and the arithmetic and not the
   * sum's recurrences at all.
   *
   * A fourth list rather than a line in a third, for the reason the third exists: what separates
   * these is the set of rules they are proved from. They also differ from every other list in being
   * proved **in order**, since [[PowerOfProduct]]'s step rewrites with [[PowerOfSum]]; the entry
   * order here is therefore load-bearing and not alphabetical.
   */
  val ExponentStatements: Vector[(String, String)] = Vector(
    (
      PowerOfSum,
      "!b:real. !m:num. !n:num. Power b (NUM_ADD m n) = Power b m * Power b n"
    ),
    (
      PowerOfProduct,
      "!b:real. !m:num. !n:num. Power b (NUM_MUL m n) = Power (Power b m) n"
    ),
    // Third and last, and its position here is not load-bearing the way the first two are: it
    // rewrites with neither of them. It is in this list rather than a fifth because the rules it
    // wants are exactly this list's, which is what the comment above says separates them.
    (
      PowerOfOne,
      "!n:num. Power 1 n = 1"
    )
  )

  /**
   * The bridge, in a list of its own because its rules are a third set again.
   *
   * It wants the recurrences of `NUM_POW`, which belong to `Peano`, the embedding of a product
   * and of the successor, which also do, and the power's own recurrences, which belong here. Its
   * step ends with `Power b n * b` against `b * Power b n`, so the driver's RING closes it and
   * no commutativity rule is needed in the rewriting.
   */
  val BridgeStatements: Vector[(String, String)] = Vector(
    (
      EmbedsPower,
      "!m:num. !n:num. real_of_num (NUM_POW m n) = Power (real_of_num m) n"
    )
  )

  /** [[Halves]], which is [[Reindex]] at one instance and is not proved by induction. */
  /** [[CongruenceBelow]], whose induction carries an implication and needs its own driver. */
  val MonotoneBelowStatement: String =
    "!f:num -> real. !g:num -> real. !n:num. " +
      "(!i:num. NUM_LT i n ==> f i <= g i) ==> Sum f n <= Sum g n"

  val CongruenceBelowStatement: String =
    "!f:num -> real. !g:num -> real. !n:num. " +
      "(!i:num. NUM_LT i n ==> f i = g i) ==> Sum f n = Sum g n"

  val HalvesStatement: String =
    "!f:num -> real. !n:num. Sum f (NUM_ADD n n) = Sum f n + Sum (\\i:num. f (NUM_ADD n i)) n"

  /**
   * Define the sum, the power and the product over the arithmetic of the naturals, and derive the
   * facts.
   *
   * The chain runs the naturals first and the reals second, because the tactics are built over a
   * `RealTheory` and `Ring` has to be able to read a goal that mentions `num`.
   *
   * **It takes a `Peano` rather than a `Natural`, and that is the whole of what changed on
   * 2026-09-11.** Until then the two were siblings over the reals, each declaring its own
   * constants, and the consequence was not that a caller had to pick: it was that `NUM_ADD` could
   * not be written **inside** a `Sum`, because the theory `Sum` was defined over had never heard of
   * it. Every reindexing that is not a single successor is that shape, and so is every argument
   * about a word that shifts by more than one place. Building this over that gives the summand the
   * arithmetic, and [[Reindex]] is what it buys.
   *
   * The order facts are built here when a caller has none, and taken when it has: `Chain` builds an
   * `Order` before this line and would otherwise pay for a second one.
   */
  def construct(peano: Peano): Either[LogicError, Series] =
    Order.construct(peano.ring).flatMap(construct(peano, _))

  /** The same, for a caller that has already built the order facts. */
  def construct(peano: Peano, order: Order): Either[LogicError, Series] = {
    val naturals = peano.naturals
    val ring = peano.ring
    val reals = ring.reals
    val base = peano.theory
    val numbers = TyApp(Natural.TypeName, Nil)
    val values = TyApp(Real.TypeName, Nil)
    val summand = Type.fun(numbers, values)

    val f = Term.variable("f", summand)

    // `peano.notation` and not `reals.notation`, which is what this read until 2026-09-12. The two
    // were the same table until `num` got numerals that day, and then they stopped being: a
    // development taking the reals' would read `3` at `real` only, while `Product` and everything
    // above it, which take Peano's, read it at either. Two developments of one chain answering
    // differently about the same text is the kind of difference nobody sees until a consumer
    // moves between them, and `SignatureSpec` reads numerals off `chain.series` while `Ask` reads
    // them off `chain.widest`.
    val notation = peano.notation

    for {
      logic <- naturals.classical.logic.over(base)
      recursion <- naturals.recursion

      // The sum, the power and the product, each by the same construction: what differs between the
      // three is the value at zero, the step, and which variable the constant is abstracted over.
      // The construction is `Recursion.define` and this file held a second copy of it until the
      // night of 2026-09-12; the copy generalised the index before the parameter, which is why
      // `SUM_SUC`, `POWER_SUC` and `PROD_SUC` used to read their arguments in the opposite order
      // from every other lemma about the same three functions. The file that defines the driver
      // carries the measurement.
      summed <- Recursion.define(
        logic,
        naturals,
        base,
        notation,
        recursion,
        SumName,
        values,
        "0:real",
        "\\v:real. \\i:num. v + (f:num->real) i",
        Some(f)
      )
      (extended, definition, atZero, atSuccessor) = summed

      powered <- Recursion.define(
        logic,
        naturals,
        extended,
        notation,
        recursion,
        PowerName,
        values,
        "1:real",
        "\\v:real. \\i:num. (b:real) * v",
        Some(Term.variable("b", values))
      )
      (withPower, _, powerAtZero, powerAtSuccessor) = powered

      multiplied <- Recursion.define(
        logic,
        naturals,
        withPower,
        notation,
        recursion,
        ProdName,
        values,
        "1:real",
        "\\v:real. \\i:num. v * (f:num->real) i",
        Some(f)
      )
      (withProd, _, prodAtZero, prodAtSuccessor) = multiplied

      recurrences <- Rewrite.Rule.all(logic, Vector(atZero, atSuccessor))
      powerRules <- Rewrite.Rule.all(logic, Vector(powerAtZero, powerAtSuccessor))
      prodRules <- Rewrite.Rule.all(logic, Vector(prodAtZero, prodAtSuccessor))

      induction <- naturals.fact(Natural.Induction)
      driver = Induct(logic, ring, induction)
      bounds <- Bounds.of(order, ring, logic)

      congruence <- congruent(logic, naturals.classical, withProd, notation, SumName)
      prodCongruence <- congruent(logic, naturals.classical, withProd, notation, ProdName)

      powerPositive <- positivePower(bounds, driver, withProd, notation, powerRules)
      powerMonotone <- monotonePower(bounds, driver, withProd, notation, powerRules, powerPositive)
      nonNegative <- nonNegativeSum(bounds, driver, withProd, notation, recurrences)
      monotone <- monotoneSum(bounds, driver, withProd, notation, recurrences)
      prodPositive <- positiveProd(bounds, driver, withProd, notation, prodRules)

      derived <- prove(driver, withProd, notation, Statements, recurrences)
      alsoDerived <- prove(driver, withProd, notation, ProductStatements, prodRules ++ powerRules)

      // The two scale lemmas are members of `Statements` and rules of the one fact below, so this
      // comes after that call and builds its rules from what it proved.
      scaleFact <- derived.toMap.get(Scaled).toRight(MissingDefinition(Scaled))
      scaleRightFact <- derived.toMap.get(ScaledRight).toRight(MissingDefinition(ScaledRight))
      scaleRules <- Rewrite.Rule.all(logic, Vector(scaleFact, scaleRightFact))
      productOfSums <- summedProducts(logic, withProd, notation, scaleRules)

      // The power of a product of bases, from the power's recurrences alone. Its own call
      // because its rule set is its own: see `BaseStatements`.
      basewise <- prove(driver, withProd, notation, BaseStatements, powerRules)

      // The geometric sum, which wants the sum's recurrences and the power's together and whose
      // step cannot use the hypothesis as a rewrite rule. Its own helper for that reason.
      geometric <- geometricSum(driver, ring, logic, withProd, notation, recurrences ++ powerRules)

      // The two recurrences of `NUM_ADD`, which are what makes the reindexing induction close. They
      // come from `Peano` rather than from anything here: this development defines the sums and
      // owns no arithmetic on `num` at all.
      addAtZero <- peano.fact(Peano.AddAtZero)
      addAtSuccessor <- peano.fact(Peano.AddAtSuccessor)
      arithmetic <- Rewrite.Rule.all(logic, Vector(addAtZero, addAtSuccessor))
      reindexed <- prove(driver, withProd, notation, ArithmeticStatements, recurrences ++ arithmetic)

      // The sign law, which wants the power's recurrences and `NUM_ADD`'s THREE. `NUM_SUC_ADD` is
      // the third and the one that is easy to leave out: without it the step peels only the right
      // successor of `NUM_ADD (SUC n) (SUC n)` and stalls at `NUM_ADD (SUC n) n`, where the
      // induction hypothesis cannot match, and the refusal reads as an algebra failure.
      successorPlus <- peano.fact(Peano.SuccessorPlus)
      doubling <- Rewrite.Rule.all(logic, Vector(addAtZero, addAtSuccessor, successorPlus))
      signwise <- prove(driver, withProd, notation, SignStatements, powerRules ++ doubling)

      // The laws of exponents, which want the same arithmetic and the power's recurrences instead
      // of the sum's. They are a separate call because they are proved in order rather than from
      // one fixed rule set: see `exponentLaws`.
      mulAtZero <- peano.fact(Peano.MulAtZero)
      mulAtSuccessor <- peano.fact(Peano.MulAtSuccessor)
      products <- Rewrite.Rule.all(logic, Vector(mulAtZero, mulAtSuccessor))
      exponents <- exponentLaws(
        driver,
        logic,
        withProd,
        notation,
        powerRules ++ arithmetic ++ products
      )

      // The bridge from `NUM_POW` to `Power`, which wants the natural power's recurrences and
      // the embedding of a product. Both are `Peano`'s; the target is this file's.
      powAtZero <- peano.fact(Peano.PowAtZero)
      powAtSuccessor <- peano.fact(Peano.PowAtSuccessor)
      embedsProduct <- peano.fact(Peano.EmbedsProduct)
      embedsSuccessor <- peano.fact(Peano.EmbedsSuccessor)
      embedsZero <- peano.fact(Peano.EmbedsZero)
      bridgeRules <- Rewrite.Rule.all(
        logic,
        Vector(powAtZero, powAtSuccessor, embedsProduct, embedsSuccessor, embedsZero))
      bridged <- prove(driver, withProd, notation, BridgeStatements, powerRules ++ bridgeRules)

      // The sum of a constant, which is the sum's own recurrences plus the embedding of zero and
      // of the successor. Neither `recurrences` nor `bridgeRules` alone reaches it: the left side
      // is a sum and the right side crosses the bridge.
      embedding <- Rewrite.Rule.all(logic, Vector(embedsSuccessor, embedsZero))
      counted <- prove(driver, withProd, notation, EmbeddingStatements, recurrences ++ embedding)

      // The middle split. Not an induction and not in any of the lists above, because it is
      // `SUM_REINDEX` at one instance with the subtraction cleared, and what clears it is the
      // linear reader rather than a rewrite.
      reindexByName = reindexed.toMap
      reindexFact <- reindexByName.get(Reindex).toRight(MissingDefinition(Reindex))
      halves <- halvedSum(logic, order, withProd, notation, reindexFact)

      // Congruence on a range, which is the one a consumer reaches for. Its own driver because
      // its induction carries an implication, which no list above does.
      strictTransitive <- peano.fact(Peano.StrictTransitive)
      belowSuccessor <- peano.fact(Peano.BelowSuccessor)
      congruenceBelow <- congruenceOnARange(
        driver, logic, order, withProd, notation, recurrences, atSuccessor,
        strictTransitive, belowSuccessor,
        CongruenceBelowStatement,
        (_, goal) =>
          Term.destEq(goal) match {
            case Some((left, right)) if left == right => Right(Kernel.refl(left))
            case _ => Left(NotOfForm("an empty range on both sides", goal))
          })

      // The same induction at the order, which is the bounded twin `Congruence`'s own note
      // predicted the first real consumer of one of the four would want. It is the Cauchy
      // product, which compares two summands only below the bound.
      monotoneBelow <- congruenceOnARange(
        driver, logic, order, withProd, notation, recurrences, atSuccessor,
        strictTransitive, belowSuccessor,
        MonotoneBelowStatement,
        (linarith, goal) => linarith.prove(goal))

      // The swap wants two of the facts just proved: `SUM_ADD` to close its step by hand, and
      // `SUM_OF_ZERO` as a rewrite rule, since its base leaves an inner sum of zeroes behind.
      byName = derived.toMap
      additive <- byName.get(Additive).toRight(MissingDefinition(Additive))
      ofZero <- byName.get(OfZero).toRight(MissingDefinition(OfZero))
      ofZeroRule <- Rewrite.Rule.of(logic, ofZero)
      swapped <- swappedSums(driver, withProd, notation, recurrences :+ ofZeroRule, additive)

      // The diagonal, which wants the bounded congruence just proved, `SUM_ADD` by hand as the
      // swap does, and the two facts about `NUM_SUB` that landed in `Peano` for it. The
      // unconditional one is a rewrite rule and the conditional one cannot be, which is why both
      // are here.
      subSelf <- peano.fact(Peano.SubSelf)
      stepMinusSelf <- peano.fact(Peano.SuccessorMinusSelf)
      stepMinus <- peano.fact(Peano.SuccessorMinus)
      atMostFromBelow <- peano.fact(Peano.AtMostFromBelow)
      differences <- Rewrite.Rule.all(logic, Vector(subSelf, stepMinusSelf))
      // The binomial theorem, which is the one fact here whose statement names a constant of
      // `Peano` rather than of this development, and the reason it waited.
      shiftFact <- byName.get(Shift).toRight(MissingDefinition(Shift))
      binomialLinarith <- Linarith.construct(order)
      binomial <- binomialTheorem(
        driver,
        logic,
        binomialLinarith,
        withProd,
        notation,
        Map(
          Congruence -> congruence,
          CongruenceBelow -> congruenceBelow,
          Additive -> additive,
          ScaledRight -> scaleRightFact,
          AtZero -> atZero,
          AtSuccessor -> atSuccessor,
          Shift -> shiftFact,
          PowerAtZero -> powerAtZero,
          PowerAtSuccessor -> powerAtSuccessor
        ),
        peano
      )

      diagonal <- summedDiagonal(
        driver, withProd, notation, recurrences ++ differences, additive, congruenceBelow,
        stepMinus, atMostFromBelow, atSuccessor)

      // The Cauchy product's partial sum and the gap to the product of the two partial sums,
      // which are the diagonal and `SUM_ADD` pointed at a product of two sequences.
      cauchyPair <- cauchyProduct(
        logic, ring, binomialLinarith, withProd, notation, diagonal, congruence, additive,
        scaleFact, scaleRightFact)
      (cauchyPartial, cauchyGap) = cauchyPair
    } yield new Series(
      ring,
      logic,
      withProd,
      notation,
      definition,
      (Vector(
        AtZero -> atZero,
        AtSuccessor -> atSuccessor,
        PowerAtZero -> powerAtZero,
        PowerAtSuccessor -> powerAtSuccessor,
        ProdAtZero -> prodAtZero,
        ProdAtSuccessor -> prodAtSuccessor,
        Congruence -> congruence,
        ProdCongruence -> prodCongruence,
        PowerPositive -> powerPositive,
        PowerMonotone -> powerMonotone,
        NonNegative -> nonNegative,
        Monotone -> monotone,
        ProdPositive -> prodPositive,
        Swapped -> swapped,
        Product -> productOfSums,
        Diagonal -> diagonal,
        Binomial -> binomial,
        Cauchy -> cauchyPartial,
        CauchyGap -> cauchyGap,
        Halves -> halves,
        CongruenceBelow -> congruenceBelow,
        MonotoneBelow -> monotoneBelow,
        Geometric -> geometric
      ) ++ derived ++ alsoDerived ++ basewise ++ signwise ++ reindexed ++ exponents ++ bridged ++
        counted).toMap
    )
  }

  /**
   * [[CongruenceBelow]] by induction on the bound, with the implication carried through.
   *
   * The base is `Sum f ZERO = Sum g ZERO`, which is `SUM_ZERO` twice and does not use the
   * hypothesis at all; it is discharged from a proof that did not assume it, which is `disch`'s
   * behaviour and the honest reading of an empty range.
   *
   * The step is the whole of it, and it is the reason this cannot be one of the lists above:
   * the induction hypothesis is itself an implication, so the step has to take it apart rather
   * than use it as a rewrite rule. Assume the agreement below `SUC v`. Every index below `v` is
   * below `SUC v` -- `NUM_LT_TRANS` with `NUM_LT_SUC`, and the first of those was missing until
   * this was written -- so the agreement below `v` follows, the induction hypothesis applies,
   * and the two sums are equal at `v`. The agreement AT `v` is the same assumption used once
   * more, at the index the successor added. `SUM_SUC` on both sides then leaves an equation
   * linear in four atoms and the linear reader closes it.
   */
  private def congruenceOnARange(
    driver: Induct,
    logic: Logic,
    bounds: Order,
    theory: Theory,
    notation: Notation,
    recurrences: Vector[Rewrite.Rule],
    atSuccessor: Kernel.Thm,
    strictTransitive: Kernel.Thm,
    belowSuccessor: Kernel.Thm,
    claim: String,
    settle: (Linarith, Term) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    /** The head of `NUM_LT a b`, read off a statement that uses it rather than rebuilt. */
    def strictlyBelow(sample: Term): Either[LogicError, Term] = sample match {
      case App(App(head, _), _) => Right(head)
      case other                => Left(NotOfForm("an order statement", other))
    }

    for {
      linarith <- Linarith.construct(bounds)
      statement <- Parser.proposition(theory, notation, claim)
      stripped <- Logic.stripForall(statement)
      (outer, inner) = stripped
      summands = outer.take(2).toList
      left <- outer.lift(0).toRight(NotOfForm("two summands", inner))
      right <- outer.lift(1).toRight(NotOfForm("two summands", inner))
      bound <- outer.lift(2).toRight(NotOfForm("a bound to induct on", inner))
      // `stripForall` takes ALL of them, and the driver wants a claim about every number, so
      // the bound goes back on. The two summands stay free and are generalised at the end.
      overEveryBound <- logic.mkForall(bound, inner)

      proved <- driver.proveBy(
        overEveryBound,
        goal =>
          for {
            parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
            opened <- Rewrite.rewrite(recurrences, parts._2)
            sides <- Term.destEq(opened.conclusion).toRight(NotOfForm("an equation", parts._2))
            closed <- settle(linarith, sides._2)
            backwards <- Conv.sym(opened)
            base <- LogicError.lift(Kernel.eqMp(backwards, closed))
            result <- rules.disch(parts._1, base)
          } yield result,
        step =>
          for {
            goalParts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
            (agreesBelowSuccessor, equalSums) = goalParts
            assumed <- LogicError.lift(Kernel.assume(agreesBelowSuccessor))

            // `v < SUC v`, which is what lifts an index from below v to below its successor
            atTheVariable <- rules.spec(step.variable, belowSuccessor)

            // rebuild `u < v` for a fresh u, with the order constant taken from the statement
            openedPremise <- Logic.stripForall(agreesBelowSuccessor)
            innerParts <- logic
              .destImp(openedPremise._2)
              .toRight(NotOfForm("a bounded agreement", openedPremise._2))
            below <- strictlyBelow(innerParts._1)
            index <- openedPremise._1.lift(0).toRight(NotOfForm("one index", openedPremise._2))
            smallerTerm <- LogicError.lift(Term.app(below, index).flatMap(Term.app(_, step.variable)))
            smaller <- LogicError.lift(Kernel.assume(smallerTerm))

            // u < v and v < SUC v give u < SUC v, and the assumption then gives f u = g u
            // `NUM_LT_TRANS` at (u, v, SUC v). The successor is read off `v < SUC v` rather
            // than built, for the reason the same choice was made in `NUM_LT_TRANS` itself.
            successor <- atTheVariable.conclusion match {
              case App(App(_, _), above) => Right(above)
              case other                 => Left(NotOfForm("an order statement", other))
            }
            liftedAt <- rules
              .spec(index, strictTransitive)
              .flatMap(rules.spec(step.variable, _))
              .flatMap(rules.spec(successor, _))
            chained <- rules.conjIntro(smaller, atTheVariable).flatMap(rules.mp(liftedAt, _))
            agreementAt <- rules.spec(index, assumed).flatMap(rules.mp(_, chained))
            agreesBelow <- rules.disch(smallerTerm, agreementAt).flatMap(rules.gen(index, _))

            // the induction hypothesis applies, and the top index is the assumption once more
            sumsBelow <- rules.mp(step.hypothesis, agreesBelow)
            top <- rules.spec(step.variable, assumed).flatMap(rules.mp(_, atTheVariable))

            // SUM_SUC on both sides, and what is left is linear. Summand first and index second,
            // which is the order `SUM_SUC` has quantified in since the night of 2026-09-12; this
            // is the one place in the repository that specialises it positionally rather than
            // matching it as a rewrite rule, and so the one place the change was visible.
            unfoldLeft <- rules.spec(left, atSuccessor).flatMap(rules.spec(step.variable, _))
            unfoldRight <- rules.spec(right, atSuccessor).flatMap(rules.spec(step.variable, _))
            facts <- rules
              .conjIntro(sumsBelow, top)
              .flatMap(rules.conjIntro(_, unfoldLeft))
              .flatMap(rules.conjIntro(_, unfoldRight))
            implication <- logic.mkImp(facts.conclusion, equalSums)
            decided <- linarith.prove(implication)
            settled <- rules.mp(decided, facts)
            result <- rules.disch(agreesBelowSuccessor, settled)
          } yield result
      )
      general <- rules.genAll(proved, summands)
    } yield general
  }

  /**
   * [[Geometric]] by the ordinary induction, with ONE extra rewrite rule that is not a recurrence.
   *
   * The step is the whole reason this is a function rather than a line in a list. `SUM_SUC` and
   * `POWER_SUC` rewrite the step goal to
   *
   * {{{
   *   (q - 1) * (Sum f n + Power q n) = q * Power q n - 1
   * }}}
   *
   * and the induction hypothesis is `(q - 1) * Sum f n = Power q n - 1`, whose left side is NOT a
   * subterm of that: the scalar multiplies the whole of the extended sum. The default step uses
   * the hypothesis as a rewrite rule, so it has nothing to fire and leaves `Ring` a goal in which
   * `Sum f n` is an unrelated atom.
   *
   * What is added is distributivity, `a * (b + c) = a * b + a * c`, as a RULE. It is a ring
   * identity and `Ring` could decide it in one line if it were the goal; it is here because what
   * is wanted from it is not a decision but a SHAPE -- it is what turns the scalar outside the
   * sum into a scalar on each summand, and so what puts the hypothesis's left side where the
   * rewriter can see it. That is a structural need and not an arithmetic one, which is why a
   * decision procedure cannot supply it.
   *
   * Two alternatives were rejected. Carrying the hypothesis as an implication and closing it with
   * `Ring` does not work at all: `Ring.prove` reads an equation and refuses an implication. And
   * stating the lemma at the summand `(q - 1) * Power q i`, where the hypothesis IS a subterm and
   * the default step closes it unaided, gives a weighted sum that no reader recognises as the
   * geometric sum, and leaves every consumer to pull the scalar back out through [[Linear]] with
   * a zero second summand and [[Congruence]] to match it -- which is the work this lemma exists
   * to spare them.
   */
  private def geometricSum(
    driver: Induct,
    ring: Ring,
    logic: Logic,
    theory: Theory,
    notation: Notation,
    rules: Vector[Rewrite.Rule]
  ): Either[LogicError, Kernel.Thm] =
    for {
      spread <- Parser.proposition(
        theory, notation, "!a:real. !b:real. !c:real. a * (b + c) = a * b + a * c")
      distributes <- ring.prove(spread)
      rule <- Rewrite.Rule.of(logic, distributes)
      statement <- Parser.proposition(theory, notation, GeometricStatement)
      proved <- driver.proveWith(statement, rules :+ rule)
    } yield proved

  /**
   * [[Halves]] from [[Reindex]]: instantiate both range arguments to the same `n` and clear
   * the subtraction.
   *
   * The clearing is the only step and it is linear in three sums, so it goes to the linear
   * reader rather than to a rewrite: `a = b - c` and the goal `b = c + a` are the same fact
   * about three atoms, and no rule set rearranges a subtraction without one being written for
   * it.
   */
  private def halvedSum(
    logic: Logic,
    bounds: Order,
    theory: Theory,
    notation: Notation,
    reindex: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val numbers = TyApp(Natural.TypeName, Nil)
    val f = Term.variable("f", Type.fun(numbers, TyApp(Real.TypeName, Nil)))
    val n = Term.variable("n", numbers)
    for {
      linarith <- Linarith.construct(bounds)
      statement <- Parser.proposition(theory, notation, HalvesStatement)
      stripped <- Logic.stripForall(statement)
      (variables, body) = stripped
      summand <- variables.lift(0).toRight(NotOfForm("a summand and a range", body))
      range <- variables.lift(1).toRight(NotOfForm("a summand and a range", body))
      instance <- logic.rules.specAll(reindex, List(summand, range, range))
      implication <- logic.mkImp(instance.conclusion, body)
      decided <- linarith.prove(implication)
      inner <- logic.rules.mp(decided, instance)
      result <- logic.rules.genAll(inner, variables.toList)
    } yield result
  }

  /** A list of statements read and proved by the driver from one set of rules. */
  private def prove(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    statements: Vector[(String, String)],
    rules: Vector[Rewrite.Rule]
  ): Either[LogicError, Vector[(String, Kernel.Thm)]] =
    statements.foldLeft[Either[LogicError, Vector[(String, Kernel.Thm)]]](Right(Vector.empty)) {
      (acc, entry) =>
        val (name, text) = entry
        for {
          done <- acc
          statement <- Parser.proposition(theory, notation, text)
          proved <- driver.proveWith(statement, rules)
        } yield done :+ (name -> proved)
    }

  /**
   * The laws of exponents, proved in the order [[ExponentStatements]] gives them, each one added to
   * the rules the next is proved from.
   *
   * Separate from [[prove]] because these two are not independent: [[PowerOfProduct]]'s inductive
   * step rewrites `NUM_MUL m (SUC n)` into a sum of exponents and is then stuck without
   * [[PowerOfSum]]. Everything else in this file is proved from a rule set fixed before its list is
   * walked, and threading the results through that helper would have made the order of every other
   * list matter without anyone noticing.
   */
  private def exponentLaws(
    driver: Induct,
    logic: Logic,
    theory: Theory,
    notation: Notation,
    rules: Vector[Rewrite.Rule]
  ): Either[LogicError, Vector[(String, Kernel.Thm)]] = {
    type Progress = (Vector[(String, Kernel.Thm)], Vector[Rewrite.Rule])

    ExponentStatements
      .foldLeft[Either[LogicError, Progress]](Right((Vector.empty, rules))) { (acc, entry) =>
        val (name, text) = entry
        for {
          progress <- acc
          (done, available) = progress
          statement <- Parser.proposition(theory, notation, text)
          proved <- driver.proveWith(statement, available)
          rule <- Rewrite.Rule.of(logic, proved)
        } yield (done :+ (name -> proved), available :+ rule)
      }
      .map { case (done, _) => done }
  }

  /**
   * `|- !f g. (!i. f i = g i) ==> !n. Op f n = Op g n`, through extensionality rather than induction.
   *
   * == What this lemma is for, and what it stopped being ==
   *
   * It exists because a pointwise hypothesis cannot be pushed under a binder without it, and the
   * comment on [[Congruence]] predicted that every future binding operator would want one of its
   * own. **That prediction held exactly once**, for `Prod`, and it was the last time: `ETA` was
   * asserted on 2026-09-10 and `docs/adr/0009` names this rewrite as the debt of that decision.
   *
   * Three steps now instead of an induction. The pointwise equation gives `f = g` by
   * `Classical.ext`; the operator is applied to both sides; the result is applied to an index and
   * generalised. Nothing about the operator is used, which is why `name` is still a parameter and
   * why there is nothing left for a third operator to want.
   *
   * **The two lemmas stay.** A caller holding a pointwise hypothesis should not have to know which
   * of the two roads is cheaper, and they are exported as before. What changed is that they are a
   * convenience rather than a necessity, and the axiom they reach says so: through the induction
   * they reached choice and infinity, and through extensionality they reach `ETA`. `SeriesSpec`
   * asserts that, which is what ties an axiom to the lemma that pays for it.
   *
   * The widened logic is not a detail. Detaching eta means specialising it at the function type
   * `num -> real`, and `Classical.standard` has never heard of either; `Classical.ext(wider, …)`
   * exists for exactly this and `Divisibility` documents the same widening one door along.
   */
  private def congruent(
    logic: Logic,
    classical: Classical,
    theory: Theory,
    notation: Notation,
    name: String
  ): Either[LogicError, Kernel.Thm] = {
    val numbers = TyApp(Natural.TypeName, Nil)
    val values = TyApp(Real.TypeName, Nil)
    val summand = Type.fun(numbers, values)
    val f = Term.variable("f", summand)
    val g = Term.variable("g", summand)
    val index = Term.variable("n", numbers)

    for {
      pointwise <- Parser.proposition(theory, notation, "!i:num. (f:num->real) i = (g:num->real) i")
      assumed <- LogicError.lift(Kernel.assume(pointwise))
      functions <- classical.ext(logic, assumed)

      operator <- LogicError.lift(theory.constant(name, Type.fun(summand, Type.fun(numbers, values))))
      applied <- Conv.apTerm(operator, functions)
      atIndex <- Conv.apThm(applied, index)

      general <- logic.rules.gen(index, atIndex)
      discharged <- logic.rules.disch(pointwise, general)
      result <- logic.rules.genAll(discharged, List(f, g))
    } yield result
  }

  /**
   * `|- !f m n. Sum (\i. Sum (\j. f i j) m) n = Sum (\j. Sum (\i. f i j) n) m`, the lemma
   * [[Swapped]] names.
   *
   * The induction runs on the **outer** length, which is the last quantifier and so the one the
   * driver takes; the inner length rides along as a parameter and is never taken apart. That is why
   * no arithmetic on `num` is wanted: nothing here ever adds two indices.
   *
   * The base is the driver's own, since it is an equation `Ring` can close once the rules have
   * turned both sides into zero, and turning the right side into zero is what [[OfZero]] is in the
   * rule set for.
   *
   * The step is hand-written for the one reason [[Swapped]] gives at length: what closes it is
   * [[Additive]] at a particular pair of summands, and a rule cannot be *matched* into that
   * position without higher-order matching. So the two summands are read off the goal the rewriting
   * produced, the lemma is instantiated at them, and its instance is beta normalised and turned
   * round. The equality check before the last step is not a formality: it is what would catch the
   * rewriting having left the goal in a shape the instance does not answer, which is the way this
   * proof can go wrong silently.
   */
  /**
   * `|- !x y n. Power (x + y) n =
   * Sum (\i. real_of_num (NUM_CHOOSE n i) * (Power x i * Power y (n - i))) (SUC n)`
   *
   * The binomial theorem, and the last thing between this repository and
   * `exp (x + y) = exp x * exp y` on the combinatorial side. What it waited on was the
   * coefficient: `NUM_CHOOSE` did not exist anywhere until 2026-09-20.
   *
   * == The step, in the order it is built ==
   *
   * [[Shift]] peels the **bottom** entry off the wide sum, and which end is not a preference. At
   * the top the coefficient has already run past the diagonal, so the two sides no longer have
   * the same number of terms; at the bottom nothing has moved. What is left, `\i. G (SUC i)`,
   * splits by Pascal's rule into a column carrying an extra `x` and one carrying an extra `y`,
   * and [[ScaledRight]] reads both back as the narrow sum times a factor.
   *
   * **Three of the four congruences are unconditional and the fourth is not**, and the fourth is
   * where the work is. `NUM_SUB (SUC n) (SUC i) = NUM_SUB n i` holds at every `i`, so Pascal's
   * split, the `x` column and the identification of the `y` column with a shifted sum all go
   * through [[Congruence]]. What does **not** hold at every `i` is `SUC (n - i) = SUC n - i`,
   * false above the diagonal and `Peano.NUM_SUC_SUB` under `i <= n`. That one needs
   * [[CongruenceBelow]], and `Peano.NUM_LE_OF_LT_SUC` to turn the bound the congruence hands
   * over, `i < SUC n`, into the bound the arithmetic asks for.
   *
   * `Peano.NUM_CHOOSE_ABOVE` is spent exactly once, on the entry the shift leaves at the top:
   * `NUM_CHOOSE n (SUC n)` is zero, so the `y` column may be summed to `SUC n` rather than to `n`
   * and the two sums have one length. Without it the assembly is short one term and no
   * rearrangement recovers it.
   *
   * == The assembly is linear, and the hypothesis is spent before it ==
   *
   * Nine equations between sums go to `Linarith` at once, over real **variables**, and what closes
   * it is that every product in sight is a sum against `x` or against `y`. The induction
   * hypothesis is folded in **before** that call rather than passed to it: `Power (x + y) n` and
   * `Sum g (SUC n)` are two atoms to a linear solver, so `l = (x + y) * p` with `p = s` beside it
   * does not give `l = (x + y) * s`. Substituting one for the other is a rewrite and not an
   * inference, and doing it late is the version of this proof that does not close.
   */
  private def binomialTheorem(
    driver: Induct,
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    series: Map[String, Kernel.Thm],
    peano: Peano
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val reals = TyApp(Real.TypeName, Nil)
    val x = Term.variable("x", reals)
    val y = Term.variable("y", reals)
    val n = Term.variable("n", numbers)

    val narrow = "\\i:num. real_of_num (NUM_CHOOSE (n:num) i) * " +
      "(Power (x:real) i * Power (y:real) (NUM_SUB (n:num) i))"
    val wide = "\\i:num. real_of_num (NUM_CHOOSE (SUC (n:num)) i) * " +
      "(Power (x:real) i * Power (y:real) (NUM_SUB (SUC (n:num)) i))"
    val wideStepped = "\\i:num. real_of_num (NUM_CHOOSE (SUC (n:num)) (SUC i)) * " +
      "(Power (x:real) (SUC i) * Power (y:real) (NUM_SUB (SUC (n:num)) (SUC i)))"
    val xColumn = "\\i:num. real_of_num (NUM_CHOOSE (n:num) i) * " +
      "(Power (x:real) (SUC i) * Power (y:real) (NUM_SUB (n:num) i))"
    val yColumn = "\\i:num. real_of_num (NUM_CHOOSE (n:num) (SUC i)) * " +
      "(Power (x:real) (SUC i) * Power (y:real) (NUM_SUB (n:num) i))"
    val bothColumns = "\\i:num. real_of_num (NUM_CHOOSE (n:num) i) * " +
      "(Power (x:real) (SUC i) * Power (y:real) (NUM_SUB (n:num) i)) + " +
      "real_of_num (NUM_CHOOSE (n:num) (SUC i)) * " +
      "(Power (x:real) (SUC i) * Power (y:real) (NUM_SUB (n:num) i))"
    val wideNarrow = "\\i:num. real_of_num (NUM_CHOOSE (n:num) i) * " +
      "(Power (x:real) i * Power (y:real) (NUM_SUB (SUC (n:num)) i))"
    val wideStepNarrow = "\\i:num. real_of_num (NUM_CHOOSE (n:num) (SUC i)) * " +
      "(Power (x:real) (SUC i) * Power (y:real) (NUM_SUB (SUC (n:num)) (SUC i)))"
    val againstX = "\\i:num. (real_of_num (NUM_CHOOSE (n:num) i) * " +
      "(Power (x:real) i * Power (y:real) (NUM_SUB (n:num) i))) * (x:real)"
    val againstY = "\\i:num. (real_of_num (NUM_CHOOSE (n:num) i) * " +
      "(Power (x:real) i * Power (y:real) (NUM_SUB (n:num) i))) * (y:real)"

    def fact(name: String): Either[LogicError, Kernel.Thm] =
      series.get(name).map(Right(_)).getOrElse(peano.fact(name))

    def normalised(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    /** The last argument of an application, which is how a peeled entry is read off a shift. */
    def lastArgument(term: Term): Either[LogicError, Term] = term match {
      case App(_, argument) => Right(argument)
      case other            => Left(NotOfForm("an application", other))
    }

    /** The function of an application, which is how a scaling is read off a product. */
    def partialOf(term: Term): Either[LogicError, Term] = term match {
      case App(partial, _) => Right(partial)
      case other           => Left(NotOfForm("an application", other))
    }

    /**
     * The two summands under the power on the left of a goal.
     *
     * `Induct.proveBy` freshens the quantified variables, so the two reals this derivation is
     * about are read off the goal the driver opened rather than taken from the names written
     * above: a term built here from `x` and `y` would be a term about two other variables.
     */
    def baseOf(goal: Term): Either[LogicError, (Term, Term)] =
      Term.destEq(goal).map(_._1) match {
        case Some(App(App(_, App(App(_, left), right)), _)) => Right((left, right))
        case _ => Left(NotOfForm("a power of a sum", goal))
      }

    def rightOfEquation(theorem: Kernel.Thm): Either[LogicError, Term] =
      Term
        .destEq(theorem.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", theorem.conclusion))

    /**
     * Two summands equal at every index, so the two sums are equal at every length.
     *
     * The obligation is opened here and closed by the caller: what each use needs is a different
     * rule set and nothing else about them differs.
     */
    def sameSummand(
      left: Term,
      right: Term,
      length: Term,
      close: Term => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        congruence <- fact(Congruence)
        instance <- rules.specAll(congruence, List(left, right)).flatMap(normalised)
        obligation <- logic
          .destImp(instance.conclusion)
          .map(_._1)
          .toRight(NotOfForm("an implication", instance.conclusion))
        stripped <- Logic.stripForall(obligation)
        index <- stripped._1.headOption
          .toRight(NotOfForm("a claim about every index", obligation))
        proved <- close(stripped._2).flatMap(rules.gen(index, _))
        everywhere <- rules.mp(instance, proved)
        here <- rules.spec(length, everywhere)
      } yield here

    /** The same where the two agree only below the bound, which is one of the four. */
    def sameSummandBelow(
      left: Term,
      right: Term,
      length: Term,
      close: (Term, FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        congruence <- fact(CongruenceBelow)
        instance <- rules.specAll(congruence, List(left, right, length)).flatMap(normalised)
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

    for {
      additive <- fact(Additive)
      scaledRight <- fact(ScaledRight)
      atZero <- fact(AtZero)
      atSuccessor <- fact(AtSuccessor)
      shift <- fact(Shift)
      powerAtZero <- fact(PowerAtZero)
      powerAtSuccessor <- fact(PowerAtSuccessor)

      pascal <- fact(Peano.ChoosePascal)
      chooseNone <- fact(Peano.ChooseNone)
      chooseAbove <- fact(Peano.ChooseAbove)
      subSuccessors <- fact(Peano.SubSuccessors)
      subAtZero <- fact(Peano.SubAtZero)
      successorMinus <- fact(Peano.SuccessorMinus)
      atMostBelow <- fact(Peano.AtMostBelowSuccessor)
      belowSuccessor <- fact(Peano.BelowSuccessor)
      embedsSum <- fact(Peano.EmbedsSum)
      embedsZero <- fact(Peano.EmbedsZero)
      embedsSuccessor <- fact(Peano.EmbedsSuccessor)

      embedding <- Rewrite.Rule.all(logic, Vector(embedsSum, embedsZero, embedsSuccessor))
      powers <- Rewrite.Rule.all(logic, Vector(powerAtZero, powerAtSuccessor))
      pascalRules <- Rewrite.Rule.all(logic, Vector(pascal, subSuccessors))
      sums <- Rewrite.Rule.all(logic, Vector(atZero, atSuccessor))
      edges <- Rewrite.Rule.all(logic, Vector(chooseNone, subAtZero))
      stepDown <- Rewrite.Rule.all(logic, Vector(subSuccessors))

      narrowBody <- Parser.term(theory, notation, narrow)
      wideBody <- Parser.term(theory, notation, wide)
      wideSteppedBody <- Parser.term(theory, notation, wideStepped)
      xBody <- Parser.term(theory, notation, xColumn)
      yBody <- Parser.term(theory, notation, yColumn)
      bothBody <- Parser.term(theory, notation, bothColumns)
      wideNarrowBody <- Parser.term(theory, notation, wideNarrow)
      wideStepNarrowBody <- Parser.term(theory, notation, wideStepNarrow)
      againstXBody <- Parser.term(theory, notation, againstX)
      againstYBody <- Parser.term(theory, notation, againstY)
      successorOfN <- Parser.term(theory, notation, "SUC (n:num)", numbers)

      /* ------------------------------------------------------------------ base */

      baseGoal <- Parser.proposition(
        theory,
        notation,
        "Power ((x:real) + (y:real)) ZERO = " +
          "Sum (\\i:num. real_of_num (NUM_CHOOSE ZERO i) * " +
          "(Power (x:real) i * Power (y:real) (NUM_SUB ZERO i))) (SUC ZERO)"
      )
      baseLemma <- driver
        .settle(sums ++ powers ++ edges ++ embedding)(baseGoal, Vector.empty)
        .flatMap(rules.genAll(_, List(x, y)))

      /* ------------------------------------------------------------------ step */

      premise <- Parser.proposition(
        theory,
        notation,
        "Power ((x:real) + (y:real)) (n:num) = Sum (" + narrow + ") (SUC (n:num))"
      )
      assumed <- LogicError.lift(Kernel.assume(premise))

      // 1. The bottom entry peeled off the wide sum.
      wideShift <- rules.specAll(shift, List(wideBody, successorOfN)).flatMap(normalised)
      wideZero <- rightOfEquation(wideShift).flatMap(lastArgument)

      // 2. Pascal's rule splits what is left, at every index and under no bound.
      pascalSplit <- sameSummand(
        wideSteppedBody,
        bothBody,
        successorOfN,
        goal => driver.settle(pascalRules ++ embedding)(goal, Vector.empty)
      )
      addSplit <- rules
        .specAll(additive, List(xBody, yBody, successorOfN))
        .flatMap(normalised)
      leftAndRight <- Conv.trans(pascalSplit, addSplit)

      // 3. The x column, where the extra factor comes out of the power at every index.
      xSame <- sameSummand(
        xBody,
        againstXBody,
        successorOfN,
        goal => driver.settle(powers)(goal, Vector.empty)
      )
      xScaled <- rules
        .specAll(scaledRight, List(x, narrowBody, successorOfN))
        .flatMap(normalised)
      xIsScaled <- Conv.trans(xSame, xScaled)

      // 4. The y column, which is the one congruence that carries a bound: `SUC (n - i)` is
      // `SUC n - i` only where `i` has not passed the diagonal.
      ySame <- sameSummandBelow(
        wideNarrowBody,
        againstYBody,
        successorOfN,
        (goal, index, bound) =>
          for {
            atMost <- rules.specAll(atMostBelow, List(n, index)).flatMap(rules.mp(_, bound))
            stepped <- rules.specAll(successorMinus, List(n, index)).flatMap(rules.mp(_, atMost))
            rule <- Rewrite.Rule.of(logic, stepped)
            proved <- driver.settle(powers)(goal, Vector(rule))
          } yield proved
      )
      yScaled <- rules
        .specAll(scaledRight, List(y, narrowBody, successorOfN))
        .flatMap(normalised)
      yIsScaled <- Conv.trans(ySame, yScaled)

      // 5. And the y column IS the second of Pascal's two, shifted: the bottom entry of the one
      // is what the other has at every index one along.
      yShift <- rules.specAll(shift, List(wideNarrowBody, n)).flatMap(normalised)
      yZero <- rightOfEquation(yShift).flatMap(lastArgument)
      narrowSame <- sameSummand(
        wideStepNarrowBody,
        yBody,
        n,
        goal => driver.settle(stepDown)(goal, Vector.empty)
      )
      shortIsShifted <- Conv.sym(narrowSame).flatMap(Conv.trans(_, yShift))

      // 6. The entry the shift leaves at the top of the y column, which is zero above the
      // diagonal and is the one place `NUM_CHOOSE_ABOVE` is spent.
      ySuc <- rules.specAll(atSuccessor, List(yBody, n)).flatMap(normalised)
      topEntry <- rightOfEquation(ySuc).flatMap(lastArgument)
      aboveDiagonal <- rules
        .spec(n, belowSuccessor)
        .flatMap(below =>
          rules.specAll(chooseAbove, List(n, successorOfN)).flatMap(rules.mp(_, below)))
      aboveRule <- Rewrite.Rule.of(logic, aboveDiagonal)
      zero <- Parser.term(theory, notation, "(0:real)", reals)
      topGoal <- LogicError.lift(Term.eq(topEntry, zero))
      topIsZero <- driver.settle(Vector(aboveRule) ++ embedding)(topGoal, Vector.empty)

      // 7. The two bottom entries are one number, because both coefficients are one.
      bottomGoal <- LogicError.lift(Term.eq(wideZero, yZero))
      bottomsAgree <- driver.settle(edges ++ embedding)(bottomGoal, Vector.empty)

      // 8. The hypothesis spent on the left-hand side, BEFORE anything linear is asked. A
      // congruence and not a rewrite: `Rewrite.Rule.of` would make the hypothesis's own `n`
      // schematic and the rule would then fire on `Power (x + y) (SUC n)` as well.
      sumOfBoth <- Parser.term(theory, notation, "(x:real) + (y:real)", reals)
      openedPower <- rules.specAll(powerAtSuccessor, List(sumOfBoth, n))
      scaling <- rightOfEquation(openedPower).flatMap(partialOf)
      folded <- Conv.apTerm(scaling, assumed).flatMap(Conv.trans(openedPower, _))

      // 9. Nine equations between sums, over real variables, and the products are all a sum
      // against `x` or against `y`.
      wideSum <- Parser.term(theory, notation, "Sum (" + wide + ") (SUC (SUC (n:num)))", reals)
      steppedSum <- Parser.term(
        theory, notation, "Sum (" + wideStepped + ") (SUC (n:num))", reals)
      xSum <- Parser.term(theory, notation, "Sum (" + xColumn + ") (SUC (n:num))", reals)
      ySum <- Parser.term(theory, notation, "Sum (" + yColumn + ") (SUC (n:num))", reals)
      yShortSum <- Parser.term(theory, notation, "Sum (" + yColumn + ") (n:num)", reals)
      wideNarrowSum <- Parser.term(
        theory, notation, "Sum (" + wideNarrow + ") (SUC (n:num))", reals)
      narrowSum <- Parser.term(theory, notation, "Sum (" + narrow + ") (SUC (n:num))", reals)
      lifted <- Parser.term(
        theory, notation, "Power ((x:real) + (y:real)) (SUC (n:num))", reals)

      assembled <- linarith
        .prove(
          "!l:real. !t:real. !g:real. !h:real. !a:real. !b:real. !c:real. !d:real. " +
            "!v:real. !w:real. !s:real. !p:real. !q:real. " +
            "h = t - g ==> h = a + b ==> a = s * p ==> b = c + d ==> c = w - v ==> " +
            "w = s * q ==> d = 0 ==> g = v ==> l = (p + q) * s ==> l = t"
        )
        .flatMap(rules.specAll(
          _,
          List(
            lifted, wideSum, wideZero, steppedSum, xSum, ySum, yShortSum, topEntry,
            yZero, wideNarrowSum, narrowSum, x, y)))
        .flatMap(rules.mp(_, wideShift))
        .flatMap(rules.mp(_, leftAndRight))
        .flatMap(rules.mp(_, xIsScaled))
        .flatMap(rules.mp(_, ySuc))
        .flatMap(rules.mp(_, shortIsShifted))
        .flatMap(rules.mp(_, yIsScaled))
        .flatMap(rules.mp(_, topIsZero))
        .flatMap(rules.mp(_, bottomsAgree))
        .flatMap(rules.mp(_, folded))

      stepLemma <- rules.disch(premise, assembled).flatMap(rules.genAll(_, List(x, y, n)))

      /* ------------------------------------------------------- the induction itself */

      statement <- Parser.proposition(
        theory,
        notation,
        "!x:real. !y:real. !n:num. Power (x + y) n = " +
          "Sum (\\i:num. real_of_num (NUM_CHOOSE n i) * " +
          "(Power x i * Power y (NUM_SUB n i))) (SUC n)"
      )
      result <- driver.proveBy(
        statement,
        goal =>
          for {
            pair <- baseOf(goal)
            proved <- rules.specAll(baseLemma, List(pair._1, pair._2))
          } yield proved,
        opened =>
          for {
            pair <- baseOf(opened.goal)
            proved <- rules
              .specAll(stepLemma, List(pair._1, pair._2, opened.variable))
              .flatMap(rules.mp(_, opened.hypothesis))
          } yield proved
      )
    } yield result
  }

  /**
   * `|- !f n. Sum (\k. Sum (\i. f i (k - i)) (SUC k)) n = Sum (\i. Sum (\j. f i j) (n - i)) n`
   *
   * The triangle of index pairs `{(i, j) : i + j < n}` added up by **antidiagonals** on the left and
   * by **rows** on the right. It is the second half of what the Cauchy product needs and the half
   * that is about the indices rather than the algebra: [[Product]] says a product of two sums is a
   * sum over a square, and this says how a triangle inside that square is re-cut. Everything left
   * between here and `exp (x + y) = exp x * exp y` is analysis, or the binomial theorem, and this
   * file owns neither.
   *
   * == Where the work is, and it is not the induction ==
   *
   * The step peels the last antidiagonal off the left and the last **row** off the right, and the
   * two do not match term for term: what comes off the right is one entry of every row that is still
   * there, plus a row of length one. So the step needs the whole right-hand sum at `SUC n` rewritten
   * into the one at `n` plus that scattering, which is `SUM_CONGRUENCE_BELOW` and [[Additive]]
   * instantiated by hand, exactly as [[Swapped]]'s step instantiates `Additive` and for the same
   * reason: the rewriter is first order and neither could be handed to it as a rule.
   *
   * **The congruence has to be the bounded one**, and that is the whole reason this lemma waited.
   * Replacing `NUM_SUB (SUC n) i` by `SUC (NUM_SUB n i)` under the binder is true **only where
   * `i < n`** — at `i = n` the left side is `SUC ZERO` and the right is `SUC ZERO` as well, but at
   * any `i` above `n` both sides are `ZERO` and `SUC ZERO` and differ. `SUM_CONGRUENCE`, the
   * unbounded one, cannot state that hypothesis at all. That lemma's own docstring predicts this
   * meeting in as many words, about four other lemmas stated at the wrong scope: **the first real
   * consumer of a bounded rewrite meets the wall**, and it did.
   *
   * == The two facts on `num` it needed, neither of which existed ==
   *
   * `Peano.NUM_SUC_SUB`, that a step on the **left** of a truncated difference comes out of it
   * under `n <= m`, and `Peano.NUM_SUC_SUB_SELF`, the unconditional instance at `m = n`. The second
   * is not a convenience: `Rewrite.Rule.of` refuses an implication, so the conditional fact cannot
   * be in a rule set and the last row of the triangle, whose length is `SUC n - n`, is reached by
   * rewriting or not at all.
   */
  /**
   * [[Cauchy]] and [[CauchyGap]], which are [[Diagonal]] and [[Additive]] pointed at a product.
   *
   * Neither is an induction. The first is the diagonal specialised at `\i j. a i * b j` with the
   * rows collapsed by [[Scaled]]; the second splits one sum in two with [[Additive]] and reads
   * the whole back through [[ScaledRight]]. What makes both cheap is that every congruence in
   * them is **unconditional**: `a i` does not depend on the index a row runs over, and the
   * algebra inside the second is a ring identity at every index. The one bounded congruence this
   * file has is in the binomial theorem and nothing here needs it.
   *
   * **The summand bodies are read off the theorems rather than parsed twice**, which is not
   * fussiness. `Sum (\u. a u * c) n` and `Sum (\i. a i * c) n` are the same sum and are not the
   * same term, so a body written here to match one a rule produced would agree with it only by
   * the accident of two files choosing one letter. Where a body has to be built it is built once
   * and specialised, and where a rule produced it, it is taken from there.
   */
  private def cauchyProduct(
    logic: Logic,
    ring: Ring,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    diagonal: Kernel.Thm,
    congruence: Kernel.Thm,
    additive: Kernel.Thm,
    scaled: Kernel.Thm,
    scaledRight: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val reals = TyApp(Real.TypeName, Nil)
    val sequences = Type.fun(numbers, reals)
    val a = Term.variable("a", sequences)
    val b = Term.variable("b", sequences)
    val n = Term.variable("n", numbers)

    def normalised(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    /** The summand of `Sum body length`, wherever it came from. */
    def summandOf(term: Term): Either[LogicError, Term] = term match {
      case App(App(_, body), _) => Right(body)
      case other                => Left(NotOfForm("a sum", other))
    }

    def sidesOf(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
      Term
        .destEq(theorem.conclusion)
        .toRight(NotOfForm("an equation", theorem.conclusion))

    /** Two summands equal at every index, so the sums are equal at the length asked for. */
    def sameSummand(
      left: Term,
      right: Term,
      length: Term,
      close: Term => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        instance <- rules.specAll(congruence, List(left, right)).flatMap(normalised)
        obligation <- logic
          .destImp(instance.conclusion)
          .map(_._1)
          .toRight(NotOfForm("an implication", instance.conclusion))
        stripped <- Logic.stripForall(obligation)
        index <- stripped._1.headOption
          .toRight(NotOfForm("a claim about every index", obligation))
        proved <- close(stripped._2).flatMap(rules.gen(index, _))
        everywhere <- rules.mp(instance, proved)
        here <- rules.spec(length, everywhere)
      } yield here

    for {
      pair <- Parser.term(
        theory, notation, "\\i:num. \\j:num. (a:num -> real) i * (b:num -> real) j")
      rowsBody <- Parser.term(
        theory,
        notation,
        "\\i:num. (a:num -> real) i * Sum (b:num -> real) (NUM_SUB (n:num) i)"
      )
      cornerBody <- Parser.term(
        theory,
        notation,
        "\\i:num. (a:num -> real) i * " +
          "(Sum (b:num -> real) (n:num) - Sum (b:num -> real) (NUM_SUB (n:num) i))"
      )

      /* ------------------------------------------- the partial sum in closed form */

      opened <- rules.specAll(diagonal, List(pair, n)).flatMap(normalised)
      byRows <- sidesOf(opened).map(_._2).flatMap(summandOf)
      collapsed <- sameSummand(
        byRows,
        rowsBody,
        n,
        goal =>
          Term.destEq(goal) match {
            case Some((App(App(_, _), length), App(App(_, factor), _))) =>
              rules.specAll(scaled, List(factor, b, length)).flatMap(normalised)
            case _ => Left(NotOfForm("a row against a scaled partial sum", goal))
          }
      )
      cauchy <- Conv.trans(opened, collapsed).flatMap(rules.genAll(_, List(a, b, n)))

      /* -------------------------------------------------------------- the gap */

      apart <- rules.specAll(additive, List(cornerBody, rowsBody, n)).flatMap(normalised)
      togetherBody <- sidesOf(apart).map(_._1).flatMap(summandOf)

      partialB <- Parser.term(theory, notation, "Sum (b:num -> real) (n:num)", reals)
      product <- rules.specAll(scaledRight, List(partialB, a, n)).flatMap(normalised)
      wholeBody <- sidesOf(product).map(_._1).flatMap(summandOf)

      // The one place algebra happens, and it is a ring identity at every index:
      // `a i * Sum b n` is `a i * (Sum b n - Sum b (n - i)) + a i * Sum b (n - i)`.
      splitEq <- sameSummand(wholeBody, togetherBody, n, goal => ring.prove(goal))

      toCorner <- Conv
        .sym(product)
        .flatMap(Conv.trans(_, splitEq))
        .flatMap(Conv.trans(_, apart))

      // And the right-hand summand read back as the antidiagonal sum a caller writes.
      atHere <- rules.specAll(cauchy, List(a, b, n))
      backwards <- Conv.sym(atHere)
      corner <- sidesOf(toCorner).map(_._2)
      leading <- corner match {
        case App(partial, _) => Right(partial)
        case other           => Left(NotOfForm("a sum of two", other))
      }
      assembled <- Conv.apTerm(leading, backwards).flatMap(Conv.trans(toCorner, _))

      pieces <- sidesOf(assembled).map(_._2).flatMap {
        case App(App(_, gap), convolution) => Right((gap, convolution))
        case other                         => Left(NotOfForm("a sum of two", other))
      }
      wholeProduct <- sidesOf(assembled).map(_._1)
      gap <- linarith
        .prove("!p:real. !g:real. !c:real. p = g + c ==> p - c = g")
        .flatMap(rules.specAll(_, List(wholeProduct, pieces._1, pieces._2)))
        .flatMap(rules.mp(_, assembled))
        .flatMap(rules.genAll(_, List(a, b, n)))
    } yield (cauchy, gap)
  }

  private def summedDiagonal(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    settleRules: Vector[Rewrite.Rule],
    additive: Kernel.Thm,
    congruenceBelow: Kernel.Thm,
    successorMinus: Kernel.Thm,
    atMostFromBelow: Kernel.Thm,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val rules = logic.rules

    /** The summand and the length of `Sum body length`. */
    def destSum(term: Term): Either[LogicError, (Term, Term)] = term match {
      case App(App(Const(SumName, _), body), length) => Right((body, length))
      case other => Left(NotOfForm("a sum", other))
    }

    /** `Sum body`, the partial application a congruence on the length rewrites through. */
    def partialSum(term: Term): Either[LogicError, Term] = term match {
      case App(partial @ App(Const(SumName, _), _), _) => Right(partial)
      case other => Left(NotOfForm("a sum", other))
    }

    def normalised(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv
        .betaNormalise(theorem.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem)))

    def sidesOf(theorem: Kernel.Thm): Either[LogicError, (Term, Term)] =
      Term.destEq(theorem.conclusion).toRight(NotOfForm("an equation", theorem.conclusion))

    for {
      statement <- Parser.proposition(
        theory,
        notation,
        "!f:num->num->real. !n:num. " +
          "Sum (\\k:num. Sum (\\i:num. f i (NUM_SUB k i)) (SUC k)) n = " +
          "Sum (\\i:num. Sum (\\j:num. f i j) (NUM_SUB n i)) n"
      )
      result <- driver.proveBy(
        statement,
        goal => driver.settle(settleRules)(goal, Vector.empty),
        opened =>
          val index = opened.variable
          for {
            goalSides <- Term
              .destEq(opened.goal)
              .toRight(NotOfForm("an equation", opened.goal))

            // Every function this step needs is READ OFF the goal and the hypothesis rather than
            // rebuilt: `proveBy` freshens the quantified variables, so a term assembled here from
            // a name written in the statement above would be a term about a different variable.
            byRows <- sidesOf(opened.hypothesis).flatMap(sides => destSum(sides._2)).map(_._1)
            byDiagonals <- destSum(goalSides._1).map(_._1)
            lastDiagonal <- LogicError
              .lift(Term.app(byDiagonals, index))
              .flatMap(applied => Conv.betaNormalise(applied))
              .flatMap(equation => sidesOf(equation))
              .flatMap(sides => destSum(sides._2))
              .map(_._1)
            wideRows <- destSum(goalSides._2).map(_._1)

            // `Sum (\i. rows i + diagonal i) n = Sum rows n + Sum diagonal n`, whose left-hand
            // summand is the function the congruence below has to reach.
            split <- rules
              .specAll(additive, List(byRows, lastDiagonal, index))
              .flatMap(normalised)
            rowsAndOne <- sidesOf(split).flatMap(sides => destSum(sides._1)).map(_._1)

            congruence <- rules
              .specAll(congruenceBelow, List(wideRows, rowsAndOne, index))
              .flatMap(normalised)
            obligation <- logic
              .destImp(congruence.conclusion)
              .toRight(NotOfForm("an implication", congruence.conclusion))
              .map(_._1)
            stripped <- Logic.stripForall(obligation)
            row <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", obligation))
            guarded <- logic
              .destImp(stripped._2)
              .toRight(NotOfForm("an implication", stripped._2))
            (below, claim) = guarded
            assumedBelow <- LogicError.lift(Kernel.assume(below))

            // The one entry: at `i < n` the row is one longer than it was, and `SUC n - i` is
            // `SUC (n - i)` for exactly that reason.
            weak <- rules.specAll(atMostFromBelow, List(row, index)).flatMap(rules.mp(_, assumedBelow))
            shifted <- rules.specAll(successorMinus, List(index, row)).flatMap(rules.mp(_, weak))
            claimSides <- Term.destEq(claim).toRight(NotOfForm("an equation", claim))
            partial <- partialSum(claimSides._1)
            longer <- Conv.apTerm(partial, shifted)
            body <- destSum(claimSides._1).map(_._1)
            shortLength <- sidesOf(shifted).flatMap(sides => sides._2 match {
              case App(_, shorter) => Right(shorter)
              case other           => Left(NotOfForm("a successor", other))
            })
            peeled <- rules.specAll(atSuccessor, List(body, shortLength)).flatMap(normalised)
            entry <- Conv.trans(longer, peeled)
            _ <-
              if (entry.conclusion == claim) Right(())
              else Left(NotOfForm("the congruence's own obligation", entry.conclusion))

            everyRow <- rules.disch(below, entry).flatMap(rules.gen(row, _))
            widened <- rules.mp(congruence, everyRow)
            gap <- Conv.trans(widened, split)

            gapRule <- Rewrite.Rule.of(logic, gap)

            // **The hypothesis is rewritten before it is offered as a rule**, and this is the one
            // place the step is not the obvious thing. Its left side is a sum whose summand is
            // itself a sum of length `SUC k`, so `SUM_SUC` fires on it under the binder and the
            // goal never carries the shape the hypothesis is stated in. Offered raw it matched
            // nothing and the refusal named the two sides differing in exactly that summand. Put
            // through the same rules first, both it and the goal are in the same normal form.
            settled <- Rewrite.rewrite(settleRules, opened.hypothesis.conclusion)
            carried <- LogicError.lift(Kernel.eqMp(settled, opened.hypothesis))
            hypothesisRule <- Rewrite.Rule.of(logic, carried)
            proved <- driver.settle(settleRules)(opened.goal, Vector(hypothesisRule, gapRule))
          } yield proved
      )
    } yield result
  }

  /**
   * `|- !f g m n. Sum (\i. Sum (\j. f i * g j) m) n = Sum f n * Sum g m`
   *
   * **No induction, and that is the measurement rather than a shortcut.** The first attempt was the
   * shared driver with [[Scaled]] in its rule set, and its step refused: the rewriting collapses
   * the inner sum everywhere it occurs, including inside the outer one, so the term the induction
   * hypothesis is about no longer exists by the time the hypothesis is offered as a rule. The
   * refusal named it, `Sum (\x. f x * Sum g m) n + f n * Sum g m is not equal to ...`.
   *
   * Adding [[ScaledRight]] to the set to repair that is what showed the induction was never needed:
   * with both, the left side rewrites to the right in two steps and nothing is left for a base or a
   * step to do. Running the induction anyway would have gone green and left a reader believing the
   * recurrences were load-bearing here, which is why this is a conversion over the equation and not
   * `proveWith`.
   *
   * So what this lemma costs is the pair above and two rewrites, and the pair is what it is worth
   * reading it for: the inner collapse binds the constant on the left, the outer one binds it on
   * the right, and a development holding one of them would be commuting a product under a binder.
   */
  private def summedProducts(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    scaleRules: Vector[Rewrite.Rule]
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- Parser.proposition(
        theory,
        notation,
        "!f:num->real. !g:num->real. !m:num. !n:num. " +
          "Sum (\\i:num. Sum (\\j:num. f i * g j) m) n = Sum f n * Sum g m"
      )
      proved <- Rewrite.proveEquation(logic, term => Rewrite.rewrite(scaleRules, term), statement)
    } yield proved

  private def swappedSums(
    driver: Induct,
    theory: Theory,
    notation: Notation,
    rules: Vector[Rewrite.Rule],
    additive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic

    /** The summand and the length of `Sum body length`. */
    def destSum(term: Term): Either[LogicError, (Term, Term)] = term match {
      case App(App(Const(SumName, _), body), length) => Right((body, length))
      case other => Left(NotOfForm("a sum", other))
    }

    for {
      statement <- Parser.proposition(
        theory,
        notation,
        "!f:num->num->real. !m:num. !n:num. " +
          "Sum (\\i:num. Sum (\\j:num. f i j) m) n = Sum (\\j:num. Sum (\\i:num. f i j) n) m"
      )
      result <- driver.proveBy(
        statement,
        goal => driver.settle(rules)(goal, Vector.empty),
        opened =>
          val goal = opened.goal
          val hypothesis = opened.hypothesis
          for {
            hypothesisRule <- Rewrite.Rule.of(logic, hypothesis)
            equation <- Rewrite.rewrite(rules :+ hypothesisRule, goal)
            rewritten <- Term
              .destEq(equation.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", goal))
            halves <- Term.destEq(rewritten).toRight(NotOfForm("an equation", rewritten))
            summands <- halves._1 match {
              case App(App(_, left), right) => Right((left, right))
              case other => Left(NotOfForm("a sum of two summations", other))
            }
            outer <- destSum(summands._1)
            inner <- destSum(summands._2)
            instance <- logic.rules.specAll(additive, List(outer._1, inner._1, outer._2))
            normalised <- Conv.normaliseSides(instance)
            turned <- Conv.sym(normalised)
            _ <-
              if (turned.conclusion == rewritten) Right(())
              else Left(NotOfForm("the step as the rewriting left it", turned.conclusion))
            backwards <- Conv.sym(equation)
            proved <- LogicError.lift(Kernel.eqMp(backwards, turned))
          } yield proved
      )
    } yield result
  }

  /* ------------------------------------------------------------------ bounds */

  /**
   * `|- !b. 0 < b ==> !n. 0 < Power b n`.
   *
   * The one to read first, and the one that checks the plumbing the three below reuse: the base is
   * `0 < 1` after a rewrite, and the step is a product of two positives, which is `LT_MUL` and so
   * an axiom rather than a derivation. The hypothesis is assumed before the induction and
   * discharged after it, because `0 < b` is needed in the step and `b` is not the variable the
   * induction is about.
   */
  private def positivePower(
    bounds: Bounds,
    driver: Induct,
    theory: Theory,
    notation: Notation,
    rules: Vector[Rewrite.Rule]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val b = Term.variable("b", TyApp(Real.TypeName, Nil))

    for {
      positive <- Parser.proposition(theory, notation, "0 < (b:real)")
      assumed <- LogicError.lift(Kernel.assume(positive))
      statement <- Parser.proposition(theory, notation, "!n:num. 0 < Power (b:real) n")

      everywhere <- driver.proveBy(
        statement,
        goal => bounds.afterRewriting(rules, goal)(_ => bounds.order.zeroLessOne),
        opened =>
          val goal = opened.goal
          val hypothesis = opened.hypothesis
          bounds.afterRewriting(rules, goal)(_ => bounds.timesPositive(assumed, hypothesis))
      )

      discharged <- logic.rules.disch(positive, everywhere)
      result <- logic.rules.gen(b, discharged)
    } yield result
  }

  /**
   * `|- !a b. 0 < a ==> a <= b ==> !n. Power a n <= Power b n`.
   *
   * The step's certificate, which is the whole of the proof:
   *
   * {{{
   *   b * Power b n - a * Power a n
   *     = (b - a) * Power b n + a * (Power b n - Power a n)
   * }}}
   *
   * The first product wants `0 <= b - a`, which is the second hypothesis, and `0 <= Power b n`,
   * which is [[PowerPositive]] at `b` and therefore wants `0 < b`: that comes from `0 < a` and
   * `a <= b`, by the same move one level down. The second product wants `0 <= a` and the induction
   * hypothesis. `Ring` sees the displayed identity and nothing else.
   */
  private def monotonePower(
    bounds: Bounds,
    driver: Induct,
    theory: Theory,
    notation: Notation,
    rules: Vector[Rewrite.Rule],
    powerPositive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val values = TyApp(Real.TypeName, Nil)
    val a = Term.variable("a", values)
    val b = Term.variable("b", values)

    for {
      positive <- Parser.proposition(theory, notation, "0 < (a:real)")
      positiveAssumed <- LogicError.lift(Kernel.assume(positive))
      ordered <- Parser.proposition(theory, notation, "(a:real) <= (b:real)")
      orderedAssumed <- LogicError.lift(Kernel.assume(ordered))

      // `0 < b`, which is `0 < (b - a) + a` with the ring identity applied. The gap and `0 < a`
      // are the two halves, and the mixed lemma is the one that takes them in that order.
      gap <- bounds.gapOf(orderedAssumed)
      difference <- bounds.sides(gap.conclusion).map(_._2)
      shifted <- bounds.order.addNonNegativePositive
      shiftedAt <- logic.rules.specAll(shifted, List(difference, a))
      sum <- logic.rules.mp(shiftedAt, gap).flatMap(logic.rules.mp(_, positiveAssumed))
      basePositive <- bounds.rephrase(sum, b)

      statement <- Parser.proposition(
        theory,
        notation,
        "!n:num. Power (a:real) n <= Power (b:real) n"
      )
      everywhere <- driver.proveBy(
        statement,
        goal =>
          bounds.afterRewriting(rules, goal) { reduced =>
            bounds.sides(reduced).flatMap(pair => bounds.reflexive(pair._1))
          },
        opened =>
          val goal = opened.goal
          val hypothesis = opened.hypothesis
          bounds.afterRewriting(rules, goal) { reduced =>
            for {
              atIndex <- bounds.sides(hypothesis.conclusion)
              index <- bounds.lastArgument(atIndex._2)
              atBase <- logic.rules.specAll(powerPositive, List(b))
              everywhere <- logic.rules.mp(atBase, basePositive)
              higher <- logic.rules.spec(index, everywhere)
              atLeastZero <- bounds.weaken(higher)
              first <- bounds.gapOf(orderedAssumed).flatMap(bounds.times(_, atLeastZero))
              second <- bounds
                .weaken(positiveAssumed)
                .flatMap(left => bounds.gapOf(hypothesis).flatMap(bounds.times(left, _)))
              target <- bounds.sides(reduced)
              result <- bounds.below(target._1, target._2, Vector(first, second))
            } yield result
          }
      )

      dischargedInner <- logic.rules.disch(ordered, everywhere)
      dischargedOuter <- logic.rules.disch(positive, dischargedInner)
      result <- logic.rules.genAll(dischargedOuter, List(a, b))
    } yield result
  }

  /**
   * `|- !f. (!i. 0 <= f i) ==> !n. 0 <= Sum f n`.
   *
   * The base is `0 <= 0`, from reflexivity of the non-strict order, and the step adds the induction
   * hypothesis to the pointwise hypothesis at the index the induction is at. The index is read off
   * the induction hypothesis rather than named, because the driver opens the quantifier itself and
   * the variable it binds is fresh: `Induct`'s own comment records that using a variable of one's
   * own here is the first of the two mistakes it exists to prevent.
   */
  private def nonNegativeSum(
    bounds: Bounds,
    driver: Induct,
    theory: Theory,
    notation: Notation,
    rules: Vector[Rewrite.Rule]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val summand = Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil))
    val f = Term.variable("f", summand)

    for {
      pointwise <- Parser.proposition(theory, notation, "!i:num. 0 <= (f:num->real) i")
      assumed <- LogicError.lift(Kernel.assume(pointwise))
      statement <- Parser.proposition(theory, notation, "!n:num. 0 <= Sum (f:num->real) n")

      everywhere <- driver.proveBy(
        statement,
        goal =>
          bounds.afterRewriting(rules, goal) { reduced =>
            bounds.sides(reduced).flatMap(pair => bounds.reflexive(pair._1))
          },
        opened =>
          val goal = opened.goal
          val hypothesis = opened.hypothesis
          bounds.afterRewriting(rules, goal) { _ =>
            for {
              atIndex <- bounds.sides(hypothesis.conclusion)
              index <- bounds.lastArgument(atIndex._2)
              here <- logic.rules.spec(index, assumed)
              result <- bounds.plus(hypothesis, here)
            } yield result
          }
      )

      discharged <- logic.rules.disch(pointwise, everywhere)
      result <- logic.rules.gen(f, discharged)
    } yield result
  }

  /**
   * `|- !f g. (!i. f i <= g i) ==> !n. Sum f n <= Sum g n`.
   *
   * [[Congruence]] with `<=` for `=`, and the same reason to exist: bare summand symbols, a
   * pointwise hypothesis, no lambda for the rewriter to enter. The step's certificate has one term
   * from each hypothesis:
   *
   * {{{
   *   (Sum g n + g n) - (Sum f n + f n) = (Sum g n - Sum f n) + (g n - f n)
   * }}}
   */
  private def monotoneSum(
    bounds: Bounds,
    driver: Induct,
    theory: Theory,
    notation: Notation,
    rules: Vector[Rewrite.Rule]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val summand = Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil))
    val f = Term.variable("f", summand)
    val g = Term.variable("g", summand)

    for {
      pointwise <- Parser.proposition(
        theory,
        notation,
        "!i:num. (f:num->real) i <= (g:num->real) i"
      )
      assumed <- LogicError.lift(Kernel.assume(pointwise))
      statement <- Parser.proposition(
        theory,
        notation,
        "!n:num. Sum (f:num->real) n <= Sum (g:num->real) n"
      )

      everywhere <- driver.proveBy(
        statement,
        goal =>
          bounds.afterRewriting(rules, goal) { reduced =>
            bounds.sides(reduced).flatMap(pair => bounds.reflexive(pair._1))
          },
        opened =>
          val goal = opened.goal
          val hypothesis = opened.hypothesis
          bounds.afterRewriting(rules, goal) { reduced =>
            for {
              atIndex <- bounds.sides(hypothesis.conclusion)
              index <- bounds.lastArgument(atIndex._1)
              here <- logic.rules.spec(index, assumed)
              first <- bounds.gapOf(hypothesis)
              second <- bounds.gapOf(here)
              target <- bounds.sides(reduced)
              result <- bounds.below(target._1, target._2, Vector(first, second))
            } yield result
          }
      )

      discharged <- logic.rules.disch(pointwise, everywhere)
      result <- logic.rules.genAll(discharged, List(f, g))
    } yield result
  }

  /**
   * `|- !f. (!i. 0 < f i) ==> !n. 0 < Prod f n`.
   *
   * [[positivePower]] at the product: the base is `0 < 1` and the step is `LT_MUL` again, this time
   * between the induction hypothesis and the pointwise hypothesis at the index rather than between
   * the hypothesis and a fixed base.
   */
  private def positiveProd(
    bounds: Bounds,
    driver: Induct,
    theory: Theory,
    notation: Notation,
    rules: Vector[Rewrite.Rule]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = driver.logic
    val summand = Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Real.TypeName, Nil))
    val f = Term.variable("f", summand)

    for {
      pointwise <- Parser.proposition(theory, notation, "!i:num. 0 < (f:num->real) i")
      assumed <- LogicError.lift(Kernel.assume(pointwise))
      statement <- Parser.proposition(theory, notation, "!n:num. 0 < Prod (f:num->real) n")

      everywhere <- driver.proveBy(
        statement,
        goal => bounds.afterRewriting(rules, goal)(_ => bounds.order.zeroLessOne),
        opened =>
          val goal = opened.goal
          val hypothesis = opened.hypothesis
          bounds.afterRewriting(rules, goal) { _ =>
            for {
              atIndex <- Positivity.destLess(bounds.order.reals, hypothesis.conclusion)
              index <- bounds.lastArgument(atIndex._2)
              here <- logic.rules.spec(index, assumed)
              result <- bounds.timesPositive(hypothesis, here)
            } yield result
          }
      )

      discharged <- logic.rules.disch(pointwise, everywhere)
      result <- logic.rules.gen(f, discharged)
    } yield result
  }

  /**
   * The order facts and the moves every bound in this file is assembled from.
   *
   * [[Order]] hands each dependency to each derivation by name, and that reads well there because
   * its lemmas take two or three of them. Every bound here takes the same three, so they are named
   * once and what a derivation's argument list carries is the certificate it chose, which is the
   * part that differs between them.
   *
   * == What replaces `Ring`, and why something has to ==
   *
   * `Induct.settle` rewrites a goal and closes it with `Ring`, which decides equations. Not one
   * statement here is an equation. So each bound drives its induction with [[Induct.proveBy]] and
   * closes the two halves with [[afterRewriting]], which is `settle` with the closing step handed
   * over: the rewriting is the same and what follows it is not.
   *
   * What follows it is a certificate. The difference between the two sides of the goal is written
   * as a sum of products of things already known to be at least zero, [[Order]] adds and multiplies
   * those, and `Ring` is asked for exactly one thing: the identity that turns that sum back into
   * the difference. [[below]] is that move, and every step in this file has a certificate of two
   * terms.
   *
   * == Why nothing here builds a term ==
   *
   * Every side, index and difference is read off a theorem or a goal that already exists rather
   * than constructed from constants. That is not economy: a term built here has to be *syntactically
   * equal* to the one in the goal for `eqMp` to accept it, and a difference assembled from
   * `Real.Subtraction` by hand is one parse convention away from not being. Reading it off the
   * instance of the lemma that will consume it makes the match hold by construction.
   */
  private final class Bounds(
    val order: Order,
    val ring: Ring,
    val logic: Logic,
    val productOfPositives: Kernel.Thm
  ) {

    private val rules: Rules = logic.rules

    /** The two sides of `x <= y`. */
    def sides(term: Term): Either[LogicError, (Term, Term)] = term match {
      case App(App(Const(Real.NonStrictOrder, _), left), right) => Right((left, right))
      case other => Left(NotOfForm("a non-strict inequality", other))
    }

    /** The argument of an application, which is the index an induction has reached. */
    def lastArgument(term: Term): Either[LogicError, Term] = term match {
      case App(_, argument) => Right(argument)
      case other => Left(NotOfForm("an application", other))
    }

    /**
     * A goal rewritten by the rules given and closed by something other than `Ring`.
     *
     * One line since 2026-09-11. This was a copy of `Induct.settle` with the closer handed over, and
     * the note here used to argue that `settle` could not be reused because it also asks, after the
     * closer refuses, whether the rewriting had finished. That argument was wrong in a way worth
     * recording: **both** copies asked that question, the two agreed in every line, and two copies
     * that agree are the hardest kind to notice. It now lives once, in `Induct`, static because it
     * uses nothing an instance holds.
     */
    def afterRewriting(rules: Vector[Rewrite.Rule], goal: Term)(
      close: Term => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] = Induct.afterRewriting(rules, goal)(close)

    /** `|- x <= x`, for the base of a monotonicity where both sides collapse to the same term. */
    def reflexive(term: Term): Either[LogicError, Kernel.Thm] =
      for {
        instance <- order.leOfEq.flatMap(rules.specAll(_, List(term, term)))
        result <- rules.mp(instance, Conv.refl(term))
      } yield result

    /** `|- x <= y` from `|- x < y`. */
    def weaken(strict: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        pair <- Positivity.destLess(order.reals, strict.conclusion)
        instance <- order.leOfLt.flatMap(rules.specAll(_, List(pair._1, pair._2)))
        result <- rules.mp(instance, strict)
      } yield result

    /** `|- 0 <= y - x` from `|- x <= y`, which is the form a certificate's terms are in. */
    def gapOf(bound: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        pair <- sides(bound.conclusion)
        instance <- order.leToZero.flatMap(rules.specAll(_, List(pair._1, pair._2)))
        result <- rules.mp(instance, bound)
      } yield result

    /** `|- 0 <= x + y` from two theorems in that form. */
    def plus(first: Kernel.Thm, second: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        left <- sides(first.conclusion).map(_._2)
        right <- sides(second.conclusion).map(_._2)
        instance <- order.addNonNegatives.flatMap(rules.specAll(_, List(left, right)))
        result <- rules.mp(instance, first).flatMap(rules.mp(_, second))
      } yield result

    /** `|- 0 <= x * y` from two theorems in that form. */
    def times(first: Kernel.Thm, second: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        left <- sides(first.conclusion).map(_._2)
        right <- sides(second.conclusion).map(_._2)
        instance <- order.multiplyNonNegatives.flatMap(rules.specAll(_, List(left, right)))
        result <- rules.mp(instance, first).flatMap(rules.mp(_, second))
      } yield result

    /**
     * `|- 0 < x * y` from `|- 0 < x` and `|- 0 < y`, which is `LT_MUL` and so an axiom.
     *
     * The only place in this file where an axiom is reached for directly. It is the whole of what
     * the two positivity lemmas need in their steps, which is why those two are the short ones.
     */
    def timesPositive(first: Kernel.Thm, second: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        left <- Positivity.destLess(order.reals, first.conclusion).map(_._2)
        right <- Positivity.destLess(order.reals, second.conclusion).map(_._2)
        instance <- rules.specAll(productOfPositives, List(left, right))
        both <- rules.conjIntro(first, second)
        result <- rules.mp(instance, both)
      } yield result

    /**
     * `|- 0 R e` from `|- 0 R s` and the ring identity `s = e`, for `R` either order.
     *
     * The bridge between a certificate and the goal it is a certificate for. It replaces the second
     * argument of the relation and leaves the first alone, which is what both orders want here
     * since every certificate is in the form `0 R something`.
     */
    def rephrase(witness: Kernel.Thm, target: Term): Either[LogicError, Kernel.Thm] =
      witness.conclusion match {
        case App(applied @ App(_, _), side) =>
          for {
            claim <- LogicError.lift(Term.eq(side, target))
            identity <- ring.prove(claim)
            lifted <- Conv.apTerm(applied, identity)
            result <- LogicError.lift(Kernel.eqMp(lifted, witness))
          } yield result
        case other => Left(NotOfForm("a bound on one side", other))
      }

    /**
     * `|- x <= y` from witnesses that are each at least zero and sum, as a ring identity, to
     * `y - x`.
     *
     * The difference is read off the instance of `LE_FROM_ZERO` that consumes it rather than built
     * from `Real.Subtraction`, so the term the certificate is rephrased to is the term the lemma
     * expects, by construction rather than by agreement.
     */
    def below(
      left: Term,
      right: Term,
      witnesses: Vector[Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        first <- witnesses.headOption.toRight(NotOfForm("at least one witness", left))
        combined <- witnesses
          .drop(1)
          .foldLeft(Right(first): Either[LogicError, Kernel.Thm])((acc, next) =>
            acc.flatMap(plus(_, next))
          )
        instance <- order.leFromZero.flatMap(rules.specAll(_, List(left, right)))
        premise <- logic
          .destImp(instance.conclusion)
          .map(_._1)
          .toRight(NotOfForm("an implication", instance.conclusion))
        target <- sides(premise).map(_._2)
        moved <- rephrase(combined, target)
        result <- rules.mp(instance, moved)
      } yield result
  }

  private object Bounds {

    /** Over the order facts and the ring the rest of the file is built on. */
    def of(order: Order, ring: Ring, logic: Logic): Either[LogicError, Bounds] =
      order.reals.axiom("LT_MUL").map(new Bounds(order, ring, logic, _))
  }
}
