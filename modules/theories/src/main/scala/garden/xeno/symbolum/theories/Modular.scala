package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Divisibility, division with remainder and congruence, on `num` rather than on the reals.
 *
 * `Divisibility` states the same first relation over the reals and its own docstring explains why
 * that says almost nothing: over a field every non-zero `a` divides every `b`, with `inv a * b` as
 * the witness, so `|- Divides 2 3` comes out with nothing assumed. Coprimality, a greatest common
 * divisor and a descent on the size of a factor each need a type in which the divisors of a
 * quantity are finitely many, and that file says so and stops.
 *
 * `num` is such a type, and this is the same development over it. The statement that measures the
 * difference is [[Modular.DividesAntisym]], `NUM_DIVIDES a b /\ NUM_DIVIDES b a ==> a = b`: it is a
 * theorem here and it is **false** over the reals, where `Divides 2 3` and `Divides 3 2` both hold.
 * `ModularSpec` asserts both halves of that pair, so the gap between the two developments is read
 * off the code rather than off this paragraph.
 *
 * == The engine is division with remainder, and it needs no subtraction ==
 *
 * [[Modular.Division]] is `!n m. NUM_LT ZERO n ==> ?q r. m = NUM_ADD (NUM_MUL n q) r /\ NUM_LT r n`,
 * by induction on `m`. The usual proof of it descends on `m - n`, which would need a subtraction
 * `num` does not have; this one goes up instead. At `SUC m` the remainder becomes `SUC r`, and
 * `SUC r` is either still below `n`, in which case the quotient does not move, or equal to `n`, in
 * which case `n * q + n` is `n * SUC q` and the remainder goes back to `ZERO`. Nothing is ever
 * taken away.
 *
 * [[Modular.DivisionUnique]] is the other half and is **not** an induction: it is the totality of
 * the order, one semiring identity and `Peano.AddCancelsLeft`. That is worth a line because this
 * file said, until the day it was proved, that uniqueness needed cancellation on a **product**,
 * `NUM_MUL n q = NUM_MUL n p ==> q = p`. It does not, and the guess cost nothing only because
 * somebody tried the other route: what the argument actually cancels is the summand `n * q`, which
 * is addition, and the gap between the two quotients is where the bound on the remainder bites.
 *
 * == The definition of the congruence, and what was rejected ==
 *
 * `NUM_CONG k m n` is `?a b. NUM_ADD m (NUM_MUL k a) = NUM_ADD n (NUM_MUL k b)`: the two numbers
 * agree after each has been pushed up by some multiple of the modulus. Over a ring the statement
 * anybody would write is `k | m - n`, and it is not available: `num` has no subtraction, and
 * writing it as `NUM_DIVIDES k (NUM_SUB m n)` would state a claim about a truncated difference,
 * which is a different claim wherever `m < n` and silently so.
 *
 * The alternative that was considered and rejected is `?r. m = n + k * r \/ n = m + k * r`, the
 * disjunction of the two directions. It is equivalent, it is shorter to read, and every proof about
 * it splits into two cases at its first step: symmetry is a swap of disjuncts, transitivity is four
 * cases, and compatibility with multiplication is four more. The pair of witnesses has none of
 * that, because the statement is already symmetric in shape, and the price is one extra
 * existential.
 *
 * The third candidate, "the remainders under [[Modular.Division]] are equal", is the definition a
 * reader would expect, and it could not be written when this file was first assembled: without
 * [[Modular.DivisionUnique]] "the remainder" did not denote. It does now, and the definition is
 * **still** this one, because changing it would rewrite every proof below for a gain a consumer
 * cannot see: the two are equivalent and this one is the one the congruence lemmas are proved from.
 *
 * [[Modular.CongAdd]] and [[Modular.CongMul]] are what the definition exists for. An argument
 * carried out mod `2^j` needs to add and multiply congruences, and until those two are theorems the
 * relation is a predicate nobody can compute with.
 *
 * == `NUM_CONG k` takes its modulus first, and that is the useful currying ==
 *
 * `NUM_CONG k` is then the relation itself, which is what a consumer holds fixed while it varies
 * the two numbers. The reverse order would make `\m n. NUM_CONG m n k` the thing to pass around,
 * which is a lambda where this is a partial application.
 *
 * == Every identity between naturals here is decided by the reals, bar one ==
 *
 * There is no `RING` for `num` and this does not write one. [[Modular.identity]] instead proves
 * `l = r` by embedding both sides with `real_of_num`, letting `Ring` decide the resulting identity
 * between reals, and coming back across `Peano.EmbedsInjectively`. `Peano` proves the embedding is
 * a homomorphism for both operations and for the order, and that it is injective, which is what
 * makes the trip a round one: distinct naturals are a whole unit apart on the reals, so their
 * images cannot coincide.
 *
 * That is worth more than the lemmas it was built for. `NUM_MUL (NUM_ADD m (NUM_MUL k a)) ... ` is
 * a five-variable semiring identity, and the alternative to transferring it was a rewriting
 * normaliser for a commutative semiring, which is what `Arithmetic` is for the reals and is eight
 * hundred lines. It is also the arrangement `docs/adr/0003` describes one level down: the side that
 * is fast proposes the normal form and the kernel checks the result.
 *
 * **What it cannot do**, and a consumer should know before reaching for it: only equations, only
 * over terms built from `ZERO`, `SUC`, `NUM_ADD` and `NUM_MUL`, and nothing about the order. An
 * inequality between naturals has no counterpart here, because the transfer back needs injectivity
 * and there is no corresponding lemma taking `real_of_num m <= real_of_num n` to `NUM_LE m n`.
 *
 * == The five order lemmas that used to be here are in `Peano` ==
 *
 * `NUM_SUC_NOT_SELF`, `NUM_LT_IRREFL`, `NUM_ZERO_LT_SUC`, `NUM_LE_CASES` and `NUM_REAL_INJECTIVE`
 * were derived in this file on 2026-09-11 and moved the same day. They are facts about the order
 * and the embedding and mention nothing this file defines; they were here only because `Peano` was
 * being changed elsewhere the hour this was written. Two things came of the move besides the
 * tidying: they were in `docs/lemmas.md` from that day, which a fact held outside the chain's
 * developments was not until this file joined the chain on 2026-09-12, and `NUM_LE_CASES` turned out to be `Peano.splitOnGap` with the two halves injected into a
 * disjunction, which is 8379 inferences against the 13385 this file paid going through trichotomy,
 * both reaching the identical term.
 *
 * One consequence is worth naming because it looks like a regression and is not. This file no
 * longer builds a `Linarith`: the linear arithmetic was here for `NUM_REAL_INJECTIVE` alone, every
 * other step being an equation between naturals, and with that lemma in `Peano` the whole
 * construction takes a `Peano` and nothing else.
 *
 * == The greatest common divisor, and exactly how far it goes ==
 *
 * [[Modular.GcdName]] is a constant since 2026-09-11, defined by **choosing** the greatest common
 * divisor rather than computing one: `Peano.GreatestBounded` says a non-empty bounded set of
 * naturals has a greatest element, [[Modular.OneDivides]] makes the common divisors of a pair
 * non-empty, and [[Modular.DividesBound]] bounds them by whichever of the pair is not zero. The
 * choice operator names the element and the definition renames it.
 *
 * Three facts come out and all three are guarded by `~(a = ZERO) \/ ~(b = ZERO)`, which is the
 * honest domain: at the origin every number is a common divisor and there is no greatest, so
 * `NUM_GCD ZERO ZERO` is a term about which nothing is provable.
 *
 * **[[Modular.GcdGreatest]] is greatest by the order**, and greatest by **divisibility** is a
 * different statement that does not follow from it: being the largest common divisor does not, on
 * its own, make every other one divide it. That was the gap a consumer hit first, and
 * `ModularSpec` asserted its absence until 2026-09-12. It is [[Modular.GcdDivides]] now, and what
 * closed it was Bezout rather than anything about the order. Both are kept: they say different
 * things and a consumer usually knows which of the two it is asking for.
 *
 * == The quotient, the remainder, Bezout and Euclid, all of 2026-09-12 ==
 *
 * Three things the file's own docstring listed as absent are here, and each one is worth a line
 * about what it cost rather than about what it says, which its own name carries.
 *
 * **[[Modular.DivName]] and [[Modular.ModName]]** are the two functions, defined by choosing in two
 * stages so that the remainder is chosen against the quotient already named. They are **total**:
 * the value at a modulus of `ZERO` is pinned by the definition rather than left as junk, which is
 * a decision that file section argues at length and which buys [[Modular.DivisionAt]] with no
 * hypothesis on it.
 *
 * **[[Modular.Bezout]]**, and the route this file proposed for it does not close. The proposal was
 * `Peano.LeastNumber` at `\n. NUM_LT ZERO n /\ (?u v. NUM_ADD (NUM_MUL a u) n = NUM_MUL b v)`, with
 * the least positive number of that shape dividing both "by dividing `a` by it with a remainder and
 * showing the remainder is of the same shape". The remainder is **not** of the same shape: dividing
 * `a` by `b v - a u` leaves `a U - b V`, which is the other sign pattern, and converting one to the
 * other is a separate argument about sizes. [[Modular.BezoutExists]] carries the correction and the
 * route that does work, which is the recursion of Euclid's algorithm turned into an induction by
 * carrying a bound.
 *
 * **[[Modular.Euclid]]**, which was one lemma behind Bezout and turned out to be exactly that: the
 * definition of a prime this file proposed, unchanged, and a case split on whether `p` divides the
 * first factor.
 *
 * == What is still not here ==
 *
 * **A gcd anybody can compute.** [[Modular.GcdName]] is chosen and not calculated, so `NUM_GCD 6 4`
 * is a term no rewriting reduces. Euclid's algorithm would give one and it is a definition by
 * well-founded recursion, which this system does not have: the recursion theorem `Natural` derives
 * is for the successor. The same limit is why [[Modular.DivName]] is chosen rather than computed,
 * and it is the next thing that would change the character of this file rather than extend it.
 *
 * **Coprimality as a constant**, which is `NUM_GCD a b = SUC ZERO` written out and has one consumer
 * so far, inside [[Modular.Euclid]]. One consumer is not enough to define a constant for.
 *
 * **The fundamental theorem of arithmetic.** Euclid's lemma is its hard half, and what is missing
 * is the other one: a factorisation is a list, and induction over a list of factors is not an
 * induction this development can state. `Word` is the nearest thing to a list here and it is a
 * fixed length.
 */
final class Modular private (
  val peano: Peano,
  val ring: Ring,
  val theory: Theory,
  val notation: Notation,
  /**
   * The connectives read against **this** signature, which is wider than `Peano`'s.
   *
   * Held rather than rebuilt for the reason `Peano` gives: a rule that has to construct a
   * quantifier asks the theory for the quantifier at that type, and a theory that has never heard
   * of the type refuses. Every existential introduction below goes through it.
   */
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The naturals this development is built on. */
  val naturals: Natural = peano.naturals

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  /**
   * `NUM_DIVIDES a b`, as a term, for a caller holding the two numbers rather than their spelling.
   *
   * The same service `Divisibility.divides` provides and for the same reason: a caller whose
   * divisor was computed cannot go through the parser, and building the application itself would
   * mean naming the constant against a theory of its own choosing, which `docs/adr/0008` is about.
   */
  def divides(divisor: Term, dividend: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(Modular.DividesName, Modular.relation))
      applied <- LogicError.lift(Term.appAll(constant, List(divisor, dividend)))
    } yield applied

  /** `NUM_CONG k m n`, as a term, for the same reason. */
  def congruent(modulus: Term, left: Term, right: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(Modular.CongruenceName, Modular.ternary))
      applied <- LogicError.lift(Term.appAll(constant, List(modulus, left, right)))
    } yield applied

  /** `NUM_DIV m n`, as a term, for the same reason. */
  def quotient(dividend: Term, modulus: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(Modular.DivName, Modular.binary))
      applied <- LogicError.lift(Term.appAll(constant, List(dividend, modulus)))
    } yield applied

  /** `NUM_MOD m n`, as a term, for the same reason. */
  def remainder(dividend: Term, modulus: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(theory.constant(Modular.ModName, Modular.binary))
      applied <- LogicError.lift(Term.appAll(constant, List(dividend, modulus)))
    } yield applied

  /** `NUM_PRIME p`, as a term, for the same reason. */
  def prime(number: Term): Either[LogicError, Term] =
    for {
      constant <- LogicError.lift(
        theory.constant(Modular.PrimeName, Type.fun(Modular.numbers, Type.Bool))
      )
      applied <- LogicError.lift(Term.app(constant, number))
    } yield applied

  private lazy val embeddingRules: Either[LogicError, Vector[Rewrite.Rule]] =
    for {
      atZero <- peano.fact(Peano.EmbedsZero)
      atSuccessor <- peano.fact(Peano.EmbedsSuccessor)
      overSums <- peano.fact(Peano.EmbedsSum)
      overProducts <- peano.fact(Peano.EmbedsProduct)
      rules <- Rewrite.Rule.all(logic, Vector(atZero, atSuccessor, overSums, overProducts))
    } yield rules

  /**
   * `|- left = right`, for an identity between naturals, decided by `Ring` over the reals.
   *
   * Both sides are embedded with `real_of_num`, the homomorphism lemmas push the embedding down to
   * the leaves, `Ring` decides what is left, and `Peano.EmbedsInjectively` brings the equation
   * back. A `num` variable becomes `real_of_num x`, which `Ring` reads as an atom, so the identity
   * it decides is the same identity in the same number of unknowns.
   *
   * **Whether it is too strong, since `num` is a semiring and `Ring` decides a ring.** Soundness is
   * not the question: what comes back is a `num` equation detached from the injectivity lemma, so
   * the kernel built it and there is nothing to argue about. The question is whether some real
   * identity could be carried back to a `num` claim that is not one, and it cannot: the naturals
   * are cancellative and embed in a ring, so two terms built from `ZERO`, `SUC`, `NUM_ADD` and
   * `NUM_MUL` agree at every natural exactly when their images agree at every real.
   *
   * **The sentence that used to close that paragraph was false, and what it was false about is
   * narrower than it looks.** It read *"subtraction is what would separate the two and no `num`
   * term can spell one"*, and `NUM_SUB` landed on 2026-09-11, inside the development that reads
   * this. `Peano.EmbedsDifference` is the counterexample already in the repository: it carries
   * `NUM_LE y x` as a **written** hypothesis, because
   * `real_of_num (NUM_SUB m n) = real_of_num m - real_of_num n` is false at `m = ZERO` and
   * `n = SUC ZERO`, where the left side is zero and the right is minus one.
   *
   * What the false clause was supporting is a claim about **scope**, and the enumeration in front
   * of it is still exact: two terms built from `ZERO`, `SUC`, `NUM_ADD` and `NUM_MUL` do agree at
   * every natural exactly when their images agree at every real. A term with `NUM_SUB` in it is
   * outside that fragment, and [[embeddingRules]] holds a rule for each of those four and for
   * nothing else, so `real_of_num (NUM_SUB m n)` is never opened: it survives as an opaque atom
   * and `Ring` proves of it only what holds of any atom. The same goes for `PRE`, `NUM_DIV`,
   * `NUM_MOD` and `NUM_GCD`. The method is therefore **sound outside its fragment and incomplete
   * there**, which is the right failure and not the one the old sentence implied.
   *
   * **What cannot happen, checked rather than assumed:** adding `Peano.EmbedsDifference` to the
   * rules above does not quietly make this unsound. `Rewrite.Rule.of` requires an equation after
   * the quantifiers come off, and that lemma's body is an implication, so `Rewrite.Rule.all`
   * refuses it, [[embeddingRules]] becomes a refusal, and every lemma that calls this stops
   * building. The failure is loud and immediate. Soundness proper was never the question and the
   * paragraph above says why: what comes back is detached from the injectivity lemma by the
   * kernel.
   *
   * The one door that check leaves open, measured rather than feared: `Rewrite.Rule.of` looks at
   * the **conclusion** and never at `theorem.hypotheses`, so the same lemma in sequent form,
   * `NUM_LE y x |- real_of_num (NUM_SUB x y) = ...`, is accepted and becomes a conditional rule
   * whose hypothesis travels into every result. That is sound, the kernel carrying the premise
   * along, and it is the shape `Rules.mp` has: not a false theorem, a theorem that rests on more
   * than it appears to. Reaching it takes a deliberate `undisch`, which is not what completing an
   * obviously short list looks like. Worth knowing because the guard exists ten lines away:
   * `Rewrite.idle` does require an empty hypothesis list, for the reason its own docstring gives.
   *
   * The refusal is `Ring`'s or the rewriter's, and [[Induct.afterRewriting]] distinguishes them:
   * an identity that is false and an identity whose embedding did not finish are different
   * findings, and the second is reported as `NotNormalised` rather than as a false claim.
   */
  def identity(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
    for {
      rules <- embeddingRules
      injective <- peano.fact(Peano.EmbedsInjectively)
      embedding <- LogicError.lift(
        theory.constant(Peano.Embedding, Type.fun(Modular.numbers, Modular.values))
      )
      embeddedLeft <- LogicError.lift(Term.app(embedding, left))
      embeddedRight <- LogicError.lift(Term.app(embedding, right))
      goal <- LogicError.lift(Term.eq(embeddedLeft, embeddedRight))
      overReals <- Induct.afterRewriting(rules, goal)(ring.prove)
      result <- logic.rules.specAll(injective, List(left, right)).flatMap(logic.rules.mp(_, overReals))
    } yield result

  /** The same, for two terms written in this development's notation. */
  def identity(left: String, right: String): Either[LogicError, Kernel.Thm] =
    for {
      leftTerm <- term(left)
      rightTerm <- term(right)
      result <- identity(leftTerm, rightTerm)
    } yield result
}

object Modular {

  /* ------------------------------------------------------------------- names */

  /**
   * `NUM_DIVIDES a b` is `?k. b = NUM_MUL a k`.
   *
   * `UPPER_SNAKE` with the `NUM_` namespace, which is what `docs/naming.md` records for the
   * naturals' own operations and is the rule it gives for a new constant: name it the way its
   * neighbours in the same development are named. `Divisibility` calls its relation `Divides`
   * because it sits over the reals, whose unsymbolled constants are lowercase or capitalised; a
   * constant here that looked like the reals' and behaved like the naturals' would be worse than
   * either convention.
   */
  val DividesName: String = "NUM_DIVIDES"

  /** `NUM_CONG k m n` is `?a b. NUM_ADD m (NUM_MUL k a) = NUM_ADD n (NUM_MUL k b)`. */
  val CongruenceName: String = "NUM_CONG"

  /**
   * `NUM_GCD a b` is the greatest common divisor of the two, chosen rather than computed.
   *
   * The body is `select` applied to the specification "divides both and is at least as large as
   * anything that does", and the specification is read off `Peano.GreatestBounded` rather than
   * written out here, so the term the definition carries and the term the existence proof produces
   * cannot be two spellings of one intention.
   *
   * **It is a choice and not a recursion**, and the difference shows at `a = b = ZERO`, where every
   * number is a common divisor, no greatest one exists and `select` returns something about which
   * nothing at all is provable. That is why all three facts below are guarded by
   * `~(a = ZERO) \/ ~(b = ZERO)`. Euclid's algorithm would give a total function with no junk
   * value, and it is a definition by well-founded recursion, which this system does not have: the
   * recursion theorem `Natural` derives is for the successor.
   */
  val GcdName: String = "NUM_GCD"

  /**
   * `NUM_DIV m n` is the quotient of `m` by `n` and `NUM_MOD m n` the remainder, both chosen.
   *
   * The same machinery as [[GcdName]] and in two stages, because the two are one answer: the
   * quotient is chosen from the numbers that leave **some** remainder below the modulus, and the
   * remainder is then chosen from the numbers that go with **that** quotient. Choosing each from a
   * predicate of its own would be two choices with nothing tying them together, and every statement
   * a consumer wants relates the pair.
   *
   * == Which half of division with remainder buys what ==
   *
   * Because the second choice is made against the first, [[DivisionAt]] follows from [[Division]]
   * alone: each choice is made from a set that existence has already shown to be non-empty. What
   * [[DivisionUnique]] buys is [[DivisionDetermined]], and that is the half that makes these names
   * honest rather than merely defined. Without it these constants would satisfy the equation and a
   * consumer holding a quotient of its own could not conclude it held **the** quotient, which is
   * the whole content of calling either one a function.
   *
   * == The arguments are `m n`, which is against one of the two conventions here ==
   *
   * [[Division]] writes the modulus first because its induction is on the dividend and `Induct`
   * inducts on the last quantifier; [[CongruenceName]] writes the modulus first because that is
   * what a consumer holds fixed while the other arguments vary. Neither argument reaches these two:
   * `NUM_MOD m n` is read as "m mod n" by everybody who reads it, and a function whose arguments
   * are the other way round from the phrase that names it is a defect that keeps costing. The
   * products **inside** are still written `NUM_MUL n q`, which is [[Division]]'s own shape, so
   * [[DivisionDetermined]] is one specialisation of [[DivisionUnique]] rather than a specialisation
   * followed by a commutation.
   *
   * == At `n = ZERO` the two are `ZERO` and `m`, and that is a decision rather than a leftover ==
   *
   * Each predicate carries a second disjunct, `n = ZERO /\ q = ZERO` for the quotient and
   * `n = ZERO /\ r = m` for the remainder. It is unsatisfiable wherever the first disjunct is
   * satisfiable, because the first asks for a remainder strictly below `n`, and it is the only
   * thing satisfiable when `n` is `ZERO`. So the pair is **total**, and [[DivAtZero]] and
   * [[ModAtZero]] are theorems rather than the silence [[GcdName]] leaves at the origin.
   *
   * The alternative considered was exactly [[GcdName]]'s: let the choice fall on a predicate
   * nothing satisfies and let `NUM_MOD m ZERO` denote something about which nothing is provable.
   * It was rejected on a testing argument rather than a mathematical one. "Nothing is provable
   * about this term" is a claim no test can interrogate, where `NUM_MOD m ZERO = m` is one
   * assertion a spec can make and a later change can break. The price is one disjunct in each
   * definition and two short derivations; what it buys is [[DivisionAt]] with **no hypothesis at
   * all**, since at `ZERO` the equation reads `NUM_MUL ZERO q + m = m`, which holds. A rewriter
   * meeting that equation has no side condition to discharge before it may use it.
   *
   * [[ModBelow]] keeps its hypothesis and cannot lose it: nothing is below `ZERO`.
   */
  val DivName: String = "NUM_DIV"

  /** `NUM_MOD m n` is the remainder of `m` by `n`; [[DivName]] carries the whole decision. */
  val ModName: String = "NUM_MOD"

  /**
   * `NUM_PRIME p` is `NUM_LT (SUC ZERO) p /\ (!d. NUM_DIVIDES d p ==> d = SUC ZERO \/ d = p)`.
   *
   * Above one, and divisible only by one and by itself. The first conjunct is what keeps one out,
   * which the second alone does not: one is divisible only by one and by itself, and those are the
   * same number there.
   *
   * Written with `SUC ZERO` rather than a numeral because `num` has none. This is the definition
   * this file's own docstring proposed before it was written and it is unchanged, which is worth a
   * line only because the proposal was made when the lemma it exists for could not be reached.
   */
  val PrimeName: String = "NUM_PRIME"

  /** `|- !a b k. b = NUM_MUL a k ==> NUM_DIVIDES a b` */
  val DividesIntro: String = "NUM_DIVIDES_INTRO"

  /** `|- !a b. NUM_DIVIDES a b ==> (?k. b = NUM_MUL a k)` */
  val DividesElim: String = "NUM_DIVIDES_ELIM"

  /** `|- !a. NUM_DIVIDES a a` */
  val DividesRefl: String = "NUM_DIVIDES_REFL"

  /** `|- !a b c. NUM_DIVIDES a b ==> NUM_DIVIDES b c ==> NUM_DIVIDES a c` */
  val DividesTrans: String = "NUM_DIVIDES_TRANS"

  /** `|- !a b c. NUM_DIVIDES a b ==> NUM_DIVIDES a (NUM_MUL b c)` */
  val DividesMul: String = "NUM_DIVIDES_MUL"

  /**
   * `|- !a b c. NUM_DIVIDES a b /\ NUM_DIVIDES a c ==> NUM_DIVIDES a (NUM_ADD b c)`
   *
   * Linearity, and over `num` it is a sum and not a linear combination: `Divisibility` states
   * `Divides a (x * b + y * c)` with arbitrary real coefficients, and the corresponding statement
   * here follows from this and [[DividesMul]] in two steps. It is not stated separately because the
   * two-step form is what a consumer writes anyway once the coefficients are naturals.
   */
  val DividesAdd: String = "NUM_DIVIDES_ADD"

  /** `|- !a. NUM_DIVIDES a ZERO` */
  val DividesZero: String = "NUM_DIVIDES_ZERO"

  /** `|- !a. NUM_DIVIDES (SUC ZERO) a`, with one in the spelling every recurrence here produces. */
  val OneDivides: String = "NUM_ONE_DIVIDES"

  /**
   * `|- !b. NUM_DIVIDES ZERO b = (b = ZERO)`
   *
   * An equality of propositions rather than a pair of implications, for the reason
   * `Divisibility.ZeroDivides` gives: that form enters the rewriter as it stands.
   */
  val ZeroDivides: String = "NUM_ZERO_DIVIDES"

  /**
   * `|- !d. NUM_DIVIDES d (SUC ZERO) ==> d = SUC ZERO`
   *
   * The converse of [[OneDivides]], and the atom of every coprimality argument: what "their only
   * common divisor is one" is finally reduced to is a divisor of one, and this is what turns that
   * into an equation. Absent until 2026-09-13, when the beta function's moduli wanted it twice in
   * the same derivation.
   *
   * Two steps and a refutation each. [[DividesBound]] puts `d` at most one, since one is not zero;
   * `Peano.BelowOrEqual` splits that into below and equal; and below one means zero by
   * `Peano.BelowSuccessorCases`, which [[ZeroDivides]] then refutes, because zero divides only
   * zero and one is not it.
   */
  val DividesOne: String = "NUM_DIVIDES_ONE"

  /**
   * `|- !k d a b. NUM_DIVIDES d k ==> NUM_CONG k a b ==> NUM_CONG d a b`
   *
   * A congruence descends to any divisor of its modulus. Agreeing to a finer grain is harder than
   * agreeing to a coarser one, so the implication runs this way and not the other: `a` and `b` that
   * differ by a multiple of `k` differ by a multiple of anything `k` is a multiple of.
   *
   * Absent until 2026-09-14, and what wanted it is the Chinese remainder theorem over many moduli:
   * the induction there solves the whole product at once and then has to read the answer back at
   * each factor, which is exactly this step.
   *
   * It is not arithmetic about remainders. The congruence here is `?p q. a + k * p = b + k * q`,
   * so `k = d * c` turns those two witnesses into `c * p` and `c * q` and nothing else moves.
   */
  val CongDivisor: String = "NUM_CONG_DIVISOR"

  /**
   * `|- !a b. NUM_DIVIDES a b ==> NUM_LE a b \/ b = ZERO`
   *
   * A divisor is no larger than what it divides, and the escape is the only one there is. Stated
   * as a disjunction rather than as `~(b = ZERO) ==> NUM_LE a b` because that is the form the case
   * analysis produces and the form [[DividesAntisym]] consumes: the witness is either `ZERO`, and
   * then `b` is, or a successor, and then `b` is `a` plus something.
   *
   * This is the lemma that has no counterpart over the reals, and it is where the whole difference
   * between the two files sits.
   */
  val DividesBound: String = "NUM_DIVIDES_LE"

  /**
   * `|- !a b. NUM_DIVIDES a b /\ NUM_DIVIDES b a ==> a = b`
   *
   * Antisymmetry, which is **false over the reals**: `Divides 2 3` and `Divides 3 2` are both
   * theorems of `Divisibility` with nothing assumed. It is the sharpest single statement of what
   * moving to `num` bought, and `ModularSpec` pins the pair.
   */
  val DividesAntisym: String = "NUM_DIVIDES_ANTISYM"

  /**
   * `|- !n m. NUM_LT ZERO n ==> (?q r. m = NUM_ADD (NUM_MUL n q) r /\ NUM_LT r n)`
   *
   * Quantified `!n m.` rather than `!m n.`, which a reader would not choose: the induction is on
   * `m` and `Induct` inducts on the **last** quantifier of the statement it is given. `Peano` has
   * two lemmas quantified the same way for the same reason and says so in the same words.
   *
   * **Existence only**, which is what this rule gives; [[DivisionUnique]] is the other half and
   * says the pair is unique. Together they make "the remainder of `m` mod `n`" denote, so a
   * `NUM_MOD` defined by choice would have facts attached to it. There is still no such constant
   * here: defining it is a decision about the signature rather than about this proof, and nothing
   * in this file needs one.
   */
  val Division: String = "NUM_DIVISION"

  /**
   * `|- !n q r p s. NUM_ADD (NUM_MUL n q) r = NUM_ADD (NUM_MUL n p) s /\ NUM_LT r n /\ NUM_LT s n
   * ==> q = p /\ r = s`
   *
   * The other half of division with remainder, and the half [[Division]]'s own docstring named as
   * the first thing a consumer would miss. With it "the quotient" and "the remainder" denote, so
   * `NUM_MOD` and `NUM_DIV` become definable by choice the way [[GcdName]] is; without it a term
   * for the remainder can be **written** and nothing whatever can be proved about it, which is
   * worse than its absence.
   *
   * **Five variables, and [[DivisionDetermined]] has four. Which of the two is wanted is decided by
   * whether the claim mentions `NUM_DIV` and `NUM_MOD`.** This one is about two pairs a consumer
   * exhibits itself and says they agree; that one is about one pair and the pair those constants
   * name. A session writing against this file on 2026-09-12 reached here wanting there, and the
   * names do not resemble each other enough to catch it: `NUM_DIVISION_UNIQUE` against
   * `NUM_DIV_MOD_UNIQUE`, under Scala names that resemble neither. Its four arguments went into the
   * prefix of this theorem's five, and what came back was not a refusal but a **partial instance**,
   * one quantifier still in front and the substitution shifted by one, which failed much later at
   * an unrelated `mp`. `Rules.specAll` refuses a short list since that day, so the same mistake now
   * stops where it is made. A refusal can name what went wrong; only a docstring can name what was
   * wanted instead, which is why this paragraph is here and not only in the instantiating rule.
   *
   * **There is no hypothesis that the modulus is positive**, and that is not an oversight: it
   * follows from either bound. `NUM_LT r n` already says something is strictly below `n`, so `n` is
   * not `ZERO`, and the derivation never needs to say so out loud.
   *
   * The proof is a case split on which quotient is the larger, and the two halves are one function
   * called twice with the pair the other way round. On the larger side `p` is `q + d`, the equation
   * becomes `n * q + r = n * q + (n * d + s)` by one semiring identity, cancellation leaves
   * `r = n * d + s`, and a `d` that is a successor makes `r` at least `n`, which the bound on `r`
   * forbids. So `d` is `ZERO`, and both halves fall out.
   */
  val DivisionUnique: String = "NUM_DIVISION_UNIQUE"

  /**
   * `|- !k m n a b. NUM_ADD m (NUM_MUL k a) = NUM_ADD n (NUM_MUL k b) ==> NUM_CONG k m n`
   */
  val CongIntro: String = "NUM_CONG_INTRO"

  /**
   * `|- !k m n. NUM_CONG k m n ==> (?a b. NUM_ADD m (NUM_MUL k a) = NUM_ADD n (NUM_MUL k b))`
   */
  val CongElim: String = "NUM_CONG_ELIM"

  /** `|- !k m. NUM_CONG k m m` */
  val CongRefl: String = "NUM_CONG_REFL"

  /** `|- !k m n. NUM_CONG k m n ==> NUM_CONG k n m` */
  val CongSym: String = "NUM_CONG_SYM"

  /** `|- !k m n p. NUM_CONG k m n ==> NUM_CONG k n p ==> NUM_CONG k m p` */
  val CongTrans: String = "NUM_CONG_TRANS"

  /**
   * `|- !k m n p q. NUM_CONG k m n ==> NUM_CONG k p q ==> NUM_CONG k (NUM_ADD m p) (NUM_ADD n q)`
   *
   * One half of what makes the relation a congruence rather than an equivalence that happens to
   * mention a modulus.
   */
  val CongAdd: String = "NUM_CONG_ADD"

  /**
   * `|- !k m n p q. NUM_CONG k m n ==> NUM_CONG k p q ==> NUM_CONG k (NUM_MUL m p) (NUM_MUL n q)`
   *
   * The other half, and the one that pays for [[Modular.identity]] on its own. The witnesses are
   * read off the product of the two witness equations: `(m + k a)(p + k c) = m p + k (m c + a p + k
   * a c)`, and the corresponding regrouping on the other side. Written by hand from distributivity
   * it is a dozen commutations; transferred to the reals it is one call.
   */
  val CongMul: String = "NUM_CONG_MUL"

  /**
   * `|- !k m. NUM_CONG k (NUM_ADD m k) m`
   *
   * The modulus is what may be added freely, which is the fact that makes `k` a modulus at all.
   * Without it `NUM_CONG k` is an equivalence relation carrying a parameter it never uses, and
   * nothing in the group above would notice.
   */
  val CongModulus: String = "NUM_CONG_MODULUS"

  /**
   * `|- !a b. ~(a = ZERO) \/ ~(b = ZERO) ==> NUM_DIVIDES (NUM_GCD a b) a`
   *
   * The guard is the pair not both being zero, and it is the honest domain rather than a
   * convenience: [[GcdName]] explains what happens at the origin.
   */
  val GcdDividesLeft: String = "NUM_GCD_DIVIDES_LEFT"

  /** `|- !a b. ~(a = ZERO) \/ ~(b = ZERO) ==> NUM_DIVIDES (NUM_GCD a b) b` */
  val GcdDividesRight: String = "NUM_GCD_DIVIDES_RIGHT"

  /**
   * `|- !a b d. ~(a = ZERO) \/ ~(b = ZERO) ==> NUM_DIVIDES d a /\ NUM_DIVIDES d b ==>
   * NUM_LE d (NUM_GCD a b)`
   *
   * Greatest **by the order**, which is what the definition says and is weaker than what a reader
   * expects. The statement a consumer usually wants is `NUM_DIVIDES d (NUM_GCD a b)`: every common
   * divisor divides the greatest one, not merely sits below it. That does not follow from this and
   * is not here; `ModularSpec` asserts its absence rather than leaving it to be assumed. What
   * unlocks it is Bezout, and the docstring of this file says what Bezout needs.
   */
  val GcdGreatest: String = "NUM_GCD_GREATEST"

  /**
   * `|- !m n. NUM_ADD (NUM_MUL n (NUM_DIV m n)) (NUM_MOD m n) = m`
   *
   * The equation the two constants exist for, and it carries **no hypothesis**: at a modulus of
   * `ZERO` it reads `NUM_MUL ZERO (NUM_DIV m ZERO) + NUM_MOD m ZERO = m`, which is `m = m` once
   * [[DivAtZero]] and [[ModAtZero]] have said what the two are there. [[DivName]] is where that
   * decision is recorded and argued.
   *
   * **The dividend is on the right, and that is not a preference.** Written the other way round
   * this is `m = ...`, whose left side is a bare variable, and `Rewrite.Rule.of` turns any equation
   * in the library into a rule: one that matches every term and replaces it with a larger term
   * containing it. `Novelty.follows` builds exactly such a rule set out of the whole library, so
   * the first form did not fail, it **hung** — one suite ran for an hour on a term that doubled
   * every step. Measured on 2026-09-12 with a thread dump, and the guard that turns the same
   * mistake into a refusal went into `Rewrite.Rule.of` in the same change.
   */
  val DivisionAt: String = "NUM_DIV_MOD"

  /**
   * `|- !m n. NUM_LT ZERO n ==> NUM_LT (NUM_MOD m n) n`
   *
   * The bound, which keeps the hypothesis [[DivisionAt]] shed and could not shed it under any
   * definition: nothing at all is strictly below `ZERO`, so no value for `NUM_MOD m ZERO` could
   * make this true there.
   */
  val ModBelow: String = "NUM_MOD_LT"

  /** `|- !m. NUM_DIV m ZERO = ZERO` — the decision at the empty domain, as a theorem. */
  val DivAtZero: String = "NUM_DIV_ZERO"

  /** `|- !m. NUM_MOD m ZERO = m` — the other half of it. */
  val ModAtZero: String = "NUM_MOD_ZERO"

  /**
   * `|- !m n q r. m = NUM_ADD (NUM_MUL n q) r /\ NUM_LT r n ==> q = NUM_DIV m n /\ r = NUM_MOD m n`
   *
   * [[DivisionUnique]] transported to the constants, and the fact that makes them functions in the
   * sense a consumer means: a pair it computed itself, by any route, **is** the pair these two
   * name. There is no hypothesis that the modulus is positive for the same reason [[DivisionUnique]]
   * has none, and it is worth repeating because it looks like an omission twice: `NUM_LT r n`
   * already says something is strictly below `n`.
   *
   * **Four variables, and [[DivisionUnique]] has five.** This is the one to reach for whenever the
   * claim mentions `NUM_DIV` or `NUM_MOD`, and that is the whole of the rule: the other one is
   * about two pairs a consumer exhibits and never mentions either constant. The two are easy to
   * confuse by hand, and the names do not help — `NUM_DIV_MOD_UNIQUE` against
   * `NUM_DIVISION_UNIQUE`, under Scala names that resemble neither — so [[DivisionUnique]] carries
   * the record of a session that reached it wanting this one.
   */
  val DivisionDetermined: String = "NUM_DIV_MOD_UNIQUE"

  /**
   * `|- !m n. NUM_LT m n ==> NUM_DIV m n = ZERO /\ NUM_MOD m n = m`
   *
   * Below the modulus, division does nothing: the quotient is zero and the remainder is the
   * number itself.
   */
  val DivisionBelow: String = "NUM_DIV_MOD_BELOW"

  /**
   * `|- !m n. NUM_LT m n ==> NUM_DIV (NUM_ADD n m) n = SUC ZERO /\ NUM_MOD (NUM_ADD n m) n = m`
   *
   * One modulus above it, division counts once: the quotient is one and the remainder is
   * unchanged.
   *
   * These two together are what a recursion over a range that DOUBLES needs, and they are the
   * reason [[DivisionDetermined]] is the useful half of the division theory rather than
   * [[DivisionAt]]. A recursion on a binary enumeration has to say which half an index is in;
   * asked of `NUM_DIV` and `NUM_MOD` directly that means unfolding two `select`s, and a proof
   * that unfolds them spends itself proving facts about the remainder it did not set out to
   * prove. Asked this way it means exhibiting `m = n*0 + m` or `n + m = n*1 + m` and letting
   * uniqueness say that those two ARE the quotient and the remainder. Neither proof below
   * unfolds anything.
   */
  val DivisionStep: String = "NUM_DIV_MOD_STEP"

  /**
   * `|- !a b c. NUM_DIVIDES a b ==> NUM_DIVIDES a (NUM_ADD b c) ==> NUM_DIVIDES a c`
   *
   * A divisor of a sum and of one summand divides the other, and it is the lemma that stands in for
   * every subtraction the rest of this file would otherwise want. Over a ring it is
   * `a | x /\ a | y ==> a | (y - x)` and its proof is one line; `num` has only a truncated
   * subtraction, so the statement is made additively and the proof does the work the subtraction
   * would have done: the two witnesses are compared with `NUM_LE_TOTAL` and the gap between them is
   * the witness for `c`, except where the gap runs the wrong way, where `c` is `ZERO` and
   * [[DividesZero]] closes it.
   *
   * Everything below rests on it. [[Bezout]], [[GcdDivides]] and [[Euclid]] each need "and
   * therefore `k` divides what is left over", which is this and nothing else.
   */
  val DividesSummand: String = "NUM_DIVIDES_SUMMAND"

  /**
   * `|- !a b. ?d x y. NUM_DIVIDES d a /\ NUM_DIVIDES d b /\
   * (NUM_MUL a x = NUM_ADD (NUM_MUL b y) d \/ NUM_MUL b x = NUM_ADD (NUM_MUL a y) d)`
   *
   * Bezout's identity for **some** common divisor, which is what the induction proves and what
   * [[Bezout]] then identifies with [[GcdName]]. Unguarded: at `a = b = ZERO` the witnesses are
   * `ZERO` throughout and every conjunct holds.
   *
   * == Why the disjunction, and why it is not a weakness ==
   *
   * Over the integers this is `d = a x - b y` with the coefficients of either sign. `num` has no
   * negatives, so the term that would have been negated moves to the other side of the equation,
   * and **which** of the two moves depends on the pair. A statement that fixed the side would be
   * false for half the pairs. The disjunction is the standard way to carry a sign in a type that
   * has none, and a consumer reads it as: one of `a` and `b` has the multiplier that reaches
   * higher, and `d` is what the other one falls short by.
   *
   * == The route is an induction with a bound, and not the least-number principle ==
   *
   * This file's own docstring proposed `Peano.LeastNumber` at `\n. NUM_LT ZERO n /\ (?u v.
   * NUM_ADD (NUM_MUL a u) n = NUM_MUL b v)` and that route does not close. The least positive
   * number of that shape does divide both, but the argument needs the remainder of `a` by it to be
   * of the **same** shape, and it is not: dividing `a` by `b v - a u` leaves a remainder of the
   * form `a U - b V`, which is the other sign pattern. Converting one to the other means shifting
   * the coefficients by a multiple of `a b` and proving the shift lands on a natural number, which
   * is a derivation about sizes rather than about divisibility. Recorded here rather than deleted,
   * because the proposal reads as though nothing were in the way, and the next reader would spend
   * the same afternoon on it.
   *
   * What works is the recursion Euclid's algorithm runs on, made into an induction by carrying a
   * bound: `!n. !a b. NUM_LE a n ==> ...`, by induction on `n`, with the step dividing `b` by `a`
   * and applying the hypothesis to the pair `(NUM_MOD b a, a)`, whose first component is below `a`
   * and so below the bound. Nothing in it is ever subtracted: `b = NUM_MUL a q + r` is substituted
   * **forwards** into the coefficients, and the two cases of the disjunction swap which side of the
   * equation grows.
   */
  val BezoutExists: String = "NUM_BEZOUT_EXISTS"

  /**
   * `|- !a b. ~(a = ZERO) \/ ~(b = ZERO) ==> (?x y. NUM_MUL a x = NUM_ADD (NUM_MUL b y) (NUM_GCD a
   * b) \/ NUM_MUL b x = NUM_ADD (NUM_MUL a y) (NUM_GCD a b))`
   *
   * The same identity at the greatest common divisor itself, which is what a consumer wants and
   * what [[GcdDivides]] and [[Euclid]] are proved from. The guard is [[GcdName]]'s own: at the
   * origin there is no greatest common divisor and the statement is about a term nothing is
   * provable about.
   *
   * The step from [[BezoutExists]] is the interesting half and it is short. The `d` the induction
   * produces divides both, so [[GcdGreatest]] puts it at or below the greatest; and the greatest
   * divides both, so by [[DividesSummand]] it divides `d`; and a divisor is no larger than what it
   * divides unless that is `ZERO`, which the guard forbids. Antisymmetry of the order closes it.
   * So the two are equal, and the identity the induction proved is the identity at the gcd.
   */
  val Bezout: String = "NUM_BEZOUT"

  /**
   * `|- !a b d. ~(a = ZERO) \/ ~(b = ZERO) ==> NUM_DIVIDES d a /\ NUM_DIVIDES d b ==>
   * NUM_DIVIDES d (NUM_GCD a b)`
   *
   * Greatest **by divisibility**, which is the statement [[GcdGreatest]]'s docstring named as the
   * gap a consumer hits first and which `ModularSpec` asserted the absence of until 2026-09-12. It
   * does not follow from being the largest common divisor; it follows from [[Bezout]] in three
   * steps, because a common divisor divides both sides of the identity and therefore divides what
   * is left over.
   */
  val GcdDivides: String = "NUM_GCD_DIVIDES"

  /** `|- !p. NUM_PRIME p ==> NUM_LT (SUC ZERO) p`, the first conjunct of the definition. */
  val PrimeAboveOne: String = "NUM_PRIME_ABOVE_ONE"

  /** `|- !p d. NUM_PRIME p ==> NUM_DIVIDES d p ==> d = SUC ZERO \/ d = p`, the second. */
  val PrimeDivisor: String = "NUM_PRIME_DIVISOR"

  /**
   * `|- !n. NUM_LT (SUC ZERO) n ==> ?p. NUM_PRIME p /\ NUM_DIVIDES p n`
   *
   * Every number above one **has** a prime factor, which is the half of the subject
   * [[PrimeDivisor]] reads as if it said and does not: that one says a prime's divisors are one and
   * itself, and is the definition unfolded in one direction. The two names are a letter apart and
   * the statements point opposite ways, which is why this docstring says so rather than leaving a
   * reader to compare them.
   *
   * It was missing until 2026-09-14 and was found by trying to state Euclid's theorem, which cannot
   * be proved without it.
   *
   * **The route is the least divisor above one, not an induction.** `NUM_LEAST` over
   * `\d. SUC ZERO < d /\ NUM_DIVIDES d n` gives a smallest such divisor, and it is prime for free:
   * a divisor of it above one would divide `n` as well, by transitivity, and be smaller, which the
   * minimality refuses. The induction the textbook uses would work too and wants the negation
   * pushed through a universal quantifier, which this logic had no law for when this was written;
   * [[garden.xeno.symbolum.logic.Classical.NotForall]] supplies one since 2026-09-15 and the route
   * here is unchanged, because taking the least divisor asks for nothing beyond `NUM_LEAST`.
   */
  val PrimeFactor: String = "NUM_PRIME_FACTOR"

  /**
   * `|- NUM_PRIME (SUC (SUC ZERO))`
   *
   * Two is prime, which nothing had needed until the irrationality of its square root. It is the
   * only concrete number this development says anything about, and it is here rather than beside
   * its consumer because being prime is this development's own predicate.
   *
   * The proof is an enumeration and reads as one: a divisor of two is at most two, so it is below
   * two or equal to it; below two it is below one or equal to one; below one it is below zero,
   * which nothing is, or zero, which divides only zero. Four cases and no induction.
   */
  val PrimeTwo: String = "NUM_PRIME_TWO"

  /**
   * `|- !p a b. NUM_PRIME p ==> NUM_DIVIDES p (NUM_MUL a b) ==> NUM_DIVIDES p a \/ NUM_DIVIDES p b`
   *
   * Euclid's lemma, which is the point of the three above it. The proof is the classical one and it
   * is one case split: either `p` divides `a`, and there is nothing to do, or it does not, and then
   * `NUM_GCD a p` divides `p` and so is one or `p` by [[PrimeDivisor]], and it cannot be `p`
   * because it divides `a`. So it is one, [[Bezout]] gives `NUM_MUL a x = NUM_ADD (NUM_MUL p y)
   * (SUC ZERO)` or the same with the sides exchanged, and multiplying through by `b` makes both
   * products multiples of `p`, which leaves `b` a multiple of `p` by [[DividesSummand]].
   *
   * The case split is `Classical`'s excluded middle at `NUM_DIVIDES p a` and not an order
   * trichotomy, which is what this repository's own convention asks for and what was impossible
   * here before 2026-09-10.
   */
  val Euclid: String = "NUM_EUCLID"

  /**
   * `|- !a b. NUM_GCD a b = NUM_GCD b a`
   *
   * **Unguarded, which is the surprise.** Every other fact about [[GcdName]] here carries "not both
   * zero", because `NUM_GCD ZERO ZERO` is a choice over a set with no greatest element and nothing
   * decides it. This one does not need the guard: where the guard fails both arguments are `ZERO`
   * and the two sides are the same term, so the case the guard exists to exclude is the case that
   * proves itself by reflexivity.
   *
   * Two splits and three leaves, and the antisymmetry argument is written once and used twice: each
   * greatest common divisor divides both arguments, so [[GcdDivides]] puts each inside the other
   * and [[DividesAntisym]] closes it.
   *
   * What wanted it is the Chinese remainder theorem's pairwise premise, which asks for
   * `NUM_GCD (m i) (m j) = SUC ZERO` at **every** ordered pair while
   * `Coding.ModuliCoprime` proves it for `i < j` alone.
   */
  val GcdSym: String = "NUM_GCD_SYM"

  /**
   * `|- !m a s. NUM_CONG m a s ==> NUM_LT s m ==> NUM_MOD a m = s`
   *
   * The remainder, read off a congruence, which is the one thing a congruence could not do here
   * until 2026-09-14: [[CongruenceName]] and [[ModName]] were built in the same file and nothing
   * related them. A congruence says two numbers differ by a multiple of the modulus; this says that
   * if one of them is already below the modulus it **is** the remainder of the other.
   *
   * It is [[DivisionUnique]] and nothing cleverer. [[CongElim]] turns the congruence into an
   * equation between two sums, [[DivisionAt]] puts `a` into the quotient-and-remainder form, and
   * what is left is two divisions of one number with two remainders both below the modulus.
   *
   * Its consumer is the beta function, whose whole definition is a `NUM_MOD` and whose sequence
   * lemma gets its congruences from the Chinese remainder theorem. Without this the two halves do
   * not meet.
   */
  val ModOfCong: String = "NUM_MOD_OF_CONG"

  /* -------------------------------------------------------------- statements */

  /**
   * Everything this development proves, as the text a person checks it by.
   *
   * The same discipline `Peano.Statements` follows and for the same reason: a statement is checked
   * by reading it, and builder calls are not read. Every theorem below is compared against its
   * entry here before it is recorded, so a derivation that reaches something else is a refusal
   * rather than a fact under the wrong name.
   */
  val Statements: Vector[(String, String)] = Vector(
    DividesIntro -> "!a:num b:num k:num. b = NUM_MUL a k ==> NUM_DIVIDES a b",
    DividesElim -> "!a:num b:num. NUM_DIVIDES a b ==> (?k:num. b = NUM_MUL a k)",
    DividesRefl -> "!a:num. NUM_DIVIDES a a",
    DividesTrans ->
      "!a:num b:num c:num. NUM_DIVIDES a b ==> NUM_DIVIDES b c ==> NUM_DIVIDES a c",
    DividesMul -> "!a:num b:num c:num. NUM_DIVIDES a b ==> NUM_DIVIDES a (NUM_MUL b c)",
    DividesAdd ->
      "!a:num b:num c:num. NUM_DIVIDES a b /\\ NUM_DIVIDES a c ==> NUM_DIVIDES a (NUM_ADD b c)",
    DividesZero -> "!a:num. NUM_DIVIDES a ZERO",
    OneDivides -> "!a:num. NUM_DIVIDES (SUC ZERO) a",
    ZeroDivides -> "!b:num. NUM_DIVIDES ZERO b = (b = ZERO)",
    DividesOne -> "!d:num. NUM_DIVIDES d (SUC ZERO) ==> d = SUC ZERO",
    CongDivisor ->
      "!k:num d:num a:num b:num. NUM_DIVIDES d k ==> NUM_CONG k a b ==> NUM_CONG d a b",
    DividesBound -> "!a:num b:num. NUM_DIVIDES a b ==> NUM_LE a b \\/ b = ZERO",
    DividesAntisym -> "!a:num b:num. NUM_DIVIDES a b /\\ NUM_DIVIDES b a ==> a = b",
    Division ->
      ("!n:num m:num. NUM_LT ZERO n ==> " +
        "(?q:num. ?r:num. m = NUM_ADD (NUM_MUL n q) r /\\ NUM_LT r n)"),
    DivisionUnique ->
      ("!n:num q:num r:num p:num s:num. " +
        "NUM_ADD (NUM_MUL n q) r = NUM_ADD (NUM_MUL n p) s /\\ NUM_LT r n /\\ NUM_LT s n ==> " +
        "q = p /\\ r = s"),
    CongIntro ->
      ("!k:num m:num n:num a:num b:num. " +
        "NUM_ADD m (NUM_MUL k a) = NUM_ADD n (NUM_MUL k b) ==> NUM_CONG k m n"),
    CongElim ->
      ("!k:num m:num n:num. NUM_CONG k m n ==> " +
        "(?a:num. ?b:num. NUM_ADD m (NUM_MUL k a) = NUM_ADD n (NUM_MUL k b))"),
    CongRefl -> "!k:num m:num. NUM_CONG k m m",
    CongSym -> "!k:num m:num n:num. NUM_CONG k m n ==> NUM_CONG k n m",
    CongTrans -> "!k:num m:num n:num p:num. NUM_CONG k m n ==> NUM_CONG k n p ==> NUM_CONG k m p",
    CongAdd ->
      ("!k:num m:num n:num p:num q:num. NUM_CONG k m n ==> NUM_CONG k p q ==> " +
        "NUM_CONG k (NUM_ADD m p) (NUM_ADD n q)"),
    CongMul ->
      ("!k:num m:num n:num p:num q:num. NUM_CONG k m n ==> NUM_CONG k p q ==> " +
        "NUM_CONG k (NUM_MUL m p) (NUM_MUL n q)"),
    CongModulus -> "!k:num m:num. NUM_CONG k (NUM_ADD m k) m",
    GcdDividesLeft ->
      "!a:num b:num. ~(a = ZERO) \\/ ~(b = ZERO) ==> NUM_DIVIDES (NUM_GCD a b) a",
    GcdDividesRight ->
      "!a:num b:num. ~(a = ZERO) \\/ ~(b = ZERO) ==> NUM_DIVIDES (NUM_GCD a b) b",
    GcdGreatest ->
      ("!a:num b:num d:num. ~(a = ZERO) \\/ ~(b = ZERO) ==> " +
        "NUM_DIVIDES d a /\\ NUM_DIVIDES d b ==> NUM_LE d (NUM_GCD a b)"),
    DivisionAt -> "!m:num n:num. NUM_ADD (NUM_MUL n (NUM_DIV m n)) (NUM_MOD m n) = m",
    ModBelow -> "!m:num n:num. NUM_LT ZERO n ==> NUM_LT (NUM_MOD m n) n",
    DivAtZero -> "!m:num. NUM_DIV m ZERO = ZERO",
    ModAtZero -> "!m:num. NUM_MOD m ZERO = m",
    DivisionDetermined ->
      ("!m:num n:num q:num r:num. m = NUM_ADD (NUM_MUL n q) r /\\ NUM_LT r n ==> " +
        "q = NUM_DIV m n /\\ r = NUM_MOD m n"),
    DivisionBelow ->
      ("!m:num n:num. NUM_LT m n ==> NUM_DIV m n = ZERO /\\ NUM_MOD m n = m"),
    DivisionStep ->
      ("!m:num n:num. NUM_LT m n ==> NUM_DIV (NUM_ADD n m) n = SUC ZERO /\\ " +
        "NUM_MOD (NUM_ADD n m) n = m"),
    DividesSummand ->
      ("!a:num b:num c:num. NUM_DIVIDES a b ==> NUM_DIVIDES a (NUM_ADD b c) ==> " +
        "NUM_DIVIDES a c"),
    BezoutExists ->
      ("!a:num b:num. ?d:num. ?x:num. ?y:num. NUM_DIVIDES d a /\\ NUM_DIVIDES d b /\\ " +
        "(NUM_MUL a x = NUM_ADD (NUM_MUL b y) d \\/ NUM_MUL b x = NUM_ADD (NUM_MUL a y) d)"),
    Bezout ->
      ("!a:num b:num. ~(a = ZERO) \\/ ~(b = ZERO) ==> " +
        "(?x:num. ?y:num. NUM_MUL a x = NUM_ADD (NUM_MUL b y) (NUM_GCD a b) \\/ " +
        "NUM_MUL b x = NUM_ADD (NUM_MUL a y) (NUM_GCD a b))"),
    GcdDivides ->
      ("!a:num b:num d:num. ~(a = ZERO) \\/ ~(b = ZERO) ==> " +
        "NUM_DIVIDES d a /\\ NUM_DIVIDES d b ==> NUM_DIVIDES d (NUM_GCD a b)"),
    PrimeAboveOne -> "!p:num. NUM_PRIME p ==> NUM_LT (SUC ZERO) p",
    PrimeDivisor -> "!p:num d:num. NUM_PRIME p ==> NUM_DIVIDES d p ==> d = SUC ZERO \\/ d = p",
    PrimeFactor ->
      "!n:num. NUM_LT (SUC ZERO) n ==> (?p:num. NUM_PRIME p /\\ NUM_DIVIDES p n)",
    PrimeTwo -> "NUM_PRIME (SUC (SUC ZERO))",
    Euclid ->
      ("!p:num a:num b:num. NUM_PRIME p ==> NUM_DIVIDES p (NUM_MUL a b) ==> " +
        "NUM_DIVIDES p a \\/ NUM_DIVIDES p b"),
    GcdSym -> "!a:num b:num. NUM_GCD a b = NUM_GCD b a",
    ModOfCong ->
      "!m:num a:num s:num. NUM_CONG m a s ==> NUM_LT s m ==> NUM_MOD a m = s"
  )

  /**
   * The predicate `NUM_DIV m n` chooses its value from, as the text a person checks it by.
   *
   * The first disjunct is [[Division]]'s own body with the quotient fixed and the remainder still
   * existential; the second is the fallback [[DivName]] argues for, and it is satisfiable exactly
   * where the first is not.
   */
  private val QuotientPredicate: String =
    "\\q:num. (?r:num. m:num = NUM_ADD (NUM_MUL n:num q) r /\\ NUM_LT r n:num) \\/ " +
      "(n:num = ZERO /\\ q = ZERO)"

  /**
   * The predicate `NUM_MOD m n` chooses from, which names `NUM_DIV m n` and so is defined after it.
   *
   * The first disjunct is the same body with the quotient now spelled out, which is what makes the
   * two constants one answer rather than two.
   */
  private val RemainderPredicate: String =
    "\\r:num. (m:num = NUM_ADD (NUM_MUL (n:num) (NUM_DIV m:num n:num)) r /\\ NUM_LT r n:num) " +
      "\\/ (n:num = ZERO /\\ r = m:num)"

  /*
   * `(n:num)` rather than `n:num` in the line above, and the parentheses are load-bearing.
   * `Parser.readAtomType` reads a `(` after a type name as the start of that type's arguments, so
   * `NUM_MUL n:num (NUM_DIV ...)` is read as the type `num(NUM_DIV ...)` and refused with a message
   * about a missing `)` from inside a type. An annotated argument followed by a parenthesised one
   * has to be parenthesised itself. Recorded here rather than worked around silently, because the
   * refusal names a position in the middle of a term and says nothing about annotations.
   */

  /** The body of [[PrimeName]], which is a predicate written out rather than a choice. */
  private val PrimeBody: String =
    "\\p:num. NUM_LT (SUC ZERO) p /\\ (!d:num. NUM_DIVIDES d p ==> d = SUC ZERO \\/ d = p)"

  private val statements: Map[String, String] = Statements.toMap

  private[theories] val numbers: Type = TyApp(Natural.TypeName, Nil)
  private[theories] val values: Type = TyApp(Real.TypeName, Nil)
  private val relation: Type = Type.fun(numbers, Type.fun(numbers, Type.Bool))
  private val ternary: Type = Type.fun(numbers, relation)
  private[theories] val binary: Type = Type.fun(numbers, Type.fun(numbers, numbers))

  /* ------------------------------------------------------------ construction */

  /**
   * The standard development, built beside the chain rather than taken from it.
   *
   * `Chain.standard.modular` is the one a caller almost always wants since 2026-09-12: it is in
   * the signature everything else is in, and it is the one `Library.of` collects and
   * `docs/lemmas.md` lists. This builds a **second** one, over the narrower theory, and it is kept because the
   * specs of this file are about what this development does on its own and because a caller with a
   * development of its own reaches for it.
   *
   * The two are not interchangeable and the kernel says so rather than letting them mix: a constant
   * defined here and a constant of the same name defined in the chain have different origins, which
   * `docs/adr/0008` is about, so a rule built from one is refused against the other. Loud, and not
   * silent.
   */
  lazy val standard: Modular =
    construct(Chain.standard.peano).fold(
      error => throw new IllegalStateException(s"the modular arithmetic does not build: ${error.message}"),
      identity
    )

  /**
   * The whole development, over a `Peano` and nothing else.
   *
   * It took a `Linarith` as well until 2026-09-11, for exactly one lemma: `NUM_REAL_INJECTIVE` is
   * an inequality and every other step here is an equation between naturals, which goes to
   * [[Modular.identity]] and so to `Ring`. That lemma is `Peano`'s now and the parameter went with
   * it, along with the two overloads that existed to build one.
   *
   * Both constants are defined before any derivation runs, so that one set of connectives and one
   * theory serve the whole file. Defining the second halfway down would leave the lemmas above it
   * stated over a narrower signature than the lemmas below, which is legal and is the arrangement
   * that makes a later rewrite fail for a reason about origins rather than about the claim.
   */
  def construct(peano: Peano): Either[LogicError, Modular] =
    construct(peano, peano.theory)

  /**
   * The same, extending a theory that already holds something else.
   *
   * The chain entry point, the shape `Peano.construct` and `Product.construct` already had, and the
   * reason is the one `Chain.peano` gives at length: two developments built beside each other
   * declare different constants of the same name, so a claim mentioning `NUM_CONG` and `Sum` at
   * once is not a proposition unless one theory holds both. `Chain` passes its widest theory so
   * far.
   *
   * The `Peano` is still separate from the base and is still the one the base was built from: every
   * fact this file takes by name (`NUM_GREATEST`, `NUM_LE_CASES`, the five embedding lemmas) is a
   * theorem of that theory and so of every extension of it.
   */
  def construct(peano: Peano, base: Theory): Either[LogicError, Modular] = {
    val notation = peano.notation

    for {
      dividesBody <- Parser.term(base, notation, "\\a:num b:num. ?k:num. b = NUM_MUL a k")
      withDivides <- LogicError.lift(Kernel.defineConstant(base, DividesName, dividesBody))
      (dividesTheory, dividesDefinition) = withDivides

      congruenceBody <- Parser.term(
        dividesTheory,
        notation,
        "\\k:num m:num n:num. ?a:num. ?b:num. NUM_ADD m (NUM_MUL k a) = NUM_ADD n (NUM_MUL k b)"
      )
      withCongruence <- LogicError.lift(
        Kernel.defineConstant(dividesTheory, CongruenceName, congruenceBody)
      )
      (congruenceTheory, congruenceDefinition) = withCongruence

      // The third constant is not parsed, because what it has to say cannot be written down twice:
      // its body is `select` applied to the very specification `NUM_GREATEST` produces, read off
      // that theorem rather than spelled again here. A hand-written copy would be a second
      // statement of one intention, free to drift from the one the existence proof reaches.
      greatest <- peano.fact(Peano.GreatestBounded)
      choice <- peano.naturals.classical.axiom(Classical.Choice)
      overCongruence <- peano.logic.over(congruenceTheory)
      specified <- gcdSpecification(
        overCongruence,
        congruenceTheory,
        greatest,
        variable("a"),
        variable("b")
      )
      select <- LogicError.lift(
        congruenceTheory.constant(
          Classical.Select,
          Type.fun(Type.fun(numbers, Type.Bool), numbers)
        )
      )
      chosen <- LogicError.lift(Term.app(select, specified._2))
      inner <- LogicError.lift(Term.abs(variable("b"), chosen))
      gcdBody <- LogicError.lift(Term.abs(variable("a"), inner))
      withGcd <- LogicError.lift(
        Kernel.defineConstant(congruenceTheory, GcdName, gcdBody)
      )
      (gcdTheory, gcdDefinition) = withGcd

      // The quotient, the remainder and the primes, defined before any derivation runs for the
      // reason the paragraph above gives. The order among the three is forced rather than chosen:
      // the remainder's predicate names the quotient, and both are needed before a prime can be
      // anything a later lemma could use.
      quotientBody <- chosenBody(gcdTheory, notation, QuotientPredicate)
      withDiv <- LogicError.lift(Kernel.defineConstant(gcdTheory, DivName, quotientBody))
      (divTheory, divDefinition) = withDiv

      remainderBody <- chosenBody(divTheory, notation, RemainderPredicate)
      withMod <- LogicError.lift(Kernel.defineConstant(divTheory, ModName, remainderBody))
      (modTheory, modDefinition) = withMod

      primeBody <- Parser.term(modTheory, notation, PrimeBody)
      withPrime <- LogicError.lift(Kernel.defineConstant(modTheory, PrimeName, primeBody))
      (theory, primeDefinition) = withPrime

      vocabulary <- Vocabulary.over(peano, theory, dividesDefinition, congruenceDefinition)

      // The case split division with remainder runs on, taken from `Peano` by name rather than
      // derived here, which is where it was until 2026-09-11.
      belowOrEqual <- peano.fact(Peano.BelowOrEqual)

      introduction <- introduce(vocabulary)
      elimination <- eliminate(vocabulary)

      reflexivity <- dividesItself(vocabulary, introduction)
      transitivity <- dividesTransitively(vocabulary, introduction)
      multiple <- dividesMultiple(vocabulary, introduction)
      sum <- dividesSum(vocabulary, introduction)
      atZero <- everythingDividesZero(vocabulary, introduction)
      byOne <- oneDividesEverything(vocabulary, introduction)
      byZero <- zeroDividesOnlyZero(vocabulary, introduction)
      bound <- divisorIsNoLarger(vocabulary, introduction)
      dividesUnit <- onlyOneDividesOne(vocabulary, byZero, bound)
      antisymmetry <- dividesAntisymmetrically(vocabulary, bound, byZero)

      division <- withRemainder(vocabulary, belowOrEqual)
      divisionUnique <- remainderIsUnique(vocabulary)

      congIntroduction <- introduceCongruence(vocabulary)
      congElimination <- eliminateCongruence(vocabulary)
      congFiner <- congruenceDescends(vocabulary, elimination, congIntroduction, congElimination)
      congReflexivity <- congruentToItself(vocabulary, congIntroduction)
      congSymmetry <- congruentSymmetrically(vocabulary, congIntroduction)
      congTransitivity <- congruentTransitively(vocabulary, congIntroduction)
      congSum <- congruenceAdds(vocabulary, congIntroduction)
      congProduct <- congruenceMultiplies(vocabulary, congIntroduction)
      congModulus <- modulusIsFree(vocabulary, congIntroduction)

      divisors <- gcdFacts(vocabulary, gcdDefinition, greatest, choice, bound, byOne)
      (gcdLeft, gcdRight, gcdMaximal) = divisors

      // The quotient and the remainder. The first call produces both facts that hold only above a
      // modulus of `ZERO`, with the guard still standing as a hypothesis, and the three after it
      // decide what happens at `ZERO` and put the two together.
      atPositive <- divisionAboveZero(vocabulary, choice, divDefinition, modDefinition, division)
      (positiveGuard, divisionEquation, remainderBound) = atPositive
      divZero <- quotientAtZero(vocabulary, choice, divDefinition)
      modZero <- remainderAtZero(vocabulary, choice, modDefinition)
      divisionAt <- divisionEverywhere(vocabulary, divisionEquation, divZero, modZero)
      modBelow <- remainderIsBelow(vocabulary, positiveGuard, remainderBound)
      determined <- divisionIsDetermined(vocabulary, divisionAt, modBelow, divisionUnique)
      below <- divisionInTheHalf(vocabulary, determined, DivisionBelow)
      step <- divisionInTheHalf(vocabulary, determined, DivisionStep)

      // Bezout, and the two facts that were one lemma behind it.
      summand <- dividesTheOtherSummand(vocabulary, introduction, atZero)
      bezoutExists <- bezoutByInduction(vocabulary, division, multiple, sum, atZero, reflexivity)
      bezout <- bezoutAtTheGcd(
        vocabulary, bezoutExists, summand, multiple, gcdLeft, gcdRight, gcdMaximal, bound, byZero
      )
      gcdDivides <- gcdDividesByBezout(vocabulary, bezout, summand, multiple)

      gcdSymmetric <- greatestCommonDivisorIsSymmetric(vocabulary, gcdLeft, gcdRight, gcdDivides, antisymmetry)
      modOfCong <- remainderOfACongruence(vocabulary, congElimination, divisionAt, modBelow, divisionUnique)

      primeAbove <- primeIsAboveOne(vocabulary, primeDefinition)
      primeDivisor <- primeHasNoOtherDivisor(vocabulary, primeDefinition)
      euclid <- euclidsLemma(
        vocabulary, primeAbove, primeDivisor, bezout, summand, multiple, introduction, gcdLeft, gcdRight
      )
      primeFactor <- everyNumberAboveOneHasAPrimeFactor(
        vocabulary, primeDefinition, reflexivity, transitivity, bound, byZero)
      primeTwo <- twoIsPrime(vocabulary, primeDefinition, bound, byZero)

      // The connectives against the finished signature, which is also the assertion that nothing
      // was defined into a side branch: `Logic.over` checks the extension rather than assuming it.
      widest <- peano.logic.over(theory)
    } yield new Modular(
      peano,
      peano.ring,
      theory,
      notation,
      widest,
      Map(
        DividesName -> dividesDefinition,
        CongruenceName -> congruenceDefinition,
        GcdName -> gcdDefinition,
        DivName -> divDefinition,
        ModName -> modDefinition,
        PrimeName -> primeDefinition
      ),
      Map(
        DividesIntro -> introduction,
        DividesElim -> elimination,
        DividesRefl -> reflexivity,
        DividesTrans -> transitivity,
        DividesMul -> multiple,
        DividesAdd -> sum,
        DividesZero -> atZero,
        OneDivides -> byOne,
        ZeroDivides -> byZero,
        DividesOne -> dividesUnit,
        CongDivisor -> congFiner,
        DividesBound -> bound,
        DividesAntisym -> antisymmetry,
        Division -> division,
        DivisionUnique -> divisionUnique,
        CongIntro -> congIntroduction,
        CongElim -> congElimination,
        CongRefl -> congReflexivity,
        CongSym -> congSymmetry,
        CongTrans -> congTransitivity,
        CongAdd -> congSum,
        CongMul -> congProduct,
        CongModulus -> congModulus,
        GcdDividesLeft -> gcdLeft,
        GcdDividesRight -> gcdRight,
        GcdGreatest -> gcdMaximal,
        DivisionAt -> divisionAt,
        ModBelow -> modBelow,
        DivAtZero -> divZero,
        ModAtZero -> modZero,
        DivisionDetermined -> determined,
        DivisionBelow -> below,
        DivisionStep -> step,
        DividesSummand -> summand,
        BezoutExists -> bezoutExists,
        Bezout -> bezout,
        GcdDivides -> gcdDivides,
        PrimeAboveOne -> primeAbove,
        PrimeDivisor -> primeDivisor,
        PrimeFactor -> primeFactor,
        PrimeTwo -> primeTwo,
        Euclid -> euclid,
        GcdSym -> gcdSymmetric,
        ModOfCong -> modOfCong
      )
    )
  }

  /**
   * `\m n. select (\x. ...)`, the body of a function that names a value by choosing it.
   *
   * The predicate is parsed with `m` and `n` free and the two abstractions close over them, so the
   * text a reader checks is the predicate alone and the plumbing that turns it into a function of
   * two arguments is written once rather than twice.
   */
  private def chosenBody(
    theory: Theory,
    notation: Notation,
    text: String
  ): Either[LogicError, Term] =
    for {
      predicate <- Parser.term(theory, notation, text)
      select <- LogicError.lift(
        theory.constant(Classical.Select, Type.fun(Type.fun(numbers, Type.Bool), numbers))
      )
      chosen <- LogicError.lift(Term.app(select, predicate))
      inner <- LogicError.lift(Term.abs(variable("n"), chosen))
      body <- LogicError.lift(Term.abs(variable("m"), inner))
    } yield body

  /* ------------------------------------------------------------------ plumbing */

  /**
   * A premise `NUM_DIVIDES x y` taken apart: the existential it unfolds to, and the equation a
   * witness satisfies, assumed.
   *
   * The same record `Divisibility` carries and for the same reason: both halves are needed together
   * and neither is useful alone, and the equation is read off the definition's own predicate rather
   * than built a second time, so a change to the defining body cannot leave the two spelling one
   * statement differently.
   */
  private final case class Opened(
    premise: Term,
    existential: Kernel.Thm,
    witness: FVar,
    equation: Kernel.Thm
  )

  /**
   * A chain of existentials opened: the variables, the existential at each level, and the body.
   *
   * `steps` pairs each variable with the existential it was opened from, outermost first, which is
   * everything [[Vocabulary.closeAll]] needs to put them back in the other order. Two records
   * rather than one field of pairs plus a list, because every caller wants the variables by
   * position and none of them wants to take a pair apart to get one.
   */
  private final case class Opening(
    variables: List[FVar],
    steps: List[(FVar, Kernel.Thm)],
    body: Kernel.Thm
  )

  /**
   * The constants, and the moves every derivation below repeats.
   *
   * Held together rather than fetched in each lemma, for the reason `Divisibility.Vocabulary`
   * gives: the alternative was twenty copies of the same lookups, and a lemma taking its
   * multiplication from a different theory than the one the definition was made in would build a
   * term the kernel refuses for its origin, which is `docs/adr/0008`.
   */
  private final class Vocabulary private (
    val peano: Peano,
    /** What decides an identity between naturals here, on `num` and not through the reals. */
    val semiring: Semiring,
    val theory: Theory,
    val notation: Notation,
    val logic: Logic,
    val dividesDefinition: Kernel.Thm,
    val congruenceDefinition: Kernel.Thm,
    val plus: Term,
    val times: Term,
    val successor: Term,
    val zeroTerm: Term,
    val dividesConstant: Term,
    val congruenceConstant: Term,
    val gcdConstant: Term,
    val quotientConstant: Term,
    val remainderConstant: Term,
    val primeConstant: Term,
    /** `NUM_LE`, held rather than looked up, for the derivations that carry an equation into one. */
    val nonStrict: Term,
    /** `NUM_LT`, for the same reason. */
    val strict: Term,
    val embeddingRules: Vector[Rewrite.Rule],
    /**
     * The injectivity of the embedding, which is what [[identity]] rests on.
     *
     * It was an `Option` until 2026-09-11, because the lemma was proved in this same file and there
     * was a prefix of the construction in which it did not exist. `Peano` holds it now, so it is
     * available before the first constant here is defined and the absence cannot arise.
     */
    val injective: Kernel.Thm
  ) {

    val rules: Rules = logic.rules
    val ring: Ring = peano.ring

    def fact(name: String): Either[LogicError, Kernel.Thm] = peano.fact(name)

    def naturalFact(name: String): Either[LogicError, Kernel.Thm] = peano.naturals.fact(name)

    def sum(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(plus, List(left, right)))

    def product(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(times, List(left, right)))

    def next(number: Term): Either[LogicError, Term] =
      LogicError.lift(Term.app(successor, number))

    def one: Either[LogicError, Term] = next(zeroTerm)

    def dividing(divisor: Term, dividend: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(dividesConstant, List(divisor, dividend)))

    def congruence(modulus: Term, left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(congruenceConstant, List(modulus, left, right)))

    def greatestCommonDivisor(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(gcdConstant, List(left, right)))

    def quotient(dividend: Term, modulus: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(quotientConstant, List(dividend, modulus)))

    def remainder(dividend: Term, modulus: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(remainderConstant, List(dividend, modulus)))

    def isPrime(number: Term): Either[LogicError, Term] =
      LogicError.lift(Term.app(primeConstant, number))

    /** `NUM_LT left right`, as a term. */
    def belowTerm(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(strict, List(left, right)))

    def statement(name: String): Either[LogicError, Term] =
      statements.get(name) match {
        case None => Left(MissingDefinition(name))
        case Some(text) => Parser.proposition(theory, notation, text)
      }

    /**
     * The theorem, if it is the statement as this file writes it.
     *
     * Every fact of this development goes through here, which is `Peano`'s arrangement: a
     * derivation that reaches something else is a refusal and not a fact under the wrong name.
     */
    def checked(name: String, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        written <- statement(name)
        result <-
          if (theorem.conclusion == written) Right(theorem)
          else Left(NotOfForm(s"$name as it is written", theorem.conclusion))
      } yield result

    /**
     * `|- left = right`, decided on `num` and not through the reals.
     *
     * This was a second copy of [[Modular.identity]] until 2026-09-13, embedding both sides with
     * `real_of_num` and asking `Ring`, and every fact of this development that needed a regrouping
     * paid the sixteen axioms of the real numbers for it. Twenty-eight of the thirty-eight were
     * paying, which is what made the accounting of a claim about `num` say something false about
     * what it needed.
     *
     * **The conversion was decided by measuring rather than by inspecting.** `Semiring` was put
     * beside this method and every call logged: of the eighty identities this development decides
     * while it is built, **seventy-four were already inside the semiring's fragment**, and the six
     * that were not were all one shape, `x * SUC j = x + x * j`, which is `Peano.MulAtSuccessor` to
     * the letter. Two rules closed the six, so the yield is eighty of eighty and nothing here needs
     * a ring.
     *
     * [[Modular.identity]] keeps the transfer and is still the wider procedure: it opens a
     * successor **additively**, so a concrete product like `SUC (SUC ZERO) * SUC (SUC (SUC ZERO))`
     * is one it decides and this is not. The two are kept apart and named rather than chained, so
     * a caller reading a refusal knows which fragment refused: a fallback would make every
     * derivation here cost sixteen again the day somebody writes a numeral into one.
     */
    def identity(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      semiring.prove(left, right)

    def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
      Term
        .destEq(theorem.conclusion)
        .map(_._1)
        .toRight(NotOfForm("an equation", theorem.conclusion))

    def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
      Term
        .destEq(theorem.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", theorem.conclusion))

    def predicateOf(term: Term): Either[LogicError, Term] =
      logic
        .destExistsPredicate(term)
        .toRight(NotOfForm("an existential quantification", term))

    /** `|- NUM_DIVIDES x y = (?k. y = NUM_MUL x k)`, the defining equation at a pair. */
    def dividesUnfoldedAt(left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      Conv.unfold(dividesDefinition, List(left, right))

    /** `|- NUM_CONG k m n = (?a b. ...)`, the defining equation at a triple. */
    def congruenceUnfoldedAt(
      modulus: Term,
      left: Term,
      right: Term
    ): Either[LogicError, Kernel.Thm] =
      Conv.unfold(congruenceDefinition, List(modulus, left, right))

    /**
     * `NUM_DIVIDES x y` opened, with a named witness and the equation it satisfies.
     *
     * `evidence` proves the relation; for a premise that is simply assumed it is
     * `Kernel.assume(premise)`, and for a conjunct it is the conjunct. The equation comes from
     * contracting the definition's own predicate at the witness, so it is the very term
     * [[garden.xeno.symbolum.logic.Rules.existsElim]] will look for among the hypotheses.
     */
    def openDivides(
      left: Term,
      right: Term,
      witness: FVar,
      evidence: Kernel.Thm
    ): Either[LogicError, Opened] =
      for {
        unfolded <- dividesUnfoldedAt(left, right)
        premise <- leftOf(unfolded)
        existential <- LogicError.lift(Kernel.eqMp(unfolded, evidence))

        predicate <- rightOf(unfolded).flatMap(predicateOf)
        applied <- LogicError.lift(Term.app(predicate, witness))
        contraction <- Conv.betaRoot(applied)
        instance <- rightOf(contraction)
        equation <- LogicError.lift(Kernel.assume(instance))
      } yield Opened(premise, existential, witness, equation)

    /** The same, for a premise this derivation assumes itself. */
    def assumeDivides(left: Term, right: Term, witness: FVar): Either[LogicError, Opened] =
      for {
        unfolded <- dividesUnfoldedAt(left, right)
        premise <- leftOf(unfolded)
        assumed <- LogicError.lift(Kernel.assume(premise))
        opened <- openDivides(left, right, witness, assumed)
      } yield opened

    /** Discharge the witness of an opened premise from a case that used it. */
    def close(opened: Opened, caseTheorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      rules.existsElim(opened.existential, opened.witness, caseTheorem)

    /**
     * `NUM_DIVIDES x y` concluded from `y = NUM_MUL x w`, through the introduction lemma.
     *
     * The antecedent is compared against the equation before the detachment, which is not
     * belt-and-braces: [[garden.xeno.symbolum.logic.Rules.mp]] leaves an antecedent that does not match
     * standing as a hypothesis, so an equation about the wrong term comes back as a **true**
     * sequent with an extra premise rather than as an error. `Divisibility` met that and the
     * comparison is its fix.
     */
    def concludeDivides(
      introduction: Kernel.Thm,
      divisor: Term,
      dividend: Term,
      witness: Term,
      equation: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        instance <- rules.specAll(introduction, List(divisor, dividend, witness))
        parts <- logic
          .destImp(instance.conclusion)
          .toRight(NotOfForm("an implication", instance.conclusion))
        _ <-
          if (parts._1 == equation.conclusion) Right(())
          else Left(NotOfForm(s"a proof of ${parts._1}", equation.conclusion))
        related <- rules.mp(instance, equation)
      } yield related

    /** `NUM_CONG k m n` concluded from the witness equation, through its introduction lemma. */
    def concludeCongruence(
      introduction: Kernel.Thm,
      modulus: Term,
      left: Term,
      right: Term,
      leftWitness: Term,
      rightWitness: Term,
      equation: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        instance <- rules.specAll(
          introduction,
          List(modulus, left, right, leftWitness, rightWitness)
        )
        parts <- logic
          .destImp(instance.conclusion)
          .toRight(NotOfForm("an implication", instance.conclusion))
        _ <-
          if (parts._1 == equation.conclusion) Right(())
          else Left(NotOfForm(s"a proof of ${parts._1}", equation.conclusion))
        related <- rules.mp(instance, equation)
      } yield related

    /** `|- s * t = u * t`, from `|- s = u` and a `t`, by congruence and not by rewriting. */
    def scaleOnTheRight(equation: Kernel.Thm, factor: Term): Either[LogicError, Kernel.Thm] =
      Conv.apTerm(times, equation).flatMap(Conv.apThm(_, factor))

    /** `|- s + u = t + v`, from `|- s = t` and `|- u = v`. */
    def addSides(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        partial <- Conv.apTerm(plus, left)
        combined <- LogicError.lift(Kernel.mkComb(partial, right))
      } yield combined

    /** `|- s * u = t * v`, from `|- s = t` and `|- u = v`. */
    def multiplySides(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        partial <- Conv.apTerm(times, left)
        combined <- LogicError.lift(Kernel.mkComb(partial, right))
      } yield combined

    /**
     * Regroup the right-hand side of an equation into `x * w` and chain it on.
     *
     * The last two steps of every lemma that produces a divisibility witness, and they are one call
     * because the term handed to the arithmetic has to be the term the introduction lemma will be
     * specialised at, to the node. Building it twice is how the two drift apart.
     */
    def asMultipleOf(
      equation: Kernel.Thm,
      divisor: Term,
      witness: Term
    ): Either[LogicError, Kernel.Thm] =
      for {
        grouped <- product(divisor, witness)
        regrouped <- rightOf(equation).flatMap(identity(_, grouped))
        chained <- Conv.trans(equation, regrouped)
      } yield chained

    /**
     * The same, where the regrouping is exactly one associativity and a named lemma closes it.
     *
     * [[identity]] decides an equation between naturals with `Ring` **over the reals**, which its
     * own docstring argues for and which is the right general answer: there is no decision
     * procedure for the ring on `num`. What it costs is the fourteen axioms of the real numbers,
     * charged to every theorem that reaches it, and on 2026-09-13 **twenty-eight of this
     * development's thirty-eight published lemmas were paying it**; the eight that were not are the
     * ones that never call it.
     *
     * Where the regrouping is `(x * y) * z = x * (y * z)` that price buys nothing.
     * `Peano.MulAssociative` is that equation, it is proved, and it costs two. This is not a
     * cheaper route to the same theorem: it is the same theorem resting on less, which is the
     * question `Derivation.axiomsOf` exists to answer and the one a development that cares what a
     * conclusion spends has to keep asking.
     *
     * **The node property [[asMultipleOf]] exists to protect is kept, and kept by assertion rather
     * than by hoping.** The grouped term is built once, here, and the specialised lemma is refused
     * unless its right side is that term, so the two cannot drift the way that docstring warns
     * about.
     */
    def asMultipleOfAssociating(
      equation: Kernel.Thm,
      divisor: Term,
      left: Term,
      right: Term
    ): Either[LogicError, Kernel.Thm] =
      for {
        witness <- product(left, right)
        grouped <- product(divisor, witness)
        associative <- fact(Peano.MulAssociative)
        instance <- rules.specAll(associative, List(divisor, left, right))
        reached <- rightOf(instance)
        _ <-
          if (reached == grouped) Right(())
          else Left(NotOfForm("the term the introduction lemma will be specialised at", reached))
        chained <- Conv.trans(equation, instance)
      } yield chained

    /** `|- NUM_LE left right`, from a proof that `left + witness = right`. */
    def atMost(
      left: Term,
      right: Term,
      witness: Term,
      evidence: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        definition <- peano.definition(Peano.NonStrictOrder)
        unfolded <- Conv.unfold(definition, List(left, right))
        body <- rightOf(unfolded)
        predicate <- predicateOf(body)
        witnessed <- rules.existsIntro(predicate, witness, evidence)
        result <- Conv
          .sym(unfolded)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, witnessed)))
      } yield result

    /** `NUM_LE left right`, as a term. */
    def atMostTerm(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(
        theory
          .constant(Peano.NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
          .flatMap(constant => Term.appAll(constant, List(left, right)))
      )

    /** `G |- NUM_LE (SUC left) right` from `G |- NUM_LT left right`: the definition, unfolded. */
    def asNonStrict(left: Term, right: Term, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        definition <- peano.definition(Peano.StrictOrder)
        unfolded <- Conv.unfold(definition, List(left, right))
        result <- LogicError.lift(Kernel.eqMp(unfolded, theorem))
      } yield result

    /**
     * `|- ?x. ?y. body`, from a proof of `body` at the two witnesses.
     *
     * The predicates are taken off the goal rather than built here, for the reason
     * [[garden.xeno.symbolum.logic.Rules.existsIntro]] gives: which existential was meant is the caller's
     * statement and cannot be recovered from a theorem.
     */
    def witnessTwo(
      goal: Term,
      first: Term,
      second: Term,
      evidence: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      witnessAll(goal, List(first, second), evidence)

    /**
     * The same for a chain of any length, which is what [[BezoutExists]] needs at three.
     *
     * One implementation rather than two: the pair above is this at two witnesses, and a second
     * copy of the same fold would be a second place for the predicate to be taken off the wrong
     * term. The predicates are still read off the goal at every level, for the reason
     * [[garden.xeno.symbolum.logic.Rules.existsIntro]] gives.
     */
    def witnessAll(
      goal: Term,
      witnesses: List[Term],
      evidence: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      witnesses match {
        case Nil => Right(evidence)
        case first :: rest =>
          for {
            predicate <- predicateOf(goal)
            inner <- bodyAt(goal, List(first))
            step <- witnessAll(inner, rest, evidence)
            result <- rules.existsIntro(predicate, first, step)
          } yield result
      }

    /**
     * The body of a chain of existentials at the witnesses given, as a term.
     *
     * What a derivation needs **before** it proves anything: the statement says which disjunct and
     * which conjuncts have to be reached, and reading them off it is what keeps a proof from
     * building a term that is one commutation away from the one the statement wants.
     */
    def bodyAt(goal: Term, witnesses: List[Term]): Either[LogicError, Term] =
      witnesses match {
        case Nil => Right(goal)
        case first :: rest =>
          for {
            predicate <- predicateOf(goal)
            applied <- LogicError.lift(Term.app(predicate, first))
            contraction <- Conv.betaRoot(applied)
            inner <- rightOf(contraction)
            result <- bodyAt(inner, rest)
          } yield result
      }

    /**
     * A doubly existential theorem opened into two fresh variables and the body assumed.
     *
     * What comes back is the assumed inner existential, which is what the outer elimination will
     * ask for among the hypotheses, and the assumed body, which is what the inner one will.
     */
    def openTwo(
      evidence: Kernel.Thm,
      avoid: Set[FVar],
      firstName: String,
      secondName: String
    ): Either[LogicError, (FVar, FVar, Kernel.Thm, Kernel.Thm)] =
      for {
        opening <- openAll(evidence, avoid, List(firstName, secondName))
        first <- opening.variables.headOption.toRight(NotOfForm("two witnesses", evidence.conclusion))
        second <- opening.variables.lift(1).toRight(NotOfForm("two witnesses", evidence.conclusion))
        inner <- opening.steps.lift(1).map(_._2).toRight(NotOfForm("two witnesses", evidence.conclusion))
      } yield (first, second, inner, opening.body)

    /**
     * A chain of existentials of any length opened into fresh variables, with the body assumed.
     *
     * The general form of the pair above and the same discipline: each variable is fresh against
     * everything already named, including the variables opened before it, because a witness that
     * collided with one of those would narrow the case to where the two are equal and would be
     * refused nowhere.
     */
    def openAll(
      evidence: Kernel.Thm,
      avoid: Set[FVar],
      names: List[String]
    ): Either[LogicError, Opening] = {
      def go(
        current: Kernel.Thm,
        taken: Set[FVar],
        remaining: List[String],
        steps: List[(FVar, Kernel.Thm)]
      ): Either[LogicError, Opening] =
        remaining match {
          case Nil => Right(Opening(steps.reverse.map(_._1), steps.reverse, current))
          case name :: rest =>
            val variable = Conv.freshVariable(name, numbers, taken)

            for {
              predicate <- predicateOf(current.conclusion)
              applied <- LogicError.lift(Term.app(predicate, variable))
              contraction <- Conv.betaRoot(applied)
              bodyTerm <- rightOf(contraction)
              assumed <- LogicError.lift(Kernel.assume(bodyTerm))
              result <- go(assumed, taken + variable, rest, (variable, current) :: steps)
            } yield result
        }

      go(evidence, avoid, names, Nil)
    }

    /** Close what [[openAll]] opened, innermost first, which is the only order that discharges. */
    def closeAll(opening: Opening, reached: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      opening.steps.reverse.foldLeft(Right(reached): Either[LogicError, Kernel.Thm]) {
        case (accumulated, (variable, existential)) =>
          accumulated.flatMap(rules.existsElim(existential, variable, _))
      }

    /** Close what [[openTwo]] opened, innermost first. */
    def closeTwo(
      evidence: Kernel.Thm,
      first: FVar,
      second: FVar,
      innerAssumed: Kernel.Thm,
      reached: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        withoutSecond <- rules.existsElim(innerAssumed, second, reached)
        withoutFirst <- rules.existsElim(evidence, first, withoutSecond)
      } yield withoutFirst
  }

  private object Vocabulary {

    def over(
      peano: Peano,
      theory: Theory,
      dividesDefinition: Kernel.Thm,
      congruenceDefinition: Kernel.Thm
    ): Either[LogicError, Vocabulary] =
      for {
        logic <- peano.logic.over(theory)
        plus <- LogicError.lift(theory.constant(Peano.Addition, binary))
        times <- LogicError.lift(theory.constant(Peano.Multiplication, binary))
        successor <- LogicError.lift(
          theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
        )
        zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
        divides <- LogicError.lift(theory.constant(DividesName, relation))
        congruence <- LogicError.lift(theory.constant(CongruenceName, ternary))
        gcd <- LogicError.lift(theory.constant(GcdName, binary))
        quotient <- LogicError.lift(theory.constant(DivName, binary))
        remainder <- LogicError.lift(theory.constant(ModName, binary))
        prime <- LogicError.lift(theory.constant(PrimeName, Type.fun(numbers, Type.Bool)))
        nonStrict <- LogicError.lift(theory.constant(Peano.NonStrictOrder, relation))
        strict <- LogicError.lift(theory.constant(Peano.StrictOrder, relation))

        injective <- peano.fact(Peano.EmbedsInjectively)
        atZero <- peano.fact(Peano.EmbedsZero)
        atSuccessor <- peano.fact(Peano.EmbedsSuccessor)
        overSums <- peano.fact(Peano.EmbedsSum)
        overProducts <- peano.fact(Peano.EmbedsProduct)
        embeddingRules <- Rewrite.Rule.all(
          logic,
          Vector(atZero, atSuccessor, overSums, overProducts)
        )
        semiring <- Semiring.construct(peano)
      } yield new Vocabulary(
        peano,
        semiring,
        theory,
        peano.notation,
        logic,
        dividesDefinition,
        congruenceDefinition,
        plus,
        times,
        successor,
        zero,
        divides,
        congruence,
        gcd,
        quotient,
        remainder,
        prime,
        nonStrict,
        strict,
        embeddingRules,
        injective
      )
  }

  private def variable(name: String): FVar = Term.variable(name, numbers)

  /* ------------------------------------------------------------- divisibility */

  /**
   * `|- !a b k. b = NUM_MUL a k ==> NUM_DIVIDES a b`.
   *
   * The witness goes in and the relation comes out: an existential introduction against the
   * definition's own predicate, then the defining equation read right to left. The predicate is
   * taken from the unfolded definition rather than built here, which is the reason this is a
   * theorem at all: a caller specialising it never has to say which existential was meant.
   */
  private def introduce(vocabulary: Vocabulary): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")
    val k = variable("k")

    for {
      unfolded <- vocabulary.dividesUnfoldedAt(a, b)
      folded <- Conv.sym(unfolded)
      predicate <- vocabulary.rightOf(unfolded).flatMap(vocabulary.predicateOf)

      applied <- LogicError.lift(Term.app(predicate, k))
      contraction <- Conv.betaRoot(applied)
      equation <- vocabulary.rightOf(contraction)
      assumed <- LogicError.lift(Kernel.assume(equation))

      witnessed <- rules.existsIntro(predicate, k, assumed)
      related <- LogicError.lift(Kernel.eqMp(folded, witnessed))
      discharged <- rules.disch(equation, related)
      general <- rules.genAll(discharged, List(a, b, k))
      result <- vocabulary.checked(DividesIntro, general)
    } yield result
  }

  /** `|- !a b. NUM_DIVIDES a b ==> (?k. b = NUM_MUL a k)`, the definition read left to right. */
  private def eliminate(vocabulary: Vocabulary): Either[LogicError, Kernel.Thm] = {
    val a = variable("a")
    val b = variable("b")

    for {
      opened <- vocabulary.assumeDivides(a, b, variable("k"))
      discharged <- vocabulary.rules.disch(opened.premise, opened.existential)
      general <- vocabulary.rules.genAll(discharged, List(a, b))
      result <- vocabulary.checked(DividesElim, general)
    } yield result
  }

  /** `|- !a. NUM_DIVIDES a a`, with `SUC ZERO` as the witness. */
  private def dividesItself(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val a = variable("a")

    for {
      unit <- vocabulary.one
      scaled <- vocabulary.product(a, unit)
      equation <- vocabulary.identity(a, scaled)
      related <- vocabulary.concludeDivides(introduction, a, a, unit, equation)
      general <- vocabulary.rules.gen(a, related)
      result <- vocabulary.checked(DividesRefl, general)
    } yield result
  }

  /**
   * `|- !a b c. NUM_DIVIDES a b ==> NUM_DIVIDES b c ==> NUM_DIVIDES a c`.
   *
   * Two witnesses multiplied: `b = a * k` scaled on the right by `m` chains onto `c = b * m`, and
   * the arithmetic regroups the result to `c = a * (k * m)`. The two eliminations nest, the inner
   * one first, and both side conditions hold because neither witness occurs in `NUM_DIVIDES a c`.
   */
  private def dividesTransitively(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")
    val c = variable("c")
    val k = variable("k")
    val m = variable("m")

    for {
      first <- vocabulary.assumeDivides(a, b, k)
      second <- vocabulary.assumeDivides(b, c, m)

      scaled <- vocabulary.scaleOnTheRight(first.equation, m)
      chained <- Conv.trans(second.equation, scaled)

      witness <- vocabulary.product(k, m)
      equation <- vocabulary.asMultipleOf(chained, a, witness)

      related <- vocabulary.concludeDivides(introduction, a, c, witness, equation)
      withoutSecond <- vocabulary.close(second, related)
      withoutFirst <- vocabulary.close(first, withoutSecond)

      dischargedSecond <- rules.disch(second.premise, withoutFirst)
      dischargedFirst <- rules.disch(first.premise, dischargedSecond)
      general <- rules.genAll(dischargedFirst, List(a, b, c))
      result <- vocabulary.checked(DividesTrans, general)
    } yield result
  }

  /** `|- !a b c. NUM_DIVIDES a b ==> NUM_DIVIDES a (NUM_MUL b c)`, with `k * c` as the witness. */
  private def dividesMultiple(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")
    val c = variable("c")
    val k = variable("k")

    for {
      opened <- vocabulary.assumeDivides(a, b, k)
      scaled <- vocabulary.scaleOnTheRight(opened.equation, c)

      witness <- vocabulary.product(k, c)
      // Not `asMultipleOf`, which would send `(a * k) * c = a * (k * c)` to a decision procedure
      // over the reals and charge this lemma their fourteen axioms. That regrouping is
      // `NUM_MUL_ASSOC` exactly.
      equation <- vocabulary.asMultipleOfAssociating(scaled, a, k, c)

      dividend <- vocabulary.product(b, c)
      related <- vocabulary.concludeDivides(introduction, a, dividend, witness, equation)
      closed <- vocabulary.close(opened, related)
      discharged <- rules.disch(opened.premise, closed)
      general <- rules.genAll(discharged, List(a, b, c))
      result <- vocabulary.checked(DividesMul, general)
    } yield result
  }

  /**
   * `|- !a b c. NUM_DIVIDES a b /\ NUM_DIVIDES a c ==> NUM_DIVIDES a (NUM_ADD b c)`.
   *
   * The witness is `k + m`, the two witness equations are joined by one congruence step on the
   * addition, and the arithmetic pulls `a` out of the sum. The premise is a conjunction rather than
   * two arrows because that is what a consumer of a linearity lemma holds: both halves come from
   * the same place.
   */
  private def dividesSum(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic
    val a = variable("a")
    val b = variable("b")
    val c = variable("c")
    val k = variable("k")
    val m = variable("m")

    for {
      dividesB <- vocabulary.dividing(a, b)
      dividesC <- vocabulary.dividing(a, c)
      both <- logic.mkConj(dividesB, dividesC)
      assumed <- LogicError.lift(Kernel.assume(both))
      firstHalf <- rules.conjElim1(assumed)
      secondHalf <- rules.conjElim2(assumed)

      first <- vocabulary.openDivides(a, b, k, firstHalf)
      second <- vocabulary.openDivides(a, c, m, secondHalf)

      combined <- vocabulary.addSides(first.equation, second.equation)
      witness <- vocabulary.sum(k, m)
      equation <- vocabulary.asMultipleOf(combined, a, witness)

      dividend <- vocabulary.sum(b, c)
      related <- vocabulary.concludeDivides(introduction, a, dividend, witness, equation)
      withoutSecond <- vocabulary.close(second, related)
      withoutFirst <- vocabulary.close(first, withoutSecond)

      discharged <- rules.disch(both, withoutFirst)
      general <- rules.genAll(discharged, List(a, b, c))
      result <- vocabulary.checked(DividesAdd, general)
    } yield result
  }

  /** `|- !a. NUM_DIVIDES a ZERO`, with `ZERO` as the witness and nothing conditional on `a`. */
  private def everythingDividesZero(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val a = variable("a")

    for {
      scaled <- vocabulary.product(a, vocabulary.zeroTerm)
      equation <- vocabulary.identity(vocabulary.zeroTerm, scaled)
      related <- vocabulary.concludeDivides(
        introduction,
        a,
        vocabulary.zeroTerm,
        vocabulary.zeroTerm,
        equation
      )
      general <- vocabulary.rules.gen(a, related)
      result <- vocabulary.checked(DividesZero, general)
    } yield result
  }

  /** `|- !a. NUM_DIVIDES (SUC ZERO) a`, with `a` itself as the witness. */
  private def oneDividesEverything(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val a = variable("a")

    for {
      unit <- vocabulary.one
      scaled <- vocabulary.product(unit, a)
      equation <- vocabulary.identity(a, scaled)
      related <- vocabulary.concludeDivides(introduction, unit, a, a, equation)
      general <- vocabulary.rules.gen(a, related)
      result <- vocabulary.checked(OneDivides, general)
    } yield result
  }


  /**
   * [[DividesOne]]: a divisor of one is one.
   *
   * The bound gives `d <= SUC ZERO`, since the right-hand side of the disjunction it also offers
   * says one is zero. The order splits that into `d < SUC ZERO` and `d = SUC ZERO`, and the first
   * makes `d` zero, which [[ZeroDivides]] refutes: zero divides only zero.
   *
   * Every refutation here is of the same shape, `SUC ZERO = ZERO`, and each is `Natural`'s
   * successor fact at `ZERO`. That is worth a line because it is what makes the derivation short:
   * nothing about arithmetic is needed, only that one is not zero, three times.
   */
  private def onlyOneDividesOne(
    vocabulary: Vocabulary,
    zeroDivides: Kernel.Thm,
    dividesBound: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val d = variable("d")

    for {
      unit <- vocabulary.one
      notZero <- vocabulary.peano.naturals.fact(Natural.SuccessorNotZero)
      unitNotZero <- rules.spec(vocabulary.zeroTerm, notZero)
      isUnit <- LogicError.lift(Term.eq(d, unit))
      premise <- vocabulary.dividing(d, unit)
      assumed <- LogicError.lift(Kernel.assume(premise))

      // `d <= SUC ZERO`, the other half of the bound being that one is zero.
      bounded <- rules.specAll(dividesBound, List(d, unit)).flatMap(rules.mp(_, assumed))
      boundSplit <- logic
        .destDisj(bounded.conclusion)
        .toRight(NotOfForm("a disjunction", bounded.conclusion))
      (atMostUnit, unitIsZero) = boundSplit
      keptBound <- LogicError.lift(Kernel.assume(atMostUnit))
      refutedBound <- LogicError
        .lift(Kernel.assume(unitIsZero))
        .flatMap(rules.notElim(unitNotZero, _))
        .flatMap(rules.falsityElim(atMostUnit, _))
      atMost <- rules.disjElim(bounded, keptBound, refutedBound)

      // Below one or equal to it, and below one is zero.
      cases <- vocabulary
        .fact(Peano.BelowOrEqual)
        .flatMap(rules.specAll(_, List(d, unit)))
        .flatMap(rules.mp(_, atMost))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (below, equal) = split

      fromBelow <- for {
        assumedBelow <- LogicError.lift(Kernel.assume(below))
        inner <- vocabulary
          .fact(Peano.BelowSuccessorCases)
          .flatMap(rules.specAll(_, List(vocabulary.zeroTerm, d)))
          .flatMap(rules.mp(_, assumedBelow))
        innerSplit <- logic.destDisj(inner.conclusion).toRight(NotOfForm("a disjunction", inner.conclusion))
        (belowZero, isZero) = innerSplit
        never <- vocabulary.fact(Peano.NotBelowZero).flatMap(rules.spec(d, _))
        impossible <- LogicError
          .lift(Kernel.assume(belowZero))
          .flatMap(assumedBelowZero => rules.notElim(never, assumedBelowZero))
          .flatMap(contradiction => rules.falsityElim(isUnit, contradiction))

        // `d = ZERO` makes the premise `ZERO | SUC ZERO`, which says one is zero.
        atZero <- for {
          assumedZero <- LogicError.lift(Kernel.assume(isZero))
          dividesConstant <- LogicError.lift(
            vocabulary.theory.constant(
              DividesName,
              Type.fun(numbers, Type.fun(numbers, Type.Bool))
            )
          )
          carried <- Conv.apTerm(dividesConstant, assumedZero).flatMap(Conv.apThm(_, unit))
          moved <- LogicError.lift(Kernel.eqMp(carried, assumed))
          collapsed <- rules.spec(unit, zeroDivides)
          absurd <- LogicError.lift(Kernel.eqMp(collapsed, moved))
          contradiction <- rules.notElim(unitNotZero, absurd)
          anything <- rules.falsityElim(isUnit, contradiction)
        } yield anything

        settled <- rules.disjElim(inner, impossible, atZero)
      } yield settled

      fromEqual <- LogicError.lift(Kernel.assume(equal))
      reached <- rules.disjElim(cases, fromBelow, fromEqual)
      discharged <- rules.disch(premise, reached)
      general <- rules.gen(d, discharged)
      result <- vocabulary.checked(DividesOne, general)
    } yield result
  }


  /**
   * [[CongDivisor]]: a congruence descends to a divisor of its modulus.
   *
   * Open the congruence for its two witnesses, open the divisibility for its cofactor, and put the
   * three together: `a + k * p = b + k * q` with `k = d * c` is `a + d * (c * p) = b + d * (c * q)`,
   * which is what the introduction wants. One semiring identity on each side and nothing else.
   */
  private def congruenceDescends(
    vocabulary: Vocabulary,
    dividesElim: Kernel.Thm,
    congIntro: Kernel.Thm,
    congElim: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val k = variable("k")
    val d = variable("d")
    val a = variable("a")
    val b = variable("b")

    for {
      divides <- vocabulary.dividing(d, k)
      congruent <- vocabulary.congruence(k, a, b)
      goal <- vocabulary.congruence(d, a, b)
      assumedDivides <- LogicError.lift(Kernel.assume(divides))
      assumedCongruent <- LogicError.lift(Kernel.assume(congruent))

      cofactorOpened <- rules.specAll(dividesElim, List(d, k)).flatMap(rules.mp(_, assumedDivides))
      witnessesOpened <- rules.specAll(congElim, List(k, a, b)).flatMap(rules.mp(_, assumedCongruent))

      reached <- withWitness(vocabulary, cofactorOpened, "c", Set(k, d, a, b)) { (c, cofactor) =>
        withTwoWitnessesHere(vocabulary, witnessesOpened, Set(k, d, a, b, c)) { (p, q, equation) =>
          for {
            leftCoefficient <- vocabulary.product(c, p)
            rightCoefficient <- vocabulary.product(c, q)

            // `a + k * p` is `a + d * (c * p)` once `k` is `d * c`, and the same on the right.
            leftWanted <- vocabulary
              .product(d, leftCoefficient)
              .flatMap(vocabulary.sum(a, _))
            rightWanted <- vocabulary
              .product(d, rightCoefficient)
              .flatMap(vocabulary.sum(b, _))
            sides <- Term
              .destEq(equation.conclusion)
              .toRight(NotOfForm("an equation", equation.conclusion))
            (leftHas, rightHas) = sides

            // `k` becomes `d * c` on each side, then the semiring regroups the coefficient. The
            // two are kept apart because only the first needs the cofactor and only the second
            // needs the arithmetic, and chaining them the other way round is what refused once.
            rule <- Rewrite.Rule.of(logic, cofactor)
            leftAsCofactor <- Rewrite.rewrite(Vector(rule), leftHas)
            rightAsCofactor <- Rewrite.rewrite(Vector(rule), rightHas)
            leftOpened <- Term
              .destEq(leftAsCofactor.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", leftAsCofactor.conclusion))
            rightOpened <- Term
              .destEq(rightAsCofactor.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", rightAsCofactor.conclusion))

            leftShape <- vocabulary.semiring.prove(leftOpened, leftWanted)
            rightShape <- vocabulary.semiring.prove(rightOpened, rightWanted)
            left <- Conv.trans(leftAsCofactor, leftShape)
            right <- Conv.trans(rightAsCofactor, rightShape)
            carried <- Conv
              .sym(left)
              .flatMap(Conv.trans(_, equation))
              .flatMap(Conv.trans(_, right))
            result <- rules
              .specAll(congIntro, List(d, a, b, leftCoefficient, rightCoefficient))
              .flatMap(rules.mp(_, carried))
          } yield result
        }
      }

      dischargedCongruent <- rules.disch(congruent, reached)
      dischargedDivides <- rules.disch(divides, dischargedCongruent)
      general <- rules.genAll(dischargedDivides, List(k, d, a, b))
      result <- vocabulary.checked(CongDivisor, general)
    } yield result
  }

  /** Open a one-witness existential, hand the instance over, and close it again. */
  private def withWitness(
    vocabulary: Vocabulary,
    existential: Kernel.Thm,
    name: String,
    avoid: Set[FVar]
  )(
    reach: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    for {
      predicate <- logic
        .destExistsPredicate(existential.conclusion)
        .toRight(NotOfForm("an existential", existential.conclusion))
      variable = Conv.freshVariable(name, numbers, avoid ++ Term.freeVariables(existential.conclusion))
      applied <- LogicError.lift(Term.app(predicate, variable))
      contraction <- Conv.betaRoot(applied)
      instance <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      assumed <- LogicError.lift(Kernel.assume(instance))
      reached <- reach(variable, assumed)
      result <- rules.existsElim(existential, variable, reached)
    } yield result
  }

  /** The same for two nested existentials, which is what a congruence opens to. */
  private def withTwoWitnessesHere(
    vocabulary: Vocabulary,
    existential: Kernel.Thm,
    avoid: Set[FVar]
  )(
    reach: (FVar, FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    withWitness(vocabulary, existential, "p", avoid) { (p, inner) =>
      withWitness(vocabulary, inner, "q", avoid + p) { (q, body) =>
        reach(p, q, body)
      }
    }

  /**
   * `|- !b. NUM_DIVIDES ZERO b = (b = ZERO)`.
   *
   * Both directions, then antisymmetry of the implication. Forwards, the witness equation is
   * `b = ZERO * k` and the arithmetic collapses that product whatever the witness was, so nothing
   * has to be known about it, which is exactly the condition the elimination asks for. Backwards,
   * `b = ZERO` chains onto `ZERO = ZERO * ZERO`.
   */
  private def zeroDividesOnlyZero(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val b = variable("b")
    val k = variable("k")
    val zero = vocabulary.zeroTerm

    for {
      opened <- vocabulary.assumeDivides(zero, b, k)
      vanishes <- vocabulary.rightOf(opened.equation).flatMap(vocabulary.identity(_, zero))
      forwardCase <- Conv.trans(opened.equation, vanishes)
      forward <- vocabulary.close(opened, forwardCase)

      target <- LogicError.lift(Term.eq(b, zero))
      assumed <- LogicError.lift(Kernel.assume(target))
      squared <- vocabulary.product(zero, zero)
      trivial <- vocabulary.identity(zero, squared)
      chained <- Conv.trans(assumed, trivial)
      backward <- vocabulary.concludeDivides(introduction, zero, b, zero, chained)

      both = Kernel.deductAntisym(backward, forward)
      general <- vocabulary.rules.gen(b, both)
      result <- vocabulary.checked(ZeroDivides, general)
    } yield result
  }

  /**
   * `|- !a b. NUM_DIVIDES a b ==> NUM_LE a b \/ b = ZERO`.
   *
   * The witness decides it. `b = a * k` with `k` zero makes `b` zero; with `k` a successor `SUC j`
   * it makes `b` equal to `a + a * j`, which is `NUM_LE a b` with `a * j` as the gap. `NUM_CASES`
   * is the split, and it is the only place in the file that opens a number rather than a relation.
   */
  private def divisorIsNoLarger(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic
    val a = variable("a")
    val b = variable("b")
    val k = variable("k")
    val j = variable("j")
    val zero = vocabulary.zeroTerm

    for {
      cases <- vocabulary.naturalFact(Natural.ZeroOrSuccessor)
      opened <- vocabulary.assumeDivides(a, b, k)

      bounded <- vocabulary.atMostTerm(a, b)
      isZero <- LogicError.lift(Term.eq(b, zero))
      goal <- logic.mkDisj(bounded, isZero)

      split <- rules.spec(k, cases)
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (witnessIsZero, witnessIsSuccessor) = branches

      // A witness of `ZERO`: `b = a * ZERO`, which is `ZERO`.
      assumedZero <- LogicError.lift(Kernel.assume(witnessIsZero))
      partial <- LogicError.lift(Term.app(vocabulary.times, a))
      carriedZero <- Conv.apTerm(partial, assumedZero)
      chainedZero <- Conv.trans(opened.equation, carriedZero)
      collapses <- vocabulary.rightOf(chainedZero).flatMap(vocabulary.identity(_, zero))
      vanishes <- Conv.trans(chainedZero, collapses)
      zeroBranch <- rules.disjIntro2(bounded, vanishes)

      // A witness of `SUC j`: `b = a * SUC j = a + a * j`, so `a * j` closes the gap.
      assumedSuccessor <- LogicError.lift(Kernel.assume(witnessIsSuccessor))
      successorOfJ <- vocabulary.next(j)
      isStep <- LogicError.lift(Term.eq(k, successorOfJ))
      assumedStep <- LogicError.lift(Kernel.assume(isStep))
      carriedStep <- Conv.apTerm(partial, assumedStep)
      chainedStep <- Conv.trans(opened.equation, carriedStep)

      gap <- vocabulary.product(a, j)
      reachable <- vocabulary.sum(a, gap)
      regrouped <- vocabulary.rightOf(chainedStep).flatMap(vocabulary.identity(_, reachable))
      reaches <- Conv.trans(chainedStep, regrouped).flatMap(Conv.sym)
      below <- vocabulary.atMost(a, b, gap, reaches)
      injected <- rules.disjIntro1(isZero, below)
      successorBranch <- rules.existsElim(assumedSuccessor, j, injected)

      decided <- rules.disjElim(split, zeroBranch, successorBranch)
      closed <- vocabulary.close(opened, decided)
      discharged <- rules.disch(opened.premise, closed)
      general <- rules.genAll(discharged, List(a, b))
      result <- vocabulary.checked(DividesBound, general)
    } yield result
  }

  /**
   * `|- !a b. NUM_DIVIDES a b /\ NUM_DIVIDES b a ==> a = b`.
   *
   * The statement that is false over the reals. Each premise bounds one number by the other unless
   * the larger is zero, and `NUM_LE_ANTISYM` closes the case where neither escape is taken. The two
   * escapes are the same argument: a zero on one side forces a zero on the other through
   * [[zeroDividesOnlyZero]], and then both are zero.
   */
  private def dividesAntisymmetrically(
    vocabulary: Vocabulary,
    bound: Kernel.Thm,
    zeroDivides: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic
    val a = variable("a")
    val b = variable("b")
    val zero = vocabulary.zeroTerm

    /** `x = y` from `x = ZERO` and a proof that the other one is zero too. */
    def bothZero(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv.sym(right).flatMap(Conv.trans(left, _))

    /**
     * `y = ZERO` from `x = ZERO` and `NUM_DIVIDES x y`, by carrying the first into the second.
     *
     * A congruence rather than a rewrite: the term being replaced is a whole argument of the
     * relation, so one `apTerm` and one `apThm` say it, where a rewrite rule with a bare variable
     * on its left would match every subterm of the goal.
     */
    def forcedZero(isZero: Kernel.Thm, divides: Kernel.Thm, other: Term): Either[LogicError, Kernel.Thm] =
      for {
        carried <- Conv.apTerm(vocabulary.dividesConstant, isZero).flatMap(Conv.apThm(_, other))
        byZero <- LogicError.lift(Kernel.eqMp(carried, divides))
        equation <- rules.spec(other, zeroDivides)
        result <- LogicError.lift(Kernel.eqMp(equation, byZero))
      } yield result

    for {
      antisymmetric <- vocabulary.fact(Peano.AntiSymmetric)

      dividesB <- vocabulary.dividing(a, b)
      dividesA <- vocabulary.dividing(b, a)
      both <- logic.mkConj(dividesB, dividesA)
      assumed <- LogicError.lift(Kernel.assume(both))
      first <- rules.conjElim1(assumed)
      second <- rules.conjElim2(assumed)

      goal <- LogicError.lift(Term.eq(a, b))

      firstBound <- rules.specAll(bound, List(a, b)).flatMap(rules.mp(_, first))
      firstBranches <- logic
        .destDisj(firstBound.conclusion)
        .toRight(NotOfForm("a disjunction", firstBound.conclusion))
      (aBelowB, bIsZero) = firstBranches

      // `b = ZERO`, so `NUM_DIVIDES b a` is `NUM_DIVIDES ZERO a`, so `a = ZERO` as well.
      assumedBIsZero <- LogicError.lift(Kernel.assume(bIsZero))
      aAlsoZero <- forcedZero(assumedBIsZero, second, a)
      bZeroCase <- bothZero(aAlsoZero, assumedBIsZero)

      assumedABelowB <- LogicError.lift(Kernel.assume(aBelowB))
      secondBound <- rules.specAll(bound, List(b, a)).flatMap(rules.mp(_, second))
      secondBranches <- logic
        .destDisj(secondBound.conclusion)
        .toRight(NotOfForm("a disjunction", secondBound.conclusion))
      (bBelowA, aIsZero) = secondBranches

      assumedBBelowA <- LogicError.lift(Kernel.assume(bBelowA))
      pair <- rules.conjIntro(assumedABelowB, assumedBBelowA)
      byOrder <- rules.specAll(antisymmetric, List(a, b)).flatMap(rules.mp(_, pair))

      assumedAIsZero <- LogicError.lift(Kernel.assume(aIsZero))
      bAlsoZero <- forcedZero(assumedAIsZero, first, b)
      aZeroCase <- bothZero(assumedAIsZero, bAlsoZero)

      belowCase <- rules.disjElim(secondBound, byOrder, aZeroCase)
      decided <- rules.disjElim(firstBound, belowCase, bZeroCase)

      discharged <- rules.disch(both, decided)
      general <- rules.genAll(discharged, List(a, b))
      result <- vocabulary.checked(DividesAntisym, general)
    } yield result
  }

  /* -------------------------------------------------- division with remainder */

  /**
   * `|- !n m. NUM_LT ZERO n ==> (?q r. m = NUM_ADD (NUM_MUL n q) r /\ NUM_LT r n)`.
   *
   * An induction on `m` that goes **up**. At `ZERO` the quotient and the remainder are both `ZERO`
   * and the bound on the remainder is the hypothesis itself. At `SUC m` the previous remainder
   * moves to `SUC r`, which by `Peano.BelowOrEqual` is either still below `n`, in which case the
   * quotient does not move, or exactly `n`, in which case `n * q + n` is `n * SUC q` and the
   * remainder goes back to `ZERO`.
   *
   * The usual proof descends on `m - n` and cannot be written here, which is the only reason this
   * one is worth a paragraph: `num` has no subtraction, and adding one at a time never needs it.
   */
  private def withRemainder(
    vocabulary: Vocabulary,
    belowOrEqual: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val zero = vocabulary.zeroTerm

    /** The premise, the existential it guards, and the modulus the premise is about. */
    def subjectOf(goal: Term): Either[LogicError, (Term, Term, Term)] =
      for {
        parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
        (premise, existential) = parts
        modulus <- premise match {
          case App(App(_, _), right) => Right(right)
          case other => Left(NotOfForm("a bound below a number", other))
        }
      } yield (premise, existential, modulus)

    for {
      statement <- vocabulary.statement(Division)
      atSuccessor <- vocabulary.fact(Peano.AddAtSuccessor)
      atZeroOfMul <- vocabulary.fact(Peano.MulAtSuccessor)
      induction <- vocabulary.naturalFact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)

      proved <- driver.proveBy(
        statement,
        goal =>
          for {
            parts <- subjectOf(goal)
            (premise, existential, modulus) = parts
            positive <- LogicError.lift(Kernel.assume(premise))

            scaled <- vocabulary.product(modulus, zero)
            whole <- vocabulary.sum(scaled, zero)
            equation <- vocabulary.identity(zero, whole)
            body <- rules.conjIntro(equation, positive)
            witnessed <- vocabulary.witnessTwo(existential, zero, zero, body)
            discharged <- rules.disch(premise, witnessed)
          } yield discharged,
        opened =>
          for {
            parts <- subjectOf(opened.goal)
            (premise, existential, modulus) = parts
            positive <- LogicError.lift(Kernel.assume(premise))
            previous <- rules.mp(opened.hypothesis, positive)

            // Fresh with respect to the hypotheses as well as the goal. A witness colliding with a
            // variable of an assumption would narrow the case to where the two are equal and would
            // be refused nowhere, which is the trap `Peano.splitOnGap` names in the same words.
            avoid = previous.hypotheses.foldLeft(
              Term.freeVariables(opened.goal) + opened.variable
            )((found, hypothesis) => found ++ Term.freeVariables(hypothesis))
            pieces <- vocabulary.openTwo(previous, avoid, "q", "r")
            (quotient, remainder, innerAssumed, bodyAssumed) = pieces
            reached <- rules.conjElim1(bodyAssumed)
            bounded <- rules.conjElim2(bodyAssumed)

            // `SUC m = SUC (n * q + r) = n * q + SUC r`.
            stepped <- Conv.apTerm(vocabulary.successor, reached)
            scaled <- vocabulary.product(modulus, quotient)
            recurrence <- rules.specAll(atSuccessor, List(scaled, remainder))
            movedIn <- Conv.sym(recurrence)
            atNextRemainder <- Conv.trans(stepped, movedIn)

            nextRemainder <- vocabulary.next(remainder)
            asNonStrict <- vocabulary.asNonStrict(remainder, modulus, bounded)
            split <- rules
              .specAll(belowOrEqual, List(nextRemainder, modulus))
              .flatMap(rules.mp(_, asNonStrict))
            branches <- logic
              .destDisj(split.conclusion)
              .toRight(NotOfForm("a disjunction", split.conclusion))
            (stillBelow, exactly) = branches

            // Still below the modulus: the quotient does not move.
            assumedBelow <- LogicError.lift(Kernel.assume(stillBelow))
            belowBody <- rules.conjIntro(atNextRemainder, assumedBelow)
            belowCase <- vocabulary.witnessTwo(existential, quotient, nextRemainder, belowBody)

            // Exactly the modulus: the quotient goes up and the remainder goes back to zero.
            assumedExact <- LogicError.lift(Kernel.assume(exactly))
            partial <- LogicError.lift(Term.app(vocabulary.plus, scaled))
            carried <- Conv.apTerm(partial, assumedExact)
            filled <- Conv.trans(atNextRemainder, carried)
            nextQuotient <- vocabulary.next(quotient)
            grouped <- rules.specAll(atZeroOfMul, List(modulus, quotient)).flatMap(Conv.sym)
            asProduct <- Conv.trans(filled, grouped)
            product <- vocabulary.product(modulus, nextQuotient)
            padded <- vocabulary.sum(product, zero)
            padding <- vocabulary.identity(product, padded)
            exactBodyEquation <- Conv.trans(asProduct, padding)
            exactBody <- rules.conjIntro(exactBodyEquation, positive)
            exactCase <- vocabulary.witnessTwo(existential, nextQuotient, zero, exactBody)

            decided <- rules.disjElim(split, belowCase, exactCase)
            closed <- vocabulary.closeTwo(previous, quotient, remainder, innerAssumed, decided)
            discharged <- rules.disch(premise, closed)
          } yield discharged
      )
      result <- vocabulary.checked(Division, proved)
    } yield result
  }

  /* ------------------------------------------------- greatest common divisor */

  /**
   * `Peano.GreatestBounded` at "divides both `a` and `b`", and the specification it produces.
   *
   * Both halves of the answer are wanted by both callers and neither is useful without the other:
   * the definition of [[GcdName]] needs the specification as a term, and the derivation needs the
   * instance whose conclusion that specification came out of. Reading the term off the theorem is
   * the point rather than an economy: the two cannot then be different terms.
   *
   * The instance is beta normalised before anything is read off it, because `Rules.spec` leaves the
   * predicate applied rather than substituted, which its own scaladoc says and which would
   * otherwise put `(\x. ...) m` where a reader and the kernel both expect the body.
   */
  private def gcdSpecification(
    logic: Logic,
    theory: Theory,
    greatest: Kernel.Thm,
    left: FVar,
    right: FVar
  ): Either[LogicError, (Kernel.Thm, Term)] = {
    val divisor = Conv.freshVariable("g", numbers, Set(left, right))

    for {
      dividesConstant <- LogicError.lift(theory.constant(DividesName, relation))
      dividesLeft <- LogicError.lift(Term.appAll(dividesConstant, List(divisor, left)))
      dividesRight <- LogicError.lift(Term.appAll(dividesConstant, List(divisor, right)))
      both <- logic.mkConj(dividesLeft, dividesRight)
      predicate <- LogicError.lift(Term.abs(divisor, both))

      instance <- logic.rules.spec(predicate, greatest)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      conclusion <- logic
        .destImp(opened.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an implication", opened.conclusion))
      specification <- logic
        .destExistsPredicate(conclusion)
        .toRight(NotOfForm("an existential quantification", conclusion))
    } yield (opened, specification)
  }

  /**
   * The three facts about [[GcdName]], which are what a consumer of it actually holds.
   *
   * The shape is: the common divisors of a pair are non-empty because `SUC ZERO` divides
   * everything, and bounded because [[DividesBound]] says a divisor of a non-zero number is no
   * larger than it. `Peano.GreatestBounded` turns those two into a greatest common divisor, the
   * choice operator names it, and the definition of the constant rewrites the name to `NUM_GCD a b`.
   *
   * **Why the guard is a disjunction and not `~(a = ZERO)`.** The bound can come from either side,
   * and taking it from the first alone would leave `NUM_GCD ZERO b` unprovable for every `b`, where
   * the mathematics has a perfectly good answer there. The two branches are the same derivation
   * with the conjunct picked from the other side, which is why [[boundedByOneOfThem]] is one
   * function called twice.
   */
  private def gcdFacts(
    vocabulary: Vocabulary,
    gcdDefinition: Kernel.Thm,
    greatest: Kernel.Thm,
    choice: Kernel.Thm,
    bound: Kernel.Thm,
    byOne: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm, Kernel.Thm)] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      statement <- vocabulary.statement(GcdDividesLeft)
      stripped <- Logic.stripForall(statement)
      left <- stripped._1.headOption.toRight(NotOfForm("a claim about two numbers", statement))
      right <- stripped._1.lift(1).toRight(NotOfForm("a claim about two numbers", statement))
      guard <- logic
        .destImp(stripped._2)
        .map(_._1)
        .toRight(NotOfForm("an implication", stripped._2))
      assumedGuard <- LogicError.lift(Kernel.assume(guard))

      specified <- gcdSpecification(logic, vocabulary.theory, greatest, left, right)
      (opened, specification) = specified
      antecedent <- logic
        .destImp(opened.conclusion)
        .map(_._1)
        .toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(antecedent).toRight(NotOfForm("a conjunction", antecedent))
      (nonEmptyTerm, boundedTerm) = halves

      // Non-empty, because one divides everything. The cheapest fact in the file is what makes the
      // set the principle asks about a set with something in it.
      unit <- vocabulary.one
      dividesLeft <- rules.spec(left, byOne)
      dividesRight <- rules.spec(right, byOne)
      pairOfDivisors <- rules.conjIntro(dividesLeft, dividesRight)
      nonEmptyPredicate <- logic
        .destExistsPredicate(nonEmptyTerm)
        .toRight(NotOfForm("an existential quantification", nonEmptyTerm))
      nonEmpty <- rules.existsIntro(nonEmptyPredicate, unit, pairOfDivisors)

      // Bounded, by whichever of the two is not zero.
      boundPredicate <- logic
        .destExistsPredicate(boundedTerm)
        .toRight(NotOfForm("an existential quantification", boundedTerm))
      disjuncts <- logic.destDisj(guard).toRight(NotOfForm("a disjunction", guard))
      fromLeft <- boundedByOneOfThem(
        vocabulary,
        bound,
        boundPredicate,
        disjuncts._1,
        left,
        rules.conjElim1
      )
      fromRight <- boundedByOneOfThem(
        vocabulary,
        bound,
        boundPredicate,
        disjuncts._2,
        right,
        rules.conjElim2
      )
      bounded <- rules.disjElim(assumedGuard, fromLeft, fromRight)

      existence <- rules.conjIntro(nonEmpty, bounded).flatMap(rules.mp(opened, _))

      // The witness, named by the choice operator, and then renamed to the constant.
      named <- nameTheWitness(logic, choice, existence)
      reduced <- Conv
        .betaRoot(named.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, named)))

      unfolded <- Conv.unfold(gcdDefinition, List(left, right))
      carried <- Conv.apTerm(specification, unfolded)
      sides <- Conv.betaSides(carried)
      atGcd <- Conv
        .sym(sides)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, reduced)))

      common <- rules.conjElim1(atGcd)
      maximal <- rules.conjElim2(atGcd)

      first <- rules
        .conjElim1(common)
        .flatMap(rules.disch(guard, _))
        .flatMap(rules.genAll(_, List(left, right)))
        .flatMap(vocabulary.checked(GcdDividesLeft, _))
      second <- rules
        .conjElim2(common)
        .flatMap(rules.disch(guard, _))
        .flatMap(rules.genAll(_, List(left, right)))
        .flatMap(vocabulary.checked(GcdDividesRight, _))

      divisor = Conv.freshVariable("d", numbers, Set(left, right))
      third <- rules
        .spec(divisor, maximal)
        .flatMap(rules.disch(guard, _))
        .flatMap(rules.genAll(_, List(left, right, divisor)))
        .flatMap(vocabulary.checked(GcdGreatest, _))
    } yield (first, second, third)
  }

  /**
   * One branch of the bound: the named side is not zero, so it bounds every common divisor.
   *
   * `pick` is which conjunct of "divides both" the branch reaches for, and it is the only thing
   * that differs between the two calls.
   */
  private def boundedByOneOfThem(
    vocabulary: Vocabulary,
    bound: Kernel.Thm,
    boundPredicate: Term,
    disjunct: Term,
    limit: Term,
    pick: Kernel.Thm => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      assumedDisjunct <- LogicError.lift(Kernel.assume(disjunct))

      applied <- LogicError.lift(Term.app(boundPredicate, limit))
      contraction <- Conv.betaRoot(applied)
      target <- vocabulary.rightOf(contraction)
      universal <- logic
        .destForallPredicate(target)
        .toRight(NotOfForm("a universal quantification", target))

      candidate = Conv.freshVariable("k", numbers, Term.freeVariables(target))
      appliedAt <- LogicError.lift(Term.app(universal, candidate))
      contractionAt <- Conv.betaRoot(appliedAt)
      body <- vocabulary.rightOf(contractionAt)
      implication <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (premise, goal) = implication

      assumedPremise <- LogicError.lift(Kernel.assume(premise))
      divides <- pick(assumedPremise)
      split <- rules.specAll(bound, List(candidate, limit)).flatMap(rules.mp(_, divides))
      splitHalves <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isBelow, isZero) = splitHalves

      belowCase <- LogicError.lift(Kernel.assume(isBelow))
      assumedZero <- LogicError.lift(Kernel.assume(isZero))
      absurd <- rules.notElim(assumedDisjunct, assumedZero)
      zeroCase <- rules.falsityElim(goal, absurd)

      decided <- rules.disjElim(split, belowCase, zeroCase)
      implied <- rules.disch(premise, decided)
      general <- rules.gen(candidate, implied)
      result <- rules.existsIntro(boundPredicate, limit, general)
    } yield result
  }

  /**
   * `G |- ?x. P x` becomes `G |- P (select P)`, against a signature wider than `Classical`'s own.
   *
   * `Classical.witness` does this and cannot be used here: eliminating an existential means
   * building a quantifier at the domain, and `Classical.standard` has never heard of `num`. The
   * same widening `Classical.ext` takes a `Logic` parameter for, and the same reason: a polymorphic
   * axiom is stated once and instantiated where the types live.
   *
   * What comes back is the **unreduced** application, which is what `Classical.witness` documents
   * and is deliberate there; this file reduces it at the one call site, because nothing here is
   * defining a type off the result.
   */
  private def nameTheWitness(
    logic: Logic,
    choice: Kernel.Thm,
    existential: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    logic.destExistsPredicate(existential.conclusion) match {
      case None =>
        Left(NotOfForm("an existential quantification", existential.conclusion))

      case Some(predicate) =>
        Type.destFun(Term.typeOf(predicate)) match {
          case None => Left(NotOfForm("a predicate", predicate))

          case Some((domain, _)) =>
            val taken = Term.freeVariables(predicate) ++
              existential.hypotheses.flatMap(Term.freeVariables).toSet
            val chosen = Conv.freshVariable("w", domain, taken)

            for {
              instantiated <- Right(
                Kernel.instType(Map(Classical.TypeVariable -> domain), choice)
              )
              atPredicate <- logic.rules.spec(predicate, instantiated)
              atVariable <- logic.rules.spec(chosen, atPredicate)

              applied <- LogicError.lift(Term.app(predicate, chosen))
              instance <- Term.betaReduce(applied).toRight(NotOfForm("a redex", applied))
              assumed <- LogicError.lift(Kernel.assume(instance))

              satisfied <- logic.rules.mp(atVariable, assumed)
              result <- logic.rules.existsElim(existential, chosen, satisfied)
            } yield result
        }
    }

  /**
   * `|- !n q r p s. n * q + r = n * p + s /\ NUM_LT r n /\ NUM_LT s n ==> q = p /\ r = s`.
   *
   * `NUM_LE_TOTAL` decides which of the two quotients is the smaller and [[quotientsAgree]] does
   * the rest. The two branches differ only in which way round the pair goes and which of the two
   * bounds is handed over; the second turns both halves of its answer back round again.
   */
  private def remainderIsUnique(vocabulary: Vocabulary): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      statement <- vocabulary.statement(DivisionUnique)
      stripped <- Logic.stripForall(statement)
      variables = stripped._1
      modulus <- variables.headOption.toRight(NotOfForm("a claim about five numbers", statement))
      quotient <- variables.lift(1).toRight(NotOfForm("a claim about five numbers", statement))
      remainder <- variables.lift(2).toRight(NotOfForm("a claim about five numbers", statement))
      otherQuotient <- variables.lift(3).toRight(NotOfForm("a claim about five numbers", statement))
      otherRemainder <- variables.lift(4).toRight(NotOfForm("a claim about five numbers", statement))

      implication <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      premises = implication._1

      assumedPremises <- LogicError.lift(Kernel.assume(premises))
      equation <- rules.conjElim1(assumedPremises)
      bounds <- rules.conjElim2(assumedPremises)
      boundOnFirst <- rules.conjElim1(bounds)
      boundOnSecond <- rules.conjElim2(bounds)

      total <- vocabulary.fact(Peano.Total)
      split <- rules.specAll(total, List(quotient, otherQuotient))
      halves <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (firstIsSmaller, secondIsSmaller) = halves

      assumedFirst <- LogicError.lift(Kernel.assume(firstIsSmaller))
      firstCase <- quotientsAgree(
        vocabulary,
        assumedFirst,
        equation,
        boundOnFirst,
        modulus,
        quotient,
        remainder,
        otherQuotient,
        otherRemainder
      )

      // The mirror image: the same argument on the equation read the other way, and the pair that
      // comes back is `p = q /\ s = r`, which is turned round to be the same claim as the first
      // branch's. Both branches of a case analysis have to prove one proposition and these two are
      // one proposition only after that turn.
      assumedSecond <- LogicError.lift(Kernel.assume(secondIsSmaller))
      flipped <- Conv.sym(equation)
      mirrored <- quotientsAgree(
        vocabulary,
        assumedSecond,
        flipped,
        boundOnSecond,
        modulus,
        otherQuotient,
        otherRemainder,
        quotient,
        remainder
      )
      quotientsEqual <- rules.conjElim1(mirrored).flatMap(Conv.sym)
      remaindersEqual <- rules.conjElim2(mirrored).flatMap(Conv.sym)
      secondCase <- rules.conjIntro(quotientsEqual, remaindersEqual)

      decided <- rules.disjElim(split, firstCase, secondCase)
      discharged <- rules.disch(premises, decided)
      general <- rules.genAll(
        discharged,
        List(modulus, quotient, remainder, otherQuotient, otherRemainder)
      )
      result <- vocabulary.checked(DivisionUnique, general)
    } yield result
  }

  /**
   * The half of [[remainderIsUnique]] where the first quotient is the smaller of the two.
   *
   * `NUM_LE q p` says `p` is `q + d` for some `d`, and what that does to the equation is the whole
   * argument. `n * p + s` is `n * (q + d) + s`, which is `n * q + (n * d + s)`: one semiring
   * identity, decided by [[Modular.identity]] over the reals like every other identity here.
   * Cancelling `n * q` off both sides with `Peano.AddCancelsLeft` leaves `r = n * d + s`.
   *
   * Then `d` cannot be a successor. If it were, `r` would be `n + (n * j + s)`, which is
   * `NUM_LE n r`; with `NUM_LT r n`, which **is** `NUM_LE (SUC r) n`, transitivity gives
   * `NUM_LE (SUC r) r`, which is `NUM_LT r r`, which `Peano.StrictIrreflexive` denies. So `d` is
   * `ZERO`, `q + ZERO = p` gives `q = p`, and `n * ZERO + s = s` gives `r = s`.
   *
   * Only the bound on the **first** remainder takes part. The second is what the mirrored call
   * consumes, and a derivation that used both here would be using one of them twice.
   */
  private def quotientsAgree(
    vocabulary: Vocabulary,
    ordered: Kernel.Thm,
    equation: Kernel.Thm,
    bound: Kernel.Thm,
    modulus: Term,
    quotient: Term,
    remainder: Term,
    otherQuotient: Term,
    otherRemainder: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val zero = vocabulary.zeroTerm

    for {
      cancels <- vocabulary.fact(Peano.AddCancelsLeft)
      irreflexive <- vocabulary.fact(Peano.StrictIrreflexive)
      transitive <- vocabulary.fact(Peano.Transitive)
      unitLaw <- vocabulary.fact(Peano.AddAtZero)
      cases <- vocabulary.naturalFact(Natural.ZeroOrSuccessor)
      nonStrict <- vocabulary.peano.definition(Peano.NonStrictOrder)
      strict <- vocabulary.peano.definition(Peano.StrictOrder)

      // `NUM_LE q p` opened into the gap it asserts.
      unfolded <- Conv.unfold(nonStrict, List(quotient, otherQuotient))
      gapExists <- LogicError.lift(Kernel.eqMp(unfolded, ordered))

      avoid = Term.freeVariables(equation.conclusion) ++
        Term.freeVariables(bound.conclusion) ++
        Term.freeVariables(gapExists.conclusion)
      gap = Conv.freshVariable("d", numbers, avoid)
      step = Conv.freshVariable("j", numbers, avoid + gap)

      gapPredicate <- vocabulary.predicateOf(gapExists.conclusion)
      appliedGap <- LogicError.lift(Term.app(gapPredicate, gap))
      gapContraction <- Conv.betaRoot(appliedGap)
      reachingTerm <- vocabulary.rightOf(gapContraction)
      reaches <- LogicError.lift(Kernel.assume(reachingTerm))

      scaleBy <- LogicError.lift(Term.app(vocabulary.times, modulus))
      scaled <- vocabulary.product(modulus, quotient)
      scaledGap <- vocabulary.product(modulus, gap)
      tail <- vocabulary.sum(scaledGap, otherRemainder)
      regrouped <- vocabulary.sum(scaled, tail)
      sumOfGap <- vocabulary.sum(quotient, gap)
      scaledSum <- vocabulary.product(modulus, sumOfGap)
      expanded <- vocabulary.sum(scaledSum, otherRemainder)

      // `n * q + r = n * (q + d) + s = n * q + (n * d + s)`, and then cancel.
      carried <- Conv.apTerm(scaleBy, reaches)
      toGap <- Conv.sym(carried)
      onTheRight <- Conv
        .apTerm(vocabulary.plus, toGap)
        .flatMap(Conv.apThm(_, otherRemainder))
      viaGap <- Conv.trans(equation, onTheRight)
      regrouping <- vocabulary.identity(expanded, regrouped)
      chained <- Conv.trans(viaGap, regrouping)
      remainderIsTail <- rules
        .specAll(cancels, List(remainder, tail, scaled))
        .flatMap(rules.mp(_, chained))

      quotientsEqualTerm <- LogicError.lift(Term.eq(quotient, otherQuotient))
      remaindersEqualTerm <- LogicError.lift(Term.eq(remainder, otherRemainder))
      goal <- logic.mkConj(quotientsEqualTerm, remaindersEqualTerm)

      gapSplit <- rules.spec(gap, cases)
      gapHalves <- logic
        .destDisj(gapSplit.conclusion)
        .toRight(NotOfForm("a disjunction", gapSplit.conclusion))
      (gapIsZero, gapIsSuccessor) = gapHalves

      // A gap of zero: both halves fall out of the two equations already in hand.
      assumedZero <- LogicError.lift(Kernel.assume(gapIsZero))
      addFrom <- LogicError.lift(Term.app(vocabulary.plus, quotient))
      carriedZero <- Conv.apTerm(addFrom, assumedZero)
      unitAt <- rules.spec(quotient, unitLaw)
      toQuotient <- Conv.trans(carriedZero, unitAt)
      quotientsEqual <- Conv.sym(toQuotient).flatMap(Conv.trans(_, reaches))

      scaleZero <- Conv.apTerm(scaleBy, assumedZero)
      addRemainder <- Conv
        .apTerm(vocabulary.plus, scaleZero)
        .flatMap(Conv.apThm(_, otherRemainder))
      scaledZero <- vocabulary.product(modulus, zero)
      zeroTail <- vocabulary.sum(scaledZero, otherRemainder)
      vanishes <- vocabulary.identity(zeroTail, otherRemainder)
      remaindersEqual <- Conv
        .trans(remainderIsTail, addRemainder)
        .flatMap(Conv.trans(_, vanishes))
      zeroBranch <- rules.conjIntro(quotientsEqual, remaindersEqual)

      // A gap of `SUC j`: the first remainder reaches the modulus, which its own bound forbids.
      assumedSuccessor <- LogicError.lift(Kernel.assume(gapIsSuccessor))
      stepPredicate <- vocabulary.predicateOf(gapIsSuccessor)
      appliedStep <- LogicError.lift(Term.app(stepPredicate, step))
      stepContraction <- Conv.betaRoot(appliedStep)
      isStepTerm <- vocabulary.rightOf(stepContraction)
      assumedStep <- LogicError.lift(Kernel.assume(isStepTerm))

      successorOfStep <- vocabulary.next(step)
      scaledStep <- vocabulary.product(modulus, successorOfStep)
      stepTail <- vocabulary.sum(scaledStep, otherRemainder)
      scaledInner <- vocabulary.product(modulus, step)
      innerTail <- vocabulary.sum(scaledInner, otherRemainder)
      aboveModulus <- vocabulary.sum(modulus, innerTail)

      scaleStep <- Conv.apTerm(scaleBy, assumedStep)
      addStep <- Conv
        .apTerm(vocabulary.plus, scaleStep)
        .flatMap(Conv.apThm(_, otherRemainder))
      regroupStep <- vocabulary.identity(stepTail, aboveModulus)
      reachesAbove <- Conv
        .trans(remainderIsTail, addStep)
        .flatMap(Conv.trans(_, regroupStep))
      witnessed <- Conv.sym(reachesAbove)
      modulusAtMost <- vocabulary.atMost(modulus, remainder, innerTail, witnessed)

      boundNonStrict <- vocabulary.asNonStrict(remainder, modulus, bound)
      successorOfRemainder <- vocabulary.next(remainder)
      pair <- rules.conjIntro(boundNonStrict, modulusAtMost)
      chainedBound <- rules
        .specAll(transitive, List(successorOfRemainder, modulus, remainder))
        .flatMap(rules.mp(_, pair))
      unfoldedSelf <- Conv.unfold(strict, List(remainder, remainder))
      selfBelow <- Conv
        .sym(unfoldedSelf)
        .flatMap(equality => LogicError.lift(Kernel.eqMp(equality, chainedBound)))
      never <- rules.spec(remainder, irreflexive)
      absurd <- rules.notElim(never, selfBelow)
      refuted <- rules.falsityElim(goal, absurd)
      successorBranch <- rules.existsElim(assumedSuccessor, step, refuted)

      decided <- rules.disjElim(gapSplit, zeroBranch, successorBranch)
      result <- rules.existsElim(gapExists, gap, decided)
    } yield result
  }

  /* --------------------------------------------------------------- congruence */

  /**
   * `|- !k m n a b. NUM_ADD m (NUM_MUL k a) = NUM_ADD n (NUM_MUL k b) ==> NUM_CONG k m n`.
   *
   * The same shape as [[introduce]] one existential deeper: the pair of witnesses goes in and the
   * relation comes out, through the definition's own two predicates.
   */
  private def introduceCongruence(vocabulary: Vocabulary): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val k = variable("k")
    val m = variable("m")
    val n = variable("n")
    val a = variable("a")
    val b = variable("b")

    for {
      unfolded <- vocabulary.congruenceUnfoldedAt(k, m, n)
      folded <- Conv.sym(unfolded)
      body <- vocabulary.rightOf(unfolded)

      outer <- vocabulary.predicateOf(body)
      applied <- LogicError.lift(Term.app(outer, a))
      contraction <- Conv.betaRoot(applied)
      innerTerm <- vocabulary.rightOf(contraction)
      inner <- vocabulary.predicateOf(innerTerm)
      appliedInner <- LogicError.lift(Term.app(inner, b))
      innerContraction <- Conv.betaRoot(appliedInner)
      equation <- vocabulary.rightOf(innerContraction)
      assumed <- LogicError.lift(Kernel.assume(equation))

      step <- rules.existsIntro(inner, b, assumed)
      witnessed <- rules.existsIntro(outer, a, step)
      related <- LogicError.lift(Kernel.eqMp(folded, witnessed))
      discharged <- rules.disch(equation, related)
      general <- rules.genAll(discharged, List(k, m, n, a, b))
      result <- vocabulary.checked(CongIntro, general)
    } yield result
  }

  /** `|- !k m n. NUM_CONG k m n ==> (?a b. ...)`, the definition read left to right. */
  private def eliminateCongruence(vocabulary: Vocabulary): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val k = variable("k")
    val m = variable("m")
    val n = variable("n")

    for {
      unfolded <- vocabulary.congruenceUnfoldedAt(k, m, n)
      premise <- vocabulary.leftOf(unfolded)
      assumed <- LogicError.lift(Kernel.assume(premise))
      existential <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      discharged <- rules.disch(premise, existential)
      general <- rules.genAll(discharged, List(k, m, n))
      result <- vocabulary.checked(CongElim, general)
    } yield result
  }

  /**
   * A congruence premise opened: the term, the existential, the two witnesses and the equation.
   *
   * Every lemma below opens one or two of these and closes them in the reverse order, so the four
   * pieces travel together for the reason [[Opened]] gives one existential up.
   */
  private final case class OpenedCongruence(
    premise: Term,
    existential: Kernel.Thm,
    first: FVar,
    second: FVar,
    innerAssumed: Kernel.Thm,
    equation: Kernel.Thm
  )

  private def openCongruence(
    vocabulary: Vocabulary,
    modulus: Term,
    left: Term,
    right: Term,
    avoid: Set[FVar],
    firstName: String,
    secondName: String
  ): Either[LogicError, OpenedCongruence] =
    for {
      unfolded <- vocabulary.congruenceUnfoldedAt(modulus, left, right)
      premise <- vocabulary.leftOf(unfolded)
      assumed <- LogicError.lift(Kernel.assume(premise))
      existential <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      pieces <- vocabulary.openTwo(existential, avoid, firstName, secondName)
      (first, second, innerAssumed, equation) = pieces
    } yield OpenedCongruence(premise, existential, first, second, innerAssumed, equation)

  private def closeCongruence(
    vocabulary: Vocabulary,
    opened: OpenedCongruence,
    reached: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    vocabulary.closeTwo(opened.existential, opened.first, opened.second, opened.innerAssumed, reached)

  /** `|- !k m. NUM_CONG k m m`, with `ZERO` twice as the witnesses. */
  private def congruentToItself(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val k = variable("k")
    val m = variable("m")
    val zero = vocabulary.zeroTerm

    for {
      scaled <- vocabulary.product(k, zero)
      side <- vocabulary.sum(m, scaled)
      equation = Conv.refl(side)
      related <- vocabulary.concludeCongruence(introduction, k, m, m, zero, zero, equation)
      general <- vocabulary.rules.genAll(related, List(k, m))
      result <- vocabulary.checked(CongRefl, general)
    } yield result
  }

  /** `|- !k m n. NUM_CONG k m n ==> NUM_CONG k n m`, with the two witnesses swapped. */
  private def congruentSymmetrically(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val k = variable("k")
    val m = variable("m")
    val n = variable("n")

    for {
      opened <- openCongruence(vocabulary, k, m, n, Set(k, m, n), "a", "b")
      flipped <- Conv.sym(opened.equation)
      related <- vocabulary.concludeCongruence(
        introduction,
        k,
        n,
        m,
        opened.second,
        opened.first,
        flipped
      )
      closed <- closeCongruence(vocabulary, opened, related)
      discharged <- rules.disch(opened.premise, closed)
      general <- rules.genAll(discharged, List(k, m, n))
      result <- vocabulary.checked(CongSym, general)
    } yield result
  }

  /**
   * `|- !k m n p. NUM_CONG k m n ==> NUM_CONG k n p ==> NUM_CONG k m p`.
   *
   * `m + k a = n + k b` and `n + k c = p + k d` give `m + k (a + c) = p + k (d + b)`, by
   * regrouping each side so that the middle term appears and substituting through it twice:
   *
   * {{{
   *   m + k (a + c) = (m + k a) + k c = (n + k b) + k c = (n + k c) + k b = (p + k d) + k b
   *                 = p + k (d + b)
   * }}}
   *
   * Three of those five steps are identities between naturals and go to [[Vocabulary.identity]];
   * the other two are one congruence each.
   */
  private def congruentTransitively(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val k = variable("k")
    val m = variable("m")
    val n = variable("n")
    val p = variable("p")
    val named = Set(k, m, n, p)

    for {
      first <- openCongruence(vocabulary, k, m, n, named, "a", "b")
      second <- openCongruence(vocabulary, k, n, p, named + first.first + first.second, "c", "d")

      scaledC <- vocabulary.product(k, second.first)
      scaledB <- vocabulary.product(k, first.second)

      leftWitness <- vocabulary.sum(first.first, second.first)
      rightWitness <- vocabulary.sum(second.second, first.second)
      scaledLeft <- vocabulary.product(k, leftWitness)
      scaledRight <- vocabulary.product(k, rightWitness)
      target <- vocabulary.sum(m, scaledLeft)
      goalRight <- vocabulary.sum(p, scaledRight)

      // `m + k (a + c) = (m + k a) + k c`
      openedLeft <- vocabulary.leftOf(first.equation).flatMap(vocabulary.sum(_, scaledC))
      spread <- vocabulary.identity(target, openedLeft)

      // `(m + k a) + k c = (n + k b) + k c`
      carriedFirst <- Conv.apTerm(vocabulary.plus, first.equation).flatMap(Conv.apThm(_, scaledC))

      // `(n + k b) + k c = (n + k c) + k b`
      exchangedLeft <- vocabulary.rightOf(carriedFirst)
      middle <- vocabulary.leftOf(second.equation).flatMap(vocabulary.sum(_, scaledB))
      exchanged <- vocabulary.identity(exchangedLeft, middle)

      // `(n + k c) + k b = (p + k d) + k b`
      carriedSecond <- Conv.apTerm(vocabulary.plus, second.equation).flatMap(Conv.apThm(_, scaledB))

      // `(p + k d) + k b = p + k (d + b)`
      gathered <- vocabulary.rightOf(carriedSecond).flatMap(vocabulary.identity(_, goalRight))

      equation <- Conv
        .trans(spread, carriedFirst)
        .flatMap(Conv.trans(_, exchanged))
        .flatMap(Conv.trans(_, carriedSecond))
        .flatMap(Conv.trans(_, gathered))

      related <- vocabulary.concludeCongruence(
        introduction,
        k,
        m,
        p,
        leftWitness,
        rightWitness,
        equation
      )
      withoutSecond <- closeCongruence(vocabulary, second, related)
      withoutFirst <- closeCongruence(vocabulary, first, withoutSecond)
      dischargedSecond <- rules.disch(second.premise, withoutFirst)
      dischargedFirst <- rules.disch(first.premise, dischargedSecond)
      general <- rules.genAll(dischargedFirst, List(k, m, n, p))
      result <- vocabulary.checked(CongTrans, general)
    } yield result
  }

  /**
   * `|- !k m n p q. NUM_CONG k m n ==> NUM_CONG k p q ==> NUM_CONG k (m + p) (n + q)`.
   *
   * `(m + p) + k (a + c) = (m + k a) + (p + k c) = (n + k b) + (q + k d) = (n + q) + k (b + d)`.
   * The middle step is the two witness equations added, which is one congruence; the outer two are
   * identities.
   */
  private def congruenceAdds(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    combine(vocabulary, introduction, CongAdd, joinBySum = true)

  /**
   * `|- !k m n p q. NUM_CONG k m n ==> NUM_CONG k p q ==> NUM_CONG k (m * p) (n * q)`.
   *
   * The two witness equations multiplied, and the witnesses read off the expanded product:
   * `(m + k a)(p + k c) = m p + k (m c + a p + k (a c))`, with the same shape on the other side.
   * That expansion is a five-variable semiring identity and is exactly what
   * [[Vocabulary.identity]] exists for; written out from distributivity it is about a dozen
   * commutations and would be the longest derivation in the file.
   */
  private def congruenceMultiplies(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    combine(vocabulary, introduction, CongMul, joinBySum = false)

  /**
   * The two compatibility lemmas, which are one derivation with two joins.
   *
   * They differ in three places and nowhere else: the operation the two numbers are combined by,
   * the operation the two witness equations are joined by, and what the witnesses come out as.
   * Writing them twice would be two chances for the shape to drift; the identities themselves are
   * decided rather than written, so the shared code carries no algebra of its own.
   */
  private def combine(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm,
    name: String,
    joinBySum: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val k = variable("k")
    val m = variable("m")
    val n = variable("n")
    val p = variable("p")
    val q = variable("q")
    val named = Set(k, m, n, p, q)

    def join(left: Term, right: Term): Either[LogicError, Term] =
      if (joinBySum) vocabulary.sum(left, right) else vocabulary.product(left, right)

    def joined(left: Kernel.Thm, right: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      if (joinBySum) vocabulary.addSides(left, right) else vocabulary.multiplySides(left, right)

    /**
     * The witness for one side: `a + c` for a sum, and `m c + a p + k (a c)` for a product.
     *
     * The product's witness is read off the expansion and not guessed: `(x + k u)(y + k v)` is
     * `x y + k (x v + u y + k (u v))`, so the multiple of `k` left over carries the two cross terms
     * and the doubly-scaled one.
     */
    def witnessFor(
      leftNumber: Term,
      leftWitness: Term,
      rightNumber: Term,
      rightWitness: Term
    ): Either[LogicError, Term] =
      if (joinBySum) vocabulary.sum(leftWitness, rightWitness)
      else
        for {
          firstCross <- vocabulary.product(leftNumber, rightWitness)
          secondCross <- vocabulary.product(leftWitness, rightNumber)
          crossed <- vocabulary.sum(firstCross, secondCross)
          both <- vocabulary.product(leftWitness, rightWitness)
          scaled <- vocabulary.product(k, both)
          whole <- vocabulary.sum(crossed, scaled)
        } yield whole

    for {
      first <- openCongruence(vocabulary, k, m, n, named, "a", "b")
      second <- openCongruence(vocabulary, k, p, q, named + first.first + first.second, "c", "d")

      leftWitness <- witnessFor(m, first.first, p, second.first)
      rightWitness <- witnessFor(n, first.second, q, second.second)

      leftNumber <- join(m, p)
      rightNumber <- join(n, q)
      scaledLeft <- vocabulary.product(k, leftWitness)
      scaledRight <- vocabulary.product(k, rightWitness)
      target <- vocabulary.sum(leftNumber, scaledLeft)
      goalRight <- vocabulary.sum(rightNumber, scaledRight)

      combined <- joined(first.equation, second.equation)
      opening <- vocabulary.leftOf(combined).flatMap(vocabulary.identity(target, _))
      closing <- vocabulary.rightOf(combined).flatMap(vocabulary.identity(_, goalRight))
      equation <- Conv.trans(opening, combined).flatMap(Conv.trans(_, closing))

      related <- vocabulary.concludeCongruence(
        introduction,
        k,
        leftNumber,
        rightNumber,
        leftWitness,
        rightWitness,
        equation
      )
      withoutSecond <- closeCongruence(vocabulary, second, related)
      withoutFirst <- closeCongruence(vocabulary, first, withoutSecond)
      dischargedSecond <- rules.disch(second.premise, withoutFirst)
      dischargedFirst <- rules.disch(first.premise, dischargedSecond)
      general <- rules.genAll(dischargedFirst, List(k, m, n, p, q))
      result <- vocabulary.checked(name, general)
    } yield result
  }

  /**
   * `|- !k m. NUM_CONG k (NUM_ADD m k) m`.
   *
   * Witnesses `ZERO` and `SUC ZERO`: `(m + k) + k * ZERO = m + k * SUC ZERO`, which is an identity.
   * The fact that makes `k` a modulus rather than an unused parameter.
   */
  private def modulusIsFree(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val k = variable("k")
    val m = variable("m")
    val zero = vocabulary.zeroTerm

    for {
      unit <- vocabulary.one
      shifted <- vocabulary.sum(m, k)
      leftScaled <- vocabulary.product(k, zero)
      rightScaled <- vocabulary.product(k, unit)
      left <- vocabulary.sum(shifted, leftScaled)
      right <- vocabulary.sum(m, rightScaled)
      equation <- vocabulary.identity(left, right)
      related <- vocabulary.concludeCongruence(
        introduction,
        k,
        shifted,
        m,
        zero,
        unit,
        equation
      )
      general <- vocabulary.rules.genAll(related, List(k, m))
      result <- vocabulary.checked(CongModulus, general)
    } yield result
  }

  /* -------------------------------------- the quotient and the remainder as terms */

  /**
   * `|- number = ZERO \/ NUM_LT ZERO number`, which is the split every claim about a modulus needs.
   *
   * `Peano.Trichotomy` at `ZERO` and the number, with the third case refused by
   * `Peano.NotBelowZero` and the second turned round. It is a fact about the order and mentions
   * nothing this file defines, so `Peano` is where it would live if it had a second consumer; it
   * has three, all of them in this file, which is why it is a derivation here rather than a lemma
   * there. The five order facts this file used to hold and moved on 2026-09-11 are the precedent
   * for the move, and the count is the reason it has not been made.
   */
  private def zeroOrPositive(vocabulary: Vocabulary, number: Term): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val zero = vocabulary.zeroTerm

    for {
      trichotomy <- vocabulary.fact(Peano.Trichotomy)
      notBelowZero <- vocabulary.fact(Peano.NotBelowZero)

      isZero <- LogicError.lift(Term.eq(number, zero))
      positive <- vocabulary.belowTerm(zero, number)
      goal <- logic.mkDisj(isZero, positive)

      split <- rules.specAll(trichotomy, List(zero, number))
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (below, rest) = branches

      assumedBelow <- LogicError.lift(Kernel.assume(below))
      belowCase <- rules.disjIntro2(isZero, assumedBelow)

      restBranches <- logic.destDisj(rest).toRight(NotOfForm("a disjunction", rest))
      (equal, above) = restBranches

      assumedEqual <- LogicError.lift(Kernel.assume(equal))
      flipped <- Conv.sym(assumedEqual)
      equalCase <- rules.disjIntro1(positive, flipped)

      assumedAbove <- LogicError.lift(Kernel.assume(above))
      never <- rules.spec(number, notBelowZero)
      absurd <- rules.notElim(never, assumedAbove)
      aboveCase <- rules.falsityElim(goal, absurd)

      assumedRest <- LogicError.lift(Kernel.assume(rest))
      decidedRest <- rules.disjElim(assumedRest, equalCase, aboveCase)
      decided <- rules.disjElim(split, belowCase, decidedRest)
    } yield decided
  }

  /** `G |- F`, from a number assumed positive and proved to be `ZERO`. */
  private def contradictPositive(
    vocabulary: Vocabulary,
    positive: Kernel.Thm,
    isZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val zero = vocabulary.zeroTerm

    for {
      irreflexive <- vocabulary.fact(Peano.StrictIrreflexive)
      partial <- LogicError.lift(Term.app(vocabulary.strict, zero))
      carried <- Conv.apTerm(partial, isZero)
      atZero <- LogicError.lift(Kernel.eqMp(carried, positive))
      never <- rules.spec(zero, irreflexive)
      absurd <- rules.notElim(never, atZero)
    } yield absurd
  }

  /**
   * The unfolding of a chosen function at its arguments, and the predicate it chooses from.
   *
   * Both halves together for the reason [[gcdSpecification]] gives one constant earlier: the
   * predicate the derivation proves something about has to be the predicate the definition carries,
   * and reading it off the unfolding is the only way to be sure there is one of them.
   */
  private def chosenAt(
    vocabulary: Vocabulary,
    definition: Kernel.Thm,
    arguments: List[Term]
  ): Either[LogicError, (Kernel.Thm, Term)] =
    for {
      unfolded <- Conv.unfold(definition, arguments)
      right <- vocabulary.rightOf(unfolded)
      predicate <- right match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("a value named by the choice operator", other))
      }
    } yield (unfolded, predicate)

  /**
   * `|- P (C args)`, from a proof that something at all satisfies `P`.
   *
   * The three steps [[gcdFacts]] takes inline, named because there are three call sites now: the
   * choice operator names a witness, the definition renames it to the constant, and the predicate
   * is carried across that renaming rather than restated at the new term.
   */
  private def satisfiedByTheChoice(
    vocabulary: Vocabulary,
    choice: Kernel.Thm,
    unfolded: Kernel.Thm,
    predicate: Term,
    existence: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      named <- nameTheWitness(vocabulary.logic, choice, existence)
      reduced <- Conv
        .betaRoot(named.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, named)))
      carried <- Conv.apTerm(predicate, unfolded)
      sides <- Conv.betaSides(carried)
      result <- Conv
        .sym(sides)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, reduced)))
    } yield result

  /** The bound below `ZERO` that no number satisfies, turned into whatever the caller wanted. */
  private def refuteBound(
    vocabulary: Vocabulary,
    subject: Term,
    bounded: Kernel.Thm,
    goal: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      notBelowZero <- vocabulary.fact(Peano.NotBelowZero)
      never <- vocabulary.rules.spec(subject, notBelowZero)
      absurd <- vocabulary.rules.notElim(never, bounded)
      result <- vocabulary.rules.falsityElim(goal, absurd)
    } yield result

  /** The quotient's impossible branch: an existential whose body carries the bound. */
  private def refuteQuantifiedBound(
    vocabulary: Vocabulary
  )(existential: Kernel.Thm, goal: Term): Either[LogicError, Kernel.Thm] = {
    val avoid = Term.freeVariables(goal) ++ Term.freeVariables(existential.conclusion)

    for {
      opening <- vocabulary.openAll(existential, avoid, List("r"))
      subject <- opening.variables.headOption
        .toRight(NotOfForm("a claim about one number", existential.conclusion))
      bounded <- vocabulary.rules.conjElim2(opening.body)
      refuted <- refuteBound(vocabulary, subject, bounded, goal)
      closed <- vocabulary.closeAll(opening, refuted)
    } yield closed
  }

  /** The remainder's impossible branch, where the number the bound is about is already named. */
  private def refutePlainBound(
    vocabulary: Vocabulary
  )(conjunction: Kernel.Thm, goal: Term): Either[LogicError, Kernel.Thm] =
    for {
      bounded <- vocabulary.rules.conjElim2(conjunction)
      subject <- bounded.conclusion match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a bound below a number", other))
      }
      refuted <- refuteBound(vocabulary, subject, bounded, goal)
    } yield refuted

  /**
   * `|- !m. C m ZERO = value`, for whichever of the two functions `definition` defines.
   *
   * At a modulus of `ZERO` the first disjunct of either predicate asks for a remainder strictly
   * below `ZERO`, so the second is all that is left and it pins the value. The two calls differ in
   * three places: the value, which is `ZERO` for the quotient and `m` for the remainder; and the
   * shape of the disjunct to be refused, which is an existential for the quotient and a plain
   * conjunction for the remainder, whose own predicate has already bound the number the bound is
   * about.
   *
   * The fallback conjunction is **compared** against the one built here before it is used. A
   * predicate whose second disjunct drifted from `n = ZERO /\ x = value` would otherwise be
   * discovered several steps later as a mismatch about something else.
   */
  private def valueAtZeroModulus(
    vocabulary: Vocabulary,
    choice: Kernel.Thm,
    definition: Kernel.Thm,
    name: String,
    value: Term => Term,
    refute: (Kernel.Thm, Term) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val m = variable("m")
    val zero = vocabulary.zeroTerm
    val chosen = value(m)

    for {
      pair <- chosenAt(vocabulary, definition, List(m, zero))
      (unfolded, predicate) = pair

      applied <- LogicError.lift(Term.app(predicate, chosen))
      contraction <- Conv.betaRoot(applied)
      body <- vocabulary.rightOf(contraction)
      halves <- logic.destDisj(body).toRight(NotOfForm("a disjunction", body))
      (impossible, fallback) = halves

      trivial <- rules.conjIntro(Conv.refl(zero), Conv.refl(chosen))
      _ <-
        if (trivial.conclusion == fallback) Right(())
        else Left(NotOfForm(s"the fallback $fallback", trivial.conclusion))

      injected <- rules.disjIntro2(impossible, trivial)
      existence <- rules.existsIntro(predicate, chosen, injected)
      satisfied <- satisfiedByTheChoice(vocabulary, choice, unfolded, predicate, existence)

      branches <- logic
        .destDisj(satisfied.conclusion)
        .toRight(NotOfForm("a disjunction", satisfied.conclusion))
      (left, right) = branches

      assumedRight <- LogicError.lift(Kernel.assume(right))
      fromRight <- rules.conjElim2(assumedRight)
      assumedLeft <- LogicError.lift(Kernel.assume(left))
      refuted <- refute(assumedLeft, fromRight.conclusion)

      decided <- rules.disjElim(satisfied, refuted, fromRight)
      general <- rules.gen(m, decided)
      result <- vocabulary.checked(name, general)
    } yield result
  }

  /** `|- !m. NUM_DIV m ZERO = ZERO`. */
  private def quotientAtZero(
    vocabulary: Vocabulary,
    choice: Kernel.Thm,
    definition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    valueAtZeroModulus(
      vocabulary,
      choice,
      definition,
      DivAtZero,
      _ => vocabulary.zeroTerm,
      refuteQuantifiedBound(vocabulary)
    )

  /** `|- !m. NUM_MOD m ZERO = m`. */
  private def remainderAtZero(
    vocabulary: Vocabulary,
    choice: Kernel.Thm,
    definition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    valueAtZeroModulus(
      vocabulary,
      choice,
      definition,
      ModAtZero,
      dividend => dividend,
      refutePlainBound(vocabulary)
    )

  /**
   * The two facts about the pair that hold above `ZERO`, with the guard left standing.
   *
   * What comes back is the guard as a term and the two theorems under it, because the callers want
   * them differently: the bound keeps its hypothesis and is discharged into [[ModBelow]], and the
   * equation is one branch of the case analysis [[divisionEverywhere]] runs.
   *
   * The shape of the derivation is the same twice. [[Division]] says a pair exists, so the
   * quotient's predicate has something in it, so the choice satisfies it; the first disjunct of
   * what the choice satisfies is then exactly the existence the remainder's predicate needs, so
   * the choice satisfies that too. The second disjunct is refused both times by the guard: a
   * modulus that is `ZERO` and positive at once is refused by `Peano.StrictIrreflexive`.
   */
  private def divisionAboveZero(
    vocabulary: Vocabulary,
    choice: Kernel.Thm,
    quotientDefinition: Kernel.Thm,
    remainderDefinition: Kernel.Thm,
    division: Kernel.Thm
  ): Either[LogicError, (Term, Kernel.Thm, Kernel.Thm)] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val m = variable("m")
    val n = variable("n")
    val zero = vocabulary.zeroTerm

    /** The first disjunct of what the choice satisfies, with the second refused by the guard. */
    def realCase(satisfied: Kernel.Thm, positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        branches <- logic
          .destDisj(satisfied.conclusion)
          .toRight(NotOfForm("a disjunction", satisfied.conclusion))
        (real, fallback) = branches
        assumedReal <- LogicError.lift(Kernel.assume(real))
        assumedFallback <- LogicError.lift(Kernel.assume(fallback))
        modulusIsZero <- rules.conjElim1(assumedFallback)
        absurd <- contradictPositive(vocabulary, positive, modulusIsZero)
        refuted <- rules.falsityElim(real, absurd)
        decided <- rules.disjElim(satisfied, assumedReal, refuted)
      } yield decided

    for {
      guard <- vocabulary.belowTerm(zero, n)
      positive <- LogicError.lift(Kernel.assume(guard))

      existence <- rules.specAll(division, List(n, m)).flatMap(rules.mp(_, positive))

      quotientPair <- chosenAt(vocabulary, quotientDefinition, List(m, n))
      (quotientUnfolded, quotientPredicate) = quotientPair

      opened <- vocabulary.openAll(existence, Set(m, n), List("q", "r"))
      quotientVariable <- opened.variables.headOption
        .toRight(NotOfForm("a claim about two numbers", existence.conclusion))
      remainderVariable <- opened.variables
        .lift(1)
        .toRight(NotOfForm("a claim about two numbers", existence.conclusion))

      appliedQuotient <- LogicError.lift(Term.app(quotientPredicate, quotientVariable))
      quotientContraction <- Conv.betaRoot(appliedQuotient)
      quotientBody <- vocabulary.rightOf(quotientContraction)
      quotientHalves <- logic
        .destDisj(quotientBody)
        .toRight(NotOfForm("a disjunction", quotientBody))
      innerPredicate <- vocabulary.predicateOf(quotientHalves._1)
      witnessed <- rules.existsIntro(innerPredicate, remainderVariable, opened.body)
      injected <- rules.disjIntro1(quotientHalves._2, witnessed)
      atQuotient <- rules.existsIntro(quotientPredicate, quotientVariable, injected)
      quotientExists <- vocabulary.closeAll(opened, atQuotient)

      quotientSatisfied <- satisfiedByTheChoice(
        vocabulary,
        choice,
        quotientUnfolded,
        quotientPredicate,
        quotientExists
      )
      remainderExistsAt <- realCase(quotientSatisfied, positive)

      remainderPair <- chosenAt(vocabulary, remainderDefinition, List(m, n))
      (remainderUnfolded, remainderPredicate) = remainderPair

      openedRemainder <- vocabulary.openAll(
        remainderExistsAt,
        Set(m, n) ++ Term.freeVariables(remainderExistsAt.conclusion),
        List("r")
      )
      remainderWitness <- openedRemainder.variables.headOption
        .toRight(NotOfForm("a claim about one number", remainderExistsAt.conclusion))
      appliedRemainder <- LogicError.lift(Term.app(remainderPredicate, remainderWitness))
      remainderContraction <- Conv.betaRoot(appliedRemainder)
      remainderBody <- vocabulary.rightOf(remainderContraction)
      remainderHalves <- logic
        .destDisj(remainderBody)
        .toRight(NotOfForm("a disjunction", remainderBody))
      injectedRemainder <- rules.disjIntro1(remainderHalves._2, openedRemainder.body)
      atRemainder <- rules.existsIntro(remainderPredicate, remainderWitness, injectedRemainder)
      remainderExists <- vocabulary.closeAll(openedRemainder, atRemainder)

      remainderSatisfied <- satisfiedByTheChoice(
        vocabulary,
        choice,
        remainderUnfolded,
        remainderPredicate,
        remainderExists
      )
      core <- realCase(remainderSatisfied, positive)
      equation <- rules.conjElim1(core)
      bound <- rules.conjElim2(core)
    } yield (guard, equation, bound)
  }

  /**
   * `|- !m n. m = NUM_ADD (NUM_MUL n (NUM_DIV m n)) (NUM_MOD m n)`, with no hypothesis.
   *
   * The positive case is [[divisionAboveZero]]'s equation and the case at `ZERO` is the two
   * at-zero lemmas carried into the goal: the modulus, the quotient and the remainder each become
   * what they are there, and what is left is `NUM_MUL ZERO ZERO + m = m`, which is an identity.
   */
  private def divisionEverywhere(
    vocabulary: Vocabulary,
    equation: Kernel.Thm,
    quotientAtZero: Kernel.Thm,
    remainderAtZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val m = variable("m")
    val n = variable("n")
    val zero = vocabulary.zeroTerm

    for {
      split <- zeroOrPositive(vocabulary, n)
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isZero, _) = branches
      assumedZero <- LogicError.lift(Kernel.assume(isZero))

      quotientPartial <- LogicError.lift(Term.app(vocabulary.quotientConstant, m))
      quotientMoves <- Conv.apTerm(quotientPartial, assumedZero)
      quotientVanishes <- rules.spec(m, quotientAtZero)
      quotientIsZero <- Conv.trans(quotientMoves, quotientVanishes)
      scaled <- vocabulary.multiplySides(assumedZero, quotientIsZero)

      remainderPartial <- LogicError.lift(Term.app(vocabulary.remainderConstant, m))
      remainderMoves <- Conv.apTerm(remainderPartial, assumedZero)
      remainderIsDividend <- rules.spec(m, remainderAtZero)
      remainderMovesToM <- Conv.trans(remainderMoves, remainderIsDividend)

      combined <- vocabulary.addSides(scaled, remainderMovesToM)
      emptyProduct <- vocabulary.product(zero, zero)
      padded <- vocabulary.sum(emptyProduct, m)
      collapses <- vocabulary.identity(padded, m)
      zeroCase <- Conv.trans(combined, collapses)

      positiveCase <- Conv.sym(equation)
      decided <- rules.disjElim(split, zeroCase, positiveCase)
      general <- rules.genAll(decided, List(m, n))
      result <- vocabulary.checked(DivisionAt, general)
    } yield result
  }

  /** `|- !m n. NUM_LT ZERO n ==> NUM_LT (NUM_MOD m n) n`, the bound with its guard discharged. */
  private def remainderIsBelow(
    vocabulary: Vocabulary,
    guard: Term,
    bound: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      discharged <- vocabulary.rules.disch(guard, bound)
      general <- vocabulary.rules.genAll(discharged, List(variable("m"), variable("n")))
      result <- vocabulary.checked(ModBelow, general)
    } yield result

  /**
   * `|- !m n q r. m = NUM_ADD (NUM_MUL n q) r /\ NUM_LT r n ==> q = NUM_DIV m n /\ r = NUM_MOD m n`.
   *
   * [[DivisionUnique]] at the caller's pair and the pair the constants name. The case at a modulus
   * of `ZERO` never arises and still has to be refused: `NUM_LT r n` with `n` at `ZERO` is a bound
   * below `ZERO`, which is what [[refuteBound]] closes, and the whole branch is there because the
   * two facts about the constants are guarded and this statement is not.
   */
  /**
   * The two halves of a doubled range, both out of [[DivisionDetermined]] and one rewrite.
   *
   * Written once for both because they differ only in the witness pair: `(ZERO, m)` against
   * `(SUC ZERO, m)`, and in the numerator that pair decomposes, `m` against `NUM_ADD n m`. The
   * bound `NUM_LT m n` is the same hypothesis in both and is discharged at the end rather than
   * assumed into the statement.
   *
   * The rewrite is the whole of the arithmetic: `NUM_MUL n ZERO = ZERO` then `NUM_ADD ZERO m = m`
   * for the first, `NUM_MUL n (SUC ZERO) = n` for the second, and each side is then the same term
   * and reflexivity closes it.
   */
  private def divisionInTheHalf(
    vocabulary: Vocabulary,
    determined: Kernel.Thm,
    which: String
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val m = variable("m")
    val n = variable("n")

    for {
      unit <- vocabulary.one
      quotient <- if (which == DivisionBelow) Right(vocabulary.zeroTerm) else Right(unit)
      numerator <- if (which == DivisionBelow) Right(m) else vocabulary.sum(n, m)
      scaled <- vocabulary.product(n, quotient)
      whole <- vocabulary.sum(scaled, m)
      equation <- LogicError.lift(Term.eq(numerator, whole))

      mulAtZero <- vocabulary.fact(Peano.MulAtZero)
      zeroPlus <- vocabulary.fact(Peano.ZeroPlus)
      timesOne <- vocabulary.fact(Peano.TimesOne)
      rules <- Rewrite.Rule.all(logic, Vector(mulAtZero, zeroPlus, timesOne))
      rewritten <- Rewrite.rewrite(rules, equation)
      sides <- Term.destEq(rewritten.conclusion).toRight(NotOfForm("an equation", equation))
      closed <- Term.destEq(sides._2).toRight(NotOfForm("two sides", sides._2))
      _ <-
        if (closed._1 == closed._2) Right(())
        else Left(NotOfForm("two sides the arithmetic brings together", sides._2))
      backwards <- Conv.sym(rewritten)
      witness <- LogicError.lift(Kernel.eqMp(backwards, Kernel.refl(closed._1)))

      boundTerm <- vocabulary.belowTerm(m, n)
      bound <- LogicError.lift(Kernel.assume(boundTerm))
      premises <- logic.rules.conjIntro(witness, bound)
      instance <- List(numerator, n, quotient, m)
        .foldLeft[Either[LogicError, Kernel.Thm]](Right(determined)) { (soFar, argument) =>
          soFar.flatMap(theorem => logic.rules.spec(argument, theorem))
        }
      applied <- logic.rules.mp(instance, premises)
      // BOTH EQUATIONS ARE TURNED ROUND, and that is not cosmetic. `DivisionDetermined`
      // concludes `q = NUM_DIV m n`, with the division on the RIGHT, because it is written as
      // "the witness you exhibited is the quotient". Left that way, each of these is a rewrite
      // rule that EXPANDS: it would replace `ZERO` by a division everywhere it matched. Turned
      // round they contract, which is what a caller wants and what the name promises. An
      // equation can be true and be an unusable rule, and nothing about its truth says which.
      firstHalf <- logic.rules.conjElim1(applied).flatMap(Conv.sym)
      secondHalf <- logic.rules.conjElim2(applied).flatMap(Conv.sym)
      oriented <- logic.rules.conjIntro(firstHalf, secondHalf)
      discharged <- logic.rules.disch(boundTerm, oriented)
      general <- logic.rules.genAll(discharged, List(m, n))
      result <- vocabulary.checked(which, general)
    } yield result
  }

  private def divisionIsDetermined(
    vocabulary: Vocabulary,
    divisionAt: Kernel.Thm,
    modBelow: Kernel.Thm,
    unique: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val m = variable("m")
    val n = variable("n")
    val q = variable("q")
    val r = variable("r")

    for {
      scaled <- vocabulary.product(n, q)
      whole <- vocabulary.sum(scaled, r)
      equationTerm <- LogicError.lift(Term.eq(m, whole))
      boundTerm <- vocabulary.belowTerm(r, n)
      premises <- logic.mkConj(equationTerm, boundTerm)
      assumed <- LogicError.lift(Kernel.assume(premises))
      stated <- rules.conjElim1(assumed)
      bounded <- rules.conjElim2(assumed)

      quotient <- vocabulary.quotient(m, n)
      remainder <- vocabulary.remainder(m, n)
      quotientsAgree <- LogicError.lift(Term.eq(q, quotient))
      remaindersAgree <- LogicError.lift(Term.eq(r, remainder))
      goal <- logic.mkConj(quotientsAgree, remaindersAgree)

      split <- zeroOrPositive(vocabulary, n)
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isZero, _) = branches

      assumedZero <- LogicError.lift(Kernel.assume(isZero))
      partial <- LogicError.lift(Term.app(vocabulary.strict, r))
      carried <- Conv.apTerm(partial, assumedZero)
      belowZero <- LogicError.lift(Kernel.eqMp(carried, bounded))
      zeroCase <- refuteBound(vocabulary, r, belowZero, goal)

      assumedPositive <- LogicError.lift(Kernel.assume(branches._2))
      theirs <- rules.specAll(divisionAt, List(m, n)).flatMap(Conv.sym)
      theirBound <- rules.specAll(modBelow, List(m, n)).flatMap(rules.mp(_, assumedPositive))
      joined <- Conv.sym(stated).flatMap(Conv.trans(_, theirs))
      bounds <- rules.conjIntro(bounded, theirBound)
      all <- rules.conjIntro(joined, bounds)
      instance <- rules.specAll(unique, List(n, q, r, quotient, remainder))
      positiveCase <- rules.mp(instance, all)

      decided <- rules.disjElim(split, zeroCase, positiveCase)
      discharged <- rules.disch(premises, decided)
      general <- rules.genAll(discharged, List(m, n, q, r))
      result <- vocabulary.checked(DivisionDetermined, general)
    } yield result
  }

  /* ------------------------------------------------ Bezout, and what stands on it */

  /**
   * `|- !a b c. NUM_DIVIDES a b ==> NUM_DIVIDES a (NUM_ADD b c) ==> NUM_DIVIDES a c`.
   *
   * The subtraction this file does not have, stated additively. Both premises give a witness,
   * `b = a * s` and `b + c = a * t`, so `a * s + c = a * t`, and `NUM_LE_TOTAL` decides which of
   * `s` and `t` is the larger.
   *
   * With `s` below `t` the gap is the answer: `t` is `s + e`, the right side becomes
   * `a * s + a * e`, cancelling the summand `a * s` leaves `c = a * e`, and `a * e` is the witness.
   * With `t` below `s` the same moves leave `a * t + (a * e + c) = a * t`, so `a * e + c` is `ZERO`
   * and so is `c`, and [[DividesZero]] closes it. Nothing is taken away in either branch, which is
   * the whole reason the statement is shaped this way rather than as a difference.
   */
  private def dividesTheOtherSummand(
    vocabulary: Vocabulary,
    introduction: Kernel.Thm,
    atZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")
    val c = variable("c")
    val s = variable("s")
    val t = variable("t")
    val named = Set(a, b, c, s, t)

    for {
      cancelsLeft <- vocabulary.fact(Peano.AddCancelsLeft)
      cancels <- vocabulary.fact(Peano.AddCancels)
      sumIsZero <- vocabulary.fact(Peano.SumIsZero)
      total <- vocabulary.fact(Peano.Total)
      nonStrict <- vocabulary.peano.definition(Peano.NonStrictOrder)

      first <- vocabulary.assumeDivides(a, b, s)
      together <- vocabulary.sum(b, c)
      second <- vocabulary.assumeDivides(a, together, t)

      goal <- vocabulary.dividing(a, c)
      scaledFirst <- vocabulary.product(a, s)
      scaledSecond <- vocabulary.product(a, t)

      carried <- Conv.apTerm(vocabulary.plus, first.equation).flatMap(Conv.apThm(_, c))
      base <- Conv.sym(carried).flatMap(Conv.trans(_, second.equation))

      split <- rules.specAll(total, List(s, t))
      halves <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (firstIsSmaller, secondIsSmaller) = halves

      // `t` is `s + e`, so what is left over is `a * e`.
      assumedFirst <- LogicError.lift(Kernel.assume(firstIsSmaller))
      firstGap <- Conv
        .unfold(nonStrict, List(s, t))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumedFirst)))
      firstOpening <- vocabulary.openAll(firstGap, named, List("e"))
      firstStep <- firstOpening.variables.headOption
        .toRight(NotOfForm("a gap between two numbers", firstGap.conclusion))
      firstScaledGap <- vocabulary.product(a, firstStep)
      firstSum <- vocabulary.sum(scaledFirst, firstScaledGap)
      scaleBy <- LogicError.lift(Term.app(vocabulary.times, a))
      firstExpanded <- Conv.sym(firstOpening.body).flatMap(Conv.apTerm(scaleBy, _))
      firstRegrouped <- vocabulary.rightOf(firstExpanded).flatMap(vocabulary.identity(_, firstSum))
      firstChained <- Conv.trans(firstExpanded, firstRegrouped).flatMap(Conv.trans(base, _))
      isMultiple <- rules
        .specAll(cancelsLeft, List(c, firstScaledGap, scaledFirst))
        .flatMap(rules.mp(_, firstChained))
      firstRelated <- vocabulary.concludeDivides(introduction, a, c, firstStep, isMultiple)
      firstCase <- vocabulary.closeAll(firstOpening, firstRelated)

      // `s` is `t + e`, so `c` has nowhere to go and is `ZERO`.
      assumedSecond <- LogicError.lift(Kernel.assume(secondIsSmaller))
      secondGap <- Conv
        .unfold(nonStrict, List(t, s))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, assumedSecond)))
      secondOpening <- vocabulary.openAll(secondGap, named, List("e"))
      secondStep <- secondOpening.variables.headOption
        .toRight(NotOfForm("a gap between two numbers", secondGap.conclusion))
      secondScaledGap <- vocabulary.product(a, secondStep)
      secondSum <- vocabulary.sum(scaledSecond, secondScaledGap)
      secondExpanded <- Conv.sym(secondOpening.body).flatMap(Conv.apTerm(scaleBy, _))
      secondRegrouped <- vocabulary
        .rightOf(secondExpanded)
        .flatMap(vocabulary.identity(_, secondSum))
      firstAsSum <- Conv.trans(secondExpanded, secondRegrouped)

      tail <- vocabulary.sum(secondScaledGap, c)
      whole <- vocabulary.sum(scaledSecond, tail)
      spread <- vocabulary.sum(secondSum, c)
      opening <- vocabulary.identity(whole, spread)
      backwards <- Conv
        .sym(firstAsSum)
        .flatMap(Conv.apTerm(vocabulary.plus, _))
        .flatMap(Conv.apThm(_, c))
      standsStill <- Conv.trans(opening, backwards).flatMap(Conv.trans(_, base))
      tailVanishes <- rules
        .specAll(cancels, List(tail, scaledSecond))
        .flatMap(rules.mp(_, standsStill))
      flipped <- vocabulary.sum(c, secondScaledGap)
      commuted <- vocabulary.identity(flipped, tail)
      sumVanishes <- Conv.trans(commuted, tailVanishes)
      isZero <- rules
        .specAll(sumIsZero, List(c, secondScaledGap))
        .flatMap(rules.mp(_, sumVanishes))
      dividesZero <- rules.spec(a, atZero)
      dividesPartial <- LogicError.lift(Term.app(vocabulary.dividesConstant, a))
      carriedZero <- Conv.apTerm(dividesPartial, isZero)
      secondRelated <- Conv
        .sym(carriedZero)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, dividesZero)))
      secondCase <- vocabulary.closeAll(secondOpening, secondRelated)

      decided <- rules.disjElim(split, firstCase, secondCase)
      closedSecond <- vocabulary.close(second, decided)
      closedFirst <- vocabulary.close(first, closedSecond)
      dischargedSecond <- rules.disch(second.premise, closedFirst)
      dischargedFirst <- rules.disch(first.premise, dischargedSecond)
      general <- rules.genAll(dischargedFirst, List(a, b, c))
      result <- vocabulary.checked(DividesSummand, general)
    } yield result
  }

  /**
   * [[BezoutExists]], by induction on a bound carried above the first number.
   *
   * The statement inducted on is `!n. !a b. NUM_LE a n ==> ...`, which is **not** what
   * [[Induct.proveBy]] can drive: that inducts on the last quantifier of what it is given, and the
   * induction here has to be on the first, because the step applies the hypothesis at a different
   * pair. So the induction theorem is instantiated here, at a predicate built from the statement
   * rather than from a second copy of it.
   *
   * The bound is then discharged at `n := a`, where `NUM_LE a a` is reflexivity.
   */
  private def bezoutByInduction(
    vocabulary: Vocabulary,
    division: Kernel.Thm,
    multiple: Kernel.Thm,
    sum: Kernel.Thm,
    atZero: Kernel.Thm,
    reflexivity: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      statement <- vocabulary.statement(BezoutExists)
      stripped <- Logic.stripForall(statement)
      left <- stripped._1.headOption.toRight(NotOfForm("a claim about two numbers", statement))
      right <- stripped._1.lift(1).toRight(NotOfForm("a claim about two numbers", statement))
      body = stripped._2
      bound = Conv.freshVariable("n", numbers, stripped._1.toSet)

      guard <- vocabulary.atMostTerm(left, bound)
      guarded <- logic.mkImp(guard, body)
      inner <- logic.mkForall(right, guarded)
      outer <- logic.mkForall(left, inner)
      predicate <- LogicError.lift(Term.abs(bound, outer))

      induction <- vocabulary.naturalFact(Natural.Induction)
      instance <- rules.spec(predicate, induction)
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      parts <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      halves <- logic.destConj(parts._1).toRight(NotOfForm("a conjunction", parts._1))
      (baseTerm, stepTerm) = halves

      provedBase <- bezoutBase(vocabulary, baseTerm, atZero, reflexivity)
      provedStep <- bezoutStep(vocabulary, stepTerm, division, multiple, sum, atZero, reflexivity)
      everywhere <- rules.conjIntro(provedBase, provedStep).flatMap(rules.mp(opened, _))

      reflexive <- vocabulary.fact(Peano.Reflexive)
      atSelf <- rules.specAll(everywhere, List(left, left, right))
      atMost <- rules.spec(left, reflexive)
      reached <- rules.mp(atSelf, atMost)
      general <- rules.genAll(reached, List(left, right))
      result <- vocabulary.checked(BezoutExists, general)
    } yield result
  }

  /**
   * The case where the first number is `ZERO`: the second divides both and reaches on its own.
   *
   * `b * SUC ZERO = a * ZERO + b` is an identity whatever `a` is, so only the divisibility needs
   * the hypothesis. Shared between the base of the induction, where `NUM_LE a ZERO` gives it, and
   * the step, where the case split on `a` does.
   */
  private def bezoutAtZero(
    vocabulary: Vocabulary,
    body: Term,
    other: Term,
    isZero: Kernel.Thm,
    atZero: Kernel.Thm,
    reflexivity: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val zero = vocabulary.zeroTerm

    for {
      unit <- vocabulary.one
      instantiated <- vocabulary.bodyAt(body, List(other, unit, zero))
      pieces <- logic.destConj(instantiated).toRight(NotOfForm("a conjunction", instantiated))
      rest <- logic.destConj(pieces._2).toRight(NotOfForm("a conjunction", pieces._2))
      disjuncts <- logic.destDisj(rest._2).toRight(NotOfForm("a disjunction", rest._2))
      (unused, wanted) = disjuncts
      sides <- Term.destEq(wanted).toRight(NotOfForm("an equation", wanted))
      equation <- vocabulary.identity(sides._1, sides._2)

      dividesZero <- rules.spec(other, atZero)
      partial <- LogicError.lift(Term.app(vocabulary.dividesConstant, other))
      carried <- Conv.apTerm(partial, isZero)
      dividesDividend <- Conv
        .sym(carried)
        .flatMap(equality => LogicError.lift(Kernel.eqMp(equality, dividesZero)))
      dividesOther <- rules.spec(other, reflexivity)

      injected <- rules.disjIntro2(unused, equation)
      tail <- rules.conjIntro(dividesOther, injected)
      whole <- rules.conjIntro(dividesDividend, tail)
      result <- vocabulary.witnessAll(body, List(other, unit, zero), whole)
    } yield result
  }

  /** The base of [[bezoutByInduction]]: a bound of `ZERO` forces the first number to be `ZERO`. */
  private def bezoutBase(
    vocabulary: Vocabulary,
    baseTerm: Term,
    atZero: Kernel.Thm,
    reflexivity: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      stripped <- Logic.stripForall(baseTerm)
      left <- stripped._1.headOption.toRight(NotOfForm("a claim about two numbers", baseTerm))
      right <- stripped._1.lift(1).toRight(NotOfForm("a claim about two numbers", baseTerm))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (guard, body) = parts

      assumed <- LogicError.lift(Kernel.assume(guard))
      atMostZero <- vocabulary.fact(Peano.AtMostZero)
      isZero <- rules.spec(left, atMostZero).flatMap(rules.mp(_, assumed))
      reached <- bezoutAtZero(vocabulary, body, right, isZero, atZero, reflexivity)
      discharged <- rules.disch(guard, reached)
      general <- rules.genAll(discharged, List(left, right))
      _ <-
        if (general.conclusion == baseTerm) Right(())
        else Left(NotOfForm("the base case as the induction states it", general.conclusion))
    } yield general
  }

  /**
   * The step of [[bezoutByInduction]], which is one division with remainder.
   *
   * At `ZERO` it is [[bezoutAtZero]] again. At a successor the modulus is positive, so `b` divides
   * into `a` with a remainder below `a` and therefore at or below the bound, the hypothesis applies
   * to the pair `(r, a)`, and the two cases of its disjunction are carried up by substituting the
   * decomposition forwards.
   */
  private def bezoutStep(
    vocabulary: Vocabulary,
    stepTerm: Term,
    division: Kernel.Thm,
    multiple: Kernel.Thm,
    sum: Kernel.Thm,
    atZero: Kernel.Thm,
    reflexivity: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      stripped <- Logic.stripForall(stepTerm)
      bound <- stripped._1.headOption.toRight(NotOfForm("a claim about every number", stepTerm))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (hypothesisTerm, conclusion) = parts
      hypothesis <- LogicError.lift(Kernel.assume(hypothesisTerm))

      inside <- Logic.stripForall(conclusion)
      left <- inside._1.headOption.toRight(NotOfForm("a claim about two numbers", conclusion))
      right <- inside._1.lift(1).toRight(NotOfForm("a claim about two numbers", conclusion))
      guarded <- logic.destImp(inside._2).toRight(NotOfForm("an implication", inside._2))
      (guard, body) = guarded
      assumedGuard <- LogicError.lift(Kernel.assume(guard))

      cases <- vocabulary.naturalFact(Natural.ZeroOrSuccessor)
      split <- rules.spec(left, cases)
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isZero, isSuccessor) = branches

      assumedZero <- LogicError.lift(Kernel.assume(isZero))
      zeroCase <- bezoutAtZero(vocabulary, body, right, assumedZero, atZero, reflexivity)

      assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
      predecessor = Conv.freshVariable("j", numbers, Set(bound, left, right))
      stepBody <- vocabulary.bodyAt(isSuccessor, List(predecessor))
      assumedStep <- LogicError.lift(Kernel.assume(stepBody))
      reached <- bezoutFromDivision(
        vocabulary,
        body,
        left,
        right,
        bound,
        hypothesis,
        assumedGuard,
        assumedStep,
        predecessor,
        division,
        multiple,
        sum
      )
      successorCase <- rules.existsElim(assumedSuccessor, predecessor, reached)

      decided <- rules.disjElim(split, zeroCase, successorCase)
      discharged <- rules.disch(guard, decided)
      general <- rules.genAll(discharged, List(left, right))
      step <- rules.disch(hypothesisTerm, general).flatMap(rules.gen(bound, _))
      _ <-
        if (step.conclusion == stepTerm) Right(())
        else Left(NotOfForm("the step as the induction states it", step.conclusion))
    } yield step
  }

  /** The half of [[bezoutStep]] where the first number is a successor, so division applies. */
  private def bezoutFromDivision(
    vocabulary: Vocabulary,
    body: Term,
    left: Term,
    right: Term,
    bound: FVar,
    hypothesis: Kernel.Thm,
    guard: Kernel.Thm,
    isSuccessor: Kernel.Thm,
    predecessor: FVar,
    division: Kernel.Thm,
    multiple: Kernel.Thm,
    sum: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val zero = vocabulary.zeroTerm

    for {
      successorPositive <- vocabulary.fact(Peano.SuccessorPositive)
      atPredecessor <- rules.spec(predecessor, successorPositive)
      partial <- LogicError.lift(Term.app(vocabulary.strict, zero))
      carried <- Conv.apTerm(partial, isSuccessor)
      positive <- Conv
        .sym(carried)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atPredecessor)))

      existence <- rules.specAll(division, List(left, right)).flatMap(rules.mp(_, positive))
      named = Set(bound, predecessor) ++
        Term.freeVariables(left) ++
        Term.freeVariables(right) ++
        Term.freeVariables(body)
      opened <- vocabulary.openAll(existence, named, List("q", "r"))
      quotient <- opened.variables.headOption
        .toRight(NotOfForm("a claim about two numbers", existence.conclusion))
      remainder <- opened.variables
        .lift(1)
        .toRight(NotOfForm("a claim about two numbers", existence.conclusion))
      decomposition <- rules.conjElim1(opened.body)
      below <- rules.conjElim2(opened.body)

      atMost <- remainderBelowBound(vocabulary, below, guard, remainder, left, bound)
      smaller <- rules.specAll(hypothesis, List(remainder, left)).flatMap(rules.mp(_, atMost))

      inner <- vocabulary.openAll(smaller, named + quotient + remainder, List("d", "x", "y"))
      divisor <- inner.variables.headOption
        .toRight(NotOfForm("a claim about three numbers", smaller.conclusion))
      first <- inner.variables
        .lift(1)
        .toRight(NotOfForm("a claim about three numbers", smaller.conclusion))
      second <- inner.variables
        .lift(2)
        .toRight(NotOfForm("a claim about three numbers", smaller.conclusion))
      dividesRemainder <- rules.conjElim1(inner.body)
      rest <- rules.conjElim2(inner.body)
      dividesLeft <- rules.conjElim1(rest)
      disjunction <- rules.conjElim2(rest)

      scaled <- vocabulary.product(left, quotient)
      dividesScaled <- rules
        .specAll(multiple, List(divisor, left, quotient))
        .flatMap(rules.mp(_, dividesLeft))
      pair <- rules.conjIntro(dividesScaled, dividesRemainder)
      dividesWhole <- rules
        .specAll(sum, List(divisor, scaled, remainder))
        .flatMap(rules.mp(_, pair))
      dividesPartial <- LogicError.lift(Term.app(vocabulary.dividesConstant, divisor))
      carriedRight <- Conv.apTerm(dividesPartial, decomposition)
      dividesRight <- Conv
        .sym(carriedRight)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, dividesWhole)))

      disjuncts <- logic
        .destDisj(disjunction.conclusion)
        .toRight(NotOfForm("a disjunction", disjunction.conclusion))
      (remainderReaches, leftReaches) = disjuncts

      assumedRemainder <- LogicError.lift(Kernel.assume(remainderReaches))
      remainderCase <- bezoutOverTheRemainder(
        vocabulary, body, left, quotient, divisor, first, second,
        decomposition, assumedRemainder, dividesLeft, dividesRight
      )
      assumedLeft <- LogicError.lift(Kernel.assume(leftReaches))
      leftCase <- bezoutOverTheDividend(
        vocabulary, body, left, quotient, divisor, first, second,
        decomposition, assumedLeft, dividesLeft, dividesRight
      )

      decided <- rules.disjElim(disjunction, remainderCase, leftCase)
      closedInner <- vocabulary.closeAll(inner, decided)
      closed <- vocabulary.closeAll(opened, closedInner)
    } yield closed
  }

  /**
   * `NUM_LE r n`, from `NUM_LT r a` and `NUM_LE a (SUC n)`: the descent the induction is carried by.
   *
   * `NUM_LT r a` is `NUM_LE (SUC r) a`, so transitivity puts `SUC r` at or below `SUC n`, which is
   * `NUM_LT r (SUC n)`, which `Peano.BelowSuccessorCases` splits into being below `n` or being `n`.
   * Both halves give `NUM_LE r n` and the second needs the equation carried into reflexivity.
   */
  private def remainderBelowBound(
    vocabulary: Vocabulary,
    below: Kernel.Thm,
    guard: Kernel.Thm,
    remainder: Term,
    left: Term,
    bound: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      transitive <- vocabulary.fact(Peano.Transitive)
      cases <- vocabulary.fact(Peano.BelowSuccessorCases)
      fromBelow <- vocabulary.fact(Peano.AtMostFromBelow)
      reflexive <- vocabulary.fact(Peano.Reflexive)
      strict <- vocabulary.peano.definition(Peano.StrictOrder)

      asNonStrict <- vocabulary.asNonStrict(remainder, left, below)
      nextBound <- vocabulary.next(bound)
      nextRemainder <- vocabulary.next(remainder)
      pair <- rules.conjIntro(asNonStrict, guard)
      chained <- rules
        .specAll(transitive, List(nextRemainder, left, nextBound))
        .flatMap(rules.mp(_, pair))
      unfolded <- Conv.unfold(strict, List(remainder, nextBound))
      belowNext <- Conv
        .sym(unfolded)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chained)))

      split <- rules.specAll(cases, List(bound, remainder)).flatMap(rules.mp(_, belowNext))
      halves <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (strictly, equal) = halves

      assumedStrict <- LogicError.lift(Kernel.assume(strictly))
      strictCase <- rules
        .specAll(fromBelow, List(remainder, bound))
        .flatMap(rules.mp(_, assumedStrict))

      assumedEqual <- LogicError.lift(Kernel.assume(equal))
      atBound <- rules.spec(bound, reflexive)
      carried <- Conv.apTerm(vocabulary.nonStrict, assumedEqual).flatMap(Conv.apThm(_, bound))
      equalCase <- Conv
        .sym(carried)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, atBound)))

      decided <- rules.disjElim(split, strictCase, equalCase)
    } yield decided
  }

  /**
   * The case where the remainder is the side that reaches: `r x = a y + d` becomes
   * `b x = a (y + q x) + d`.
   *
   * The decomposition `b = a q + r` is substituted **forwards** and the arithmetic regroups, which
   * is why no subtraction appears anywhere in this induction. Both identities go to
   * [[Vocabulary.identity]]; the only proper inference is the one congruence that puts the
   * hypothesis in.
   */
  private def bezoutOverTheRemainder(
    vocabulary: Vocabulary,
    body: Term,
    left: Term,
    quotient: Term,
    divisor: Term,
    first: Term,
    second: Term,
    decomposition: Kernel.Thm,
    reaches: Kernel.Thm,
    dividesLeft: Kernel.Thm,
    dividesRight: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      shifted <- vocabulary.product(quotient, first)
      witness <- vocabulary.sum(second, shifted)
      instantiated <- vocabulary.bodyAt(body, List(divisor, first, witness))
      pieces <- logic.destConj(instantiated).toRight(NotOfForm("a conjunction", instantiated))
      rest <- logic.destConj(pieces._2).toRight(NotOfForm("a conjunction", pieces._2))
      disjuncts <- logic.destDisj(rest._2).toRight(NotOfForm("a disjunction", rest._2))
      (unused, wanted) = disjuncts

      scaled <- vocabulary.scaleOnTheRight(decomposition, first)
      scaledQuotient <- vocabulary.product(left, shifted)
      scaledRemainder <- vocabulary.leftOf(reaches)
      expanded <- vocabulary.sum(scaledQuotient, scaledRemainder)
      opening <- vocabulary.rightOf(scaled).flatMap(vocabulary.identity(_, expanded))
      inParts <- Conv.trans(scaled, opening)
      partial <- LogicError.lift(Term.app(vocabulary.plus, scaledQuotient))
      substituted <- Conv.apTerm(partial, reaches)
      combined <- Conv.trans(inParts, substituted)
      target <- Term.destEq(wanted).map(_._2).toRight(NotOfForm("an equation", wanted))
      closing <- vocabulary.rightOf(combined).flatMap(vocabulary.identity(_, target))
      equation <- Conv.trans(combined, closing)
      _ <-
        if (equation.conclusion == wanted) Right(())
        else Left(NotOfForm(s"a proof of $wanted", equation.conclusion))

      injected <- rules.disjIntro2(unused, equation)
      tail <- rules.conjIntro(dividesRight, injected)
      whole <- rules.conjIntro(dividesLeft, tail)
      result <- vocabulary.witnessAll(body, List(divisor, first, witness), whole)
    } yield result
  }

  /** The mirror case: `a x = r y + d` becomes `a (x + q y) = b y + d`, by the same substitution. */
  private def bezoutOverTheDividend(
    vocabulary: Vocabulary,
    body: Term,
    left: Term,
    quotient: Term,
    divisor: Term,
    first: Term,
    second: Term,
    decomposition: Kernel.Thm,
    reaches: Kernel.Thm,
    dividesLeft: Kernel.Thm,
    dividesRight: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      shifted <- vocabulary.product(quotient, second)
      witness <- vocabulary.sum(first, shifted)
      instantiated <- vocabulary.bodyAt(body, List(divisor, witness, second))
      pieces <- logic.destConj(instantiated).toRight(NotOfForm("a conjunction", instantiated))
      rest <- logic.destConj(pieces._2).toRight(NotOfForm("a conjunction", pieces._2))
      disjuncts <- logic.destDisj(rest._2).toRight(NotOfForm("a disjunction", rest._2))
      (wanted, unused) = disjuncts

      scaledWitness <- vocabulary.product(left, witness)
      scaledFirst <- vocabulary.leftOf(reaches)
      scaledShift <- vocabulary.product(left, shifted)
      expanded <- vocabulary.sum(scaledFirst, scaledShift)
      opening <- vocabulary.identity(scaledWitness, expanded)
      substituted <- Conv.apTerm(vocabulary.plus, reaches).flatMap(Conv.apThm(_, scaledShift))
      combined <- Conv.trans(opening, substituted)

      decomposed <- vocabulary.rightOf(decomposition)
      middleProduct <- vocabulary.product(decomposed, second)
      middle <- vocabulary.sum(middleProduct, divisor)
      regrouped <- vocabulary.rightOf(combined).flatMap(vocabulary.identity(_, middle))
      toMiddle <- Conv.trans(combined, regrouped)
      flipped <- Conv.sym(decomposition)
      backwards <- vocabulary.scaleOnTheRight(flipped, second)
      lifted <- Conv.apTerm(vocabulary.plus, backwards).flatMap(Conv.apThm(_, divisor))
      equation <- Conv.trans(toMiddle, lifted)
      _ <-
        if (equation.conclusion == wanted) Right(())
        else Left(NotOfForm(s"a proof of $wanted", equation.conclusion))

      injected <- rules.disjIntro1(unused, equation)
      tail <- rules.conjIntro(dividesRight, injected)
      whole <- rules.conjIntro(dividesLeft, tail)
      result <- vocabulary.witnessAll(body, List(divisor, witness, second), whole)
    } yield result
  }

  /**
   * `|- NUM_DIVIDES k t`, from `k` dividing both numbers of an equation `l = r + t`.
   *
   * [[DividesSummand]] with the equation carried into the divisibility rather than the other way
   * about: `k | l` and `l = r + t` give `k | (r + t)` by one congruence, and the summand lemma
   * takes `r` off it.
   */
  private def dividesWhatIsLeftOver(
    vocabulary: Vocabulary,
    summand: Kernel.Thm,
    divisor: Term,
    dividesWhole: Kernel.Thm,
    dividesPart: Kernel.Thm,
    equation: Kernel.Thm,
    part: Term,
    target: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      partial <- LogicError.lift(Term.app(vocabulary.dividesConstant, divisor))
      carried <- Conv.apTerm(partial, equation)
      dividesSum <- LogicError.lift(Kernel.eqMp(carried, dividesWhole))
      instance <- rules.specAll(summand, List(divisor, part, target))
      once <- rules.mp(instance, dividesPart)
      result <- rules.mp(once, dividesSum)
    } yield result
  }

  /**
   * `|- NUM_DIVIDES k t` from a Bezout pair, whichever way round the equation came out.
   *
   * The two branches are the same three moves with the two numbers exchanged, which is what the
   * disjunction costs and all it costs: a common divisor divides both products whichever side each
   * one is on.
   */
  private def dividesFromBezout(
    vocabulary: Vocabulary,
    summand: Kernel.Thm,
    multiple: Kernel.Thm,
    divisor: Term,
    dividesLeft: Kernel.Thm,
    dividesRight: Kernel.Thm,
    left: Term,
    right: Term,
    first: Term,
    second: Term,
    disjunction: Kernel.Thm,
    target: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    def branch(
      whole: Term,
      part: Term,
      dividesWholeSide: Kernel.Thm,
      dividesPartSide: Kernel.Thm,
      wholeFactor: Term,
      partFactor: Term,
      disjunct: Term
    ): Either[LogicError, Kernel.Thm] =
      for {
        wholeProduct <- vocabulary.product(whole, wholeFactor)
        partProduct <- vocabulary.product(part, partFactor)
        dividesWhole <- rules
          .specAll(multiple, List(divisor, whole, wholeFactor))
          .flatMap(rules.mp(_, dividesWholeSide))
        dividesPart <- rules
          .specAll(multiple, List(divisor, part, partFactor))
          .flatMap(rules.mp(_, dividesPartSide))
        assumed <- LogicError.lift(Kernel.assume(disjunct))
        result <- dividesWhatIsLeftOver(
          vocabulary, summand, divisor, dividesWhole, dividesPart, assumed, partProduct, target
        )
      } yield result

    for {
      disjuncts <- logic
        .destDisj(disjunction.conclusion)
        .toRight(NotOfForm("a disjunction", disjunction.conclusion))
      (leftReaches, rightReaches) = disjuncts
      leftCase <- branch(left, right, dividesLeft, dividesRight, first, second, leftReaches)
      rightCase <- branch(right, left, dividesRight, dividesLeft, first, second, rightReaches)
      decided <- rules.disjElim(disjunction, leftCase, rightCase)
    } yield decided
  }

  /**
   * [[Bezout]]: the divisor the induction produced **is** the greatest common divisor.
   *
   * Three facts meet. It divides both, so [[GcdGreatest]] puts it at or below the gcd; the gcd
   * divides both, so [[dividesFromBezout]] makes it divide the divisor; and [[DividesBound]] turns
   * that round unless the divisor is `ZERO`, which would make both numbers `ZERO` and is what the
   * guard forbids. Antisymmetry closes it, and the identity is then carried to the gcd by one
   * transitivity per disjunct rather than by rewriting a proposition.
   */
  private def bezoutAtTheGcd(
    vocabulary: Vocabulary,
    existence: Kernel.Thm,
    summand: Kernel.Thm,
    multiple: Kernel.Thm,
    gcdLeft: Kernel.Thm,
    gcdRight: Kernel.Thm,
    gcdGreatest: Kernel.Thm,
    bound: Kernel.Thm,
    zeroDivides: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      // The two numbers are the statement's own variables and not a pair named here. `stripForall`
      // renames what it opens, so a derivation that stripped the statement and then built terms
      // over `a` and `b` would be working on two claims at once: the first witness this opened was
      // called `y`, which is what the statement's second number is called, and the substitution
      // captured it. Caught by `Conv.trans`, several steps after the mistake.
      statement <- vocabulary.statement(Bezout)
      stripped <- Logic.stripForall(statement)
      a <- stripped._1.headOption.toRight(NotOfForm("a claim about two numbers", statement))
      b <- stripped._1.lift(1).toRight(NotOfForm("a claim about two numbers", statement))
      parts <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (guard, goal) = parts
      assumedGuard <- LogicError.lift(Kernel.assume(guard))

      gcd <- vocabulary.greatestCommonDivisor(a, b)
      instance <- rules.specAll(existence, List(a, b))
      opened <- vocabulary.openAll(instance, stripped._1.toSet, List("d", "x", "y"))
      divisor <- opened.variables.headOption
        .toRight(NotOfForm("a claim about three numbers", instance.conclusion))
      first <- opened.variables
        .lift(1)
        .toRight(NotOfForm("a claim about three numbers", instance.conclusion))
      second <- opened.variables
        .lift(2)
        .toRight(NotOfForm("a claim about three numbers", instance.conclusion))
      dividesA <- rules.conjElim1(opened.body)
      rest <- rules.conjElim2(opened.body)
      dividesB <- rules.conjElim1(rest)
      disjunction <- rules.conjElim2(rest)

      gcdDividesA <- rules.specAll(gcdLeft, List(a, b)).flatMap(rules.mp(_, assumedGuard))
      gcdDividesB <- rules.specAll(gcdRight, List(a, b)).flatMap(rules.mp(_, assumedGuard))
      gcdDividesDivisor <- dividesFromBezout(
        vocabulary, summand, multiple, gcd, gcdDividesA, gcdDividesB, a, b, first, second,
        disjunction, divisor
      )

      common <- rules.conjIntro(dividesA, dividesB)
      atMostGcd <- rules
        .specAll(gcdGreatest, List(a, b, divisor))
        .flatMap(rules.mp(_, assumedGuard))
        .flatMap(rules.mp(_, common))
      split <- rules
        .specAll(bound, List(gcd, divisor))
        .flatMap(rules.mp(_, gcdDividesDivisor))
      halves <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (gcdIsBelow, divisorIsZero) = halves

      antisymmetric <- vocabulary.fact(Peano.AntiSymmetric)
      assumedBelow <- LogicError.lift(Kernel.assume(gcdIsBelow))
      pair <- rules.conjIntro(atMostGcd, assumedBelow)
      sameNumber <- rules.specAll(antisymmetric, List(divisor, gcd)).flatMap(rules.mp(_, pair))
      belowCase <- bezoutCarriedToTheGcd(vocabulary, goal, disjunction, sameNumber, first, second)

      assumedZero <- LogicError.lift(Kernel.assume(divisorIsZero))
      absurd <- bothNumbersAreZero(
        vocabulary, zeroDivides, assumedGuard, assumedZero, dividesA, dividesB, a, b
      )
      zeroCase <- rules.falsityElim(goal, absurd)

      decided <- rules.disjElim(split, belowCase, zeroCase)
      closed <- vocabulary.closeAll(opened, decided)
      discharged <- rules.disch(guard, closed)
      general <- rules.genAll(discharged, List(a, b))
      result <- vocabulary.checked(Bezout, general)
    } yield result
  }

  /** The identity at `d`, carried to the gcd once the two are known to be the same number. */
  private def bezoutCarriedToTheGcd(
    vocabulary: Vocabulary,
    goal: Term,
    disjunction: Kernel.Thm,
    sameNumber: Kernel.Thm,
    first: Term,
    second: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      instantiated <- vocabulary.bodyAt(goal, List(first, second))
      wanted <- logic.destDisj(instantiated).toRight(NotOfForm("a disjunction", instantiated))
      held <- logic
        .destDisj(disjunction.conclusion)
        .toRight(NotOfForm("a disjunction", disjunction.conclusion))

      moved <- Term
        .destEq(wanted._1)
        .map(_._2)
        .toRight(NotOfForm("an equation", wanted._1))
        .flatMap {
          case App(partial, _) => Conv.apTerm(partial, sameNumber)
          case other => Left(NotOfForm("a sum", other))
        }
      assumedFirst <- LogicError.lift(Kernel.assume(held._1))
      firstAtGcd <- Conv.trans(assumedFirst, moved)
      firstCase <- rules
        .disjIntro1(wanted._2, firstAtGcd)
        .flatMap(vocabulary.witnessAll(goal, List(first, second), _))

      movedSecond <- Term
        .destEq(wanted._2)
        .map(_._2)
        .toRight(NotOfForm("an equation", wanted._2))
        .flatMap {
          case App(partial, _) => Conv.apTerm(partial, sameNumber)
          case other => Left(NotOfForm("a sum", other))
        }
      assumedSecond <- LogicError.lift(Kernel.assume(held._2))
      secondAtGcd <- Conv.trans(assumedSecond, movedSecond)
      secondCase <- rules
        .disjIntro2(wanted._1, secondAtGcd)
        .flatMap(vocabulary.witnessAll(goal, List(first, second), _))

      decided <- rules.disjElim(disjunction, firstCase, secondCase)
    } yield decided
  }

  /** `G |- F`: a divisor of `ZERO` on both sides makes both numbers `ZERO`, which the guard denies. */
  private def bothNumbersAreZero(
    vocabulary: Vocabulary,
    zeroDivides: Kernel.Thm,
    guard: Kernel.Thm,
    isZero: Kernel.Thm,
    dividesLeft: Kernel.Thm,
    dividesRight: Kernel.Thm,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    def forced(divides: Kernel.Thm, number: Term): Either[LogicError, Kernel.Thm] =
      for {
        carried <- Conv.apTerm(vocabulary.dividesConstant, isZero).flatMap(Conv.apThm(_, number))
        byZero <- LogicError.lift(Kernel.eqMp(carried, divides))
        equation <- rules.spec(number, zeroDivides)
        result <- LogicError.lift(Kernel.eqMp(equation, byZero))
      } yield result

    for {
      leftIsZero <- forced(dividesLeft, left)
      rightIsZero <- forced(dividesRight, right)
      halves <- logic
        .destDisj(guard.conclusion)
        .toRight(NotOfForm("a disjunction", guard.conclusion))
      (notLeft, notRight) = halves
      assumedNotLeft <- LogicError.lift(Kernel.assume(notLeft))
      leftCase <- rules.notElim(assumedNotLeft, leftIsZero)
      assumedNotRight <- LogicError.lift(Kernel.assume(notRight))
      rightCase <- rules.notElim(assumedNotRight, rightIsZero)
      absurd <- rules.disjElim(guard, leftCase, rightCase)
    } yield absurd
  }

  /**
   * [[GcdDivides]]: every common divisor divides the greatest one, which is what a consumer wanted.
   *
   * One application of [[dividesFromBezout]] and nothing else. It is worth seeing how short this is
   * against how long it was unreachable: the statement was named as the gap in [[GcdGreatest]]'s
   * docstring and asserted absent by `ModularSpec`, and what stood between was [[Bezout]] rather
   * than anything about the gcd itself.
   */
  private def gcdDividesByBezout(
    vocabulary: Vocabulary,
    bezout: Kernel.Thm,
    summand: Kernel.Thm,
    multiple: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      // The statement's own variables, for the reason [[bezoutAtTheGcd]] gives at length.
      statement <- vocabulary.statement(GcdDivides)
      stripped <- Logic.stripForall(statement)
      a <- stripped._1.headOption.toRight(NotOfForm("a claim about three numbers", statement))
      b <- stripped._1.lift(1).toRight(NotOfForm("a claim about three numbers", statement))
      d <- stripped._1.lift(2).toRight(NotOfForm("a claim about three numbers", statement))
      gcd <- vocabulary.greatestCommonDivisor(a, b)
      guarded <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (guard, rest) = guarded
      inner <- logic.destImp(rest).toRight(NotOfForm("an implication", rest))
      (common, _) = inner
      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      assumedCommon <- LogicError.lift(Kernel.assume(common))
      dividesLeft <- rules.conjElim1(assumedCommon)
      dividesRight <- rules.conjElim2(assumedCommon)

      instance <- rules.specAll(bezout, List(a, b)).flatMap(rules.mp(_, assumedGuard))
      opened <- vocabulary.openAll(instance, stripped._1.toSet, List("x", "y"))
      first <- opened.variables.headOption
        .toRight(NotOfForm("a claim about two numbers", instance.conclusion))
      second <- opened.variables
        .lift(1)
        .toRight(NotOfForm("a claim about two numbers", instance.conclusion))
      reached <- dividesFromBezout(
        vocabulary, summand, multiple, d, dividesLeft, dividesRight, a, b, first, second,
        opened.body, gcd
      )
      closed <- vocabulary.closeAll(opened, reached)
      dischargedCommon <- rules.disch(common, closed)
      discharged <- rules.disch(guard, dischargedCommon)
      general <- rules.genAll(discharged, List(a, b, d))
      result <- vocabulary.checked(GcdDivides, general)
    } yield result
  }

  /* --------------------------------------------------- primes, and Euclid's lemma */

  /** `|- !p. NUM_PRIME p ==> NUM_LT (SUC ZERO) p`, the first conjunct of the definition. */
  private def primeIsAboveOne(
    vocabulary: Vocabulary,
    definition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val p = variable("p")

    for {
      unfolded <- Conv.unfold(definition, List(p))
      premise <- vocabulary.leftOf(unfolded)
      assumed <- LogicError.lift(Kernel.assume(premise))
      body <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      above <- rules.conjElim1(body)
      discharged <- rules.disch(premise, above)
      general <- rules.gen(p, discharged)
      result <- vocabulary.checked(PrimeAboveOne, general)
    } yield result
  }

  /** `|- !p d. NUM_PRIME p ==> NUM_DIVIDES d p ==> d = SUC ZERO \/ d = p`, the second. */
  private def primeHasNoOtherDivisor(
    vocabulary: Vocabulary,
    definition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val p = variable("p")
    val d = variable("d")

    for {
      unfolded <- Conv.unfold(definition, List(p))
      premise <- vocabulary.leftOf(unfolded)
      assumed <- LogicError.lift(Kernel.assume(premise))
      body <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      divisors <- rules.conjElim2(body)
      instance <- rules.spec(d, divisors)
      discharged <- rules.disch(premise, instance)
      general <- rules.genAll(discharged, List(p, d))
      result <- vocabulary.checked(PrimeDivisor, general)
    } yield result
  }

  /** `|- ~(p = ZERO)`, from a number above one. */
  /**
   * [[PrimeFactor]], by taking the least divisor above one and showing it has no others.
   *
   * `NUM_LEAST` over `\d. SUC ZERO < d /\ NUM_DIVIDES d n` needs the property inhabited, and `n`
   * itself inhabits it. What comes back is a smallest `m` with those two, and the whole content of
   * the lemma is that `m` is prime, which [[everyDivisorOfTheLeastIsTrivial]] does.
   *
   * Split in two because the inner half is where the work is: the outer one opens an existential,
   * folds the definition of prime and closes another, and reads as those three things only when the
   * case analysis is somewhere else.
   */
  private def everyNumberAboveOneHasAPrimeFactor(
    vocabulary: Vocabulary,
    primeDefinition: Kernel.Thm,
    reflexivity: Kernel.Thm,
    transitivity: Kernel.Thm,
    bound: Kernel.Thm,
    byZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val n = Term.variable("n", Modular.numbers)

    for {
      unit <- vocabulary.one
      aboveOne <- vocabulary.belowTerm(unit, n)
      held <- LogicError.lift(Kernel.assume(aboveOne))

      subject = Conv.freshVariable("d", Modular.numbers, Set(n))
      dividesN <- vocabulary.dividing(subject, n)
      aboveOneToo <- vocabulary.belowTerm(unit, subject)
      body <- logic.mkConj(aboveOneToo, dividesN)
      property <- LogicError.lift(Term.abs(subject, body))

      // `n` divides itself and is above one, so something has the property.
      existential <- logic.mkExists(subject, body)
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))
      itself <- rules.spec(n, reflexivity)
      inhabited <- rules.conjIntro(held, itself).flatMap(rules.existsIntro(predicate, n, _))

      leastPrinciple <- vocabulary.fact(Peano.LeastNumber)
      instance <- rules.spec(property, leastPrinciple)
      reduced <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      least <- rules.mp(reduced, inhabited)

      inner <- logic
        .destExistsPredicate(least.conclusion)
        .toRight(NotOfForm("an existential", least.conclusion))
      m = Conv.freshVariable("m", Modular.numbers, Set(n) ++ Term.freeVariables(least.conclusion))
      applied <- LogicError.lift(Term.app(inner, m))
      contraction <- Conv.betaRoot(applied)
      opened <- vocabulary.rightOf(contraction)
      atM <- LogicError.lift(Kernel.assume(opened))

      holds <- rules.conjElim1(atM)
      isLeast <- rules.conjElim2(atM)
      aboveOneAtM <- rules.conjElim1(holds)
      dividesAtM <- rules.conjElim2(holds)

      trivial <- everyDivisorOfTheLeastIsTrivial(
        vocabulary, isLeast, aboveOneAtM, dividesAtM, transitivity, bound, byZero, m, n)
      unfolded <- Conv.unfold(primeDefinition, List(m))
      isPrime <- rules
        .conjIntro(aboveOneAtM, trivial)
        .flatMap(pair => Conv.sym(unfolded).flatMap(e => LogicError.lift(Kernel.eqMp(e, pair))))

      witness = Conv.freshVariable("p", Modular.numbers, Set(n, m))
      primeTerm <- vocabulary.isPrime(witness)
      dividesTerm <- vocabulary.dividing(witness, n)
      wantedBody <- logic.mkConj(primeTerm, dividesTerm)
      wanted <- logic.mkExists(witness, wantedBody)
      wantedPredicate <- logic
        .destExistsPredicate(wanted)
        .toRight(NotOfForm("an existential", wanted))
      found <- rules
        .conjIntro(isPrime, dividesAtM)
        .flatMap(rules.existsIntro(wantedPredicate, m, _))
      closed <- rules.existsElim(least, m, found)
      general <- rules.disch(aboveOne, closed).flatMap(rules.gen(n, _))
      result <- vocabulary.checked(Modular.PrimeFactor, general)
    } yield result
  }

  /**
   * The least divisor above one has no divisor but one and itself, which is what makes it prime.
   *
   * Given `d | m`, the excluded middle on `d = SUC ZERO` settles one branch at once. The other
   * proves `d = m` by contradiction, and everything in that branch exists to put `d` into the
   * property `m` is least for: `d | m | n` gives `d | n`; `d | m` with `m` not zero gives `d <= m`,
   * and `d` not `m` sharpens it to `d < m`; and `d` is above one because it is neither zero, since
   * zero divides only zero, nor one, which is the branch's own assumption. Minimality then refuses
   * exactly the pair that has just been assembled.
   */
  private def everyDivisorOfTheLeastIsTrivial(
    vocabulary: Vocabulary,
    isLeast: Kernel.Thm,
    aboveOneAtM: Kernel.Thm,
    dividesAtM: Kernel.Thm,
    transitivity: Kernel.Thm,
    bound: Kernel.Thm,
    byZero: Kernel.Thm,
    m: Term,
    n: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val d = Conv.freshVariable("d", Modular.numbers, Term.freeVariables(n) ++ Term.freeVariables(m))

    for {
      unit <- vocabulary.one
      middle <- vocabulary.peano.naturals.classical.fact(Classical.ExcludedMiddle)
      doubleNegation <- vocabulary.peano.naturals.classical.fact(Classical.DoubleNegation)

      dividesM <- vocabulary.dividing(d, m)
      assumedDivides <- LogicError.lift(Kernel.assume(dividesM))
      isOne <- LogicError.lift(Term.eq(d, unit))
      isM <- LogicError.lift(Term.eq(d, m))
      goal <- logic.mkDisj(isOne, isM)

      split <- rules.spec(isOne, middle)
      parts <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      whenOne <- LogicError
        .lift(Kernel.assume(parts._1))
        .flatMap(rules.disjIntro1(isM, _))

      notOne <- LogicError.lift(Kernel.assume(parts._2))
      notM <- logic.mkNot(isM)
      assumedNotM <- LogicError.lift(Kernel.assume(notM))

      // `d | m` and `m | n`, so `d` divides `n` as well.
      dividesN <- rules
        .specAll(transitivity, List(d, m, n))
        .flatMap(rules.mp(_, assumedDivides))
        .flatMap(rules.mp(_, dividesAtM))

      // `d <= m`, and then `d < m`, since `m` is not zero and `d` is not `m`.
      notZero <- aboveOneIsNotZero(vocabulary, aboveOneAtM, m)
      cases <- rules.specAll(bound, List(d, m)).flatMap(rules.mp(_, assumedDivides))
      atMostM <- eitherOrAbsurd(vocabulary, cases, notZero)
      belowOrEqual <- vocabulary.fact(Peano.BelowOrEqual)
      split2 <- rules.specAll(belowOrEqual, List(d, m)).flatMap(rules.mp(_, atMostM))
      belowM <- eitherOrAbsurd(vocabulary, split2, assumedNotM)

      aboveOneAtD <- neitherZeroNorOne(vocabulary, notOne, assumedDivides, notZero, byZero, d, m)

      // Which is the property `m` was chosen least for, at something below `m`.
      refused <- rules
        .spec(d, isLeast)
        .flatMap(rules.mp(_, belowM))
        .flatMap(refusal =>
          Conv
            .betaNormalise(refusal.conclusion)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, refusal)))
        )
      absurd <- rules.conjIntro(aboveOneAtD, dividesN).flatMap(rules.notElim(refused, _))

      negated <- rules.notIntro(notM, absurd)
      equalsM <- rules.spec(isM, doubleNegation).flatMap(rules.mp(_, negated))
      whenNotOne <- rules.disjIntro2(isOne, equalsM)

      settled <- rules.disjElim(split, whenOne, whenNotOne)
      result <- rules.disch(dividesM, settled).flatMap(rules.gen(d, _))
    } yield result
  }

  /**
   * A disjunction whose right half is refuted, which is how three of the steps above narrow.
   *
   * `d <= m \/ m = 0` against `~(m = 0)`, and `d < m \/ d = m` against `~(d = m)`: the same shape
   * twice, and writing it once is what keeps the two readable where they are used.
   */
  private def eitherOrAbsurd(
    vocabulary: Vocabulary,
    cases: Kernel.Thm,
    refuted: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      parts <- vocabulary.logic
        .destDisj(cases.conclusion)
        .toRight(NotOfForm("a disjunction", cases.conclusion))
      left <- LogicError.lift(Kernel.assume(parts._1))
      right <- LogicError.lift(Kernel.assume(parts._2))
      absurd <- rules.notElim(refuted, right)
      elsewhere <- rules.falsityElim(parts._1, absurd)
      result <- rules.disjElim(cases, left, elsewhere)
    } yield result
  }

  /**
   * A divisor that is neither one nor zero is above one, by trichotomy against one.
   *
   * Zero is ruled out by the divisor's own dividend: zero divides only zero, and the dividend here
   * is not zero. Below one is ruled out the same way, since the only number below one is zero.
   */
  private def neitherZeroNorOne(
    vocabulary: Vocabulary,
    notOne: Kernel.Thm,
    dividesM: Kernel.Thm,
    notZero: Kernel.Thm,
    byZero: Kernel.Thm,
    d: Term,
    m: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      unit <- vocabulary.one
      target <- vocabulary.belowTerm(unit, d)
      trichotomy <- vocabulary.fact(Peano.Trichotomy)
      cases <- rules.specAll(trichotomy, List(d, unit))
      first <- logic
        .destDisj(cases.conclusion)
        .toRight(NotOfForm("a disjunction", cases.conclusion))
      rest <- logic.destDisj(first._2).toRight(NotOfForm("a disjunction", first._2))

      // Below one means zero, and zero divides only zero.
      belowSuccessor <- vocabulary.fact(Peano.BelowSuccessorCases)
      notBelowZero <- vocabulary.fact(Peano.NotBelowZero)
      peeled <- LogicError
        .lift(Kernel.assume(first._1))
        .flatMap(assumed => rules.specAll(belowSuccessor, List(vocabulary.zeroTerm, d))
          .flatMap(rules.mp(_, assumed)))
      peeledParts <- logic
        .destDisj(peeled.conclusion)
        .toRight(NotOfForm("a disjunction", peeled.conclusion))
      fromBelowZero <- LogicError
        .lift(Kernel.assume(peeledParts._1))
        .flatMap(assumed => rules.spec(d, notBelowZero).flatMap(rules.notElim(_, assumed)))
        .flatMap(rules.falsityElim(target, _))
      fromZero <- for {
        assumed <- LogicError.lift(Kernel.assume(peeledParts._2))
        carried <- Conv
          .apTerm(vocabulary.dividesConstant, assumed)
          .flatMap(Conv.apThm(_, m))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, dividesM)))
        isZero <- rules
          .spec(m, byZero)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, carried)))
        absurd <- rules.notElim(notZero, isZero)
        reached <- rules.falsityElim(target, absurd)
      } yield reached
      belowOne <- rules.disjElim(peeled, fromBelowZero, fromZero)

      fromEqual <- LogicError
        .lift(Kernel.assume(rest._1))
        .flatMap(rules.notElim(notOne, _))
        .flatMap(rules.falsityElim(target, _))
      fromAbove <- LogicError.lift(Kernel.assume(rest._2))

      tail <- logic.mkDisj(rest._1, rest._2).flatMap(t => LogicError.lift(Kernel.assume(t)))
      inner <- rules.disjElim(tail, fromEqual, fromAbove)
      result <- rules.disjElim(cases, belowOne, inner)
    } yield result
  }

  /**
   * [[PrimeTwo]], by walking the four numbers a divisor of two could be.
   *
   * Nothing here is an induction and nothing is a search: `NUM_DIVIDES_LE` bounds the divisor,
   * `NUM_LE_CASES` and `NUM_LT_SUC_CASES` peel the bound one successor at a time, and the two ends
   * are closed by `NUM_NOT_LT_ZERO` and by zero dividing only zero.
   */
  private def twoIsPrime(
    vocabulary: Vocabulary,
    primeDefinition: Kernel.Thm,
    bound: Kernel.Thm,
    byZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val d = Term.variable("d", Modular.numbers)

    for {
      unit <- vocabulary.one
      two <- vocabulary.next(unit)
      zeroTerm = vocabulary.zeroTerm

      notZero <- twoIsNotZero(vocabulary, two, unit)

      dividesTwo <- vocabulary.dividing(d, two).flatMap(t => LogicError.lift(Kernel.assume(t)))
      isOne <- LogicError.lift(Term.eq(d, unit))
      isTwo <- LogicError.lift(Term.eq(d, two))
      goal <- logic.mkDisj(isOne, isTwo)

      atMostTwo <- rules
        .specAll(bound, List(d, two))
        .flatMap(rules.mp(_, dividesTwo))
        .flatMap(eitherOrAbsurd(vocabulary, _, notZero))

      belowOrEqual <- vocabulary.fact(Peano.BelowOrEqual)
      split <- rules.specAll(belowOrEqual, List(d, two)).flatMap(rules.mp(_, atMostTwo))
      splitParts <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))

      peelOne <- vocabulary.fact(Peano.BelowSuccessorCases)
      peeled <- LogicError
        .lift(Kernel.assume(splitParts._1))
        .flatMap(assumed => rules.specAll(peelOne, List(unit, d)).flatMap(rules.mp(_, assumed)))
      peeledParts <- logic
        .destDisj(peeled.conclusion)
        .toRight(NotOfForm("a disjunction", peeled.conclusion))

      inner <- LogicError
        .lift(Kernel.assume(peeledParts._1))
        .flatMap(assumed => rules.specAll(peelOne, List(zeroTerm, d)).flatMap(rules.mp(_, assumed)))
      innerParts <- logic
        .destDisj(inner.conclusion)
        .toRight(NotOfForm("a disjunction", inner.conclusion))

      notBelowZero <- vocabulary.fact(Peano.NotBelowZero)
      fromBelowZero <- LogicError
        .lift(Kernel.assume(innerParts._1))
        .flatMap(assumed => rules.spec(d, notBelowZero).flatMap(rules.notElim(_, assumed)))
        .flatMap(rules.falsityElim(goal, _))
      fromZero <- for {
        assumed <- LogicError.lift(Kernel.assume(innerParts._2))
        carried <- Conv
          .apTerm(vocabulary.dividesConstant, assumed)
          .flatMap(Conv.apThm(_, two))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, dividesTwo)))
        collapsed <- rules
          .spec(two, byZero)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, carried)))
        absurd <- rules.notElim(notZero, collapsed)
        reached <- rules.falsityElim(goal, absurd)
      } yield reached
      belowOne <- rules.disjElim(inner, fromBelowZero, fromZero)

      fromOne <- LogicError.lift(Kernel.assume(peeledParts._2)).flatMap(rules.disjIntro1(isTwo, _))
      belowTwo <- rules.disjElim(peeled, belowOne, fromOne)
      fromTwo <- LogicError.lift(Kernel.assume(splitParts._2)).flatMap(rules.disjIntro2(isOne, _))
      trivial <- rules.disjElim(split, belowTwo, fromTwo)

      onlyTrivial <- vocabulary
        .dividing(d, two)
        .flatMap(rules.disch(_, trivial))
        .flatMap(rules.gen(d, _))
      belowSuccessor <- vocabulary.fact(Peano.BelowSuccessor)
      aboveOne <- rules.spec(unit, belowSuccessor)
      unfolded <- Conv.unfold(primeDefinition, List(two))
      isPrime <- rules
        .conjIntro(aboveOne, onlyTrivial)
        .flatMap(pair => Conv.sym(unfolded).flatMap(e => LogicError.lift(Kernel.eqMp(e, pair))))
      result <- vocabulary.checked(Modular.PrimeTwo, isPrime)
    } yield result
  }

  /** `~(SUC (SUC ZERO) = ZERO)`, which the enumeration above closes two of its cases with. */
  private def twoIsNotZero(
    vocabulary: Vocabulary,
    two: Term,
    unit: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      positive <- vocabulary.fact(Peano.SuccessorPositive).flatMap(rules.spec(unit, _))
      isZero <- LogicError.lift(Term.eq(two, vocabulary.zeroTerm))
      assumed <- LogicError.lift(Kernel.assume(isZero))
      partial <- LogicError.lift(Term.app(vocabulary.strict, vocabulary.zeroTerm))
      moved <- Conv
        .apTerm(partial, assumed)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, positive)))
      never <- vocabulary.fact(Peano.StrictIrreflexive).flatMap(rules.spec(vocabulary.zeroTerm, _))
      absurd <- rules.notElim(never, moved)
      result <- rules.notIntro(isZero, absurd)
    } yield result
  }

  private def aboveOneIsNotZero(
    vocabulary: Vocabulary,
    above: Kernel.Thm,
    number: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      notBelowZero <- vocabulary.fact(Peano.NotBelowZero)
      unit <- vocabulary.one
      isZero <- LogicError.lift(Term.eq(number, vocabulary.zeroTerm))
      assumed <- LogicError.lift(Kernel.assume(isZero))
      partial <- LogicError.lift(Term.app(vocabulary.strict, unit))
      carried <- Conv.apTerm(partial, assumed)
      atZero <- LogicError.lift(Kernel.eqMp(carried, above))
      never <- rules.spec(unit, notBelowZero)
      absurd <- rules.notElim(never, atZero)
      result <- rules.notIntro(isZero, absurd)
    } yield result
  }

  /**
   * [[Euclid]], by the classical argument and one case split on whether `p` divides `a`.
   *
   * The interesting half is the one where it does not. `NUM_GCD a p` divides `p`, so
   * [[PrimeDivisor]] makes it one or `p`; it cannot be `p`, because it divides `a` and `p` does
   * not. So it is one, and [[Bezout]] gives an identity with `SUC ZERO` on the right. Multiplying
   * it through by `b` makes both products multiples of `p` — one because `p` divides `a * b` by
   * hypothesis, the other because it has `p` as a factor — and [[DividesSummand]] leaves `b`.
   */
  private def euclidsLemma(
    vocabulary: Vocabulary,
    primeAbove: Kernel.Thm,
    primeDivisor: Kernel.Thm,
    bezout: Kernel.Thm,
    summand: Kernel.Thm,
    multiple: Kernel.Thm,
    introduction: Kernel.Thm,
    gcdLeft: Kernel.Thm,
    gcdRight: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val p = variable("p")
    val a = variable("a")
    val b = variable("b")

    for {
      middle <- vocabulary.peano.naturals.classical.fact(Classical.ExcludedMiddle)

      primeTerm <- vocabulary.isPrime(p)
      assumedPrime <- LogicError.lift(Kernel.assume(primeTerm))
      productTerm <- vocabulary.product(a, b)
      dividesProductTerm <- vocabulary.dividing(p, productTerm)
      assumedProduct <- LogicError.lift(Kernel.assume(dividesProductTerm))

      dividesATerm <- vocabulary.dividing(p, a)
      dividesBTerm <- vocabulary.dividing(p, b)
      goal <- logic.mkDisj(dividesATerm, dividesBTerm)

      above <- rules.spec(p, primeAbove).flatMap(rules.mp(_, assumedPrime))
      notZero <- aboveOneIsNotZero(vocabulary, above, p)
      aIsZero <- LogicError.lift(Term.eq(a, vocabulary.zeroTerm))
      notA <- logic.mkNot(aIsZero)
      guard <- rules.disjIntro2(notA, notZero)

      assumedDivides <- LogicError.lift(Kernel.assume(dividesATerm))
      positiveCase <- rules.disjIntro1(dividesBTerm, assumedDivides)

      notDividesTerm <- logic.mkNot(dividesATerm)
      assumedNot <- LogicError.lift(Kernel.assume(notDividesTerm))
      negativeCase <- euclidWhenItDoesNotDivide(
        vocabulary, goal, dividesATerm, assumedPrime, assumedProduct, assumedNot,
        guard, primeDivisor, bezout, summand, multiple, introduction, gcdLeft, gcdRight, p, a, b
      )

      split <- rules.spec(dividesATerm, middle)
      decided <- rules.disjElim(split, positiveCase, negativeCase)
      dischargedProduct <- rules.disch(dividesProductTerm, decided)
      discharged <- rules.disch(primeTerm, dischargedProduct)
      general <- rules.genAll(discharged, List(p, a, b))
      result <- vocabulary.checked(Euclid, general)
    } yield result
  }

  /** The half of [[euclidsLemma]] where `p` does not divide the first factor. */
  private def euclidWhenItDoesNotDivide(
    vocabulary: Vocabulary,
    goal: Term,
    dividesATerm: Term,
    prime: Kernel.Thm,
    dividesProduct: Kernel.Thm,
    doesNotDivide: Kernel.Thm,
    guard: Kernel.Thm,
    primeDivisor: Kernel.Thm,
    bezout: Kernel.Thm,
    summand: Kernel.Thm,
    multiple: Kernel.Thm,
    introduction: Kernel.Thm,
    gcdLeft: Kernel.Thm,
    gcdRight: Kernel.Thm,
    p: FVar,
    a: FVar,
    b: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      gcd <- vocabulary.greatestCommonDivisor(a, p)
      dividesModulus <- rules.specAll(gcdRight, List(a, p)).flatMap(rules.mp(_, guard))
      split <- rules
        .specAll(primeDivisor, List(p, gcd))
        .flatMap(rules.mp(_, prime))
        .flatMap(rules.mp(_, dividesModulus))
      halves <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isOne, isPrime) = halves

      // The gcd cannot be `p` itself, because it divides `a` and `p` does not.
      assumedIsPrime <- LogicError.lift(Kernel.assume(isPrime))
      dividesFirst <- rules.specAll(gcdLeft, List(a, p)).flatMap(rules.mp(_, guard))
      carried <- Conv.apTerm(vocabulary.dividesConstant, assumedIsPrime).flatMap(Conv.apThm(_, a))
      wouldDivide <- LogicError.lift(Kernel.eqMp(carried, dividesFirst))
      absurd <- rules.notElim(doesNotDivide, wouldDivide)
      primeCase <- rules.falsityElim(goal, absurd)

      // So it is one, and the identity carries `SUC ZERO` through the multiplication by `b`.
      assumedIsOne <- LogicError.lift(Kernel.assume(isOne))
      instance <- rules.specAll(bezout, List(a, p)).flatMap(rules.mp(_, guard))
      opened <- vocabulary.openAll(instance, Set(p, a, b), List("x", "y"))
      first <- opened.variables.headOption
        .toRight(NotOfForm("a claim about two numbers", instance.conclusion))
      second <- opened.variables
        .lift(1)
        .toRight(NotOfForm("a claim about two numbers", instance.conclusion))
      disjuncts <- logic
        .destDisj(opened.body.conclusion)
        .toRight(NotOfForm("a disjunction", opened.body.conclusion))
      (aReaches, pReaches) = disjuncts

      assumedAReaches <- LogicError.lift(Kernel.assume(aReaches))
      overA <- euclidBranch(
        vocabulary, summand, multiple, introduction, assumedAReaches, assumedIsOne,
        dividesProduct, p, a, b, first, second, productSideReaches = true
      )
      firstCase <- rules.disjIntro2(dividesATerm, overA)

      assumedPReaches <- LogicError.lift(Kernel.assume(pReaches))
      overP <- euclidBranch(
        vocabulary, summand, multiple, introduction, assumedPReaches, assumedIsOne,
        dividesProduct, p, a, b, second, first, productSideReaches = false
      )
      secondCase <- rules.disjIntro2(dividesATerm, overP)

      decided <- rules.disjElim(opened.body, firstCase, secondCase)
      closed <- vocabulary.closeAll(opened, decided)
      result <- rules.disjElim(split, closed, primeCase)
    } yield result
  }

  /**
   * One branch of Euclid: an identity with one on the right, multiplied through by `b`.
   *
   * `dividendReaches` says which side of the identity the multiplier `a` is on, which decides which
   * of the two products is a multiple of `p` by hypothesis and which is one by carrying a factor of
   * `p`. Everything else is the same three identities.
   */
  private def euclidBranch(
    vocabulary: Vocabulary,
    summand: Kernel.Thm,
    multiple: Kernel.Thm,
    introduction: Kernel.Thm,
    reaches: Kernel.Thm,
    gcdIsOne: Kernel.Thm,
    dividesProduct: Kernel.Thm,
    p: Term,
    a: Term,
    b: Term,
    productFactor: Term,
    primeFactor: Term,
    productSideReaches: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      product <- vocabulary.product(a, b)

      // One in place of the gcd, and then both sides multiplied by `b`.
      carriedPartial <- vocabulary.rightOf(reaches).flatMap {
        case App(partial, _) => Right(partial)
        case other => Left(NotOfForm("a sum", other))
      }
      movedToOne <- Conv.apTerm(carriedPartial, gcdIsOne)
      withOne <- Conv.trans(reaches, movedToOne)
      scaled <- vocabulary.scaleOnTheRight(withOne, b)

      // The two sides in the shape the divisibility wants them, and why each one is a multiple.
      productSide <- vocabulary.product(product, productFactor)
      primeWitness <- vocabulary.product(primeFactor, b)
      primeSide <- vocabulary.product(p, primeWitness)
      dividesProductSide <- rules
        .specAll(multiple, List(p, product, productFactor))
        .flatMap(rules.mp(_, dividesProduct))
      dividesPrimeSide <- vocabulary.concludeDivides(
        introduction, p, primeSide, primeWitness, Conv.refl(primeSide)
      )

      reaching = if (productSideReaches) productSide else primeSide
      other = if (productSideReaches) primeSide else productSide
      dividesReaching = if (productSideReaches) dividesProductSide else dividesPrimeSide
      dividesOther = if (productSideReaches) dividesPrimeSide else dividesProductSide

      whole <- vocabulary.sum(other, b)
      opening <- vocabulary.leftOf(scaled).flatMap(vocabulary.identity(reaching, _))
      closing <- vocabulary.rightOf(scaled).flatMap(vocabulary.identity(_, whole))
      equation <- Conv.trans(opening, scaled).flatMap(Conv.trans(_, closing))

      result <- dividesWhatIsLeftOver(
        vocabulary, summand, p, dividesReaching, dividesOther, equation, other, b
      )
    } yield result
  }

  /* ------------------------------------------------- symmetry, and the remainder of a congruence */

  /**
   * [[GcdSym]], by two case splits whose third leaf is a reflexivity.
   *
   * The antisymmetry argument is the interesting one and it is written once: each of the two
   * greatest common divisors divides both arguments, so [[GcdDivides]] puts each one inside the
   * other and [[DividesAntisym]] makes them equal. It runs on the two leaves where the guard can be
   * discharged.
   *
   * The third leaf is where the guard cannot be discharged, and it needs no argument at all: there
   * both arguments are `ZERO`, so the two sides are the same term and the claim is a congruence out
   * of the two hypotheses. That is why this lemma is unguarded while everything around it is not.
   */
  private def greatestCommonDivisorIsSymmetric(
    vocabulary: Vocabulary,
    gcdLeft: Kernel.Thm,
    gcdRight: Kernel.Thm,
    gcdDivides: Kernel.Thm,
    antisymmetry: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val a = variable("a")
    val b = variable("b")

    def antisymmetric(
      guardAB: Kernel.Thm,
      guardBA: Kernel.Thm
    ): Either[LogicError, Kernel.Thm] =
      for {
        left <- vocabulary.greatestCommonDivisor(a, b)
        right <- vocabulary.greatestCommonDivisor(b, a)
        leftDividesA <- rules.specAll(gcdLeft, List(a, b)).flatMap(rules.mp(_, guardAB))
        leftDividesB <- rules.specAll(gcdRight, List(a, b)).flatMap(rules.mp(_, guardAB))
        rightDividesB <- rules.specAll(gcdLeft, List(b, a)).flatMap(rules.mp(_, guardBA))
        rightDividesA <- rules.specAll(gcdRight, List(b, a)).flatMap(rules.mp(_, guardBA))
        leftInside <- rules
          .conjIntro(leftDividesB, leftDividesA)
          .flatMap(pair =>
            rules
              .specAll(gcdDivides, List(b, a, left))
              .flatMap(rules.mp(_, guardBA))
              .flatMap(rules.mp(_, pair))
          )
        rightInside <- rules
          .conjIntro(rightDividesA, rightDividesB)
          .flatMap(pair =>
            rules
              .specAll(gcdDivides, List(a, b, right))
              .flatMap(rules.mp(_, guardAB))
              .flatMap(rules.mp(_, pair))
          )
        result <- rules
          .conjIntro(leftInside, rightInside)
          .flatMap(pair =>
            rules.specAll(antisymmetry, List(left, right)).flatMap(rules.mp(_, pair))
          )
      } yield result

    for {
      middle <- vocabulary.peano.naturals.classical.fact(Classical.ExcludedMiddle)
      aIsZero <- LogicError.lift(Term.eq(a, vocabulary.zeroTerm))
      bIsZero <- LogicError.lift(Term.eq(b, vocabulary.zeroTerm))
      notA <- logic.mkNot(aIsZero)
      notB <- logic.mkNot(bIsZero)
      aCases <- rules.spec(aIsZero, middle)

      fromNotA <- for {
        assumed <- LogicError.lift(Kernel.assume(notA))
        guardAB <- rules.disjIntro1(notB, assumed)
        guardBA <- rules.disjIntro2(notB, assumed)
        settled <- antisymmetric(guardAB, guardBA)
      } yield settled

      fromAZero <- for {
        assumedA <- LogicError.lift(Kernel.assume(aIsZero))
        bCases <- rules.spec(bIsZero, middle)
        fromNotB <- for {
          assumed <- LogicError.lift(Kernel.assume(notB))
          guardAB <- rules.disjIntro2(notA, assumed)
          guardBA <- rules.disjIntro1(notA, assumed)
          settled <- antisymmetric(guardAB, guardBA)
        } yield settled
        fromBZero <- for {
          assumedB <- LogicError.lift(Kernel.assume(bIsZero))
          settled <- bothVanish(vocabulary, a, b, assumedA, assumedB)
        } yield settled
        settled <- rules.disjElim(bCases, fromBZero, fromNotB)
      } yield settled

      settled <- rules.disjElim(aCases, fromAZero, fromNotA)
      general <- rules.genAll(settled, List(a, b))
      result <- vocabulary.checked(GcdSym, general)
    } yield result
  }

  /**
   * `NUM_GCD a b = NUM_GCD b a` where both arguments vanish, which is a congruence and not a proof.
   *
   * The leaf [[GcdName]]'s guard exists to exclude. Nothing is known about `NUM_GCD ZERO ZERO` and
   * nothing needs to be: both sides reduce to that one term.
   */
  private def bothVanish(
    vocabulary: Vocabulary,
    a: Term,
    b: Term,
    aIsZero: Kernel.Thm,
    bIsZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val zero = vocabulary.zeroTerm

    def collapse(first: Term, firstIsZero: Kernel.Thm, second: Term, secondIsZero: Kernel.Thm) =
      for {
        outer <- Conv.apTerm(vocabulary.gcdConstant, firstIsZero).flatMap(Conv.apThm(_, second))
        head <- LogicError.lift(Term.app(vocabulary.gcdConstant, zero))
        inner <- Conv.apTerm(head, secondIsZero)
        result <- Conv.trans(outer, inner)
      } yield result

    for {
      forwards <- collapse(a, aIsZero, b, bIsZero)
      backwards <- collapse(b, bIsZero, a, aIsZero)
      reversed <- Conv.sym(backwards)
      result <- Conv.trans(forwards, reversed)
    } yield result
  }

  /**
   * `NUM_LT ZERO m` from `NUM_LT s m`, which the remainder's own bound asks for.
   *
   * By [[Peano.Trichotomy]] rather than by an order lemma, because the one a reader reaches for,
   * `ZERO <= s` together with `s < m`, is a mixed transitivity and `Peano` holds the two pure ones.
   * The two branches that are not the answer are both closed by nothing being below zero.
   */
  private def modulusIsPositive(
    vocabulary: Vocabulary,
    modulus: Term,
    residue: Term,
    below: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val zero = vocabulary.zeroTerm

    for {
      notBelowZero <- vocabulary.fact(Peano.NotBelowZero)
      wanted <- vocabulary.belowTerm(zero, modulus)
      cases <- vocabulary
        .fact(Peano.Trichotomy)
        .flatMap(rules.specAll(_, List(zero, modulus)))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (positive, rest) = split
      restSplit <- logic.destDisj(rest).toRight(NotOfForm("a disjunction", rest))
      (equal, negative) = restSplit

      fromPositive <- LogicError.lift(Kernel.assume(positive))

      fromEqual <- for {
        assumed <- LogicError.lift(Kernel.assume(equal))
        reversed <- Conv.sym(assumed)
        head <- LogicError.lift(Term.app(vocabulary.strict, residue))
        carried <- Conv.apTerm(head, reversed)
        absurdly <- LogicError.lift(Kernel.eqMp(carried, below))
        never <- rules.spec(residue, notBelowZero)
        contradiction <- rules.notElim(never, absurdly)
        anything <- rules.falsityElim(wanted, contradiction)
      } yield anything

      fromNegative <- for {
        assumed <- LogicError.lift(Kernel.assume(negative))
        never <- rules.spec(modulus, notBelowZero)
        contradiction <- rules.notElim(never, assumed)
        anything <- rules.falsityElim(wanted, contradiction)
      } yield anything

      assumedRest <- LogicError.lift(Kernel.assume(rest))
      tail <- rules.disjElim(assumedRest, fromEqual, fromNegative)
      result <- rules.disjElim(cases, fromPositive, tail)
    } yield result
  }

  /**
   * [[ModOfCong]], which is [[DivisionUnique]] with the congruence opened.
   *
   * One number divided two ways: `a` is `m * (a div m) + (a mod m)` by [[DivisionAt]], and the
   * congruence says it is also `s` plus a multiple of `m` less a multiple of `m`. Putting the two
   * multiples on one side gives `m * ((a div m) + p) + (a mod m) = m * q + s`, and both remainders
   * are below `m`, so the division of one number with remainder being unique makes them equal.
   *
   * The rearrangement is the semiring's, which is the reason it is three lines rather than thirty:
   * `NUM_DIV` and `NUM_MOD` are atoms there, so the identity is about four opaque quantities and a
   * modulus.
   */
  private def remainderOfACongruence(
    vocabulary: Vocabulary,
    congElim: Kernel.Thm,
    divisionAt: Kernel.Thm,
    modBelow: Kernel.Thm,
    divisionUnique: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val m = variable("m")
    val a = variable("a")
    val s = variable("s")

    for {
      congruent <- vocabulary.congruence(m, a, s)
      assumedCong <- LogicError.lift(Kernel.assume(congruent))
      belowM <- vocabulary.belowTerm(s, m)
      assumedBelow <- LogicError.lift(Kernel.assume(belowM))

      positive <- modulusIsPositive(vocabulary, m, s, assumedBelow)
      remainder <- vocabulary.remainder(a, m)
      quotient <- vocabulary.quotient(a, m)
      remainderBelow <- rules.specAll(modBelow, List(a, m)).flatMap(rules.mp(_, positive))
      atA <- rules.specAll(divisionAt, List(a, m))
      opened <- rules.specAll(congElim, List(m, a, s)).flatMap(rules.mp(_, assumedCong))

      found <- withTwoWitnessesHere(vocabulary, opened, Set(m, a, s)) { (p, q, equation) =>
        for {
          combined <- vocabulary.sum(quotient, p)
          leftProduct <- vocabulary.product(m, combined)
          leftSum <- vocabulary.sum(leftProduct, remainder)
          rightProduct <- vocabulary.product(m, q)
          rightSum <- vocabulary.sum(rightProduct, s)
          scaled <- vocabulary.product(m, p)

          divided <- vocabulary.product(m, quotient).flatMap(vocabulary.sum(_, remainder))
          expanded <- vocabulary.sum(divided, scaled)
          rearranged <- vocabulary.identity(leftSum, expanded)
          carried <- Conv.apTerm(vocabulary.plus, atA).flatMap(Conv.apThm(_, scaled))
          reachesA <- Conv.trans(rearranged, carried)
          acrossCongruence <- Conv.trans(reachesA, equation)
          tail <- vocabulary.sum(s, rightProduct)
          swapped <- vocabulary.identity(tail, rightSum)
          asDivision <- Conv.trans(acrossCongruence, swapped)

          bounds <- rules.conjIntro(remainderBelow, assumedBelow)
          premise <- rules.conjIntro(asDivision, bounds)
          determined <- rules
            .specAll(divisionUnique, List(m, combined, remainder, q, s))
            .flatMap(rules.mp(_, premise))
          result <- rules.conjElim2(determined)
        } yield result
      }

      discharged <- rules.disch(belowM, found).flatMap(rules.disch(congruent, _))
      general <- rules.genAll(discharged, List(m, a, s))
      result <- vocabulary.checked(ModOfCong, general)
    } yield result
  }
}
