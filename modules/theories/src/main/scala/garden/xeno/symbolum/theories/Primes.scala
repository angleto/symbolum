package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Theorems about the primes that are results rather than infrastructure.
 *
 * `Modular` holds the arithmetic of divisibility, congruence and the greatest common divisor, and
 * everything in it is there because something above it needs it. This is the other kind: a theorem
 * somebody would want to read.
 *
 * **It is here and not in `Modular` because of one constant.** Euclid's theorem is proved from
 * `NUM_FACT`, and the factorial is defined in `Coding`, which is built over `Modular` rather than
 * under it. So the theorem cannot be stated one floor down, and putting it in `Coding` would make
 * that development's own first sentence false: `Coding` says it is the bottom of the Goedel
 * numbering, and this is not that.
 *
 * **It declares nothing**: no type, no constant, no definition, no axiom, so `Chain.widest` does
 * not move to it. `Deduction` is the other link of that kind and landed the same day.
 */
final class Primes private (
  val coding: Coding,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  published: Map[String, Kernel.Thm]
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** The arithmetic of divisibility this rests on. */
  val modular: Modular = coding.modular

  /** A derived fact of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Primes {

  /**
   * `|- !n. ?p. NUM_PRIME p /\ NUM_LT n p`
   *
   * Euclid's theorem: there is a prime above every number, which is what "there are infinitely many
   * primes" says in a logic with no notion of an infinite set. Stating it this way is not a
   * workaround for the missing notion, it is the statement Euclid proved.
   *
   * The proof is his. `n! + 1` is above one, so it has a prime factor `p` by
   * `Modular.NUM_PRIME_FACTOR`. If `p` were at most `n` it would divide `n!`, because every
   * positive number up to `n` does, and it divides `n! + 1` by choice, so it would divide their
   * difference, which is one. A prime is above one, and nothing above one divides one.
   *
   * **What it cost to prove was one missing lemma, and finding it is the point.**
   * `NUM_PRIME_FACTOR` did not exist: `NUM_PRIME_DIVISOR` is a letter away and says the opposite
   * direction, that a prime's divisors are one and itself. The theorem is reachable today only
   * because stating it exposed that.
   *
   * The subtraction the informal proof does is not done here. `NUM_DIVIDES_SUMMAND` says that a
   * number dividing `a` and dividing `a + b` divides `b`, which is the same step without ever
   * writing a difference, and `num` has only a truncated subtraction to write one with.
   */
  val Unbounded: String = "NUM_PRIME_UNBOUNDED"

  /**
   * `|- !p q. NUM_LT ZERO q ==> ~(NUM_MUL p p = NUM_MUL (SUC (SUC ZERO)) (NUM_MUL q q))`
   *
   * No square is twice a square, except where the denominator is zero. This is the arithmetic
   * content of the irrationality of the square root of two, and it is **not** that statement. The
   * classical sentence is `Root.SQRT_TWO_IRRATIONAL`, which could not be written here because this
   * development is built before `sqrt` exists, and whose proof is this fact carried across
   * `real_of_num`. What this proves is the thing the classical proof actually establishes, that the
   * equation has no solution in positive naturals, and the name says that.
   *
   * The proof is the descent, run through `NUM_LEAST` rather than through an infinite regress: take
   * the **least** `q` for which some `p` solves it. Two divides `p * p`, hence `p`, because two is
   * prime, so `p` is `2k`; cancelling the two leaves `q * q = 2 * (k * k)`, which makes `k` another
   * solution's denominator. It is positive, or `q * q` would be zero, and it is below `q`, or the
   * squares would satisfy `x + x <= x`. The least one had no smaller one, and that is the
   * contradiction.
   *
   * **Three lemmas had to be proved before this could be**, and all three were absent for the same
   * reason: nothing in the development had needed to multiply an inequality.
   * `Peano.NUM_MUL_CANCEL_LEFT` does the cancelling, `Peano.NUM_MUL_MONOTONE` compares the squares,
   * and `Modular.NUM_PRIME_TWO` is what Euclid's lemma is applied at.
   */
  val SquareNotDouble: String = "NUM_SQUARE_NOT_DOUBLE"

  /**
   * `|- !p f n. NUM_PRIME p ==> NUM_DIVIDES p (NUM_PROD f n) ==>
   * (?i. NUM_LT i n /\ NUM_DIVIDES p (f i))`
   *
   * Euclid's lemma over a whole family: a prime dividing a product divides one of its factors, and
   * the index of that factor is what comes back. `Modular.Euclid` is the two-factor case and is
   * the step of the induction here; what this adds is that a product of unbounded length is still
   * reducible to one factor, which is the half a factorisation argument spends.
   *
   * The base is the empty product, which is one, and a prime dividing one would be one.
   */
  val PrimeDividesProduct: String = "NUM_PRIME_DIVIDES_PROD"

  /**
   * `|- !f k. (!i. NUM_LT i k ==> NUM_PRIME (f i)) ==> NUM_PROD f k = SUC ZERO ==> k = ZERO`
   *
   * A product of primes is one only when there is nothing in it, which is what says the empty
   * factorisation of one is the only factorisation of one.
   *
   * It is not an induction. The last factor divides the whole product by `Coding.ProductDivides`,
   * so at a positive length it divides one and is one, and no prime is.
   */
  val PrimeProductIsOne: String = "NUM_PRIME_PROD_ONE"

  /**
   * `|- !n. NUM_LT (SUC ZERO) n ==> (?f k. NUM_LT ZERO k /\ (!i. NUM_LT i k ==> NUM_PRIME (f i))
   * /\ (!a b. NUM_LT a b /\ NUM_LT b k ==> NUM_LE (f a) (f b)) /\ NUM_PROD f k = n)`
   *
   * The existence half of the fundamental theorem of arithmetic: every number above one is a
   * product of primes, and the family can be taken **non-decreasing**.
   *
   * **The monotonicity is not decoration and it is why this is not the textbook induction.** A
   * factorisation is unique only up to the order of its factors, and this repository has no
   * permutations, no finite sets and no multisets to say "up to the order" with. Asking the family
   * to be sorted is what makes [[FactorisationUnique]] an equation between two families rather
   * than a statement about a rearrangement, and it costs the existence proof one thing: the factor
   * taken off is the **greatest** prime divisor rather than any one of them, so that it can be
   * appended on the right, where `NUM_PROD`'s recurrence puts the new factor.
   *
   * That greatest divisor is where `Peano.GreatestBounded` is spent: the prime divisors of `n` are
   * a non-empty set, by `Modular.PrimeFactor`, bounded by `n` itself, by `Modular.DividesBound`,
   * and `num` has no maximum operator to take it with instead.
   *
   * The induction is `Peano.StrongInduction` and not the ordinary one, because the number the
   * hypothesis is wanted at is `n` divided by a prime rather than `n`'s predecessor.
   */
  val Factorisation: String = "NUM_FACTORISATION"

  /**
   * `|- !f k g j. (!i. NUM_LT i k ==> NUM_PRIME (f i)) ==>
   * (!a b. NUM_LT a b /\ NUM_LT b k ==> NUM_LE (f a) (f b)) ==>
   * (!i. NUM_LT i j ==> NUM_PRIME (g i)) ==>
   * (!a b. NUM_LT a b /\ NUM_LT b j ==> NUM_LE (g a) (g b)) ==>
   * NUM_PROD f k = NUM_PROD g j ==> k = j /\ (!i. NUM_LT i k ==> f i = g i)`
   *
   * The uniqueness half, and the reason [[Factorisation]] sorts its family: two non-decreasing
   * families of primes with the same product are the same family, index for index, and have the
   * same length. That is the sentence a reader can compare with "the factorisation is unique"
   * without having to trust whoever wrote it, which is the criterion this statement was chosen by.
   *
   * **What is deliberately not stated is "the same multiset".** That form needs permutations or a
   * multiplicity function, neither of which exists here; this one needs neither and says the same
   * thing about sorted families. A multiplicity version would be shorter to state and would leave
   * a reader checking a different claim than the one they came for.
   *
   * The proof is strong induction on the common value, and the step is the classical argument:
   * the last factor of each family is the greatest prime divisor of that value, because every
   * prime dividing the product divides one of the factors ([[PrimeDividesProduct]]) and a prime
   * dividing a prime is that prime, so each last factor bounds the other and they are equal.
   * Cancelling it leaves two shorter factorisations of a strictly smaller number, which is where
   * the hypothesis applies and why the induction has to be the strong one.
   *
   * No hypothesis asks the two lengths to be positive, and none is needed: at length zero the
   * product is one, and [[PrimeProductIsOne]] is what closes that corner.
   */
  val FactorisationUnique: String = "NUM_FACTORISATION_UNIQUE"

  /**
   * `|- !p a. NUM_PRIME p ==> NUM_CONG p (NUM_POW a p) a`
   *
   * Fermat's little theorem, in the form that needs no division: `a^p` and `a` leave the same
   * remainder on division by a prime `p`, for every `a`, including the multiples of `p`. The route
   * is the freshman's dream below it and an induction on `a`; `Freshman` has the argument.
   */
  val Fermat: String = "NUM_FERMAT"

  /**
   * `|- !p a. NUM_PRIME p ==> NUM_CONG p (NUM_POW (SUC a) p) (NUM_ADD (NUM_POW a p) (SUC 0))`
   *
   * `(a + 1)^p` is congruent to `a^p + 1` modulo a prime, because every other term of the binomial
   * expansion is a multiple of `p`.
   */
  val Freshman: String = "NUM_FRESHMAN"

  /**
   * `|- !a n. NUM_POW (SUC a) n = NUM_SUM (\k. NUM_CHOOSE n k * NUM_POW a k) (SUC n)`
   *
   * The binomial theorem on `num`, at `x + 1`, which is the case Fermat needs. It is proved by
   * Pascal's rule and not carried from `Series.POWER_BINOMIAL` across `real_of_num`, which would
   * work and would rest a theorem about the naturals on the sixteen axioms of the reals.
   */
  val Binomial: String = "NUM_BINOMIAL"

  /** `|- !f g n. NUM_SUM (\k. f k + g k) n = NUM_SUM f n + NUM_SUM g n` */
  val SumAdd: String = "NUM_SUM_ADD"

  /** `|- !f c n. NUM_SUM (\k. f k * c) n = NUM_SUM f n * c` */
  val SumTimes: String = "NUM_SUM_MUL"

  /** `|- !d g n. (!u. NUM_LT u n ==> NUM_DIVIDES d (g u)) ==> NUM_DIVIDES d (NUM_SUM g n)` */
  val DividesSum: String = "NUM_DIVIDES_SUM"

  /** `|- !p n. NUM_PRIME p ==> NUM_LT n p ==> ~(NUM_DIVIDES p (NUM_FACT n))` */
  val NotDividesFactorial: String = "NUM_PRIME_NOT_DIVIDES_FACT"

  /** `|- !p k. NUM_PRIME p ==> NUM_LT 0 k ==> NUM_LT k p ==> NUM_DIVIDES p (NUM_CHOOSE p k)` */
  val DividesChoose: String = "NUM_PRIME_DIVIDES_CHOOSE"

  /**
   * `|- !n a. 0 < n ==> NUM_GCD a n = SUC 0 ==> NUM_CONG n (NUM_POW a (NUM_TOTIENT n)) (SUC 0)`
   *
   * Euler's theorem: `a` to the number of residues coprime to `n` leaves remainder one, for every
   * `a` coprime to `n`. `Euler` derives it by permuting the product of the coprime residues, and says
   * which permutation and why.
   */
  val Euler: String = "NUM_EULER"

  /**
   * `|- !f n s. (!i. i < n ==> s i < n) ==> (!i j. i < n ==> j < n ==> s i = s j ==> i = j) ==>
   *     (!j. j < n ==> ?i. i < n /\ s i = j) ==> NUM_PROD (\i. f (s i)) n = NUM_PROD f n`
   *
   * A product over `[0, n)` does not change when its indices are permuted. Surjectivity is a
   * hypothesis rather than a consequence of injectivity, for the reason `Euler` gives.
   */
  val ProdPermute: String = "NUM_PROD_PERMUTE"

  /**
   * `|- !f g k n. k < n ==> (!i. i < n ==> ~(i = k) ==> f i = g i) ==>
   *     NUM_PROD f n * g k = NUM_PROD g n * f k`
   *
   * Two products that differ at one index trade the factor there. What the permutation's induction
   * stitches with.
   */
  val ProdPoint: String = "NUM_PROD_POINT"

  /** `|- !m f g n. (!i. i < n ==> NUM_CONG m (f i) (g i)) ==> NUM_CONG m (NUM_PROD f n) (NUM_PROD g n)` */
  val ProdCongMod: String = "NUM_PROD_CONG_MOD"

  /** `|- !f g n. NUM_PROD (\i. f i * g i) n = NUM_PROD f n * NUM_PROD g n` */
  val ProdMul: String = "NUM_PROD_MUL"

  /** `|- !p a n. NUM_PROD (\i. COND (p i) a (SUC 0)) n = NUM_POW a (NUM_SUM (\i. COND (p i) (SUC 0) 0) n)` */
  val ProdCondPow: String = "NUM_PROD_COND_POW"

  /** `|- !n a. 0 < n ==> NUM_GCD a n = SUC 0 ==> ?b. NUM_CONG n (a * b) (SUC 0)`: a coprime residue has an inverse. */
  val Inverse: String = "NUM_INVERSE"

  /** `|- !n x. 0 < n ==> NUM_GCD x n = SUC 0 ==> NUM_GCD (NUM_MOD x n) n = SUC 0` */
  val GcdMod: String = "NUM_GCD_MOD"

  /** `|- !n x y. 0 < n ==> NUM_CONG n (x * y) (SUC 0) ==> NUM_GCD y n = SUC 0`: an inverse is coprime. */
  val UnitCoprime: String = "NUM_UNIT_COPRIME"

  /**
   * `|- !p n. NUM_LT (SUC 0) p ==> NUM_LT n (NUM_POW p n)`
   *
   * A power of anything above one outgrows its exponent. What bounds the exponents whose power
   * divides a positive number, which the existence of [[ValuationSpec]] needs.
   */
  val BelowPower: String = "NUM_LT_POW"

  /** `|- !p j k. NUM_LE j k ==> NUM_DIVIDES (NUM_POW p j) (NUM_POW p k)`: a smaller power divides a larger. */
  val PowerDividesPower: String = "NUM_POW_DIVIDES_POW"

  /**
   * `|- !p n k. NUM_DIVIDES (NUM_POW p k) n ==> ~(NUM_DIVIDES (NUM_POW p (SUC k)) n) ==> NUM_VALUATION p n = k`
   *
   * The characterisation of the p-adic valuation, with no hypothesis on `p` or `n`: an exponent
   * whose power divides and whose next power does not is the valuation. Every other fact about
   * `NUM_VALUATION` is proved by exhibiting such an exponent. `Valuation` has the argument.
   */
  val ValuationUnique: String = "NUM_VALUATION_UNIQUE"

  /**
   * `|- !p n. NUM_LT (SUC 0) p ==> NUM_LT 0 n ==> NUM_DIVIDES (NUM_POW p (NUM_VALUATION p n)) n /\
   *     ~(NUM_DIVIDES (NUM_POW p (SUC (NUM_VALUATION p n))) n)`
   *
   * The valuation passes its own test, wherever the test has a passing exponent: above one and at a
   * positive number. Outside that the definition's choice is over an empty set and nothing is said.
   */
  val ValuationSpec: String = "NUM_VALUATION_SPEC"

  /**
   * `|- !p n k. NUM_LT (SUC 0) p ==> NUM_LT 0 n ==>
   *     (NUM_DIVIDES (NUM_POW p k) n = NUM_LE k (NUM_VALUATION p n))`
   *
   * The register reading of divisibility by a prime power: `p^k` divides `n` exactly when the
   * register of `p` in `n` holds at least `k`.
   */
  val ValuationDivides: String = "NUM_VALUATION_DIVIDES"

  /** `|- !p n. ~(NUM_DIVIDES p n) ==> NUM_VALUATION p n = 0` */
  val ValuationNotDivides: String = "NUM_VALUATION_NOT_DIVIDES"

  /** `|- !p k. NUM_PRIME p ==> NUM_VALUATION p (NUM_POW p k) = k` */
  val ValuationPower: String = "NUM_VALUATION_POW"

  /**
   * `|- !p a b. NUM_PRIME p ==> NUM_LT 0 a ==> NUM_LT 0 b ==>
   *     NUM_VALUATION p (a * b) = NUM_VALUATION p a + NUM_VALUATION p b`
   *
   * The valuation at a prime turns a product into a sum: multiplying by a number adds its
   * registers. The prime is what Euclid's lemma needs, and both positivities are what existence
   * needs; `Valuation` says why neither can be dropped.
   */
  val ValuationMul: String = "NUM_VALUATION_MUL"

  /**
   * `|- !b c. NUM_LT 0 b ==> NUM_LT 0 c ==>
   *     (NUM_DIVIDES b c = (!p. NUM_PRIME p ==> NUM_LE (NUM_VALUATION p b) (NUM_VALUATION p c)))`
   *
   * Divisibility between positive numbers, read one prime register at a time: `b` divides `c`
   * exactly when no register of `b` holds more than the same register of `c`. It is what turns
   * FRACTRAN's test, whether a denominator divides the state, into a comparison of registers.
   */
  val DividesByValuations: String = "NUM_DIVIDES_VALUATION"

  /**
   * `|- !m n. NUM_LT 0 m ==> NUM_LT 0 n ==>
   *     (!p. NUM_PRIME p ==> NUM_VALUATION p m = NUM_VALUATION p n) ==> m = n`
   *
   * A positive number is determined by its registers: the uniqueness of factorisation in the form
   * a register machine reads it, and what identifies the state after a FRACTRAN step.
   */
  val ValuationDetermines: String = "NUM_VALUATION_EXT"

  /**
   * `|- !n a b. NUM_LT 0 n ==> NUM_LT 0 a ==> NUM_LT 0 b ==>
   *     (NUM_DIVIDES b (n * a) = (!p. NUM_PRIME p ==> NUM_LE (NUM_VALUATION p b) (NUM_VALUATION p n + NUM_VALUATION p a)))`
   *
   * Whether the fraction `a/b` applies to the state `n`, read on the registers.
   */
  val FractionApplies: String = "NUM_DIVIDES_MUL_VALUATION"

  /**
   * `|- !p n a b. NUM_PRIME p ==> NUM_LT 0 n ==> NUM_LT 0 a ==> NUM_LT 0 b ==> NUM_DIVIDES b (n * a) ==>
   *     NUM_VALUATION p (NUM_DIV (n * a) b) + NUM_VALUATION p b = NUM_VALUATION p n + NUM_VALUATION p a`
   *
   * What applying `a/b` does to the register of `p`: the numerator's is added and the
   * denominator's taken away, stated with the subtraction on the other side.
   */
  val FractionEffect: String = "NUM_VALUATION_DIV"

  /**
   * `|- !n a q m. NUM_LT 0 n ==> NUM_LT 0 a ==> NUM_LT 0 q ==> NUM_DIVIDES q (n * a) ==>
   *     ((m = NUM_DIV (n * a) q) = (NUM_LT 0 m /\
   *       (!p. NUM_PRIME p ==> NUM_VALUATION p m + NUM_VALUATION p q = NUM_VALUATION p n + NUM_VALUATION p a)))`
   *
   * Where a fraction that applies sends the state, on the registers and in both directions: the
   * quotient is the one positive number with those registers.
   */
  val FractionLands: String = "NUM_DIV_VALUATION"

  /**
   * `|- !p q. NUM_PRIME p ==> NUM_PRIME q ==> ~(q = p) ==> NUM_VALUATION p q = 0`
   *
   * A prime holds nothing in another prime's register.
   */
  val ValuationOtherPrime: String = "NUM_VALUATION_OTHER_PRIME"

  /**
   * The statement [[FactorisationUnique]] is proved through, which carries the value explicitly.
   *
   * The induction is on the value of the two products, and a statement that mentions the value
   * only as `NUM_PROD f k` gives the strong induction nothing to be about. So the published
   * statement is read off this one at `n := NUM_PROD f k`, where the fifth premise is reflexivity
   * and the sixth is the published statement's own.
   */
  private val UniqueAtValue: String =
    "!n:num. !f:num -> num. !k:num. !g:num -> num. !j:num. " +
      "(!i:num. NUM_LT i k ==> NUM_PRIME (f i)) ==> " +
      "(!a:num. !b:num. NUM_LT a b /\\ NUM_LT b k ==> NUM_LE (f a) (f b)) ==> " +
      "(!i:num. NUM_LT i j ==> NUM_PRIME (g i)) ==> " +
      "(!a:num. !b:num. NUM_LT a b /\\ NUM_LT b j ==> NUM_LE (g a) (g b)) ==> " +
      "NUM_PROD f k = n ==> NUM_PROD g j = n ==> " +
      "k = j /\\ (!i:num. NUM_LT i k ==> f i = g i)"

  val Statements: Vector[(String, String)] = Vector(
    Unbounded -> "!n:num. ?p:num. NUM_PRIME p /\\ NUM_LT n p",
    SquareNotDouble ->
      ("!p:num q:num. NUM_LT ZERO q ==> " +
        "~(NUM_MUL p p = NUM_MUL (SUC (SUC ZERO)) (NUM_MUL q q))"),
    PrimeDividesProduct ->
      ("!p:num. !f:num -> num. !n:num. NUM_PRIME p ==> NUM_DIVIDES p (NUM_PROD f n) ==> " +
        "(?i:num. NUM_LT i n /\\ NUM_DIVIDES p (f i))"),
    PrimeProductIsOne ->
      ("!f:num -> num. !k:num. (!i:num. NUM_LT i k ==> NUM_PRIME (f i)) ==> " +
        "NUM_PROD f k = SUC ZERO ==> k = ZERO"),
    Factorisation ->
      ("!n:num. NUM_LT (SUC ZERO) n ==> (?f:num -> num. ?k:num. NUM_LT ZERO k /\\ " +
        "(!i:num. NUM_LT i k ==> NUM_PRIME (f i)) /\\ " +
        "(!a:num. !b:num. NUM_LT a b /\\ NUM_LT b k ==> NUM_LE (f a) (f b)) /\\ " +
        "NUM_PROD f k = n)"),
    FactorisationUnique ->
      ("!f:num -> num. !k:num. !g:num -> num. !j:num. " +
        "(!i:num. NUM_LT i k ==> NUM_PRIME (f i)) ==> " +
        "(!a:num. !b:num. NUM_LT a b /\\ NUM_LT b k ==> NUM_LE (f a) (f b)) ==> " +
        "(!i:num. NUM_LT i j ==> NUM_PRIME (g i)) ==> " +
        "(!a:num. !b:num. NUM_LT a b /\\ NUM_LT b j ==> NUM_LE (g a) (g b)) ==> " +
        "NUM_PROD f k = NUM_PROD g j ==> " +
        "k = j /\\ (!i:num. NUM_LT i k ==> f i = g i)"),
    SumAdd ->
      "!f:num -> num. !g:num -> num. !n:num. NUM_SUM (\\k:num. f k + g k) n = NUM_SUM f n + NUM_SUM g n",
    SumTimes -> "!f:num -> num. !c:num. !n:num. NUM_SUM (\\k:num. f k * c) n = NUM_SUM f n * c",
    Binomial ->
      "!a:num. !n:num. NUM_POW (SUC a) n = NUM_SUM (\\k:num. NUM_CHOOSE n k * NUM_POW a k) (SUC n)",
    DividesSum ->
      ("!d:num. !g:num -> num. !n:num. (!u:num. NUM_LT u n ==> NUM_DIVIDES d (g u)) ==> " +
        "NUM_DIVIDES d (NUM_SUM g n)"),
    NotDividesFactorial ->
      "!p:num. !n:num. NUM_PRIME p ==> NUM_LT n p ==> ~(NUM_DIVIDES p (NUM_FACT n))",
    DividesChoose ->
      "!p:num. !k:num. NUM_PRIME p ==> NUM_LT 0 k ==> NUM_LT k p ==> NUM_DIVIDES p (NUM_CHOOSE p k)",
    Freshman ->
      "!p:num. !a:num. NUM_PRIME p ==> NUM_CONG p (NUM_POW (SUC a) p) (NUM_ADD (NUM_POW a p) (SUC 0))",
    Fermat -> "!p:num. !a:num. NUM_PRIME p ==> NUM_CONG p (NUM_POW a p) a",
    ProdPoint ->
      ("!f:num->num. !g:num->num. !k:num. !n:num. NUM_LT k n ==> " +
        "(!i:num. NUM_LT i n ==> ~(i = k) ==> f i = g i) ==> NUM_PROD f n * g k = NUM_PROD g n * f k"),
    ProdPermute ->
      ("!f:num->num. !n:num. !s:num->num. (!i:num. NUM_LT i n ==> NUM_LT (s i) n) ==> " +
        "(!i:num. !j:num. NUM_LT i n ==> NUM_LT j n ==> s i = s j ==> i = j) ==> " +
        "(!j:num. NUM_LT j n ==> ?i:num. NUM_LT i n /\\ s i = j) ==> " +
        "NUM_PROD (\\i:num. f (s i)) n = NUM_PROD f n"),
    ProdCongMod ->
      ("!m:num. !f:num->num. !g:num->num. !n:num. (!i:num. NUM_LT i n ==> NUM_CONG m (f i) (g i)) ==> " +
        "NUM_CONG m (NUM_PROD f n) (NUM_PROD g n)"),
    ProdMul ->
      "!f:num->num. !g:num->num. !n:num. NUM_PROD (\\i:num. f i * g i) n = NUM_PROD f n * NUM_PROD g n",
    ProdCondPow ->
      ("!p:num->bool. !a:num. !n:num. NUM_PROD (\\i:num. COND (p i) a (SUC 0)) n = " +
        "NUM_POW a (NUM_SUM (\\i:num. COND (p i) (SUC 0) 0) n)"),
    Inverse -> "!n:num. !a:num. NUM_LT 0 n ==> NUM_GCD a n = SUC 0 ==> ?b:num. NUM_CONG n (a * b) (SUC 0)",
    GcdMod -> "!n:num. !x:num. NUM_LT 0 n ==> NUM_GCD x n = SUC 0 ==> NUM_GCD (NUM_MOD x n) n = SUC 0",
    UnitCoprime ->
      "!n:num. !x:num. !y:num. NUM_LT 0 n ==> NUM_CONG n (x * y) (SUC 0) ==> NUM_GCD y n = SUC 0",
    Euler ->
      "!n:num. !a:num. NUM_LT 0 n ==> NUM_GCD a n = SUC 0 ==> NUM_CONG n (NUM_POW a (NUM_TOTIENT n)) (SUC 0)",
    BelowPower -> "!p:num. !n:num. NUM_LT (SUC 0) p ==> NUM_LT n (NUM_POW p n)",
    PowerDividesPower ->
      "!p:num. !j:num. !k:num. NUM_LE j k ==> NUM_DIVIDES (NUM_POW p j) (NUM_POW p k)",
    ValuationUnique ->
      ("!p:num. !n:num. !k:num. NUM_DIVIDES (NUM_POW p k) n ==> " +
        "~(NUM_DIVIDES (NUM_POW p (SUC k)) n) ==> NUM_VALUATION p n = k"),
    ValuationSpec ->
      ("!p:num. !n:num. NUM_LT (SUC 0) p ==> NUM_LT 0 n ==> " +
        "NUM_DIVIDES (NUM_POW p (NUM_VALUATION p n)) n /\\ " +
        "~(NUM_DIVIDES (NUM_POW p (SUC (NUM_VALUATION p n))) n)"),
    ValuationDivides ->
      ("!p:num. !n:num. !k:num. NUM_LT (SUC 0) p ==> NUM_LT 0 n ==> " +
        "(NUM_DIVIDES (NUM_POW p k) n = NUM_LE k (NUM_VALUATION p n))"),
    ValuationNotDivides -> "!p:num. !n:num. ~(NUM_DIVIDES p n) ==> NUM_VALUATION p n = 0",
    ValuationPower -> "!p:num. !k:num. NUM_PRIME p ==> NUM_VALUATION p (NUM_POW p k) = k",
    ValuationMul ->
      ("!p:num. !a:num. !b:num. NUM_PRIME p ==> NUM_LT 0 a ==> NUM_LT 0 b ==> " +
        "NUM_VALUATION p (a * b) = NUM_VALUATION p a + NUM_VALUATION p b"),
    ValuationOtherPrime ->
      "!p:num. !q:num. NUM_PRIME p ==> NUM_PRIME q ==> ~(q = p) ==> NUM_VALUATION p q = 0",
    DividesByValuations ->
      ("!b:num. !c:num. NUM_LT 0 b ==> NUM_LT 0 c ==> (NUM_DIVIDES b c = " +
        "(!p:num. NUM_PRIME p ==> NUM_LE (NUM_VALUATION p b) (NUM_VALUATION p c)))"),
    ValuationDetermines ->
      ("!m:num. !n:num. NUM_LT 0 m ==> NUM_LT 0 n ==> " +
        "(!p:num. NUM_PRIME p ==> NUM_VALUATION p m = NUM_VALUATION p n) ==> m = n"),
    FractionApplies ->
      ("!n:num. !a:num. !b:num. NUM_LT 0 n ==> NUM_LT 0 a ==> NUM_LT 0 b ==> (NUM_DIVIDES b (n * a) = " +
        "(!p:num. NUM_PRIME p ==> NUM_LE (NUM_VALUATION p b) (NUM_VALUATION p n + NUM_VALUATION p a)))"),
    FractionEffect ->
      ("!p:num. !n:num. !a:num. !b:num. NUM_PRIME p ==> NUM_LT 0 n ==> NUM_LT 0 a ==> NUM_LT 0 b ==> " +
        "NUM_DIVIDES b (n * a) ==> " +
        "NUM_VALUATION p (NUM_DIV (n * a) b) + NUM_VALUATION p b = NUM_VALUATION p n + NUM_VALUATION p a"),
    FractionLands ->
      ("!n:num. !a:num. !q:num. !m:num. NUM_LT 0 n ==> NUM_LT 0 a ==> NUM_LT 0 q ==> NUM_DIVIDES q (n * a) ==> " +
        "((m = NUM_DIV (n * a) q) = (NUM_LT 0 m /\\ (!p:num. NUM_PRIME p ==> " +
        "NUM_VALUATION p m + NUM_VALUATION p q = NUM_VALUATION p n + NUM_VALUATION p a)))")
  )

  /** Build it over the arithmetic that holds the factorial. It extends nothing. */
  def construct(coding: Coding, induct: Induct): Either[LogicError, Primes] = {
    val builder = new Builder(coding)
    val peano = coding.peano
    def lookup(name: String): Either[LogicError, Kernel.Thm] =
      peano.fact(name)
        .orElse(peano.naturals.fact(name))
        .orElse(coding.modular.fact(name))
        .orElse(coding.fact(name))
        .orElse(peano.naturals.classical.fact(name))
        .left
        .map(_ => MissingDefinition(name))
    val fermat =
      for {
        semiring <- Semiring.construct(peano)
        kit = garden.xeno.symbolum.theories.Freshman.Kit(
          coding.logic, coding.theory, coding.notation, semiring, induct, lookup)
        derived <- garden.xeno.symbolum.theories.Freshman.derive(kit)
        totient <- coding.modular.definition(Modular.TotientName)
        euler <- garden.xeno.symbolum.theories.Euler.derive(kit, totient)
        strictOrder <- peano.definition(Peano.StrictOrder)
        nonStrictOrder <- peano.definition(Peano.NonStrictOrder)
        valuationDefinition <- coding.modular.definition(Modular.ValuationName)
        choice <- peano.naturals.classical.axiom(Classical.Choice)
        valuation <- garden.xeno.symbolum.theories.Valuation.derive(
          kit,
          garden.xeno.symbolum.theories.Valuation.Definitions(strictOrder, nonStrictOrder, valuationDefinition, choice))
      } yield derived ++ euler ++ valuation
    try
      Right(
        new Primes(
          coding,
          coding.theory,
          coding.notation,
          coding.logic,
          Map(
            Unbounded -> builder.checked(Unbounded, builder.unbounded),
            SquareNotDouble -> builder.checked(SquareNotDouble, builder.squareNotDouble),
            PrimeDividesProduct ->
              builder.checked(PrimeDividesProduct, builder.primeDividesProduct),
            PrimeProductIsOne -> builder.checked(PrimeProductIsOne, builder.primeProductIsOne),
            Factorisation -> builder.checked(Factorisation, builder.factorisation),
            FactorisationUnique ->
              builder.checked(FactorisationUnique, builder.factorisationUnique)
          ) ++ fermat
            .fold(error => throw new RefusedHere(error), identity)
            .map { case (name, theorem) => name -> builder.checked(name, theorem) }
        )
      )
    catch { case refused: RefusedHere => Left(refused.error) }
  }

  /** Carry a refusal out of a derivation written in direct style. */
  private final class RefusedHere(val error: LogicError) extends RuntimeException

  /**
   * Euclid's argument, written in direct style for the reason `Provability` gives.
   *
   * The proof is a case analysis whose branches are independent, and a `for` comprehension over
   * `Either` turns "which obligation failed" into "which binding came first".
   */
  private final class Builder(coding: Coding) {
    private val theory = coding.theory
    private val notation = coding.notation
    private val logic = coding.logic
    private val rules = logic.rules
    private val modular = coding.modular
    private val peano = coding.peano
    private val numbers = TyApp(Natural.TypeName, Nil)
    private val relation = Type.fun(numbers, Type.fun(numbers, Type.Bool))
    private val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))

    private def force[T](result: Either[LogicError, T]): T =
      result.fold(error => throw new RefusedHere(error), identity)

    private def app(head: Term, args: List[Term]): Term =
      force(LogicError.lift(Term.appAll(head, args)))
    private def text(source: String): Term =
      force(Parser.term(theory, notation, source, numbers))
    private def pf(name: String): Kernel.Thm = force(peano.fact(name))
    private def mf(name: String): Kernel.Thm = force(modular.fact(name))
    private def cf(name: String): Kernel.Thm = force(peano.naturals.classical.fact(name))

    private val dividesConstant =
      force(LogicError.lift(theory.constant(Modular.DividesName, relation)))
    private val primeConstant = force(LogicError.lift(
      theory.constant(Modular.PrimeName, Type.fun(numbers, Type.Bool))))
    private val belowConstant =
      force(LogicError.lift(theory.constant(Peano.StrictOrder, relation)))
    private val atMostConstant =
      force(LogicError.lift(theory.constant(Peano.NonStrictOrder, relation)))
    private val plus = force(LogicError.lift(theory.constant(Peano.Addition, arithmetic)))
    private val times =
      force(LogicError.lift(theory.constant(Peano.Multiplication, arithmetic)))
    private val semiring = force(Semiring.construct(peano))
    private val factorial = force(LogicError.lift(
      theory.constant(Coding.FactorialName, Type.fun(numbers, numbers))))

    private def divides(a: Term, b: Term): Term = app(dividesConstant, List(a, b))
    private def mul(a: Term, b: Term): Term = app(times, List(a, b))
    private def square(x: Term): Term = mul(x, x)
    private def doubled(x: Term): Term = mul(two, x)
    private def eq(a: Term, b: Term): Term = force(LogicError.lift(Term.eq(a, b)))
    private def isPrime(a: Term): Term = app(primeConstant, List(a))
    private def below(a: Term, b: Term): Term = app(belowConstant, List(a, b))
    private val one = text("SUC ZERO")
    private val zero = text("ZERO")
    private val two = text("SUC (SUC ZERO)")

    private def assume(claim: Term): Kernel.Thm = force(LogicError.lift(Kernel.assume(claim)))
    private def conj(a: Term, b: Term): Term = force(logic.mkConj(a, b))
    private def absurd(negation: Kernel.Thm, held: Kernel.Thm): Kernel.Thm =
      force(rules.notElim(negation, held))

    private def open(existential: Kernel.Thm, name: String, taken: Set[FVar])(
      reach: (FVar, Kernel.Thm) => Kernel.Thm
    ): Kernel.Thm = {
      val predicate = logic.destExistsPredicate(existential.conclusion)
        .getOrElse(throw new RefusedHere(NotOfForm("an existential", existential.conclusion)))
      // The witness takes its type from the predicate rather than being a number. Every
      // existential this file opened until 2026-09-16 was over `num` and the type was written in;
      // the factorisation's is over a family, and a hard-wired `num` refuses it by complaining
      // about an application rather than about the quantifier it is opening.
      val domain = Type
        .destFun(Term.typeOf(predicate))
        .map(_._1)
        .getOrElse(throw new RefusedHere(NotOfForm("a predicate", predicate)))
      val fresh = Conv.freshVariable(
        name, domain, taken ++ Term.freeVariables(existential.conclusion))
      val body = Term
        .destEq(force(Conv.betaRoot(app(predicate, List(fresh)))).conclusion)
        .map(_._2)
        .getOrElse(throw new RefusedHere(NotOfForm("an equation", fresh)))
      force(rules.existsElim(existential, fresh, reach(fresh, assume(body))))
    }

    /* ------------------------------------ what the factorisation derivations reach for */

    private val successorConstant =
      force(LogicError.lift(theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))))
    private val productConstant = force(LogicError.lift(theory.constant(
      Coding.ProductName, Type.fun(Type.fun(numbers, numbers), Type.fun(numbers, numbers)))))
    private val conditional = force(LogicError.lift(theory.constant(
      Classical.Conditional, Type.fun(Type.Bool, Type.fun(numbers, Type.fun(numbers, numbers))))))
    private val driver: Induct =
      Induct.overNaturals(logic, force(peano.naturals.fact(Natural.Induction)))

    private def nf(name: String): Kernel.Thm = force(peano.naturals.fact(name))

    /**
     * A conditional law at `num`, which is where its type variable is instantiated.
     *
     * `Classical.CondTrue` and `CondFalse` are stated at `'a`, and `Rules.spec` reads a quantifier
     * at the type it was written at rather than at the one the argument has, so specialising one at
     * a number without this is a refusal about a witness of the wrong type.
     */
    private def condAt(name: String): Kernel.Thm =
      Kernel.instType(Map(Classical.TypeVariable -> numbers), cf(name))
    private def cdf(name: String): Kernel.Thm = force(coding.fact(name))

    private def suc(x: Term): Term = app(successorConstant, List(x))
    private def atMost(left: Term, right: Term): Term = app(atMostConstant, List(left, right))
    private def prodOf(family: Term, length: Term): Term =
      app(productConstant, List(family, length))
    private def at(family: Term, index: Term): Term =
      force(LogicError.lift(Term.app(family, index)))

    /** The statement this development publishes under `name`, read against the signature. */
    private def published(name: String): Term =
      force(
        Statements
          .collectFirst { case (key, source) if key == name => source }
          .toRight(MissingDefinition(name))
          .flatMap(Parser.proposition(theory, notation, _)))

    private def claim(source: String): Term =
      force(Parser.proposition(theory, notation, source))

    private def impParts(term: Term): (Term, Term) =
      logic.destImp(term).getOrElse(throw new RefusedHere(NotOfForm("an implication", term)))

    private def conjParts(term: Term): (Term, Term) =
      logic.destConj(term).getOrElse(throw new RefusedHere(NotOfForm("a conjunction", term)))

    /** The first `count` antecedents of an implication chain, and what is left under them. */
    private def peel(term: Term, count: Int): (Vector[Term], Term) =
      if (count == 0) (Vector.empty, term)
      else {
        val (antecedent, rest) = impParts(term)
        val (others, conclusion) = peel(rest, count - 1)
        (antecedent +: others, conclusion)
      }

    private def forallPredicate(term: Term): Term =
      logic
        .destForallPredicate(term)
        .getOrElse(throw new RefusedHere(NotOfForm("a universal", term)))

    private def existsPredicate(term: Term): Term =
      logic
        .destExistsPredicate(term)
        .getOrElse(throw new RefusedHere(NotOfForm("an existential", term)))

    /**
     * The body of a quantification at one argument, contracted at the root and nowhere else.
     *
     * The root and nowhere else is what `Rules.existsIntro` asks a witness's proof to be stated
     * over, so a body opened here can be handed back to it unchanged.
     */
    private def openAt(quantified: Term, argument: Term): Term = {
      val predicate = logic
        .destForallPredicate(quantified)
        .orElse(logic.destExistsPredicate(quantified))
        .getOrElse(throw new RefusedHere(NotOfForm("a quantification", quantified)))
      val contraction =
        force(LogicError.lift(Term.app(predicate, argument)).flatMap(Conv.betaRoot))
      Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .getOrElse(throw new RefusedHere(NotOfForm("an equation", contraction.conclusion)))
    }

    private def reduced(theorem: Kernel.Thm): Kernel.Thm =
      force(
        Conv
          .betaNormalise(theorem.conclusion)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))

    private def normalise(term: Term): Term =
      Term
        .destEq(force(Conv.betaNormalise(term)).conclusion)
        .map(_._2)
        .getOrElse(throw new RefusedHere(NotOfForm("an equation", term)))

    /** A theorem proved in normal form, restated over the term a caller wrote with redexes in it. */
    private def unreduce(target: Term, theorem: Kernel.Thm): Kernel.Thm =
      force(
        Conv
          .betaNormalise(target)
          .flatMap(Conv.sym)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, theorem))))

    /** Rewrite inside `context`, by congruence and not by rewriting. */
    private def carryInto(context: Term, equation: Kernel.Thm, theorem: Kernel.Thm): Kernel.Thm =
      force(
        Conv
          .apTerm(context, equation)
          .flatMap(congruence => LogicError.lift(Kernel.eqMp(congruence, theorem))))

    /** Rewrite the left argument of a binary relation, leaving the right one alone. */
    private def carryLeft(
      relation: Term,
      equation: Kernel.Thm,
      right: Term,
      theorem: Kernel.Thm
    ): Kernel.Thm =
      force(
        Conv
          .apTerm(relation, equation)
          .flatMap(Conv.apThm(_, right))
          .flatMap(congruence => LogicError.lift(Kernel.eqMp(congruence, theorem))))

    private def freeOf(term: Term): Set[FVar] = Term.freeVariables(term)

    private def argumentOf(term: Term): Term = term match {
      case App(_, argument) => argument
      case other => throw new RefusedHere(NotOfForm("an application", other))
    }

    private def leftArgument(term: Term): Term = term match {
      case App(App(_, left), _) => left
      case other => throw new RefusedHere(NotOfForm("a binary application", other))
    }

    private def rightArgument(term: Term): Term = term match {
      case App(App(_, _), right) => right
      case other => throw new RefusedHere(NotOfForm("a binary application", other))
    }

    /** `|- NUM_LT ZERO x` from `|- NUM_LT (SUC ZERO) x`, which four derivations below want. */
    private def positiveFromAboveOne(aboveOne: Kernel.Thm, x: Term): Kernel.Thm =
      force(
        rules
          .specAll(pf(Peano.StrictTransitive), List(zero, one, x))
          .flatMap(implication =>
            rules
              .conjIntro(force(rules.spec(zero, pf(Peano.SuccessorPositive))), aboveOne)
              .flatMap(rules.mp(implication, _))))

    /** `|- NUM_LT ZERO (f i)` for every index below `length`, which is what a product wants. */
    private def factorsArePositive(
      family: Term,
      length: Term,
      primes: Kernel.Thm,
      taken: Set[FVar]
    ): Kernel.Thm = {
      val index = Conv.freshVariable("i", numbers, taken)
      val premise = below(index, length)
      val assumed = assume(premise)
      val isPrimeHere = force(rules.spec(index, primes).flatMap(rules.mp(_, assumed)))
      val aboveOne = force(
        rules.spec(at(family, index), mf(Modular.PrimeAboveOne)).flatMap(rules.mp(_, isPrimeHere)))
      force(
        rules
          .disch(premise, positiveFromAboveOne(aboveOne, at(family, index)))
          .flatMap(rules.gen(index, _)))
    }

    def unbounded: Kernel.Thm = {
      val n = Term.variable("n", numbers)
      val fact = app(factorial, List(n))
      val bigger = app(plus, List(fact, one))

      // `1 < n! + 1`, because `0 < n!` and adding one to both keeps the order.
      val biggerAboveOne = {
        val positive = force(rules.spec(n, force(coding.fact(Coding.FactorialPositive))))
        val shifted = force(rules.specAll(pf(Peano.AddStrictlyMonotone), List(one, zero, fact))
          .flatMap(rules.mp(_, positive)))
        val identity = force(rules.spec(one, pf(Peano.AddAtZero)))
        val commuted = force(rules.specAll(pf(Peano.AddCommutative), List(one, fact)))
        val carried = force(
          Conv.apThm(force(Conv.apTerm(belowConstant, identity)), app(plus, List(one, fact)))
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, shifted))))
        force(Conv.apTerm(app(belowConstant, List(one)), commuted)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, carried))))
      }

      val hasFactor = force(
        rules.spec(bigger, mf(Modular.PrimeFactor)).flatMap(rules.mp(_, biggerAboveOne)))

      val above = open(hasFactor, "p", Set(n)) { (prime, atPrime) =>
        val prime_ = force(rules.conjElim1(atPrime))
        val dividesBigger = force(rules.conjElim2(atPrime))
        val target = below(n, prime)
        val aboveOne =
          force(rules.spec(prime, mf(Modular.PrimeAboveOne)).flatMap(rules.mp(_, prime_)))

        /** From `p <= n`, falsity: `p` divides `n!` and `n! + 1`, so it divides one. */
        def whenAtMost(atMostN: Kernel.Thm): Kernel.Thm = {
          val positive = force(rules.conjIntro(
            force(rules.specAll(pf(Peano.StrictTransitive), List(zero, one, prime))
              .flatMap(rules.mp(_, force(rules.conjIntro(
                force(rules.spec(zero, pf(Peano.SuccessorPositive))), aboveOne))))),
            atMostN))
          val dividesFactorial = force(
            rules.specAll(force(coding.fact(Coding.FactorialDivides)), List(prime, n))
              .flatMap(rules.mp(_, positive)))
          val dividesOne = force(rules.specAll(mf(Modular.DividesSummand), List(prime, fact, one))
            .flatMap(rules.mp(_, dividesFactorial))
            .flatMap(rules.mp(_, dividesBigger)))
          val equalsOne = force(
            rules.spec(prime, mf(Modular.DividesOne)).flatMap(rules.mp(_, dividesOne)))
          val reflexive = force(Conv.apTerm(app(belowConstant, List(one)), equalsOne)
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, aboveOne))))
          absurd(force(rules.spec(one, pf(Peano.StrictIrreflexive))), reflexive)
        }

        val cases = force(rules.specAll(pf(Peano.Trichotomy), List(prime, n)))
        val first = logic.destDisj(cases.conclusion)
          .getOrElse(throw new RefusedHere(NotOfForm("a disjunction", cases.conclusion)))
        val rest = logic.destDisj(first._2)
          .getOrElse(throw new RefusedHere(NotOfForm("a disjunction", first._2)))

        val fromBelow = force(rules.falsityElim(target, whenAtMost(
          force(rules.specAll(pf(Peano.AtMostFromBelow), List(prime, n))
            .flatMap(rules.mp(_, assume(first._1)))))))
        val fromEqual = force(rules.falsityElim(target, whenAtMost(
          force(Conv.apTerm(app(atMostConstant, List(prime)), assume(rest._1))
            .flatMap(equation => LogicError.lift(
              Kernel.eqMp(equation, force(rules.spec(prime, pf(Peano.Reflexive))))))))))
        val fromAbove = assume(rest._2)

        val tail = assume(force(logic.mkDisj(rest._1, rest._2)))
        val reached = force(rules.disjElim(cases, fromBelow,
          force(rules.disjElim(tail, fromEqual, fromAbove))))

        val witness = Conv.freshVariable("q", numbers, Set(n, prime))
        val wanted = force(logic.mkExists(witness, conj(isPrime(witness), below(n, witness))))
        force(rules.existsIntro(
          logic.destExistsPredicate(wanted)
            .getOrElse(throw new RefusedHere(NotOfForm("an existential", wanted))),
          prime,
          force(rules.conjIntro(prime_, reached))))
      }

      force(rules.gen(n, above))
    }

    private def disjunctsOf(subject: Term, count: Int): Vector[Term] =
      if (count == 1) Vector(subject)
      else {
        val (first, rest) = logic.destDisj(subject)
          .getOrElse(throw new RefusedHere(NotOfForm("a disjunction", subject)))
        first +: disjunctsOf(rest, count - 1)
      }

    /** A number that is not zero is above it, which the descent needs twice. */
    private def positiveFromNonZero(notZero: Kernel.Thm, x: Term): Kernel.Thm = {
      val cases = force(rules.specAll(pf(Peano.BelowOrEqual), List(zero, x))
        .flatMap(rules.mp(_, force(rules.spec(x, pf(Peano.ZeroIsLeast))))))
      val parts = disjunctsOf(cases.conclusion, 2)
      val fromEqual = force(rules.falsityElim(below(zero, x),
        absurd(notZero, force(Conv.sym(assume(parts(1)))))))
      force(rules.disjElim(cases, assume(parts(0)), fromEqual))
    }

    /** [[SquareNotDouble]]. The descent is written out in that name's docstring. */
    def squareNotDouble: Kernel.Thm = {
      val twoPositive = force(rules.spec(one, pf(Peano.SuccessorPositive)))
      val p = Term.variable("p", numbers)
      val q = Term.variable("q", numbers)

      /** `?y. y * y = 2 * (x * x)`, the claim that `x` is a solution's denominator. */
      def solutionFor(x: Term): Term = {
        val y = Conv.freshVariable("y", numbers, Set(p, q) ++ Term.freeVariables(x))
        force(logic.mkExists(y, eq(square(y), doubled(square(x)))))
      }
      def propertyAt(x: Term): Term = conj(below(zero, x), solutionFor(x))
      def witnessSolution(x: Term, witness: Term, proof: Kernel.Thm): Kernel.Thm =
        force(rules.existsIntro(
          logic.destExistsPredicate(solutionFor(x))
            .getOrElse(throw new RefusedHere(NotOfForm("an existential", solutionFor(x)))),
          witness, proof))

      val positiveQ = assume(below(zero, q))
      val equationTerm = eq(square(p), doubled(square(q)))
      val equation = assume(equationTerm)

      val subject = Conv.freshVariable("x", numbers, Set(p, q))
      val property = force(LogicError.lift(Term.abs(subject, propertyAt(subject))))

      val inhabited = {
        val existential = force(logic.mkExists(subject, propertyAt(subject)))
        force(rules.existsIntro(
          logic.destExistsPredicate(existential)
            .getOrElse(throw new RefusedHere(NotOfForm("an existential", existential))),
          q,
          force(rules.conjIntro(positiveQ, witnessSolution(q, p, equation)))))
      }

      val least = {
        val instance = force(rules.spec(property, pf(Peano.LeastNumber)))
        val reduced = force(Conv.betaNormalise(instance.conclusion)
          .flatMap(step => LogicError.lift(Kernel.eqMp(step, instance))))
        force(rules.mp(reduced, inhabited))
      }

      val descent = open(least, "b", Set(p, q)) { (b, atB) =>
        val holds = force(rules.conjElim1(atB))
        val isLeast = force(rules.conjElim2(atB))
        val positiveB = force(rules.conjElim1(holds))

        open(force(rules.conjElim2(holds)), "a", Set(p, q, b)) { (a, atA) =>
          // Two divides `a * a`, hence `a`, because two is prime.
          val dividesSquare = force(
            rules.specAll(mf(Modular.DividesIntro), List(two, square(a), square(b)))
              .flatMap(rules.mp(_, atA)))
          val split = force(rules.specAll(mf(Modular.Euclid), List(two, a, a))
            .flatMap(rules.mp(_, mf(Modular.PrimeTwo)))
            .flatMap(rules.mp(_, dividesSquare)))
          val parts = disjunctsOf(split.conclusion, 2)
          val dividesA = force(rules.disjElim(split, assume(parts(0)), assume(parts(1))))
          val halves = force(rules.specAll(mf(Modular.DividesElim), List(two, a))
            .flatMap(rules.mp(_, dividesA)))

          open(halves, "k", Set(p, q, b, a)) { (k, isDouble) =>
            // `(2k)(2k) = a * a = 2 * (b * b)`, and the two cancels off both sides.
            val rebuilt = force(LogicError.lift(Kernel.mkComb(
              force(Conv.apTerm(times, isDouble)), isDouble)))
            val asDouble = force(Conv.sym(rebuilt).flatMap(Conv.trans(_, atA)))
            val expanded = force(
              semiring.prove(mul(doubled(k), doubled(k)), doubled(doubled(square(k)))))
            val stacked = force(Conv.sym(expanded).flatMap(Conv.trans(_, asDouble)))
            val cancelled = force(rules
              .specAll(pf(Peano.MulCancelsLeft), List(two, doubled(square(k)), square(b)))
              .flatMap(rules.mp(_, twoPositive))
              .flatMap(rules.mp(_, stacked)))
            val squareOfB = force(Conv.sym(cancelled))

            val squarePositive = force(rules.specAll(pf(Peano.MulPositive), List(b, b))
              .flatMap(rules.mp(_, positiveB))
              .flatMap(rules.mp(_, positiveB)))

            // `k` is not zero, or `b * b` would be.
            val positiveK = {
              val isZero = eq(k, zero)
              val cases = force(rules.spec(isZero, cf(Classical.ExcludedMiddle)))
              val caseParts = disjunctsOf(cases.conclusion, 2)
              val fromZero = {
                val atZero = assume(caseParts(0))
                val squareIsZero = force(LogicError.lift(Kernel.mkComb(
                  force(Conv.apTerm(times, atZero)), atZero)))
                val moved = force(Conv.trans(squareOfB, force(Conv.trans(
                  force(Conv.apTerm(app(times, List(two)), squareIsZero)),
                  force(semiring.prove(doubled(square(zero)), zero))))))
                val absurdity = force(Conv.apTerm(app(belowConstant, List(zero)), moved)
                  .flatMap(step => LogicError.lift(Kernel.eqMp(step, squarePositive))))
                force(rules.falsityElim(below(zero, k),
                  absurd(force(rules.spec(zero, pf(Peano.StrictIrreflexive))), absurdity)))
              }
              force(rules.disjElim(cases, fromZero,
                positiveFromNonZero(assume(caseParts(1)), k)))
            }

            val squareOfKPositive = force(rules.specAll(pf(Peano.MulPositive), List(k, k))
              .flatMap(rules.mp(_, positiveK))
              .flatMap(rules.mp(_, positiveK)))

            /** From `b <= k`, falsity: the squares would then satisfy `x + x <= x`. */
            def whenNotBelow(atMostK: Kernel.Thm): Kernel.Thm = {
              val first = force(rules.specAll(pf(Peano.MulMonotone), List(b, b, k))
                .flatMap(rules.mp(_, atMostK)))
              val second = force(rules.specAll(pf(Peano.MulMonotone), List(k, b, k))
                .flatMap(rules.mp(_, atMostK)))
              val commuted = force(rules.specAll(pf(Peano.MulCommutative), List(b, k)))
              val aligned = force(
                Conv.apThm(force(Conv.apTerm(atMostConstant, commuted)), square(k))
                  .flatMap(Conv.sym)
                  .flatMap(step => LogicError.lift(Kernel.eqMp(step, second))))
              val chained = force(
                rules.specAll(pf(Peano.Transitive), List(square(b), mul(b, k), square(k)))
                  .flatMap(rules.mp(_, force(rules.conjIntro(first, aligned)))))

              val asSum = force(semiring.prove(
                doubled(square(k)), app(plus, List(square(k), square(k)))))
              val moved = force(Conv
                .apThm(force(Conv.apTerm(atMostConstant,
                  force(Conv.trans(squareOfB, asSum)))), square(k))
                .flatMap(step => LogicError.lift(Kernel.eqMp(step, chained))))
              val other = force(rules.specAll(pf(Peano.AtMostSum), List(square(k), square(k))))
              val equal = force(rules.specAll(pf(Peano.AntiSymmetric),
                List(app(plus, List(square(k), square(k))), square(k)))
                .flatMap(rules.mp(_, force(rules.conjIntro(moved, other)))))
              val isZero = force(rules.specAll(pf(Peano.AddCancels), List(square(k), square(k)))
                .flatMap(rules.mp(_, equal)))
              val absurdity = force(Conv.apTerm(app(belowConstant, List(zero)), isZero)
                .flatMap(step => LogicError.lift(Kernel.eqMp(step, squareOfKPositive))))
              absurd(force(rules.spec(zero, pf(Peano.StrictIrreflexive))), absurdity)
            }

            val belowB = {
              val cases = force(rules.specAll(pf(Peano.Trichotomy), List(k, b)))
              val three = disjunctsOf(cases.conclusion, 3)
              val target = below(k, b)
              val fromEqual = force(rules.falsityElim(target, whenNotBelow(
                force(Conv.apTerm(app(atMostConstant, List(b)), force(Conv.sym(assume(three(1)))))
                  .flatMap(step => LogicError.lift(
                    Kernel.eqMp(step, force(rules.spec(b, pf(Peano.Reflexive))))))))))
              val fromAbove = force(rules.falsityElim(target, whenNotBelow(
                force(rules.specAll(pf(Peano.AtMostFromBelow), List(b, k))
                  .flatMap(rules.mp(_, assume(three(2))))))))
              val tail = assume(force(logic.mkDisj(three(1), three(2))))
              force(rules.disjElim(cases, assume(three(0)),
                force(rules.disjElim(tail, fromEqual, fromAbove))))
            }

            val refused = {
              val instance = force(rules.spec(k, isLeast).flatMap(rules.mp(_, belowB)))
              force(Conv.betaNormalise(instance.conclusion)
                .flatMap(step => LogicError.lift(Kernel.eqMp(step, instance))))
            }
            absurd(refused, force(rules.conjIntro(positiveK, witnessSolution(k, b, squareOfB))))
          }
        }
      }

      force(rules.notIntro(equationTerm, descent)
        .flatMap(rules.disch(below(zero, q), _))
        .flatMap(rules.genAll(_, List(p, q))))
    }

    /* ---------------------------------------------- the fundamental theorem of arithmetic */

    /** [[PrimeDividesProduct]], by induction on the length with `Modular.Euclid` as the step. */
    lazy val primeDividesProduct: Kernel.Thm =
      force(
        driver.proveBy(
          published(PrimeDividesProduct),
          goal => Right(primeDividesEmpty(goal)),
          step => Right(primeDividesLonger(step))))

    /** The base: the empty product is one, and a prime dividing one would be one. */
    private def primeDividesEmpty(goal: Term): Kernel.Thm = {
      val (primeTerm, rest) = impParts(goal)
      val (dividesTerm, conclusion) = impParts(rest)
      val subject = argumentOf(primeTerm)
      val family = leftArgument(rightArgument(dividesTerm))
      val isPrimeHere = assume(primeTerm)
      val dividesEmpty = assume(dividesTerm)

      val empty = force(rules.spec(family, cdf(Coding.ProductAtZero)))
      val dividesOne = carryInto(app(dividesConstant, List(subject)), empty, dividesEmpty)
      val isOne =
        force(rules.spec(subject, mf(Modular.DividesOne)).flatMap(rules.mp(_, dividesOne)))
      val aboveOne =
        force(rules.spec(subject, mf(Modular.PrimeAboveOne)).flatMap(rules.mp(_, isPrimeHere)))
      val absurdity = carryInto(app(belowConstant, List(one)), isOne, aboveOne)

      force(
        rules
          .falsityElim(
            conclusion,
            absurd(force(rules.spec(one, pf(Peano.StrictIrreflexive))), absurdity))
          .flatMap(rules.disch(dividesTerm, _))
          .flatMap(rules.disch(primeTerm, _)))
    }

    /** The step: Euclid on the recurrence, and the index comes from whichever half answered. */
    private def primeDividesLonger(step: Induct.Step): Kernel.Thm = {
      val (primeTerm, rest) = impParts(step.goal)
      val (dividesTerm, conclusion) = impParts(rest)
      val subject = argumentOf(primeTerm)
      val family = leftArgument(rightArgument(dividesTerm))
      val isPrimeHere = assume(primeTerm)
      val dividesLonger = assume(dividesTerm)

      val recurrence =
        force(rules.specAll(cdf(Coding.ProductAtSuccessor), List(family, step.variable)))
      val split = carryInto(app(dividesConstant, List(subject)), recurrence, dividesLonger)
      val shorter = prodOf(family, step.variable)
      val newest = at(family, step.variable)
      val cases = force(
        rules
          .specAll(mf(Modular.Euclid), List(subject, shorter, newest))
          .flatMap(rules.mp(_, isPrimeHere))
          .flatMap(rules.mp(_, split)))
      val parts = disjunctsOf(cases.conclusion, 2)
      val belowSuccessor = force(rules.spec(step.variable, pf(Peano.BelowSuccessor)))

      def witnessAt(point: Term, isBelow: Kernel.Thm, dividing: Kernel.Thm): Kernel.Thm =
        force(
          rules.existsIntro(
            existsPredicate(conclusion),
            point,
            force(rules.conjIntro(isBelow, dividing))))

      val fromShorter = {
        val assumed = assume(parts(0))
        val found = force(rules.mp(step.hypothesis, isPrimeHere).flatMap(rules.mp(_, assumed)))
        open(found, "i", freeOf(step.goal) + step.variable) { (index, atIndex) =>
          val isBelow = force(rules.conjElim1(atIndex))
          val dividing = force(rules.conjElim2(atIndex))
          val carried = force(
            rules
              .specAll(
                pf(Peano.StrictTransitive),
                List(index, step.variable, suc(step.variable)))
              .flatMap(implication =>
                rules.conjIntro(isBelow, belowSuccessor).flatMap(rules.mp(implication, _))))
          witnessAt(index, carried, dividing)
        }
      }
      val fromNewest = witnessAt(step.variable, belowSuccessor, assume(parts(1)))

      force(
        rules
          .disjElim(cases, fromShorter, fromNewest)
          .flatMap(rules.disch(dividesTerm, _))
          .flatMap(rules.disch(primeTerm, _)))
    }

    /** [[PrimeProductIsOne]]: at a positive length the last factor would divide one. */
    lazy val primeProductIsOne: Kernel.Thm = {
      val statement = published(PrimeProductIsOne)
      val (binders, body) = force(Logic.stripForall(statement))
      val family = binders(0)
      val length = binders(1)
      val (antecedents, conclusion) = peel(body, 2)
      val primes = assume(antecedents(0))
      val isOne = assume(antecedents(1))
      val taken = freeOf(statement) ++ binders.toSet

      val cases = force(rules.spec(length, nf(Natural.ZeroOrSuccessor)))
      val parts = disjunctsOf(cases.conclusion, 2)

      val fromSuccessor = open(assume(parts(1)), "m", taken) { (predecessor, isSuccessor) =>
        val belowLength = carryInto(
          app(belowConstant, List(predecessor)),
          force(Conv.sym(isSuccessor)),
          force(rules.spec(predecessor, pf(Peano.BelowSuccessor))))
        val last = at(family, predecessor)
        val lastDivides = force(
          rules
            .specAll(cdf(Coding.ProductDivides), List(family, predecessor, length))
            .flatMap(rules.mp(_, belowLength)))
        val dividesOne = carryInto(app(dividesConstant, List(last)), isOne, lastDivides)
        val equalsOne =
          force(rules.spec(last, mf(Modular.DividesOne)).flatMap(rules.mp(_, dividesOne)))
        val isPrimeHere =
          force(rules.spec(predecessor, primes).flatMap(rules.mp(_, belowLength)))
        val aboveOne =
          force(rules.spec(last, mf(Modular.PrimeAboveOne)).flatMap(rules.mp(_, isPrimeHere)))
        val absurdity = carryInto(app(belowConstant, List(one)), equalsOne, aboveOne)
        force(
          rules.falsityElim(
            conclusion,
            absurd(force(rules.spec(one, pf(Peano.StrictIrreflexive))), absurdity)))
      }

      force(
        rules
          .disjElim(cases, assume(parts(0)), fromSuccessor)
          .flatMap(rules.disch(antecedents(1), _))
          .flatMap(rules.disch(antecedents(0), _))
          .flatMap(rules.genAll(_, List(family, length))))
    }

    /**
     * [[Factorisation]]: strong induction, taking the greatest prime divisor off the right.
     *
     * The greatest one rather than any one, because `NUM_PROD`'s recurrence appends on the right
     * and the family has to come back non-decreasing. Everything else is the textbook argument:
     * the quotient is smaller, so the induction hypothesis factors it, and the new factor is at
     * least every factor of the quotient because those divide it and it divides the subject.
     */
    lazy val factorisation: Kernel.Thm = {
      val statement = published(Factorisation)
      val instance =
        reduced(force(rules.spec(forallPredicate(statement), pf(Peano.StrongInduction))))
      val (stepGoal, _) = impParts(instance.conclusion)
      val subject = Conv.freshVariable("n", numbers, freeOf(statement))
      val (hypothesisTerm, claimAt) = impParts(openAt(stepGoal, subject))
      val hypothesis = assume(hypothesisTerm)
      val (aboveOneTerm, existential) = impParts(claimAt)
      val aboveOne = assume(aboveOneTerm)
      val taken = freeOf(claimAt) + subject

      /** The existential, from a proof of its body written in normal form. */
      def introduce(family: Term, length: Term)(prove: Term => Kernel.Thm): Kernel.Thm = {
        val inner = openAt(existential, family)
        val body = openAt(inner, length)
        val restored = unreduce(body, prove(normalise(body)))
        force(
          rules
            .existsIntro(existsPredicate(inner), length, restored)
            .flatMap(rules.existsIntro(existsPredicate(existential), family, _)))
      }

      // The prime divisors of the subject are a non-empty set bounded by the subject itself, so
      // one of them is greatest. `num` has no maximum to take instead, which is why this is
      // `Peano.GreatestBounded` and not a two-line definition.
      val greatestInstance = {
        val candidate = Conv.freshVariable("d", numbers, taken)
        val property = force(
          LogicError.lift(Term.abs(candidate, conj(isPrime(candidate), divides(candidate, subject)))))
        reduced(force(rules.spec(property, pf(Peano.GreatestBounded))))
      }
      val (greatestPremise, _) = impParts(greatestInstance.conclusion)
      val (inhabitedTerm, boundedTerm) = conjParts(greatestPremise)

      val inhabited =
        force(rules.spec(subject, mf(Modular.PrimeFactor)).flatMap(rules.mp(_, aboveOne)))
      val bounded = {
        val candidate = Conv.freshVariable("k", numbers, taken)
        val premise = conj(isPrime(candidate), divides(candidate, subject))
        val holds = assume(premise)
        val cases = force(
          rules
            .specAll(mf(Modular.DividesBound), List(candidate, subject))
            .flatMap(rules.mp(_, force(rules.conjElim2(holds)))))
        val parts = disjunctsOf(cases.conclusion, 2)
        val fromVanishing = {
          val isZero = assume(parts(1))
          val absurdity = carryInto(app(belowConstant, List(one)), isZero, aboveOne)
          force(
            rules.falsityElim(
              atMost(candidate, subject),
              absurd(force(rules.spec(one, pf(Peano.NotBelowZero))), absurdity)))
        }
        val atMostSubject = force(rules.disjElim(cases, assume(parts(0)), fromVanishing))
        val universal =
          force(rules.disch(premise, atMostSubject).flatMap(rules.gen(candidate, _)))
        force(rules.existsIntro(existsPredicate(boundedTerm), subject, universal))
      }
      val greatest =
        force(rules.conjIntro(inhabited, bounded).flatMap(rules.mp(greatestInstance, _)))

      val built = open(greatest, "p", taken) { (prime, atPrime) =>
        val holds = force(rules.conjElim1(atPrime))
        val isGreatest = force(rules.conjElim2(atPrime))
        val primeIsPrime = force(rules.conjElim1(holds))
        val primeDivides = force(rules.conjElim2(holds))
        val primeAboveOne = force(
          rules.spec(prime, mf(Modular.PrimeAboveOne)).flatMap(rules.mp(_, primeIsPrime)))
        val primePositive = positiveFromAboveOne(primeAboveOne, prime)
        val quotients = force(
          rules
            .specAll(mf(Modular.DividesElim), List(prime, subject))
            .flatMap(rules.mp(_, primeDivides)))

        open(quotients, "m", taken + prime) { (quotient, isProduct) =>
          // `isProduct` is `n = NUM_MUL p m`, which every branch below reads one way or another.
          val quotientPositive = {
            val vanishing = eq(quotient, zero)
            val vanishes = force(
              Conv.trans(
                isProduct,
                force(
                  Conv.trans(
                    force(Conv.apTerm(app(times, List(prime)), assume(vanishing))),
                    force(rules.spec(prime, pf(Peano.MulAtZero)))))))
            val absurdity = carryInto(app(belowConstant, List(one)), vanishes, aboveOne)
            val contradiction =
              absurd(force(rules.spec(one, pf(Peano.NotBelowZero))), absurdity)
            positiveFromNonZero(force(rules.notIntro(vanishing, contradiction)), quotient)
          }

          // `m < n`, which is the number the strong hypothesis is wanted at.
          val quotientBelow = {
            val scaled = force(
              rules
                .specAll(pf(Peano.MulStrictlyMonotone), List(quotient, one, prime))
                .flatMap(rules.mp(_, quotientPositive))
                .flatMap(rules.mp(_, primeAboveOne)))
            val unit = force(rules.spec(quotient, pf(Peano.TimesOne)))
            val belowProduct =
              carryLeft(belowConstant, unit, mul(quotient, prime), scaled)
            val asSubject = force(
              Conv.trans(
                force(semiring.prove(mul(quotient, prime), mul(prime, quotient))),
                force(Conv.sym(isProduct))))
            carryInto(app(belowConstant, List(quotient)), asSubject, belowProduct)
          }

          val quotientDividesSubject = {
            val commuted = force(
              Conv.trans(isProduct, force(semiring.prove(mul(prime, quotient), mul(quotient, prime)))))
            force(
              rules
                .specAll(mf(Modular.DividesIntro), List(quotient, subject, prime))
                .flatMap(rules.mp(_, commuted)))
          }

          // One comparison decides which of the three branches below is the one taken: the
          // quotient is above one, is one, or is below it and cannot be.
          val cases = force(rules.specAll(pf(Peano.Trichotomy), List(one, quotient)))
          val three = disjunctsOf(cases.conclusion, 3)

          // The quotient is one, so the subject is the prime itself and one factor is enough.
          val single = {
            val isOne = assume(three(1))
            val subjectIsPrime = force(
              Conv.trans(
                isProduct,
                force(
                  Conv.trans(
                    force(Conv.apTerm(app(times, List(prime)), force(Conv.sym(isOne)))),
                    force(rules.spec(prime, pf(Peano.TimesOne)))))))
            val index = Conv.freshVariable("i", numbers, taken + prime + quotient)
            val family = force(LogicError.lift(Term.abs(index, prime)))

            introduce(family, one) { _ =>
              val lengthPositive = force(rules.spec(zero, pf(Peano.SuccessorPositive)))
              val everyPrime = {
                val i = Conv.freshVariable("i", numbers, taken + prime + quotient)
                force(
                  rules
                    .disch(below(i, one), primeIsPrime)
                    .flatMap(rules.gen(i, _)))
              }
              // The family is constant, so being non-decreasing is reflexivity and not a vacuous
              // claim about the indices below one: what has to be proved after the contraction is
              // `p <= p`, and the bound never comes into it.
              val monotone = {
                val a = Conv.freshVariable("a", numbers, taken + prime + quotient)
                val b = Conv.freshVariable("b", numbers, taken + prime + quotient + a)
                force(
                  rules
                    .disch(
                      conj(below(a, b), below(b, one)),
                      force(rules.spec(prime, pf(Peano.Reflexive))))
                    .flatMap(rules.gen(b, _))
                    .flatMap(rules.gen(a, _)))
              }
              val product = {
                val recurrence =
                  reduced(force(rules.specAll(cdf(Coding.ProductAtSuccessor), List(family, zero))))
                val emptyIsOne = force(rules.spec(family, cdf(Coding.ProductAtZero)))
                val collapsed = force(
                  Conv
                    .apTerm(times, emptyIsOne)
                    .flatMap(Conv.apThm(_, prime))
                    .flatMap(scaled =>
                      Conv.trans(scaled, force(semiring.prove(mul(one, prime), prime)))))
                force(
                  Conv.trans(
                    force(Conv.trans(recurrence, collapsed)),
                    force(Conv.sym(subjectIsPrime))))
              }
              force(
                rules.conjIntro(
                  lengthPositive,
                  force(rules.conjIntro(everyPrime, force(rules.conjIntro(monotone, product))))))
            }
          }

          // The quotient is above one, so the hypothesis factors it and this prime goes on the end.
          val many = {
            val quotientAboveOne = assume(three(0))
            val factored = force(
              rules
                .spec(quotient, hypothesis)
                .flatMap(rules.mp(_, quotientBelow))
                .map(reduced)
                .flatMap(rules.mp(_, quotientAboveOne)))

            open(factored, "g", taken + prime + quotient) { (family, atFamily) =>
              open(atFamily, "k", taken + prime + quotient + family) { (length, atLength) =>
                val afterPositive = force(rules.conjElim2(atLength))
                val primesBelow = force(rules.conjElim1(afterPositive))
                val afterPrimes = force(rules.conjElim2(afterPositive))
                val monotoneBelow = force(rules.conjElim1(afterPrimes))
                val productIsQuotient = force(rules.conjElim2(afterPrimes))

                val avoid = taken + prime + quotient + family + length
                val index = Conv.freshVariable("i", numbers, avoid)
                val extended = force(
                  LogicError.lift(Term.abs(
                    index,
                    app(conditional, List(below(index, length), at(family, index), prime)))))

                /** `|- ~(NUM_LT x length)` from `x = length`, which both branches at the end need. */
                def notBelowItself(isLength: Kernel.Thm): Kernel.Thm = {
                  val irreflexive = force(rules.spec(length, pf(Peano.StrictIrreflexive)))
                  val equation = force(
                    Conv.apTerm(belowConstant, isLength).flatMap(Conv.apThm(_, length)))
                  force(
                    Conv
                      .apTerm(logic.negation, equation)
                      .flatMap(Conv.sym)
                      .flatMap(step => LogicError.lift(Kernel.eqMp(step, irreflexive))))
                }

                /** `|- COND (NUM_LT x length) (g x) p = g x` where `x` is below the length. */
                def branchTaken(point: Term, isBelow: Kernel.Thm): Kernel.Thm =
                  force(
                    rules
                      .specAll(
                        condAt(Classical.CondTrue),
                        List(below(point, length), at(family, point), prime))
                      .flatMap(rules.mp(_, isBelow)))

                /** `|- COND (NUM_LT x length) (g x) p = p` where `x` is the length itself. */
                def branchLeft(point: Term, notBelow: Kernel.Thm): Kernel.Thm =
                  force(
                    rules
                      .specAll(
                        condAt(Classical.CondFalse),
                        List(below(point, length), at(family, point), prime))
                      .flatMap(rules.mp(_, notBelow)))

                val newestIsPrime = branchLeft(
                  length,
                  notBelowItself(Conv.refl(length)))

                introduce(extended, suc(length)) { _ =>
                  val lengthPositive = force(rules.spec(length, pf(Peano.SuccessorPositive)))

                  val everyPrime = {
                    val i = Conv.freshVariable("i", numbers, avoid)
                    val premise = below(i, suc(length))
                    val assumed = assume(premise)
                    val cases = force(
                      rules
                        .specAll(pf(Peano.BelowSuccessorCases), List(length, i))
                        .flatMap(rules.mp(_, assumed)))
                    val parts = disjunctsOf(cases.conclusion, 2)
                    val fromBelow = {
                      val isBelow = assume(parts(0))
                      val here =
                        force(rules.spec(i, primesBelow).flatMap(rules.mp(_, isBelow)))
                      carryInto(
                        primeConstant, force(Conv.sym(branchTaken(i, isBelow))), here)
                    }
                    val fromEnd = {
                      val isLength = assume(parts(1))
                      carryInto(
                        primeConstant,
                        force(Conv.sym(branchLeft(i, notBelowItself(isLength)))),
                        primeIsPrime)
                    }
                    force(
                      rules
                        .disjElim(cases, fromBelow, fromEnd)
                        .flatMap(rules.disch(premise, _))
                        .flatMap(rules.gen(i, _)))
                  }

                  val monotone = {
                    val a = Conv.freshVariable("a", numbers, avoid)
                    val b = Conv.freshVariable("b", numbers, avoid + a)
                    val premise = conj(below(a, b), below(b, suc(length)))
                    val assumed = assume(premise)
                    val aBelowB = force(rules.conjElim1(assumed))
                    val bBelow = force(rules.conjElim2(assumed))
                    val cases = force(
                      rules
                        .specAll(pf(Peano.BelowSuccessorCases), List(length, b))
                        .flatMap(rules.mp(_, bBelow)))
                    val parts = disjunctsOf(cases.conclusion, 2)

                    val fromBelow = {
                      val bBelowLength = assume(parts(0))
                      val aBelowLength = force(
                        rules
                          .specAll(pf(Peano.StrictTransitive), List(a, b, length))
                          .flatMap(implication =>
                            rules.conjIntro(aBelowB, bBelowLength).flatMap(rules.mp(implication, _))))
                      val ordered = force(
                        rules
                          .specAll(monotoneBelow, List(a, b))
                          .flatMap(implication =>
                            rules.conjIntro(aBelowB, bBelowLength).flatMap(rules.mp(implication, _))))
                      val onTheLeft = carryLeft(
                        atMostConstant,
                        force(Conv.sym(branchTaken(a, aBelowLength))),
                        at(family, b),
                        ordered)
                      carryInto(
                        app(
                          atMostConstant,
                          List(app(conditional, List(below(a, length), at(family, a), prime)))),
                        force(Conv.sym(branchTaken(b, bBelowLength))),
                        onTheLeft)
                    }

                    val fromEnd = {
                      val bIsLength = assume(parts(1))
                      val aBelowLength = carryInto(
                        app(belowConstant, List(a)), bIsLength, aBelowB)
                      val factorIsPrime =
                        force(rules.spec(a, primesBelow).flatMap(rules.mp(_, aBelowLength)))
                      val dividesShorter = force(
                        rules
                          .specAll(cdf(Coding.ProductDivides), List(family, a, length))
                          .flatMap(rules.mp(_, aBelowLength)))
                      val dividesQuotient = carryInto(
                        app(dividesConstant, List(at(family, a))),
                        productIsQuotient,
                        dividesShorter)
                      val dividesSubject = force(
                        rules
                          .specAll(mf(Modular.DividesTrans), List(at(family, a), quotient, subject))
                          .flatMap(rules.mp(_, dividesQuotient))
                          .flatMap(rules.mp(_, quotientDividesSubject)))
                      val ordered = force(
                        rules
                          .spec(at(family, a), isGreatest)
                          .map(reduced)
                          .flatMap(implication =>
                            rules
                              .conjIntro(factorIsPrime, dividesSubject)
                              .flatMap(rules.mp(implication, _))))
                      val onTheLeft = carryLeft(
                        atMostConstant,
                        force(Conv.sym(branchTaken(a, aBelowLength))),
                        prime,
                        ordered)
                      carryInto(
                        app(
                          atMostConstant,
                          List(app(conditional, List(below(a, length), at(family, a), prime)))),
                        force(Conv.sym(branchLeft(b, notBelowItself(bIsLength)))),
                        onTheLeft)
                    }

                    force(
                      rules
                        .disjElim(cases, fromBelow, fromEnd)
                        .flatMap(rules.disch(premise, _))
                        .flatMap(rules.gen(b, _))
                        .flatMap(rules.gen(a, _)))
                  }

                  val product = {
                    val congruence = force(
                      rules.specAll(cdf(Coding.ProductCongruent), List(extended, family, length)))
                    val (agreementTerm, _) = impParts(congruence.conclusion)
                    val agreement = {
                      val i = Conv.freshVariable("i", numbers, avoid)
                      val premise = below(i, length)
                      force(
                        rules
                          .disch(premise, branchTaken(i, assume(premise)))
                          .flatMap(rules.gen(i, _)))
                    }
                    val sameShorter =
                      force(rules.mp(congruence, unreduce(agreementTerm, agreement)))
                    val recurrence = reduced(
                      force(rules.specAll(cdf(Coding.ProductAtSuccessor), List(extended, length))))
                    val asQuotient = force(
                      Conv
                        .apTerm(times, force(Conv.trans(sameShorter, productIsQuotient)))
                        .flatMap(Conv.apThm(_, prime)))
                    val stepped = force(
                      Conv.trans(
                        recurrence,
                        force(
                          Conv.trans(
                            force(
                              Conv
                                .apTerm(app(times, List(prodOf(extended, length))), newestIsPrime)),
                            asQuotient))))
                    force(
                      Conv.trans(
                        stepped,
                        force(
                          Conv.trans(
                            force(semiring.prove(mul(quotient, prime), mul(prime, quotient))),
                            force(Conv.sym(isProduct))))))
                  }

                  force(
                    rules.conjIntro(
                      lengthPositive,
                      force(rules.conjIntro(everyPrime, force(rules.conjIntro(monotone, product))))))
                }
              }
            }
          }

          val impossible = {
            val belowOne = assume(three(2))
            val split = force(
              rules
                .specAll(pf(Peano.BelowSuccessorCases), List(zero, quotient))
                .flatMap(rules.mp(_, belowOne)))
            val parts = disjunctsOf(split.conclusion, 2)
            val fromBelowZero = force(
              rules.falsityElim(
                existential,
                absurd(force(rules.spec(quotient, pf(Peano.NotBelowZero))), assume(parts(0)))))
            val fromZero = force(
              rules.falsityElim(
                existential,
                absurd(
                  force(rules.spec(zero, pf(Peano.StrictIrreflexive))),
                  carryInto(app(belowConstant, List(zero)), assume(parts(1)), quotientPositive))))
            force(rules.disjElim(split, fromBelowZero, fromZero))
          }

          val tail = assume(force(logic.mkDisj(three(1), three(2))))
          force(
            rules.disjElim(
              cases,
              many,
              force(rules.disjElim(tail, single, impossible))))
        }
      }

      force(
        rules
          .disch(aboveOneTerm, built)
          .flatMap(rules.disch(hypothesisTerm, _))
          .flatMap(rules.gen(subject, _))
          .flatMap(rules.mp(instance, _)))
    }

    /**
     * [[FactorisationUnique]], by strong induction on the value the two products share.
     *
     * The step is the classical argument and the two corners are where the lengths vanish. At a
     * positive length on both sides the two last factors each divide the other's product, so each
     * is at most the other by [[PrimeDividesProduct]] and the family's own order, and cancelling
     * the common factor leaves two factorisations of a strictly smaller number.
     */
    lazy val factorisationUnique: Kernel.Thm = {
      val auxiliary = claim(UniqueAtValue)
      val instance =
        reduced(force(rules.spec(forallPredicate(auxiliary), pf(Peano.StrongInduction))))
      val (stepGoal, _) = impParts(instance.conclusion)
      val subject = Conv.freshVariable("n", numbers, freeOf(auxiliary))
      val (hypothesisTerm, claimAt) = impParts(openAt(stepGoal, subject))
      val hypothesis = assume(hypothesisTerm)

      val (binders, body) = force(Logic.stripForall(claimAt))
      val first = binders(0)
      val firstLength = binders(1)
      val second = binders(2)
      val secondLength = binders(3)
      val (antecedents, conclusion) = peel(body, 6)
      val primesFirst = assume(antecedents(0))
      val monotoneFirst = assume(antecedents(1))
      val primesSecond = assume(antecedents(2))
      val monotoneSecond = assume(antecedents(3))
      val productFirst = assume(antecedents(4))
      val productSecond = assume(antecedents(5))
      val taken = freeOf(claimAt) ++ binders.toSet + subject

      /** `|- SUC ZERO = n` from a length that is zero: the empty product is one. */
      def valueIsOne(family: Term, isZero: Kernel.Thm, product: Kernel.Thm): Kernel.Thm = {
        val shifted = force(Conv.apTerm(app(productConstant, List(family)), isZero))
        val atZero = force(Conv.sym(shifted).flatMap(Conv.trans(_, product)))
        force(
          Conv
            .sym(force(rules.spec(family, cdf(Coding.ProductAtZero))))
            .flatMap(Conv.trans(_, atZero)))
      }

      /** `|- length = ZERO` from the other family's length being zero. */
      def alsoEmpty(
        family: Term,
        length: Term,
        primes: Kernel.Thm,
        product: Kernel.Thm,
        isOne: Kernel.Thm
      ): Kernel.Thm =
        force(
          rules
            .specAll(primeProductIsOne, List(family, length))
            .flatMap(rules.mp(_, primes))
            .flatMap(rules.mp(_, force(Conv.trans(product, force(Conv.sym(isOne)))))))

      val firstCases = force(rules.spec(firstLength, nf(Natural.ZeroOrSuccessor)))
      val firstParts = disjunctsOf(firstCases.conclusion, 2)

      val whenFirstIsEmpty = {
        val isZero = assume(firstParts(0))
        val isOne = valueIsOne(first, isZero, productFirst)
        val secondIsZero =
          alsoEmpty(second, secondLength, primesSecond, productSecond, isOne)
        val sameLength = force(Conv.trans(isZero, force(Conv.sym(secondIsZero))))
        val agreement = {
          val index = Conv.freshVariable("i", numbers, taken)
          val premise = below(index, firstLength)
          val belowZero =
            carryInto(app(belowConstant, List(index)), isZero, assume(premise))
          force(
            rules
              .falsityElim(
                eq(at(first, index), at(second, index)),
                absurd(force(rules.spec(index, pf(Peano.NotBelowZero))), belowZero))
              .flatMap(rules.disch(premise, _))
              .flatMap(rules.gen(index, _)))
        }
        force(rules.conjIntro(sameLength, agreement))
      }

      val whenFirstIsLonger = open(assume(firstParts(1)), "u", taken) { (firstLast, firstIsSuc) =>
        val secondCases = force(rules.spec(secondLength, nf(Natural.ZeroOrSuccessor)))
        val secondParts = disjunctsOf(secondCases.conclusion, 2)

        val whenSecondIsEmpty = {
          val isZero = assume(secondParts(0))
          val isOne = valueIsOne(second, isZero, productSecond)
          val firstIsZero = alsoEmpty(first, firstLength, primesFirst, productFirst, isOne)
          val absurdity = force(Conv.sym(firstIsSuc).flatMap(Conv.trans(_, firstIsZero)))
          force(
            rules.falsityElim(
              conclusion,
              absurd(force(rules.spec(firstLast, nf(Natural.SuccessorNotZero))), absurdity)))
        }

        val whenSecondIsLonger =
          open(assume(secondParts(1)), "v", taken + firstLast) { (secondLast, secondIsSuc) =>
            /** The index one below a length that is a successor is below the length. */
            def lastIsBelow(point: Term, isSuccessor: Kernel.Thm): Kernel.Thm =
              carryInto(
                app(belowConstant, List(point)),
                force(Conv.sym(isSuccessor)),
                force(rules.spec(point, pf(Peano.BelowSuccessor))))

            val firstBelow = lastIsBelow(firstLast, firstIsSuc)
            val secondBelow = lastIsBelow(secondLast, secondIsSuc)
            val leftFactor = at(first, firstLast)
            val rightFactor = at(second, secondLast)
            val leftIsPrime =
              force(rules.spec(firstLast, primesFirst).flatMap(rules.mp(_, firstBelow)))
            val rightIsPrime =
              force(rules.spec(secondLast, primesSecond).flatMap(rules.mp(_, secondBelow)))
            val leftAboveOne = force(
              rules.spec(leftFactor, mf(Modular.PrimeAboveOne)).flatMap(rules.mp(_, leftIsPrime)))
            val leftPositive = positiveFromAboveOne(leftAboveOne, leftFactor)

            /** `|- n = NUM_MUL (NUM_PROD f u) (f u)`, the value read through the recurrence. */
            def valueAsProduct(
              family: Term,
              last: Term,
              isSuccessor: Kernel.Thm,
              product: Kernel.Thm
            ): Kernel.Thm = {
              val recurrence =
                force(rules.specAll(cdf(Coding.ProductAtSuccessor), List(family, last)))
              val shifted = force(Conv.apTerm(app(productConstant, List(family)), isSuccessor))
              force(
                Conv
                  .sym(product)
                  .flatMap(Conv.trans(_, shifted))
                  .flatMap(Conv.trans(_, recurrence)))
            }

            val leftShorter = prodOf(first, firstLast)
            val rightShorter = prodOf(second, secondLast)
            val valueLeft =
              valueAsProduct(first, firstLast, firstIsSuc, productFirst)
            val valueRight =
              valueAsProduct(second, secondLast, secondIsSuc, productSecond)

            /**
             * `|- NUM_LE (f u) (g v)`: the left factor divides the right product, so it is one of
             * the right factors, and the right family's order puts every one of those at `g v`.
             *
             * Twelve arguments and deliberately not a record: the two calls below are this same
             * argument with the two sides exchanged, and that is the whole reason both bounds hold.
             * A record would put the swap inside a value and leave the call site unable to show it.
             */
            def atMostTheOther(
              factor: Term,
              factorIsPrime: Kernel.Thm,
              shorter: Term,
              value: Kernel.Thm,
              otherFamily: Term,
              otherLength: Term,
              otherLast: Term,
              otherIsSuc: Kernel.Thm,
              otherProduct: Kernel.Thm,
              otherPrimes: Kernel.Thm,
              otherMonotone: Kernel.Thm,
              otherBelow: Kernel.Thm
            ): Kernel.Thm = {
              val other = at(otherFamily, otherLast)
              val asFactor = force(
                Conv.trans(value, force(semiring.prove(mul(shorter, factor), mul(factor, shorter)))))
              val dividesValue = force(
                rules
                  .specAll(mf(Modular.DividesIntro), List(factor, subject, shorter))
                  .flatMap(rules.mp(_, asFactor)))
              val dividesProduct = carryInto(
                app(dividesConstant, List(factor)),
                force(Conv.sym(otherProduct)),
                dividesValue)
              val found = force(
                rules
                  .specAll(primeDividesProduct, List(factor, otherFamily, otherLength))
                  .flatMap(rules.mp(_, factorIsPrime))
                  .flatMap(rules.mp(_, dividesProduct)))

              open(found, "i", taken + firstLast + secondLast) { (index, atIndex) =>
                val indexBelow = force(rules.conjElim1(atIndex))
                val dividesEntry = force(rules.conjElim2(atIndex))
                val entryIsPrime =
                  force(rules.spec(index, otherPrimes).flatMap(rules.mp(_, indexBelow)))
                val split = force(
                  rules
                    .specAll(mf(Modular.PrimeDivisor), List(at(otherFamily, index), factor))
                    .flatMap(rules.mp(_, entryIsPrime))
                    .flatMap(rules.mp(_, dividesEntry)))
                val branches = disjunctsOf(split.conclusion, 2)
                val isOne = {
                  val assumed = assume(branches(0))
                  val aboveOne = force(
                    rules
                      .spec(factor, mf(Modular.PrimeAboveOne))
                      .flatMap(rules.mp(_, factorIsPrime)))
                  force(
                    rules.falsityElim(
                      eq(factor, at(otherFamily, index)),
                      absurd(
                        force(rules.spec(one, pf(Peano.StrictIrreflexive))),
                        carryInto(app(belowConstant, List(one)), assumed, aboveOne))))
                }
                val isEntry = force(rules.disjElim(split, isOne, assume(branches(1))))

                val cases = force(
                  rules
                    .specAll(pf(Peano.BelowSuccessorCases), List(otherLast, index))
                    .flatMap(rules.mp(
                      _,
                      carryInto(app(belowConstant, List(index)), otherIsSuc, indexBelow))))
                val parts = disjunctsOf(cases.conclusion, 2)
                val fromInside = {
                  val indexIsBelow = assume(parts(0))
                  val ordered = force(
                    rules
                      .specAll(otherMonotone, List(index, otherLast))
                      .flatMap(implication =>
                        rules
                          .conjIntro(indexIsBelow, otherBelow)
                          .flatMap(rules.mp(implication, _))))
                  carryLeft(atMostConstant, force(Conv.sym(isEntry)), other, ordered)
                }
                val fromEnd = {
                  val indexIsLast = assume(parts(1))
                  val sameFactor = force(
                    Conv.trans(isEntry, force(Conv.apTerm(otherFamily, indexIsLast))))
                  carryInto(
                    app(atMostConstant, List(factor)),
                    sameFactor,
                    force(rules.spec(factor, pf(Peano.Reflexive))))
                }
                force(rules.disjElim(cases, fromInside, fromEnd))
              }
            }

            val leftAtMostRight = atMostTheOther(
              leftFactor, leftIsPrime, leftShorter, valueLeft,
              second, secondLength, secondLast, secondIsSuc, productSecond,
              primesSecond, monotoneSecond, secondBelow)
            val rightAtMostLeft = atMostTheOther(
              rightFactor, rightIsPrime, rightShorter, valueRight,
              first, firstLength, firstLast, firstIsSuc, productFirst,
              primesFirst, monotoneFirst, firstBelow)
            val sameFactor = force(
              rules
                .specAll(pf(Peano.AntiSymmetric), List(leftFactor, rightFactor))
                .flatMap(implication =>
                  rules
                    .conjIntro(leftAtMostRight, rightAtMostLeft)
                    .flatMap(rules.mp(implication, _))))

            // The shared factor cancels, and what is left is two factorisations of one number.
            val sameShorter = {
              val rightWithLeft = force(
                Conv.trans(
                  valueRight,
                  force(Conv.apTerm(app(times, List(rightShorter)), force(Conv.sym(sameFactor))))))
              val equalProducts =
                force(Conv.sym(valueLeft).flatMap(Conv.trans(_, rightWithLeft)))
              val commuted = force(
                Conv.trans(
                  force(semiring.prove(mul(leftFactor, leftShorter), mul(leftShorter, leftFactor))),
                  force(
                    Conv.trans(
                      equalProducts,
                      force(semiring.prove(
                        mul(rightShorter, leftFactor), mul(leftFactor, rightShorter)))))))
              force(
                rules
                  .specAll(pf(Peano.MulCancelsLeft), List(leftFactor, leftShorter, rightShorter))
                  .flatMap(rules.mp(_, leftPositive))
                  .flatMap(rules.mp(_, commuted)))
            }

            /** The premises of the statement, restricted from a length to its predecessor. */
            def shorterPrimes(
              last: Term,
              isSuccessor: Kernel.Thm,
              primes: Kernel.Thm
            ): Kernel.Thm = {
              val index = Conv.freshVariable("i", numbers, taken + firstLast + secondLast)
              val premise = below(index, last)
              val carried = carryInto(
                app(belowConstant, List(index)),
                force(Conv.sym(isSuccessor)),
                force(
                  rules
                    .specAll(pf(Peano.StrictTransitive), List(index, last, suc(last)))
                    .flatMap(implication =>
                      rules
                        .conjIntro(assume(premise), force(rules.spec(last, pf(Peano.BelowSuccessor))))
                        .flatMap(rules.mp(implication, _)))))
              force(
                rules
                  .disch(premise, force(rules.spec(index, primes).flatMap(rules.mp(_, carried))))
                  .flatMap(rules.gen(index, _)))
            }

            /** The same for the order, where the premise to weaken is inside a conjunction. */
            def shorterMonotone(
              last: Term,
              isSuccessor: Kernel.Thm,
              monotone: Kernel.Thm
            ): Kernel.Thm = {
              val avoid = taken + firstLast + secondLast
              val a = Conv.freshVariable("a", numbers, avoid)
              val b = Conv.freshVariable("b", numbers, avoid + a)
              val premise = conj(below(a, b), below(b, last))
              val assumed = assume(premise)
              val bBelowLength = carryInto(
                app(belowConstant, List(b)),
                force(Conv.sym(isSuccessor)),
                force(
                  rules
                    .specAll(pf(Peano.StrictTransitive), List(b, last, suc(last)))
                    .flatMap(implication =>
                      rules
                        .conjIntro(
                          force(rules.conjElim2(assumed)),
                          force(rules.spec(last, pf(Peano.BelowSuccessor))))
                        .flatMap(rules.mp(implication, _)))))
              val ordered = force(
                rules
                  .specAll(monotone, List(a, b))
                  .flatMap(implication =>
                    rules
                      .conjIntro(force(rules.conjElim1(assumed)), bBelowLength)
                      .flatMap(rules.mp(implication, _))))
              force(rules.disch(premise, ordered).flatMap(rules.gen(b, _)).flatMap(rules.gen(a, _)))
            }

            // The shorter product is strictly smaller, which is what the strong hypothesis needs.
            val shorterBelow = {
              val positives = factorsArePositive(
                first, firstLast, shorterPrimes(firstLast, firstIsSuc, primesFirst),
                taken + firstLast + secondLast)
              val shorterPositive = force(
                rules
                  .specAll(cdf(Coding.ProductPositive), List(first, firstLast))
                  .flatMap(rules.mp(_, positives)))
              val scaled = force(
                rules
                  .specAll(pf(Peano.MulStrictlyMonotone), List(leftShorter, one, leftFactor))
                  .flatMap(rules.mp(_, shorterPositive))
                  .flatMap(rules.mp(_, leftAboveOne)))
              val unit = force(rules.spec(leftShorter, pf(Peano.TimesOne)))
              val belowProduct =
                carryLeft(belowConstant, unit, mul(leftShorter, leftFactor), scaled)
              carryInto(
                app(belowConstant, List(leftShorter)),
                force(Conv.sym(valueLeft)),
                belowProduct)
            }

            val shorterUnique = force(
              rules
                .spec(leftShorter, hypothesis)
                .flatMap(rules.mp(_, shorterBelow))
                .map(reduced)
                .flatMap(rules.specAll(_, List(first, firstLast, second, secondLast)))
                .flatMap(rules.mp(
                  _, shorterPrimes(firstLast, firstIsSuc, primesFirst)))
                .flatMap(rules.mp(
                  _, shorterMonotone(firstLast, firstIsSuc, monotoneFirst)))
                .flatMap(rules.mp(
                  _, shorterPrimes(secondLast, secondIsSuc, primesSecond)))
                .flatMap(rules.mp(
                  _, shorterMonotone(secondLast, secondIsSuc, monotoneSecond)))
                .flatMap(rules.mp(_, Conv.refl(leftShorter)))
                .flatMap(rules.mp(_, force(Conv.sym(sameShorter)))))

            val sameShorterLength = force(rules.conjElim1(shorterUnique))
            val shorterAgreement = force(rules.conjElim2(shorterUnique))

            val sameLength = force(
              Conv.trans(
                firstIsSuc,
                force(
                  Conv.trans(
                    force(Conv.apTerm(successorConstant, sameShorterLength)),
                    force(Conv.sym(secondIsSuc))))))

            val agreement = {
              val index = Conv.freshVariable("i", numbers, taken + firstLast + secondLast)
              val premise = below(index, firstLength)
              val assumed = assume(premise)
              val cases = force(
                rules
                  .specAll(pf(Peano.BelowSuccessorCases), List(firstLast, index))
                  .flatMap(rules.mp(
                    _, carryInto(app(belowConstant, List(index)), firstIsSuc, assumed))))
              val parts = disjunctsOf(cases.conclusion, 2)
              val fromInside = {
                val isBelow = assume(parts(0))
                force(rules.spec(index, shorterAgreement).flatMap(rules.mp(_, isBelow)))
              }
              val fromEnd = {
                val isLast = assume(parts(1))
                val toSecondLast = force(Conv.trans(isLast, sameShorterLength))
                force(
                  Conv.trans(
                    force(Conv.apTerm(first, isLast)),
                    force(
                      Conv.trans(
                        sameFactor,
                        force(Conv.apTerm(second, force(Conv.sym(toSecondLast))))))))
              }
              force(
                rules
                  .disjElim(cases, fromInside, fromEnd)
                  .flatMap(rules.disch(premise, _))
                  .flatMap(rules.gen(index, _)))
            }

            force(rules.conjIntro(sameLength, agreement))
          }

        force(rules.disjElim(secondCases, whenSecondIsEmpty, whenSecondIsLonger))
      }

      val everywhere = force(
        rules
          .genAll(
            antecedents.foldRight(
              force(rules.disjElim(firstCases, whenFirstIsEmpty, whenFirstIsLonger)))(
              (antecedent, theorem) => force(rules.disch(antecedent, theorem))),
            binders.toList)
          .flatMap(rules.disch(hypothesisTerm, _))
          .flatMap(rules.gen(subject, _))
          .flatMap(rules.mp(instance, _)))

      // The published statement is this one at the value the first product already has.
      val statement = published(FactorisationUnique)
      val (outer, outerBody) = force(Logic.stripForall(statement))
      val (premises, _) = peel(outerBody, 5)
      val value = prodOf(outer(0), outer(1))
      val assumed = premises.map(assume)
      val reachedHere = force(
        rules
          .specAll(everywhere, List(value, outer(0), outer(1), outer(2), outer(3)))
          .flatMap(rules.mp(_, assumed(0)))
          .flatMap(rules.mp(_, assumed(1)))
          .flatMap(rules.mp(_, assumed(2)))
          .flatMap(rules.mp(_, assumed(3)))
          .flatMap(rules.mp(_, Conv.refl(value)))
          .flatMap(rules.mp(_, force(Conv.sym(assumed(4))))))

      force(
        rules.genAll(
          premises.foldRight(reachedHere)((premise, theorem) =>
            force(rules.disch(premise, theorem))),
          outer.toList))
    }

    /** A finished derivation against the statement this development publishes for it. */
    def checked(name: String, theorem: Kernel.Thm): Kernel.Thm = {
      val wanted = force(
        Statements
          .collectFirst { case (published, source) if published == name => source }
          .toRight(MissingDefinition(name))
          .flatMap(Parser.proposition(theory, notation, _))
      )
      if (theorem.conclusion == wanted) theorem
      else
        throw new RefusedHere(
          NotOfForm(s"the statement published for $name", theorem.conclusion))
    }
  }
}
