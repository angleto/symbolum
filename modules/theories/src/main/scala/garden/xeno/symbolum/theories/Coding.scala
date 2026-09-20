package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Coding a finite sequence of naturals as a single natural, which is the primitive the syntax of a
 * formal language is missing and everything above it waits on.
 *
 * `docs/adr/0013` is the decision and the argument: the target is the **second** incompleteness
 * theorem, so the decoding has to be Delta-0, which selects Goedel's beta function and rejects both
 * a product of prime powers and iterated pairing. This file is that function, built from the
 * bottom, and what is here today is the bottom.
 *
 * == What the beta function needs, and where it already exists ==
 *
 * `beta a b i = a mod (1 + (i + 1) * b)`, and the theorem that earns it is that **every** finite
 * sequence is some `beta a b`. The usual proof takes `b = k!` for a `k` above both the length and
 * every entry, observes that the moduli `1 + (i + 1) * b` are then pairwise coprime, and puts the
 * entries together with the Chinese remainder theorem.
 *
 * `Modular` is most of the ground floor and was not built for this: `NUM_MOD` as a function that
 * denotes, division with remainder in both halves, Bezout, the greatest common divisor and Euclid's
 * lemma are all there. What is missing in front of it is three things, in this order:
 *
 *  1. the factorial, and that every `d` between one and `k` divides `k!`. **This is what is here.**
 *  2. the Chinese remainder theorem, which `Modular` does not have and Bezout is the way to.
 *  3. the beta function itself and its sequence lemma.
 *
 * == Why the factorial and not the least common multiple ==
 *
 * What the coprimality argument actually uses is that `b` is divisible by every `d <= k`, and any
 * common multiple of `1..k` would do. The factorial is the one a primitive recursion writes in a
 * line, which `Recursion.define` already drives; the least common multiple is a fold over a range
 * and this system has neither the range nor the fold. Nothing below depends on `b` being *least*.
 *
 * == The shape of the one lemma here, and the trap in stating it ==
 *
 * [[Coding.FactorialDivides]] is `!d k. NUM_LT 0 d /\ NUM_LE d k ==> NUM_DIVIDES d (NUM_FACT k)`,
 * with `d` quantified **first**. That is not how a reader would write it and it is not decorative:
 * `Induct.proveBy` inducts on the last leading quantifier and generalises the others outside, so
 * `!k d. ...` would be inducted on `d` and would prove something else. The induction wanted here is
 * on `k` with `d` fixed, and the step applies the hypothesis at the same `d`, so fixing it is
 * exactly right. `Descent` carries the same note for the same driver and the same reason.
 *
 * The positivity hypothesis is not decoration either. At `k = 0` the claim would read
 * `NUM_DIVIDES 0 (NUM_FACT 0)`, that is `0 | 1`, which is false; `NUM_LT 0 d` is what makes the
 * base case vacuous rather than wrong.
 */
final class Coding private (
  val modular: Modular,
  val theory: Theory,
  val notation: Notation,
  /** The connectives read against **this** signature, which is wider than `Modular`'s. */
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The arithmetic this development is built on. */
  val peano: Peano = modular.peano

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A theorem of this development, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Coding {

  /** `NUM_FACT k` is `k!`, by recursion on `k` exactly as `NUM_POW` recurses on its exponent. */
  val FactorialName: String = "NUM_FACT"

  /** `|- NUM_FACT ZERO = SUC ZERO`. The empty product is one, not zero. */
  val FactorialAtZero: String = "NUM_FACT_ZERO"

  /** `|- !k. NUM_FACT (SUC k) = NUM_MUL (NUM_FACT k) (SUC k)`. */
  val FactorialAtSuccessor: String = "NUM_FACT_SUC"

  /**
   * `|- !d k. NUM_LT 0 d /\ NUM_LE d k ==> NUM_DIVIDES d (NUM_FACT k)`
   *
   * The reason the factorial is here at all: it is the `b` the beta function's moduli are built
   * from, and what makes those moduli pairwise coprime is this.
   */
  val FactorialDivides: String = "NUM_FACT_DIVIDES"

  /**
   * `|- !m n a b. NUM_GCD m n = SUC ZERO /\ NUM_LT ZERO m /\ NUM_LT ZERO n ==>
   * ?x. NUM_CONG m x a /\ NUM_CONG n x b`
   *
   * The Chinese remainder theorem for two moduli, which `Modular` does not have and which the beta
   * function's sequence lemma is an induction over.
   */
  val Remainders: String = "NUM_CRT_PAIR"

  /** `NUM_PROD f n` is `f ZERO * ... * f (n - 1)`, the twin of `Peano.PartialSum` at the product. */
  val ProductName: String = "NUM_PROD"

  /** `|- !f. NUM_PROD f ZERO = SUC ZERO`. The empty product is one. */
  val ProductAtZero: String = "NUM_PROD_ZERO"

  /** `|- !f n. NUM_PROD f (SUC n) = NUM_MUL (NUM_PROD f n) (f n)`. */
  val ProductAtSuccessor: String = "NUM_PROD_SUC"

  /**
   * `|- !a b c. (~(a = ZERO) \/ ~(b = ZERO)) ==> NUM_GCD a b = SUC ZERO ==>
   * NUM_DIVIDES a (NUM_MUL b c) ==> NUM_DIVIDES a c`
   *
   * Gauss's lemma, and the piece the moduli of the beta function are proved coprime with.
   * `Modular.Euclid` is the same statement for a **prime** divisor and does not cover this: what
   * the argument needs is that a divisor coprime to one factor divides the other, whatever it is
   * made of.
   *
   * The guard is Bezout's own, and it is not decoration: at `a = b = ZERO` the conclusion is
   * `NUM_DIVIDES ZERO c`, which says `c = ZERO`, while the premise `NUM_DIVIDES ZERO (NUM_MUL ZERO
   * c)` holds for every `c`. `NUM_GCD ZERO ZERO` is a `select` over a set with no greatest element,
   * so nothing decides whether it is one, and the guard is what keeps the question from arising.
   */
  val Gauss: String = "NUM_GAUSS"

  /**
   * `|- !s n. ?M. !i. NUM_LT i n ==> NUM_LE (s i) M`
   *
   * Every finite stretch of a sequence is bounded, which the beta function needs in order to choose
   * the `k` its modulus is built from: `b = k!` wants a `k` above the length **and** above every
   * entry, and the entries are the half nothing else supplies.
   *
   * **The bound is a sum and not a maximum**, and that is the whole reason this is three dozen
   * lines rather than a development of its own. A maximum over `num` does not exist here:
   * `Magnitude` defines `max` over the reals and nothing carries it across. `M + s k` is a bound
   * whenever `M` is one, because nothing on `num` is negative, and the two facts it wants,
   * `x <= x + y` and `y <= x + y`, are each one step from what `NUM_LE` is defined as.
   */
  val Bound: String = "NUM_BOUNDED_BELOW_LENGTH"

  /**
   * `|- !b i j. NUM_LT i j /\ NUM_DIVIDES (NUM_SUB j i) b ==>
   * NUM_GCD (SUC (NUM_MUL (SUC i) b)) (SUC (NUM_MUL (SUC j) b)) = SUC ZERO`
   *
   * The moduli of the beta function are pairwise coprime, which is the fact the Chinese remainder
   * theorem is applied to and the reason the factorial is here at all.
   *
   * **The factorial does not appear in the statement, deliberately.** What the argument uses is
   * `(j - i) | b` and nothing else about how `b` was chosen; `b = k!` with `j - i` at most `k` is
   * one way to arrange that and [[FactorialDivides]] is what arranges it, but the lemma is about
   * the moduli and not about factorials. Stating it with `NUM_FACT` in it would have tied a fact
   * about `1 + a * b` to one supplier of `b`.
   *
   * The argument is Gauss twice over a shape used twice. A common divisor of the two moduli divides
   * their difference `(j - i) * b`; it is coprime to `b`, because anything dividing both it and `b`
   * divides `SUC ((i + 1) * b)` and `(i + 1) * b` and so divides one; Gauss then puts it into
   * `j - i`, which divides `b`, so it divides `b` and the same step that proved coprimality now
   * proves it is one.
   */
  val ModuliCoprime: String = "NUM_GCD_SHIFTED_MULTIPLES"

  /**
   * `|- !m i n. NUM_LT i n ==> NUM_DIVIDES (m i) (NUM_PROD m n)`
   *
   * Each factor divides the product, which is how the Chinese remainder theorem reads its answer
   * back: it solves the whole product at once and then needs `m i` to be a divisor of it before
   * `Modular.CongDivisor` can descend to the factor.
   */
  val ProductDivides: String = "NUM_PROD_DIVIDES"

  /**
   * `|- !f g n. (!i. NUM_LT i n ==> f i = g i) ==> NUM_PROD f n = NUM_PROD g n`
   *
   * Two families that agree below the length have the same product, which is what a caller needs
   * the moment it **builds** a family rather than receiving one: a family extended at one index is
   * written with a conditional, and nothing said that the conditional's true branch leaves the
   * shorter product where it was.
   *
   * It is stated over an agreement **below the length** rather than everywhere, and that is the
   * whole of its use: a family extended at `k` disagrees with the old one exactly at `k`, and a
   * version asking for agreement at every index would not apply to the one place it is wanted.
   *
   * The induction is the ordinary one. The step splits the agreement it is given in two, at the
   * new index and below it, because `NUM_PROD` puts the new factor on the right and the two halves
   * of the recurrence want different halves of the hypothesis.
   */
  val ProductCongruent: String = "NUM_PROD_CONG"

  /**
   * `|- !m n. (!i. NUM_LT i n ==> NUM_LT ZERO (m i)) ==> NUM_LT ZERO (NUM_PROD m n)`
   *
   * The product of positives is positive, which the two-modulus theorem asks of its moduli and
   * which the empty product satisfies because it is one rather than zero.
   */
  val ProductPositive: String = "NUM_PROD_POSITIVE"

  /**
   * `|- !a b c. NUM_LT ZERO c ==> NUM_GCD a c = SUC ZERO ==> NUM_GCD b c = SUC ZERO ==>
   * NUM_GCD (NUM_MUL a b) c = SUC ZERO`
   *
   * Coprime to each factor is coprime to the product, which is [[Gauss]] spent on the one thing
   * Gauss is for. A common divisor of `a * b` and `c` is coprime to `a`, because anything dividing
   * it and `a` divides `c` through it and so divides `NUM_GCD a c`; Gauss then puts it into `b`,
   * where the same step run against `NUM_GCD b c` makes it one.
   *
   * **`NUM_LT ZERO c` is carried and is not a convenience.** Every fact about a greatest common
   * divisor here is guarded by "not both zero", because `NUM_GCD ZERO ZERO` is a choice over a set
   * with no greatest element and nothing decides it. At `c = ZERO` the hypotheses do not settle
   * whether `a` and `b` vanish, so the guard the conclusion needs cannot be derived; a positive `c`
   * discharges every one of them at once, and it is what the caller has anyway, since a modulus
   * the Chinese remainder theorem divides by is positive.
   */
  val CoprimeToProduct: String = "NUM_GCD_MUL"

  /**
   * `|- !m c n. NUM_LT ZERO c ==> (!i. NUM_LT i n ==> NUM_GCD (m i) c = SUC ZERO) ==>
   * NUM_GCD (NUM_PROD m n) c = SUC ZERO`
   *
   * The same over a whole family, by induction on the length with [[CoprimeToProduct]] as the step.
   * The base is where the empty product being one rather than zero pays for itself a second time:
   * `NUM_GCD (SUC ZERO) c` divides one and so is one, whatever `c` is.
   */
  val CoprimeToFamily: String = "NUM_GCD_PROD"

  /**
   * `|- !m a n. (!i. NUM_LT i n ==> NUM_LT ZERO (m i)) ==>
   * (!i j. NUM_LT i n /\ NUM_LT j n /\ ~(i = j) ==> NUM_GCD (m i) (m j) = SUC ZERO) ==>
   * (?x. !i. NUM_LT i n ==> NUM_CONG (m i) x (a i))`
   *
   * The Chinese remainder theorem for `n` moduli, which is what the beta function's sequence lemma
   * is an application of and the reason every lemma above it exists.
   *
   * **The induction does not need a stronger statement than the one published**, which is the part
   * a reader expects to be otherwise. The usual strengthening is "and the solution is unique modulo
   * the product", carried so that the step has something to extend; here the step never needs it,
   * because [[Remainders]] hands back a number congruent to the shorter solution **modulo the whole
   * product**, and [[ProductDivides]] with `Modular.CongDivisor` walks that down to each factor.
   * What makes that available is that [[Remainders]] was stated as two congruences rather than as a
   * residue, and this is where that choice is spent.
   */
  val RemaindersFamily: String = "NUM_CRT"

  /**
   * `|- !k. NUM_LT ZERO (NUM_FACT k)`
   *
   * The factorial never vanishes, which is the one thing `Modular.DividesBound` needs before
   * `k | k!` can be read as `k <= k!`: that lemma concludes a disjunction whose other half is
   * `b = ZERO`, because zero is divided by everything.
   */
  val FactorialPositive: String = "NUM_FACT_POSITIVE"

  /**
   * `|- !k. NUM_LE (NUM_POW (SUC (SUC ZERO)) k) (NUM_MUL (SUC (SUC ZERO)) (NUM_FACT k))`
   *
   * A power of two is at most twice the factorial, which is the **dominating series** the
   * exponential's convergence waits on: putting `1 / i!` under `2 * (1/2)^i` is this inequality
   * divided through, and `Limit.SUM_COMPARISON` has been provable and unspent since 2026-09-16 for
   * want of it. Five documents of this repository said the comparison test bought `exp 1 > 2` and
   * were wrong for a day; this is one of the two facts that were missing, the other being
   * `Order.INV_ANTITONE`, which landed on 2026-09-18.
   *
   * == Why the obvious induction does not close it, and why it is not a two-base one ==
   *
   * `P k := 2^k <= 2 * k!` has a step that is valid only from one upwards: `2^(SUC k)` is
   * `2^k * 2`, the hypothesis carries that under `(2 * k!) * 2 = 2 * (k! * 2)`, and reaching
   * `2 * (k! * SUC k)` asks for `2 <= SUC k`, which is false at zero. `P 0` is nonetheless true,
   * `1 <= 2`, so the statement holds everywhere and one induction cannot see it.
   *
   * A two-base induction is what that shape usually asks for and it is not what is done here.
   * `Q k := P (SUC k)` is proved by the ordinary induction instead: its step needs
   * `2 <= SUC (SUC k)`, which holds for every `k` because the index inside `Q` is already a
   * successor. `P ZERO` is three lines on its own, and `Natural.NUM_CASES` is what puts the two
   * together, every number being zero or a successor. Nothing new is needed anywhere.
   *
   * == Where it lives ==
   *
   * Here, with `NUM_FACT`, rather than in `Peano` with `NUM_POW`: a fact about both belongs with
   * the one that is defined later, and `Coding` is built before `Transcendental` in the chain, so
   * the lemma is in scope where `exp` is. It reaches the reals through `Series.NUM_REAL_POW`.
   */
  val PowerBelowFactorial: String = "NUM_POW_LE_FACT"

  /**
   * `NUM_BETA a b i` is `a mod (1 + (i + 1) * b)`, Goedel's beta function.
   *
   * A definition and not a recursion, which is the whole reason `docs/adr/0013` chose it over a
   * product of prime powers: **decoding is one remainder**. Reading the `i`th entry of a coded
   * sequence costs a multiplication and a `NUM_MOD`, so the decoding relation is Delta-0 and the
   * embedded theory can reason about it without an induction of its own. A prime-power coding
   * decodes by an exponent search, which is not.
   *
   * It has no spelling of its own, for the reason `COND` has none: `NUM_BETA a b i` is what it is
   * written as, and giving it one would be a change to the parser rather than a row in the
   * precedence table.
   */
  val BetaName: String = "NUM_BETA"

  /**
   * `|- !s n. ?a b. !i. NUM_LT i n ==> NUM_BETA a b i = s i`
   *
   * **The sequence lemma, which is what everything in this file was built for.** Any finite stretch
   * of any sequence of naturals is the beta function of two numbers, so two numbers code a sequence
   * of any length, which is what lets a theory with no sequences talk about them.
   *
   * The construction is Goedel's. Take `k` above the length and above every entry, let `b = k!`,
   * and take the moduli `1 + (i + 1) * b`. They are pairwise coprime by [[ModuliCoprime]], because
   * the gap between any two indices is positive and at most `k` and so divides `k!`; they are
   * positive because each is a successor; so [[RemaindersFamily]] produces one `a` congruent to
   * `s i` modulo the `i`th. Each `s i` is below its own modulus, because `s i <= k <= k! = b` and
   * `b <= (i + 1) * b < 1 + (i + 1) * b`, and `Modular.ModOfCong` turns a congruence to something
   * already below the modulus into the remainder itself.
   *
   * **`k` is `SUC (M + n)` rather than a maximum**, for the reason [[Bound]] gives about itself:
   * `num` has no maximum here, a sum is a bound whenever either summand is, and the successor makes
   * `k` positive, which is what [[FactorialDivides]] asks of every divisor it is handed.
   */
  val BetaSequence: String = "NUM_BETA_SEQUENCE"

  /**
   * Every statement this development publishes, as text.
   *
   * Text and not terms, for the reason `Peano` gives at the same table: what a reader checks
   * against the informal claim is the text, and a statement built twice in two notations is a
   * statement free to drift from itself.
   */
  val Statements: Vector[(String, String)] = Vector(
    FactorialAtZero -> "NUM_FACT ZERO = SUC ZERO",
    FactorialAtSuccessor -> "!k:num. NUM_FACT (SUC k) = NUM_MUL (NUM_FACT k) (SUC k)",
    FactorialDivides ->
      "!d:num k:num. NUM_LT ZERO d /\\ NUM_LE d k ==> NUM_DIVIDES d (NUM_FACT k)",
    ProductDivides -> "!m:num -> num. !i:num. !n:num. NUM_LT i n ==> NUM_DIVIDES (m i) (NUM_PROD m n)",
    ProductCongruent ->
      ("!f:num -> num. !g:num -> num. !n:num. (!i:num. NUM_LT i n ==> f i = g i) ==> " +
        "NUM_PROD f n = NUM_PROD g n"),
    ProductPositive ->
      ("!m:num -> num. !n:num. (!i:num. NUM_LT i n ==> NUM_LT ZERO (m i)) ==> " +
        "NUM_LT ZERO (NUM_PROD m n)"),
    CoprimeToProduct ->
      ("!a:num b:num c:num. NUM_LT ZERO c ==> NUM_GCD a c = SUC ZERO ==> " +
        "NUM_GCD b c = SUC ZERO ==> NUM_GCD (NUM_MUL a b) c = SUC ZERO"),
    CoprimeToFamily ->
      ("!m:num -> num. !c:num. !n:num. NUM_LT ZERO c ==> " +
        "(!i:num. NUM_LT i n ==> NUM_GCD (m i) c = SUC ZERO) ==> " +
        "NUM_GCD (NUM_PROD m n) c = SUC ZERO"),
    FactorialPositive -> "!k:num. NUM_LT ZERO (NUM_FACT k)",
    PowerBelowFactorial ->
      "!k:num. NUM_LE (NUM_POW (SUC (SUC ZERO)) k) (NUM_MUL (SUC (SUC ZERO)) (NUM_FACT k))",
    BetaSequence ->
      ("!s:num -> num. !n:num. ?a:num. ?b:num. !i:num. " +
        "NUM_LT i n ==> NUM_BETA a b i = s i"),
    RemaindersFamily ->
      ("!m:num -> num. !a:num -> num. !n:num. " +
        "(!i:num. NUM_LT i n ==> NUM_LT ZERO (m i)) ==> " +
        "(!i:num. !j:num. NUM_LT i n /\\ NUM_LT j n /\\ ~(i = j) ==> " +
        "NUM_GCD (m i) (m j) = SUC ZERO) ==> " +
        "(?x:num. !i:num. NUM_LT i n ==> NUM_CONG (m i) x (a i))"),
    ModuliCoprime ->
      ("!b:num i:num j:num. NUM_LT i j /\\ NUM_DIVIDES (NUM_SUB j i) b ==> " +
        "NUM_GCD (SUC (NUM_MUL (SUC i) b)) (SUC (NUM_MUL (SUC j) b)) = SUC ZERO"),
    Bound ->
      "!s:num -> num. !n:num. ?M:num. !i:num. NUM_LT i n ==> NUM_LE (s i) M",
    ProductAtZero -> "!f:num -> num. NUM_PROD f ZERO = SUC ZERO",
    ProductAtSuccessor ->
      "!f:num -> num. !n:num. NUM_PROD f (SUC n) = NUM_MUL (NUM_PROD f n) (f n)",
    Gauss ->
      ("!a:num b:num c:num. (~(a = ZERO) \\/ ~(b = ZERO)) ==> NUM_GCD a b = SUC ZERO ==> " +
        "NUM_DIVIDES a (NUM_MUL b c) ==> NUM_DIVIDES a c"),
    Remainders ->
      ("!m:num n:num a:num b:num. " +
        "NUM_GCD m n = SUC ZERO /\\ NUM_LT ZERO m /\\ NUM_LT ZERO n ==> " +
        "(?x:num. NUM_CONG m x a /\\ NUM_CONG n x b)")
  )

  /** Build it over a development that has divisibility, in that development's own notation. */
  def construct(modular: Modular): Either[LogicError, Coding] =
    construct(modular, modular.theory, modular.notation)

  /**
   * The same, extending a theory that already holds something else.
   *
   * The chain entry point, the shape `Modular.construct` already had and for the same reason: two
   * developments built beside each other declare different constants of the same name, so a claim
   * mentioning `NUM_FACT` and `NUM_CONG` at once is not a proposition unless one theory holds both.
   *
   * **The notation is a parameter for a reason that only shows once this is `Chain.widest`.** That
   * signature is what `docs/lemmas.md` is printed through, so a notation narrower than the theory
   * generates a document naming constants it cannot write: reading `Peano`'s here would print every
   * lemma of `Magnitude` with `abs` and `max` unwritable. The base and the notation travel together
   * and come from the same link.
   */
  def construct(modular: Modular, base: Theory, notation: Notation): Either[LogicError, Coding] = {
    val peano = modular.peano
    val numbers = TyApp(Natural.TypeName, Nil)

    for {
      recursion <- peano.naturals.recursion
      defined <- Recursion.define(
        modular.logic,
        peano.naturals,
        base,
        notation,
        recursion,
        FactorialName,
        numbers,
        "SUC ZERO",
        "\\v:num. \\i:num. NUM_MUL v (SUC i)",
        None
      )
      (factorialTheory, definition, atZero, atSuccessor) = defined

      function = Term.variable("f", Type.fun(numbers, numbers))
      definedProduct <- Recursion.define(
        modular.logic,
        peano.naturals,
        factorialTheory,
        notation,
        recursion,
        ProductName,
        numbers,
        "SUC ZERO",
        "\\v:num. \\i:num. NUM_MUL v ((f:num -> num) i)",
        Some(function)
      )
      (productTheory, productDefinition, productZero, productSuccessor) = definedProduct

      // The beta function, which is a definition and not a recursion: one remainder.
      betaBody <- Parser.term(
        productTheory,
        notation,
        "\\a:num b:num i:num. NUM_MOD a (SUC (NUM_MUL (SUC i) b))"
      )
      withBeta <- LogicError.lift(Kernel.defineConstant(productTheory, BetaName, betaBody))
      (theory, betaDefinition) = withBeta

      logic <- modular.logic.over(theory)
      induction <- peano.naturals.fact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)

      vocabulary <- Vocabulary.of(modular, theory, notation, logic)
      zeroChecked <- vocabulary.checked(FactorialAtZero, atZero)
      successorChecked <- vocabulary.checked(FactorialAtSuccessor, atSuccessor)
      divides <- factorialDivides(vocabulary, driver, successorChecked)
      productZeroChecked <- vocabulary.checked(ProductAtZero, productZero)
      productSuccessorChecked <- vocabulary.checked(ProductAtSuccessor, productSuccessor)
      semiring <- Semiring.construct(peano)
      gauss <- gaussLemma(vocabulary, semiring)
      bound <- boundedStretch(vocabulary, driver)
      productDivides <- eachFactorDivides(vocabulary, driver, semiring, productSuccessorChecked)
      productCongruent <- productsOfAgreeingFamilies(
        vocabulary, driver, productZeroChecked, productSuccessorChecked)
      productPositive <- productOfPositives(vocabulary, driver, productZeroChecked, productSuccessorChecked)
      coprime <- moduliCoprime(vocabulary, semiring, gauss)
      crt <- remainders(vocabulary, semiring)
      coprimeProduct <- coprimeToProduct(vocabulary, gauss)
      coprimeFamily <- coprimeToFamily(vocabulary, driver, productZeroChecked, productSuccessorChecked, coprimeProduct)
      family <- remaindersOverAFamily(vocabulary, driver, crt, productDivides, productPositive, coprimeFamily)
      factorialPositive <- factorialNeverVanishes(vocabulary, driver, zeroChecked, successorChecked)
      powerBelow <- powerBelowFactorial(vocabulary, driver, zeroChecked, successorChecked)
      betaSequence <- sequenceOfResidues(
        vocabulary, bound, divides, factorialPositive, coprime, family, betaDefinition)
    } yield new Coding(
      modular,
      theory,
      notation,
      logic,
      Map(
        FactorialName -> definition,
        ProductName -> productDefinition,
        BetaName -> betaDefinition
      ),
      Map(
        FactorialAtZero -> zeroChecked,
        FactorialAtSuccessor -> successorChecked,
        FactorialDivides -> divides,
        ProductAtZero -> productZeroChecked,
        ProductAtSuccessor -> productSuccessorChecked,
        Gauss -> gauss,
        Bound -> bound,
        ProductDivides -> productDivides,
        ProductCongruent -> productCongruent,
        ProductPositive -> productPositive,
        ModuliCoprime -> coprime,
        Remainders -> crt,
        CoprimeToProduct -> coprimeProduct,
        CoprimeToFamily -> coprimeFamily,
        RemaindersFamily -> family,
        FactorialPositive -> factorialPositive,
        PowerBelowFactorial -> powerBelow,
        BetaSequence -> betaSequence
      )
    )
  }

  /**
   * What every derivation below needs to hand, gathered once.
   *
   * A record rather than eleven arguments threaded through four private methods. `Modular` has the
   * same thing under the same name and it is not shared: that one carries what a congruence proof
   * reaches for, this one carries what a divisibility induction reaches for, and merging them would
   * make each file hold the other's vocabulary.
   */
  private final case class Vocabulary(
    peano: Peano,
    theory: Theory,
    notation: Notation,
    logic: Logic,
    numbers: Type,
    zero: Term,
    successor: Term,
    below: Term,
    atMost: Term,
    plus: Term,
    times: Term,
    divides: Term,
    factorial: Term,
    strictOrder: Kernel.Thm,
    facts: Map[String, Kernel.Thm]
  ) {

    val rules: Rules = logic.rules

    /** `SUC ZERO`, which is the unit `Peano.TimesOne` is stated at and not the numeral `1`. */
    lazy val one: Either[LogicError, Term] = LogicError.lift(Term.app(successor, zero))

    def sum(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(plus, List(left, right)))

    def product(left: Term, right: Term): Either[LogicError, Term] =
      LogicError.lift(Term.appAll(times, List(left, right)))

    /** `|- left = right` by the semiring, or a refusal that names the identity that did not close. */
    def identity(semiring: Semiring, left: Term, right: Term): Either[LogicError, Kernel.Thm] =
      semiring.prove(left, right)

    /** `|- head + left = head + right` from `|- left = right`. */
    def underSum(head: Term, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      LogicError.lift(Term.app(plus, head)).flatMap(Conv.apTerm(_, equation))

    /** `|- left + tail = right + tail` from `|- left = right`. */
    def overSum(equation: Kernel.Thm, tail: Term): Either[LogicError, Kernel.Thm] =
      Conv.apTerm(plus, equation).flatMap(Conv.apThm(_, tail))

    /** `|- head * left = head * right` from `|- left = right`. */
    def underProduct(head: Term, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      LogicError.lift(Term.app(times, head)).flatMap(Conv.apTerm(_, equation))

    def fact(name: String): Either[LogicError, Kernel.Thm] =
      facts.get(name).toRight(MissingDefinition(name))

    /** The statement `name` publishes, read against this signature. */
    def statement(name: String): Either[LogicError, Term] =
      Statements
        .collectFirst { case (key, text) if key == name => text }
        .toRight(MissingDefinition(name))
        .flatMap(Parser.proposition(theory, notation, _))

    /**
     * A theorem, checked against the text this development publishes for it.
     *
     * The check is the point rather than the naming: a derivation that reaches a theorem close to
     * the one intended is the failure mode that survives a passing test, and the text above is what
     * a reader compared against the informal claim.
     */
    def checked(name: String, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      statement(name).flatMap { expected =>
        if (theorem.conclusion == expected) Right(theorem)
        else Left(NotOfForm(s"the statement published for $name", theorem.conclusion))
      }

    /** Carry `theorem` across an equation between two terms, by congruence and not by rewriting. */
    def carry(context: Term, equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        congruence <- Conv.apTerm(context, equation)
        result <- LogicError.lift(Kernel.eqMp(congruence, theorem))
      } yield result
  }

  private object Vocabulary {

    def of(
      modular: Modular,
      theory: Theory,
      notation: Notation,
      logic: Logic
    ): Either[LogicError, Vocabulary] = {
      val peano = modular.peano
      val numbers = TyApp(Natural.TypeName, Nil)
      val binary = Type.fun(numbers, Type.fun(numbers, Type.Bool))
      val arithmetic = Type.fun(numbers, Type.fun(numbers, numbers))

      val needed = Vector(
        Peano.NotBelowZero,
        Peano.BelowSuccessorCases,
        Peano.BelowOrEqual,
        Peano.AtMostFromBelow,
        Peano.Reflexive,
        Peano.AtMostZero,
        Peano.StrictIrreflexive,
        Peano.MulCommutative,
        Peano.MinusThenPlus,
        Peano.Transitive,
        Peano.AddCommutative,
        Peano.SuccessorPlus,
        Peano.AddAtSuccessor,
        Peano.AddAtZero,
        Peano.MulPositive,
        Peano.SuccessorPositive,
        Peano.BelowSuccessor,
        Peano.StrictTransitive,
        Peano.AtMostThenBelow,
        Peano.Trichotomy,
        Peano.AtMostSuccessor,
        Peano.SubBelow,
        Peano.ZeroPlus,
        Peano.SuccessorTimes,
        // What [[PowerBelowFactorial]] reaches for and nothing else here does: the two recurrences
        // of the power, the unit of multiplication, its monotonicity, and that a summand is at
        // most its sum.
        Peano.PowAtZero,
        Peano.PowAtSuccessor,
        Peano.TimesOne,
        Peano.MulMonotone,
        Peano.AtMostSum
      )

      for {
        zero <- LogicError.lift(theory.constant(Natural.NumberZero, numbers))
        successor <- LogicError.lift(
          theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers))
        )
        below <- LogicError.lift(theory.constant(Peano.StrictOrder, binary))
        atMost <- LogicError.lift(theory.constant(Peano.NonStrictOrder, binary))
        plus <- LogicError.lift(theory.constant(Peano.Addition, arithmetic))
        times <- LogicError.lift(theory.constant(Peano.Multiplication, arithmetic))
        divides <- LogicError.lift(theory.constant(Modular.DividesName, binary))
        factorial <- LogicError.lift(
          theory.constant(FactorialName, Type.fun(numbers, numbers))
        )
        strictOrder <- peano.definition(Peano.StrictOrder)
        fromPeano <- needed.foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](
          Right(Map.empty)
        ) { (acc, name) =>
          for {
            found <- acc
            theorem <- peano.fact(name)
          } yield found.updated(name, theorem)
        }
        fromModular <- Vector(
          Modular.DividesIntro,
          Modular.DividesMul,
          Modular.CongIntro,
          Modular.Bezout,
          Modular.DividesSummand,
          Modular.DividesOne,
          Modular.DividesTrans,
          Modular.GcdDividesLeft,
          Modular.GcdDividesRight,
          Modular.GcdDivides,
          Modular.ZeroDivides,
          Modular.DividesRefl,
          Modular.CongDivisor,
          Modular.CongTrans,
          Modular.DividesBound,
          Modular.GcdSym,
          Modular.ModOfCong
        ).foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(fromPeano)) { (acc, name) =>
          for {
            found <- acc
            theorem <- modular.fact(name)
          } yield found.updated(name, theorem)
        }
      } yield Vocabulary(
        peano,
        theory,
        notation,
        logic,
        numbers,
        zero,
        successor,
        below,
        atMost,
        plus,
        times,
        divides,
        factorial,
        strictOrder,
        fromModular
      )
    }
  }

  /**
   * [[FactorialDivides]], by induction on the bound with the divisor fixed.
   *
   * Three cases at `SUC k` and not two, which is where the derivation is longer than the argument a
   * reader would give. `NUM_LE_CASES` splits `d <= SUC k` into `d < SUC k` and `d = SUC k`, and the
   * first of those has to be split again by `NUM_LT_SUC_CASES` into `d < k` and `d = k`, because
   * what the induction hypothesis wants is `d <= k` and neither half of the first split is that.
   * Both halves reach it, by weakening and by reflexivity respectively, and from there the two
   * share every remaining step.
   */
  private def factorialDivides(
    vocabulary: Vocabulary,
    driver: Induct,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      statement <- vocabulary.statement(FactorialDivides)
      proved <- driver.proveBy(
        statement,
        goal => vacuousUnderPositivity(vocabulary, goal),
        step => factorialStep(vocabulary, atSuccessor, step)
      )
      // Nothing assumed, asserted here rather than left to the caller. `Induct.proveBy` checks the
      // conclusion and says nothing about the hypotheses, and a branch that forgot to discharge an
      // assumption comes back with the right conclusion carrying it.
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(FactorialDivides, proved)
    } yield result
  }

  /**
   * At zero the two hypotheses cannot both hold: `d <= 0` makes `d` zero and `0 < d` denies it.
   *
   * The premise here is a **conjunction** and both halves are used. [[vacuousBelowZero]] is the
   * other shape, where the premise is the comparison alone, and they are two methods rather than
   * one that looks at what it was handed: a premise that is not the shape expected is a refusal
   * worth getting at the call site, and reusing this one for the bound is the mistake that made
   * the chain refuse with "expected a conjunction".
   */
  private def vacuousUnderPositivity(vocabulary: Vocabulary, goal: Term): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
      (premise, consequent) = parts
      assumed <- LogicError.lift(Kernel.assume(premise))
      positive <- rules.conjElim1(assumed)
      bounded <- rules.conjElim2(assumed)

      divisor <- positive.conclusion match {
        case App(App(_, _), right) => Right(right)
        case other => Left(NotOfForm("a comparison", other))
      }
      atMostZero <- vocabulary.fact(Peano.AtMostZero)
      isZero <- rules.spec(divisor, atMostZero).flatMap(rules.mp(_, bounded))

      // `0 < d` carried across `d = 0`, which is `0 < 0`, which nothing is.
      context <- LogicError.lift(Term.app(vocabulary.below, vocabulary.zero))
      absurdly <- vocabulary.carry(context, isZero, positive)
      irreflexive <- vocabulary.fact(Peano.StrictIrreflexive)
      never <- rules.spec(vocabulary.zero, irreflexive)
      contradiction <- rules.notElim(never, absurdly)
      anything <- rules.falsityElim(consequent, contradiction)
      result <- rules.disch(premise, anything)
    } yield result
  }

  /**
   * At `SUC k`: either `d` is `SUC k`, and the factorial's own recurrence is the witness, or `d` is
   * at most `k`, and the hypothesis gives a divisor of `k!` which survives multiplication.
   */
  private def factorialStep(
    vocabulary: Vocabulary,
    atSuccessor: Kernel.Thm,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
      (premise, consequent) = parts
      assumed <- LogicError.lift(Kernel.assume(premise))
      positive <- rules.conjElim1(assumed)
      bounded <- rules.conjElim2(assumed)
      divisor <- positive.conclusion match {
        case App(App(_, _), right) => Right(right)
        case other => Left(NotOfForm("a comparison", other))
      }

      // `k!` and `(SUC k)! = k! * SUC k`, which both branches end at.
      previous <- LogicError.lift(Term.app(vocabulary.factorial, step.variable))
      successorOfK <- LogicError.lift(Term.app(vocabulary.successor, step.variable))
      recurrence <- rules.spec(step.variable, atSuccessor)

      cases <- vocabulary
        .fact(Peano.BelowOrEqual)
        .flatMap(rules.specAll(_, List(divisor, successorOfK)))
        .flatMap(rules.mp(_, bounded))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (strictly, exactly) = split

      whenBelow <- fromHypothesis(
        vocabulary, step, positive, divisor, previous, successorOfK, recurrence, strictly, consequent)
      whenEqual <- fromRecurrence(
        vocabulary, divisor, previous, successorOfK, recurrence, exactly, consequent)
      settled <- rules.disjElim(cases, whenBelow, whenEqual)
      result <- rules.disch(premise, settled)
    } yield result
  }

  /**
   * `d < SUC k`, so `d <= k` and the induction hypothesis applies.
   *
   * The second split lives here. `NUM_LT_SUC_CASES` turns `d < SUC k` into `d < k \/ d = k`, and
   * the two reach `d <= k` by different routes: weakening a strict inequality, and reflexivity
   * carried across an equation. Everything after that is shared, so it is done once, below.
   */
  private def fromHypothesis(
    vocabulary: Vocabulary,
    step: Induct.Step,
    positive: Kernel.Thm,
    divisor: Term,
    previous: Term,
    successorOfK: Term,
    recurrence: Kernel.Thm,
    strictly: Term,
    consequent: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      assumedStrict <- LogicError.lift(Kernel.assume(strictly))
      inner <- vocabulary
        .fact(Peano.BelowSuccessorCases)
        .flatMap(rules.specAll(_, List(step.variable, divisor)))
        .flatMap(rules.mp(_, assumedStrict))
      split <- logic.destDisj(inner.conclusion).toRight(NotOfForm("a disjunction", inner.conclusion))
      (belowK, equalK) = split

      // `d < k` weakens to `d <= k`.
      byWeakening <- for {
        assumed <- LogicError.lift(Kernel.assume(belowK))
        weakened <- vocabulary
          .fact(Peano.AtMostFromBelow)
          .flatMap(rules.specAll(_, List(divisor, step.variable)))
          .flatMap(rules.mp(_, assumed))
      } yield weakened

      // `d = k` carries `d <= d` to `d <= k`.
      byReflexivity <- for {
        assumed <- LogicError.lift(Kernel.assume(equalK))
        reflexive <- vocabulary.fact(Peano.Reflexive).flatMap(rules.spec(divisor, _))
        context <- LogicError.lift(Term.app(vocabulary.atMost, divisor))
        carried <- vocabulary.carry(context, assumed, reflexive)
      } yield carried

      atMostK <- rules.disjElim(inner, byWeakening, byReflexivity)
      antecedent <- rules.conjIntro(positive, atMostK)
      dividesPrevious <- rules.mp(step.hypothesis, antecedent)

      result <- throughRecurrence(
        vocabulary, divisor, previous, successorOfK, recurrence, dividesPrevious, consequent)
    } yield result
  }

  /** `d | k!` survives being multiplied by `SUC k`, which is what `(SUC k)!` is. */
  private def throughRecurrence(
    vocabulary: Vocabulary,
    divisor: Term,
    previous: Term,
    successorOfK: Term,
    recurrence: Kernel.Thm,
    dividesPrevious: Kernel.Thm,
    consequent: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      multiplied <- vocabulary
        .fact(Modular.DividesMul)
        .flatMap(rules.specAll(_, List(divisor, previous, successorOfK)))
        .flatMap(rules.mp(_, dividesPrevious))
      back <- Conv.sym(recurrence)
      context <- LogicError.lift(Term.app(vocabulary.divides, divisor))
      result <- vocabulary.carry(context, back, multiplied)
      _ <-
        if (result.conclusion == consequent) Right(())
        else Left(NotOfForm("what the step has to reach", result.conclusion))
    } yield result
  }

  /**
   * `d = SUC k`, and then `(SUC k)! = d * k!` is the witness divisibility asks for.
   *
   * The commutation is not avoidable by stating the recurrence the other way round: `NUM_FACT`'s
   * step is `k! * SUC k` because that is the order `Recursion.define` produces, and `NUM_DIVIDES`
   * wants its divisor on the left of the product. One `NUM_MUL_SYM` is the whole of it.
   */
  private def fromRecurrence(
    vocabulary: Vocabulary,
    divisor: Term,
    previous: Term,
    successorOfK: Term,
    recurrence: Kernel.Thm,
    exactly: Term,
    consequent: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      assumedEqual <- LogicError.lift(Kernel.assume(exactly))
      commuted <- vocabulary
        .fact(Peano.MulCommutative)
        .flatMap(rules.specAll(_, List(previous, successorOfK)))
      reordered <- Conv.trans(recurrence, commuted)

      // `SUC k * k!` becomes `d * k!`, by carrying the equation backwards into the left factor.
      back <- Conv.sym(assumedEqual)
      onTheLeft <- Conv.apTerm(vocabulary.times, back)
      applied <- Conv.apThm(onTheLeft, previous)
      witness <- Conv.trans(reordered, applied)

      target <- Term
        .destEq(witness.conclusion)
        .map(_._1)
        .toRight(NotOfForm("an equation", witness.conclusion))
      result <- vocabulary
        .fact(Modular.DividesIntro)
        .flatMap(rules.specAll(_, List(divisor, target, previous)))
        .flatMap(rules.mp(_, witness))
      _ <-
        if (result.conclusion == consequent) Right(())
        else Left(NotOfForm("what the step has to reach", result.conclusion))
    } yield result
  }

  /**
   * [[Remainders]], from Bezout, with one derivation used for both of its cases.
   *
   * `NUM_BEZOUT` is a **disjunction**, `m * z = n * u + g \/ n * z = m * u + g`, and it is one
   * because `num` has no subtraction: over the integers the two are one statement with a sign, and
   * here neither side can be moved across. That shape is the whole reason this derivation is
   * arranged the way it is. [[solveBezoutCase]] takes the roles as arguments and is called twice
   * with them swapped, so the second case costs one `conjIntro` to put the two congruences back in
   * the order the statement asks for, rather than a second copy of the argument.
   *
   * == The witness, and the `-1` that cannot be written ==
   *
   * With `m * z = n * u + 1`, the number `m * z` is zero mod `m` and one mod `n`, which is half of
   * what a solution needs. The other half wants something that is one mod `m` and zero mod `n`, and
   * the term that would be is `-(n * u)`, which does not exist here. What stands in for it is
   * `n * u * (m - 1)`: modulo `m` the factor `m - 1` is itself `-1`, so the two negatives multiply
   * out, and modulo `n` it is still a multiple of `n`. The truncated subtraction is safe because
   * `0 < m` is a hypothesis, and `Peano.MinusThenPlus` turns it into `(m - 1) + 1 = m`, which is
   * the only fact about `NUM_SUB` this file uses.
   *
   * The witness is then `a * (n * u * (m - 1)) + b * (m * z)`.
   *
   * == What `Semiring` does here, and what it cannot ==
   *
   * Every step that is an identity of the semiring is one call, at two axioms. The two steps that
   * are **not** identities are Bezout itself and `(m - 1) + 1 = m`: those are facts about these
   * particular terms, so they enter by congruence at the exact occurrence, never by rewriting.
   * Before `Semiring` existed this derivation would have gone through `Modular.identity` and cost
   * the sixteen axioms of the reals; `docs/adr/0013` is why that was worth removing first.
   */
  private def remainders(
    vocabulary: Vocabulary,
    semiring: Semiring
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)
    val a = Term.variable("a", numbers)
    val b = Term.variable("b", numbers)

    for {
      one <- vocabulary.one
      gcd <- LogicError.lift(
        vocabulary.theory.constant(
          Modular.GcdName,
          Type.fun(numbers, Type.fun(numbers, numbers))
        )
      )
      congruence <- LogicError.lift(
        vocabulary.theory.constant(
          Modular.CongruenceName,
          Type.fun(numbers, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
        )
      )

      greatest <- LogicError.lift(Term.appAll(gcd, List(m, n)))
      coprime <- LogicError.lift(Term.eq(greatest, one))
      positiveM <- LogicError.lift(Term.appAll(vocabulary.below, List(vocabulary.zero, m)))
      positiveN <- LogicError.lift(Term.appAll(vocabulary.below, List(vocabulary.zero, n)))
      positives <- logic.mkConj(positiveM, positiveN)
      premise <- logic.mkConj(coprime, positives)
      assumed <- LogicError.lift(Kernel.assume(premise))
      isOne <- rules.conjElim1(assumed)
      bothPositive <- rules.conjElim2(assumed)
      aboveZeroM <- rules.conjElim1(bothPositive)
      aboveZeroN <- rules.conjElim2(bothPositive)

      atLeastOneM <- atLeastOne(vocabulary, aboveZeroM, m)
      atLeastOneN <- atLeastOne(vocabulary, aboveZeroN, n)
      notZeroM <- notZero(vocabulary, aboveZeroM, m)

      // The goal both branches reach, built once so the disjunction elimination can compare them.
      x = Conv.freshVariable("x", numbers, Set(m, n, a, b))
      congruentToA <- LogicError.lift(Term.appAll(congruence, List(m, x, a)))
      congruentToB <- LogicError.lift(Term.appAll(congruence, List(n, x, b)))
      bothCongruent <- logic.mkConj(congruentToA, congruentToB)
      existential <- logic.mkExists(x, bothCongruent)
      predicate <- logic
        .destExistsPredicate(existential)
        .toRight(NotOfForm("an existential", existential))

      // Bezout, with the greatest common divisor replaced by the one the premise says it is.
      notZeroEither <- logic.mkNot(zeroOf(vocabulary, n)).flatMap(rules.disjIntro1(_, notZeroM))
      opened <- vocabulary
        .fact(Modular.Bezout)
        .flatMap(rules.specAll(_, List(m, n)))
        .flatMap(rules.mp(_, notZeroEither))
      rule <- Rewrite.Rule.of(logic, isOne)
      simplified <- Rewrite.inTheorem(Vector(rule), opened)

      found <- withTwoWitnesses(vocabulary, simplified, Set(m, n, a, b, x)) { (z, u, cases) =>
        for {
          split <- logic
            .destDisj(cases.conclusion)
            .toRight(NotOfForm("a disjunction", cases.conclusion))
          (throughM, throughN) = split

          // `m * z = n * u + 1`: `m` is the modulus whose residue is `a`.
          first <- for {
            assumedCase <- LogicError.lift(Kernel.assume(throughM))
            solved <- solveBezoutCase(
              vocabulary, semiring, m, n, a, b, z, u, assumedCase, atLeastOneM)
            (witness, toA, toB) = solved
            both <- rules.conjIntro(toA, toB)
            introduced <- rules.existsIntro(predicate, witness, both)
          } yield introduced

          // `n * z = m * u + 1`: the same derivation with the two moduli exchanged, and the two
          // congruences put back in the statement's order.
          second <- for {
            assumedCase <- LogicError.lift(Kernel.assume(throughN))
            solved <- solveBezoutCase(
              vocabulary, semiring, n, m, b, a, z, u, assumedCase, atLeastOneN)
            (witness, toB, toA) = solved
            both <- rules.conjIntro(toA, toB)
            introduced <- rules.existsIntro(predicate, witness, both)
          } yield introduced

          settled <- rules.disjElim(cases, first, second)
        } yield settled
      }

      discharged <- rules.disch(premise, found)
      general <- rules.genAll(discharged, List(m, n, a, b))
      result <- vocabulary.checked(Remainders, general)
    } yield result
  }

  /** `p = ZERO`, as a term. */
  private def zeroOf(vocabulary: Vocabulary, subject: Term): Term =
    Term.eq(subject, vocabulary.zero).getOrElse(subject)

  /**
   * `NUM_LE (SUC ZERO) p` from `NUM_LT ZERO p`, which is an unfolding and not a lemma.
   *
   * `Peano` defines `NUM_LT m n` as `NUM_LE (SUC m) n`, so the two are the same proposition with
   * the constant folded. Worth a method rather than four lines inline because the derivation below
   * needs it for each modulus and the fact that it costs nothing is the kind of thing a reader
   * should be able to see once.
   */
  private def atLeastOne(
    vocabulary: Vocabulary,
    positive: Kernel.Thm,
    subject: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      unfolded <- Conv
        .unfold(vocabulary.strictOrder, List(vocabulary.zero, subject))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, positive)))
    } yield unfolded

  /** `~(p = ZERO)` from `NUM_LT ZERO p`, which Bezout asks for and the order does not hand over. */
  private def notZero(
    vocabulary: Vocabulary,
    positive: Kernel.Thm,
    subject: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val isZero = zeroOf(vocabulary, subject)

    for {
      assumed <- LogicError.lift(Kernel.assume(isZero))
      context <- LogicError.lift(Term.app(vocabulary.below, vocabulary.zero))
      absurdly <- vocabulary.carry(context, assumed, positive)
      never <- vocabulary.fact(Peano.StrictIrreflexive).flatMap(rules.spec(vocabulary.zero, _))
      contradiction <- rules.notElim(never, absurdly)
      result <- rules.notIntro(isZero, contradiction)
    } yield result
  }

  /**
   * Open `?z. ?u. body` with two fresh names and hand the instance to the caller.
   *
   * Two nested eliminations, and the inner one is the one that has to be done first: its case
   * theorem is what the outer one discharges. `Modular` has the same helper and it is not shared,
   * for the reason its own `Vocabulary` is not: each file's is shaped by the eliminations it does.
   */
  private def withTwoWitnesses(
    vocabulary: Vocabulary,
    existential: Kernel.Thm,
    avoid: Set[FVar]
  )(
    reach: (Term, Term, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    def instanceOf(theorem: Kernel.Thm, name: String, taken: Set[FVar]): Either[LogicError, (FVar, Kernel.Thm)] =
      for {
        predicate <- logic
          .destExistsPredicate(theorem.conclusion)
          .toRight(NotOfForm("an existential", theorem.conclusion))
        variable = Conv.freshVariable(name, vocabulary.numbers, taken ++ Term.freeVariables(theorem.conclusion))
        applied <- LogicError.lift(Term.app(predicate, variable))
        contraction <- Conv.betaRoot(applied)
        instance <- Term
          .destEq(contraction.conclusion)
          .map(_._2)
          .toRight(NotOfForm("an equation", contraction.conclusion))
        assumed <- LogicError.lift(Kernel.assume(instance))
      } yield (variable, assumed)

    for {
      outer <- instanceOf(existential, "z", avoid)
      (z, innerExistential) = outer
      inner <- instanceOf(innerExistential, "u", avoid + z)
      (u, body) = inner
      reached <- reach(z, u, body)
      closedInner <- rules.existsElim(innerExistential, u, reached)
      closedOuter <- rules.existsElim(existential, z, closedInner)
    } yield closedOuter
  }

  /**
   * One case of Bezout: `p * z = q * u + 1` gives a number congruent to `s` mod `p` and `t` mod `q`.
   *
   * Returns the witness alongside the two congruences, because the caller has to put the same term
   * into the existential and cannot rebuild it: the second Bezout case calls this with the roles
   * exchanged, so the term it produces is not the one the first case produced.
   */
  private def solveBezoutCase(
    vocabulary: Vocabulary,
    semiring: Semiring,
    p: Term,
    q: Term,
    s: Term,
    t: Term,
    z: Term,
    u: Term,
    bezout: Kernel.Thm,
    atLeastOne: Kernel.Thm
  ): Either[LogicError, (Term, Kernel.Thm, Kernel.Thm)] = {
    val rules = vocabulary.rules

    for {
      one <- vocabulary.one
      subtraction <- LogicError.lift(
        vocabulary.theory.constant(
          Peano.Subtraction,
          Type.fun(vocabulary.numbers, Type.fun(vocabulary.numbers, vocabulary.numbers))
        )
      )
      lowered <- LogicError.lift(Term.appAll(subtraction, List(p, one)))
      restored <- vocabulary
        .fact(Peano.MinusThenPlus)
        .flatMap(rules.specAll(_, List(p, one)))
        .flatMap(rules.mp(_, atLeastOne))

      multiple <- vocabulary.product(q, u)
      stretched <- vocabulary.product(multiple, lowered)
      scaled <- vocabulary.product(p, z)

      key <- coreIdentity(vocabulary, semiring, one, p, multiple, lowered, scaled, bezout, restored)

      // `s * (q * u * (p - 1)) + t * (p * z)`
      firstPart <- vocabulary.product(s, stretched)
      secondPart <- vocabulary.product(t, scaled)
      witness <- vocabulary.sum(firstPart, secondPart)

      toS <- congruentToFirst(
        vocabulary, semiring, one, p, s, t, z, witness, key, stretched, scaled, multiple)
      toT <- congruentToSecond(
        vocabulary, semiring, one, q, s, t, u, witness, bezout, stretched, scaled, multiple, lowered)
    } yield (witness, toS, toT)
  }


  /**
   * `|- F * P + p * z = 1 + p * F`, which is the whole arithmetic content of the construction.
   *
   * Read it as `F * (p - 1) ≡ 1 (mod p)`, written additively because that is what `NUM_CONG` is and
   * because `num` cannot write the other form. Five steps: put Bezout in at the one place it
   * belongs, let the semiring group `F * P + F` into `F * (P + 1)`, put `(p - 1) + 1 = p` in at the
   * one place **it** belongs, and let the semiring finish.
   *
   * The two facts enter by congruence under a fixed context rather than by rewriting. A rewrite
   * with `(p - 1) + 1 = p` would be looking for a pattern that occurs once here and could occur
   * again in a caller's term; a congruence says which occurrence.
   */
  private def coreIdentity(
    vocabulary: Vocabulary,
    semiring: Semiring,
    one: Term,
    p: Term,
    multiple: Term,
    lowered: Term,
    scaled: Term,
    bezout: Kernel.Thm,
    restored: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      stretched <- vocabulary.product(multiple, lowered)
      // `F + 1`, which is what Bezout says `p * z` is, and `(p - 1) + 1`, which is what
      // `Peano.MinusThenPlus` says `p` is. Two sums that look alike and are not: the first is what
      // arrives on the right of the equation, the second is what leaves on the left.
      afterBezout <- vocabulary.sum(multiple, one)
      beforeRestoring <- vocabulary.sum(lowered, one)
      grouped <- vocabulary.product(multiple, beforeRestoring)

      opened <- vocabulary.underSum(stretched, bezout)
      regrouped <- for {
        left <- vocabulary.sum(stretched, afterBezout)
        right <- vocabulary.sum(grouped, one)
        proved <- semiring.prove(left, right)
      } yield proved
      collapsed <- vocabulary.underProduct(multiple, restored)
      carried <- vocabulary.overSum(collapsed, one)
      finished <- for {
        left <- vocabulary.product(multiple, p).flatMap(vocabulary.sum(_, one))
        right <- vocabulary.product(p, multiple).flatMap(vocabulary.sum(one, _))
        proved <- semiring.prove(left, right)
      } yield proved

      whole <- Conv
        .trans(opened, regrouped)
        .flatMap(Conv.trans(_, carried))
        .flatMap(Conv.trans(_, finished))
    } yield whole

  /** The congruence at the modulus Bezout's equation is about, which is where `key` is spent. */
  private def congruentToFirst(
    vocabulary: Vocabulary,
    semiring: Semiring,
    one: Term,
    p: Term,
    s: Term,
    t: Term,
    z: Term,
    witness: Term,
    key: Kernel.Thm,
    stretched: Term,
    scaled: Term,
    multiple: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      inner <- vocabulary.sum(stretched, scaled)
      scaledBy <- vocabulary.product(s, inner)
      tail <- vocabulary.product(t, scaled)
      shift <- vocabulary.product(s, z)
      quotient <- for {
        first <- vocabulary.product(s, multiple)
        second <- vocabulary.product(t, z)
        both <- vocabulary.sum(first, second)
      } yield both

      start <- for {
        left <- vocabulary.product(p, shift).flatMap(vocabulary.sum(witness, _))
        right <- vocabulary.sum(scaledBy, tail)
        proved <- semiring.prove(left, right)
      } yield proved
      stepped <- vocabulary.underProduct(s, key).flatMap(vocabulary.overSum(_, tail))
      finish <- for {
        raised <- vocabulary.product(p, multiple).flatMap(vocabulary.sum(one, _))
        left <- vocabulary.product(s, raised).flatMap(vocabulary.sum(_, tail))
        right <- vocabulary.product(p, quotient).flatMap(vocabulary.sum(s, _))
        proved <- semiring.prove(left, right)
      } yield proved

      equation <- Conv.trans(start, stepped).flatMap(Conv.trans(_, finish))
      result <- vocabulary
        .fact(Modular.CongIntro)
        .flatMap(vocabulary.rules.specAll(_, List(p, witness, s, shift, quotient)))
        .flatMap(vocabulary.rules.mp(_, equation))
    } yield result

  /**
   * The congruence at the other modulus, which needs no shift at all.
   *
   * Both summands of the witness are already multiples of `q`: the first has `q * u` in it by
   * construction and the second becomes one as soon as Bezout is put in. So the multiplier on the
   * left of `NUM_CONG_INTRO` is `ZERO`, and this half is two semiring steps rather than three.
   */
  private def congruentToSecond(
    vocabulary: Vocabulary,
    semiring: Semiring,
    one: Term,
    q: Term,
    s: Term,
    t: Term,
    u: Term,
    witness: Term,
    bezout: Kernel.Thm,
    stretched: Term,
    scaled: Term,
    multiple: Term,
    lowered: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      head <- vocabulary.product(s, stretched)
      tail <- vocabulary.product(t, scaled)
      raised <- vocabulary.sum(multiple, one)
      quotient <- for {
        first <- vocabulary.product(u, lowered).flatMap(vocabulary.product(s, _))
        second <- vocabulary.product(t, u)
        both <- vocabulary.sum(first, second)
      } yield both

      start <- for {
        left <- vocabulary.product(q, vocabulary.zero).flatMap(vocabulary.sum(witness, _))
        right <- vocabulary.sum(head, tail)
        proved <- semiring.prove(left, right)
      } yield proved
      stepped <- vocabulary.underProduct(t, bezout).flatMap(vocabulary.underSum(head, _))
      finish <- for {
        left <- vocabulary.product(t, raised).flatMap(vocabulary.sum(head, _))
        right <- vocabulary.product(q, quotient).flatMap(vocabulary.sum(t, _))
        proved <- semiring.prove(left, right)
      } yield proved

      equation <- Conv.trans(start, stepped).flatMap(Conv.trans(_, finish))
      result <- vocabulary
        .fact(Modular.CongIntro)
        .flatMap(vocabulary.rules.specAll(_, List(q, witness, t, vocabulary.zero, quotient)))
        .flatMap(vocabulary.rules.mp(_, equation))
    } yield result


  /**
   * [[Gauss]], from Bezout, with one derivation used for both of its cases.
   *
   * The argument in one line: `a * z = b * u + 1` multiplied by `c` gives
   * `c * (a * z) = (b * c) * u + c`, whose left side is a multiple of `a` by construction and whose
   * first summand is one because `a` divides `b * c`. `Modular.DividesSummand` takes the second
   * summand out, and that summand is `c`.
   *
   * **Nothing is subtracted anywhere**, which is what makes it short. The textbook proof writes
   * `c = c * (a * z - b * u)` and needs the difference to be a natural; the additive form
   * `NUM_DIVIDES_SUMMAND` asks for is the same step without the question. The two Bezout cases
   * differ only in which side of the equation carries `a`, so they are one derivation called twice.
   */
  private def gaussLemma(
    vocabulary: Vocabulary,
    semiring: Semiring
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val a = Term.variable("a", numbers)
    val b = Term.variable("b", numbers)
    val c = Term.variable("c", numbers)

    for {
      one <- vocabulary.one
      gcd <- LogicError.lift(
        vocabulary.theory.constant(Modular.GcdName, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      greatest <- LogicError.lift(Term.appAll(gcd, List(a, b)))
      coprime <- LogicError.lift(Term.eq(greatest, one))
      notZeroA <- logic.mkNot(zeroOf(vocabulary, a))
      notZeroB <- logic.mkNot(zeroOf(vocabulary, b))
      guard <- logic.mkDisj(notZeroA, notZeroB)
      product <- vocabulary.product(b, c)
      dividesProduct <- LogicError.lift(Term.appAll(vocabulary.divides, List(a, product)))
      goal <- LogicError.lift(Term.appAll(vocabulary.divides, List(a, c)))

      assumedGuard <- LogicError.lift(Kernel.assume(guard))
      assumedCoprime <- LogicError.lift(Kernel.assume(coprime))
      assumedDivides <- LogicError.lift(Kernel.assume(dividesProduct))

      opened <- vocabulary
        .fact(Modular.Bezout)
        .flatMap(rules.specAll(_, List(a, b)))
        .flatMap(rules.mp(_, assumedGuard))
      rule <- Rewrite.Rule.of(logic, assumedCoprime)
      simplified <- Rewrite.inTheorem(Vector(rule), opened)

      found <- withTwoWitnesses(vocabulary, simplified, Set(a, b, c)) { (z, u, cases) =>
        for {
          split <- logic
            .destDisj(cases.conclusion)
            .toRight(NotOfForm("a disjunction", cases.conclusion))
          (throughA, throughB) = split

          // `a * z = b * u + 1`: the coefficient of `a` is `z` and the rest is `b * u`.
          first <- LogicError
            .lift(Kernel.assume(throughA))
            .flatMap(gaussCase(vocabulary, semiring, a, b, c, z, u, _, assumedDivides, goal,
              carriesA = true))

          // `b * z = a * u + 1`: the same with the two coefficients exchanged.
          second <- LogicError
            .lift(Kernel.assume(throughB))
            .flatMap(gaussCase(vocabulary, semiring, a, b, c, z, u, _, assumedDivides, goal,
              carriesA = false))

          settled <- rules.disjElim(cases, first, second)
        } yield settled
      }

      dischargedDivides <- rules.disch(dividesProduct, found)
      dischargedCoprime <- rules.disch(coprime, dischargedDivides)
      dischargedGuard <- rules.disch(guard, dischargedCoprime)
      general <- rules.genAll(dischargedGuard, List(a, b, c))
      result <- vocabulary.checked(Gauss, general)
    } yield result
  }

  /**
   * One Bezout case of [[Gauss]], and the two differ by which side carries the multiple of `a`.
   *
   * Case one is `a * z = b * u + 1`. Multiplied by `c` it reads `c * (a * z) = (b * c) * u + c`,
   * whose left side is `a * (c * z)` and whose first summand is a multiple of `b * c`. Case two is
   * `b * z = a * u + 1`, and multiplied by `c` it reads `c * (b * z) = a * (c * u) + c`, where the
   * left side is the multiple of `b * c` and the first summand is the multiple of `a`.
   *
   * So the shape is one and the **justifications swap**: in both cases `a` divides the whole and
   * divides the first summand, and `Modular.DividesSummand` takes `c` out. What differs is which
   * of the two facts comes from the premise `a | b * c` and which from the semiring.
   */
  private def gaussCase(
    vocabulary: Vocabulary,
    semiring: Semiring,
    a: Term,
    b: Term,
    c: Term,
    z: Term,
    u: Term,
    bezout: Kernel.Thm,
    dividesProduct: Kernel.Thm,
    goal: Term,
    carriesA: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      one <- vocabulary.one
      product <- vocabulary.product(b, c)

      // The whole and the first summand, named the way the case puts them.
      inner <- if (carriesA) vocabulary.product(a, z) else vocabulary.product(b, z)
      whole <- vocabulary.product(c, inner)
      tailFactor = if (carriesA) u else u
      tail <-
        if (carriesA) vocabulary.product(product, u)
        else vocabulary.product(c, u).flatMap(vocabulary.product(a, _))
      sum <- vocabulary.sum(tail, c)

      // `c * (a * z) = c * (b * u + 1)`, then the semiring puts the right side into `tail + c`.
      scaled <- vocabulary.underProduct(c, bezout)
      right <- Term
        .destEq(scaled.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", scaled.conclusion))
      shaped <- semiring.prove(right, sum)
      equation <- Conv.trans(scaled, shaped)

      // `a` divides the whole, and `a` divides the first summand. One of the two is the premise and
      // the other is arithmetic, and which is which is the whole of the difference.
      dividesWhole <-
        if (carriesA)
          for {
            multiplier <- vocabulary.product(c, z)
            asMultiple <- vocabulary.product(a, multiplier)
            grouped <- semiring.prove(whole, asMultiple)
            found <- vocabulary
              .fact(Modular.DividesIntro)
              .flatMap(rules.specAll(_, List(a, whole, multiplier)))
              .flatMap(rules.mp(_, grouped))
          } yield found
        else
          for {
            scaledProduct <- vocabulary.product(product, z)
            found <- vocabulary
              .fact(Modular.DividesMul)
              .flatMap(rules.specAll(_, List(a, product, z)))
              .flatMap(rules.mp(_, dividesProduct))
            regrouped <- semiring.prove(scaledProduct, whole)
            context <- LogicError.lift(Term.app(vocabulary.divides, a))
            carried <- vocabulary.carry(context, regrouped, found)
          } yield carried

      dividesTail <-
        if (carriesA)
          vocabulary
            .fact(Modular.DividesMul)
            .flatMap(rules.specAll(_, List(a, product, u)))
            .flatMap(rules.mp(_, dividesProduct))
        else
          for {
            multiplier <- vocabulary.product(c, u)
            asMultiple <- vocabulary.product(a, multiplier)
            grouped <- semiring.prove(tail, asMultiple)
            found <- vocabulary
              .fact(Modular.DividesIntro)
              .flatMap(rules.specAll(_, List(a, tail, multiplier)))
              .flatMap(rules.mp(_, grouped))
          } yield found

      context <- LogicError.lift(Term.app(vocabulary.divides, a))
      dividesSum <- vocabulary.carry(context, equation, dividesWhole)
      result <- vocabulary
        .fact(Modular.DividesSummand)
        .flatMap(rules.specAll(_, List(a, tail, c)))
        .flatMap(rules.mp(_, dividesTail))
        .flatMap(rules.mp(_, dividesSum))
      _ <-
        if (result.conclusion == goal) Right(())
        else Left(NotOfForm("what the case has to reach", result.conclusion))
    } yield result
  }


  /**
   * [[Bound]], by induction on the length with the sequence fixed.
   *
   * At zero the bound is zero and the claim is vacuous; at `SUC k` it is the old bound plus the new
   * entry, which works because nothing on `num` is negative. The step splits on
   * `Peano.BelowSuccessorCases`: below `k` the induction hypothesis bounds the entry and the bound
   * only grew, and at `k` the entry is a summand of its own bound.
   *
   * `Induct.proveBy` inducts on the **last** leading quantifier, so the statement is written
   * `!s n.` and not `!n s.`, and the sequence is fixed across the induction. That is right rather
   * than merely convenient: the bound for a longer stretch of the same sequence is what the step
   * builds, and a hypothesis quantified over sequences would be a stronger claim nobody needs.
   */
  private def boundedStretch(
    vocabulary: Vocabulary,
    driver: Induct
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- vocabulary.statement(Bound)
      proved <- driver.proveBy(
        statement,
        goal => boundAtZero(vocabulary, goal),
        step => boundAtSuccessor(vocabulary, step)
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(Bound, proved)
    } yield result

  /** `NUM_LE left right` from a witness and a proof that `left + witness = right`. */
  private def atMost(
    vocabulary: Vocabulary,
    left: Term,
    right: Term,
    witness: Term,
    evidence: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    for {
      definition <- vocabulary.peano.definition(Peano.NonStrictOrder)
      unfolded <- Conv.unfold(definition, List(left, right))
      body <- Term
        .destEq(unfolded.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", unfolded.conclusion))
      predicate <- vocabulary.logic
        .destExistsPredicate(body)
        .toRight(NotOfForm("an existential", body))
      witnessed <- rules.existsIntro(predicate, witness, evidence)
      back <- Conv.sym(unfolded)
      result <- LogicError.lift(Kernel.eqMp(back, witnessed))
    } yield result
  }

  /** `NUM_LE x (NUM_ADD x y)`, one step from what the order is defined as. */
  private def atMostSum(
    vocabulary: Vocabulary,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      sum <- vocabulary.sum(left, right)
      result <- atMost(vocabulary, left, sum, right, Conv.refl(sum))
    } yield result

  /** `NUM_LE y (NUM_ADD x y)`, the same with the summands the other way round. */
  private def atMostSumRight(
    vocabulary: Vocabulary,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      sum <- vocabulary.sum(left, right)
      swapped <- vocabulary.sum(right, left)
      commuted <- vocabulary
        .fact(Peano.AddCommutative)
        .flatMap(vocabulary.rules.specAll(_, List(right, left)))
      result <- atMost(vocabulary, right, sum, left, commuted)
    } yield result

  /** At zero the bound is zero and nothing is below zero to be bounded. */
  private def boundAtZero(vocabulary: Vocabulary, goal: Term): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    for {
      predicate <- logic.destExistsPredicate(goal).toRight(NotOfForm("an existential", goal))
      applied <- LogicError.lift(Term.app(predicate, vocabulary.zero))
      contraction <- Conv.betaRoot(applied)
      instance <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      stripped <- Logic.stripForall(instance)
      index <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", instance))
      vacuous <- vacuousBelowZero(vocabulary, stripped._2)
      general <- rules.gen(index, vacuous)
      result <- rules.existsIntro(predicate, vocabulary.zero, general)
    } yield result
  }

  /** At `SUC k` the bound is the old one plus the new entry, which is a bound because nothing is negative. */
  private def boundAtSuccessor(
    vocabulary: Vocabulary,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    for {
      inner <- logic
        .destExistsPredicate(step.hypothesis.conclusion)
        .toRight(NotOfForm("an existential", step.hypothesis.conclusion))
      previous = Conv.freshVariable(
        "M",
        vocabulary.numbers,
        Term.freeVariables(step.goal) + step.variable
      )
      applied <- LogicError.lift(Term.app(inner, previous))
      contraction <- Conv.betaRoot(applied)
      bounds <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      assumedBounds <- LogicError.lift(Kernel.assume(bounds))

      sequence <- sequenceOf(vocabulary, step.goal)
      atStep <- LogicError.lift(Term.app(sequence, step.variable))
      widened <- vocabulary.sum(previous, atStep)

      predicate <- logic
        .destExistsPredicate(step.goal)
        .toRight(NotOfForm("an existential", step.goal))
      appliedGoal <- LogicError.lift(Term.app(predicate, widened))
      goalContraction <- Conv.betaRoot(appliedGoal)
      goalBody <- Term
        .destEq(goalContraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", goalContraction.conclusion))
      strippedGoal <- Logic.stripForall(goalBody)
      index <- strippedGoal._1.headOption.toRight(NotOfForm("a claim about every index", goalBody))
      parts <- logic
        .destImp(strippedGoal._2)
        .toRight(NotOfForm("an implication", strippedGoal._2))
      (below, conclusion) = parts
      assumedBelow <- LogicError.lift(Kernel.assume(below))

      cases <- vocabulary
        .fact(Peano.BelowSuccessorCases)
        .flatMap(rules.specAll(_, List(step.variable, index)))
        .flatMap(rules.mp(_, assumedBelow))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (strictly, exactly) = split

      grew <- atMostSum(vocabulary, previous, atStep)

      // Below `k`: the hypothesis bounds the entry and the bound only grew.
      fromHypothesis <- for {
        assumed <- LogicError.lift(Kernel.assume(strictly))
        bounded <- rules.spec(index, assumedBounds).flatMap(rules.mp(_, assumed))
        entry <- LogicError.lift(Term.app(sequence, index))
        joined <- rules.conjIntro(bounded, grew)
        chained <- vocabulary
          .fact(Peano.Transitive)
          .flatMap(rules.specAll(_, List(entry, previous, widened)))
          .flatMap(rules.mp(_, joined))
      } yield chained

      // At `k`: the entry is a summand of its own bound.
      fromEquality <- for {
        assumed <- LogicError.lift(Kernel.assume(exactly))
        summand <- atMostSumRight(vocabulary, previous, atStep)

        // `s k <= M + s k` is what is proved and `s i <= M + s k` is what is wanted, so the
        // equation `i = k` is carried backwards into the entry. By congruence under a fixed
        // context rather than by rewriting, because `i` and `k` both occur elsewhere in the goal.
        entryAt <- Conv.sym(assumed).flatMap(Conv.apTerm(sequence, _))
        carried <- Conv
          .apTerm(vocabulary.atMost, entryAt)
          .flatMap(Conv.apThm(_, widened))
        result <- LogicError.lift(Kernel.eqMp(carried, summand))
      } yield result

      settled <- rules.disjElim(cases, fromHypothesis, fromEquality)
      _ <-
        if (settled.conclusion == conclusion) Right(())
        else Left(NotOfForm("what the step has to reach", settled.conclusion))
      discharged <- rules.disch(below, settled).flatMap(rules.gen(index, _))
      witnessed <- rules.existsIntro(predicate, widened, discharged)
      result <- rules.existsElim(step.hypothesis, previous, witnessed)
    } yield result
  }

  /** `NUM_LT i ZERO ==> anything`: nothing is below zero, and here the premise is that alone. */
  private def vacuousBelowZero(vocabulary: Vocabulary, goal: Term): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    for {
      parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
      (premise, consequent) = parts
      index <- premise match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a comparison", other))
      }
      never <- vocabulary.fact(Peano.NotBelowZero).flatMap(rules.spec(index, _))
      assumed <- LogicError.lift(Kernel.assume(premise))
      contradiction <- rules.notElim(never, assumed)
      anything <- rules.falsityElim(consequent, contradiction)
      result <- rules.disch(premise, anything)
    } yield result
  }

  /** The sequence the goal is about, read off the goal rather than rebuilt. */
  private def sequenceOf(vocabulary: Vocabulary, goal: Term): Either[LogicError, Term] = {
    def find(term: Term): Option[Term] = term match {
      case App(App(_, App(candidate, _)), _) if Term.typeOf(candidate) ==
        Type.fun(vocabulary.numbers, vocabulary.numbers) => Some(candidate)
      case App(fn, argument) => find(fn).orElse(find(argument))
      case Abs(_, body) => find(body)
      case _ => None
    }
    find(goal).toRight(NotOfForm("a claim about a sequence", goal))
  }


  /**
   * [[ModuliCoprime]]: two shifted multiples of `b` whose shifts differ by a divisor of `b`.
   *
   * The whole argument rests on one step used twice, [[dividesBothIsOne]]: anything that divides
   * `b` and divides `SUC ((i + 1) * b)` divides one. It is used first on `NUM_GCD d b`, to get the
   * coprimality Gauss asks for, and then on `d` itself once Gauss has put `d` into `j - i`. Writing
   * it once is not tidiness: the two uses are the same fact about the same modulus, and a reader
   * who sees it twice is entitled to ask whether they are.
   */
  private def moduliCoprime(
    vocabulary: Vocabulary,
    semiring: Semiring,
    gauss: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val b = Term.variable("b", numbers)
    val i = Term.variable("i", numbers)
    val j = Term.variable("j", numbers)

    for {
      one <- vocabulary.one
      gcd <- LogicError.lift(
        vocabulary.theory.constant(Modular.GcdName, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      subtraction <- LogicError.lift(
        vocabulary.theory.constant(Peano.Subtraction, Type.fun(numbers, Type.fun(numbers, numbers)))
      )

      below <- LogicError.lift(Term.appAll(vocabulary.below, List(i, j)))
      gap <- LogicError.lift(Term.appAll(subtraction, List(j, i)))
      gapDivides <- LogicError.lift(Term.appAll(vocabulary.divides, List(gap, b)))
      premise <- logic.mkConj(below, gapDivides)
      assumed <- LogicError.lift(Kernel.assume(premise))
      assumedBelow <- rules.conjElim1(assumed)
      assumedGap <- rules.conjElim2(assumed)

      lower <- modulus(vocabulary, i, b)
      upper <- modulus(vocabulary, j, b)

      // `NUM_GCD` of the two divides both, which needs them not both zero, and a successor is not.
      notZero <- vocabulary.peano.naturals.fact(Natural.SuccessorNotZero)
      lowerInside <- lower match {
        case App(_, inside) => Right(inside)
        case other => Left(NotOfForm("a successor", other))
      }
      lowerNotZero <- rules.spec(lowerInside, notZero)
      eitherNotZero <- LogicError
        .lift(Term.eq(upper, vocabulary.zero))
        .flatMap(logic.mkNot)
        .flatMap(rules.disjIntro1(_, lowerNotZero))

      greatest <- LogicError.lift(Term.appAll(gcd, List(lower, upper)))
      dividesLower <- vocabulary
        .fact(Modular.GcdDividesLeft)
        .flatMap(rules.specAll(_, List(lower, upper)))
        .flatMap(rules.mp(_, eitherNotZero))
      dividesUpper <- vocabulary
        .fact(Modular.GcdDividesRight)
        .flatMap(rules.specAll(_, List(lower, upper)))
        .flatMap(rules.mp(_, eitherNotZero))

      isOne <- commonDivisorIsOne(
        vocabulary, semiring, gauss, b, i, j, gap, greatest,
        dividesLower, dividesUpper, assumedBelow, assumedGap)

      discharged <- rules.disch(premise, isOne)
      general <- rules.genAll(discharged, List(b, i, j))
      result <- vocabulary.checked(ModuliCoprime, general)
    } yield result
  }

  /** `SUC ((n + 1) * b)`, the modulus the beta function reads at index `n`. */
  private def modulus(vocabulary: Vocabulary, index: Term, b: Term): Either[LogicError, Term] =
    for {
      successor <- LogicError.lift(Term.app(vocabulary.successor, index))
      scaled <- vocabulary.product(successor, b)
      shifted <- LogicError.lift(Term.app(vocabulary.successor, scaled))
    } yield shifted

  /**
   * A common divisor of the two moduli is one.
   *
   * `upper = lower + (j - i) * b`, so the divisor divides `(j - i) * b` by
   * `Modular.DividesSummand`. It is coprime to `b` by [[dividesBothIsOne]] applied to
   * `NUM_GCD d b`, which divides `b` and divides `lower` through `d`. Gauss then puts it into
   * `j - i`, which divides `b` by hypothesis, so it divides `b`; and [[dividesBothIsOne]] applied
   * to it now says it is one.
   */
  private def commonDivisorIsOne(
    vocabulary: Vocabulary,
    semiring: Semiring,
    gauss: Kernel.Thm,
    b: Term,
    i: Term,
    j: Term,
    gap: Term,
    divisor: Term,
    dividesLower: Kernel.Thm,
    dividesUpper: Kernel.Thm,
    below: Kernel.Thm,
    gapDividesB: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      lower <- modulus(vocabulary, i, b)
      step <- gapStep(vocabulary, semiring, b, i, j, gap, below)

      // `d | lower + (j - i) * b` and `d | lower` leave `d | (j - i) * b`.
      scaled <- vocabulary.product(gap, b)
      widened <- vocabulary.sum(lower, scaled)
      context <- LogicError.lift(Term.app(vocabulary.divides, divisor))
      acrossStep <- vocabulary.carry(context, step, dividesUpper)
      dividesGapTimesB <- vocabulary
        .fact(Modular.DividesSummand)
        .flatMap(rules.specAll(_, List(divisor, lower, scaled)))
        .flatMap(rules.mp(_, dividesLower))
        .flatMap(rules.mp(_, acrossStep))

      // Coprime to `b`: the greatest common divisor of `d` and `b` divides both, so it divides
      // `lower` through `d`, and one step says it is one.
      coprime <- coprimeToBase(vocabulary, semiring, b, i, divisor, dividesLower)

      // Gauss wants the product with `b` on the left.
      swapped <- vocabulary.product(b, gap)
      commuted <- semiring.prove(scaled, swapped)
      dividesSwapped <- vocabulary.carry(context, commuted, dividesGapTimesB)
      dividesGap <- rules
        .specAll(gauss, List(divisor, b, gap))
        .flatMap(implication =>
          notBothZero(vocabulary, divisor, b, dividesLower).flatMap(rules.mp(implication, _))
        )
        .flatMap(rules.mp(_, coprime))
        .flatMap(rules.mp(_, dividesSwapped))

      dividesB <- vocabulary
        .fact(Modular.DividesTrans)
        .flatMap(rules.specAll(_, List(divisor, gap, b)))
        .flatMap(rules.mp(_, dividesGap))
        .flatMap(rules.mp(_, gapDividesB))

      result <- dividesBothIsOne(vocabulary, semiring, b, i, divisor, dividesB, dividesLower)
    } yield result
  }

  /**
   * `~(d = ZERO) \\/ ~(b = ZERO)`, which Gauss and the greatest common divisor both ask for.
   *
   * The left disjunct is the one that holds, and it comes from the divisor's own premise: `d`
   * divides a **successor**, so `d` is not zero, because zero divides only zero and a successor is
   * not zero. Nothing is assumed about `b`, which is right: `b` may be zero and the lemma still
   * holds, since then both moduli are `SUC ZERO`.
   *
   * It was a stub returning a reflexivity for one compile, which typechecked and would have been a
   * theorem about the wrong thing. What caught it was not the compiler.
   */
  private def notBothZero(
    vocabulary: Vocabulary,
    divisor: Term,
    b: Term,
    dividesSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      dividend <- dividesSuccessor.conclusion match {
        case App(App(_, _), right) => Right(right)
        case other => Left(NotOfForm("a divisibility", other))
      }
      inside <- dividend match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("a successor", other))
      }
      never <- vocabulary.peano.naturals
        .fact(Natural.SuccessorNotZero)
        .flatMap(rules.spec(inside, _))
      notZeroDivisor <- dividesNotZero(vocabulary, divisor, dividend, dividesSuccessor, never)
      bIsZero <- LogicError.lift(Term.eq(b, vocabulary.zero)).flatMap(logic.mkNot)
      result <- rules.disjIntro1(bIsZero, notZeroDivisor)
    } yield result
  }

  /** `SUC ((j + 1) * b) = SUC ((i + 1) * b) + (j - i) * b`, which is where `NUM_SUB_ADD` is spent. */
  private def gapStep(
    vocabulary: Vocabulary,
    semiring: Semiring,
    b: Term,
    i: Term,
    j: Term,
    gap: Term,
    below: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      atMost <- vocabulary
        .fact(Peano.AtMostFromBelow)
        .flatMap(rules.specAll(_, List(i, j)))
        .flatMap(rules.mp(_, below))
      restored <- vocabulary
        .fact(Peano.MinusThenPlus)
        .flatMap(rules.specAll(_, List(j, i)))
        .flatMap(rules.mp(_, atMost))

      lower <- modulus(vocabulary, i, b)
      upper <- modulus(vocabulary, j, b)
      scaled <- vocabulary.product(gap, b)
      widened <- vocabulary.sum(lower, scaled)

      // `j` becomes `(j - i) + i` inside the upper modulus, and the rest is the semiring plus the
      // one lemma that takes a successor out of a sum.
      back <- Conv.sym(restored)
      inside <- Conv
        .apTerm(vocabulary.successor, back)
        .flatMap(equation => Conv.apTerm(vocabulary.times, equation))
        .flatMap(Conv.apThm(_, b))
        .flatMap(Conv.apTerm(vocabulary.successor, _))

      reached <- Term
        .destEq(inside.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", inside.conclusion))
      opened <- successorOfSum(vocabulary, semiring, reached, widened)
      result <- Conv.trans(inside, opened)
    } yield result
  }

  /** `SUC (((j - i) + i + 1) * b) = SUC ((i + 1) * b) + (j - i) * b`, the semiring under a successor. */
  private def successorOfSum(
    vocabulary: Vocabulary,
    semiring: Semiring,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      inside <- left match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("a successor", other))
      }
      tail <- right match {
        case App(App(_, _), second) => Right(second)
        case other => Left(NotOfForm("a sum", other))
      }
      head <- right match {
        case App(App(_, first), _) => Right(first)
        case other => Left(NotOfForm("a sum", other))
      }
      headInside <- head match {
        case App(_, argument) => Right(argument)
        case other => Left(NotOfForm("a successor", other))
      }
      regrouped <- vocabulary.sum(headInside, tail)
      byTheSemiring <- semiring.prove(inside, regrouped)
      carried <- Conv.apTerm(vocabulary.successor, byTheSemiring)
      pulled <- vocabulary
        .fact(Peano.SuccessorPlus)
        .flatMap(rules.specAll(_, List(headInside, tail)))
        .flatMap(Conv.sym)
      result <- Conv.trans(carried, pulled)
    } yield result
  }

  /**
   * `NUM_GCD d b = SUC ZERO`, from `d` dividing the lower modulus.
   *
   * The greatest common divisor of `d` and `b` divides `b` and divides `d`, so it divides the lower
   * modulus through `d`, and [[dividesBothIsOne]] closes it.
   */
  private def coprimeToBase(
    vocabulary: Vocabulary,
    semiring: Semiring,
    b: Term,
    i: Term,
    divisor: Term,
    dividesLower: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      lower <- modulus(vocabulary, i, b)
      guard <- notBothZero(vocabulary, divisor, b, dividesLower)
      gcdDividesDivisor <- vocabulary
        .fact(Modular.GcdDividesLeft)
        .flatMap(rules.specAll(_, List(divisor, b)))
        .flatMap(rules.mp(_, guard))
      gcdDividesB <- vocabulary
        .fact(Modular.GcdDividesRight)
        .flatMap(rules.specAll(_, List(divisor, b)))
        .flatMap(rules.mp(_, guard))
      gcdConstant <- LogicError.lift(
        vocabulary.theory.constant(
          Modular.GcdName,
          Type.fun(vocabulary.numbers, Type.fun(vocabulary.numbers, vocabulary.numbers))
        )
      )
      greatest <- LogicError.lift(Term.appAll(gcdConstant, List(divisor, b)))
      through <- vocabulary
        .fact(Modular.DividesTrans)
        .flatMap(rules.specAll(_, List(greatest, divisor, lower)))
        .flatMap(rules.mp(_, gcdDividesDivisor))
        .flatMap(rules.mp(_, dividesLower))
      result <- dividesBothIsOne(vocabulary, semiring, b, i, greatest, gcdDividesB, through)
    } yield result
  }

  /**
   * Anything dividing `b` and the lower modulus is one.
   *
   * `SUC ((i + 1) * b)` is `(i + 1) * b + SUC ZERO`, and a divisor of `b` divides the first
   * summand, so `Modular.DividesSummand` leaves it dividing one and `Modular.DividesOne` makes
   * that an equation. Used twice, on the greatest common divisor and on the divisor itself, which
   * is the whole shape of the coprimality argument.
   */
  private def dividesBothIsOne(
    vocabulary: Vocabulary,
    semiring: Semiring,
    b: Term,
    i: Term,
    divisor: Term,
    dividesB: Kernel.Thm,
    dividesLower: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      one <- vocabulary.one
      lower <- modulus(vocabulary, i, b)
      successorOfI <- LogicError.lift(Term.app(vocabulary.successor, i))
      scaled <- vocabulary.product(successorOfI, b)
      asSum <- vocabulary.sum(scaled, one)

      // `SUC x = x + SUC ZERO`, and **not** by the semiring. A successor added to something is an
      // atom there, deliberately, so `Semiring` refuses this and is right to: it is the boundary
      // that file draws and the refusal arrived here as one. Two named lemmas instead.
      shape <- successorAsSum(vocabulary, scaled)

      context <- LogicError.lift(Term.app(vocabulary.divides, divisor))
      dividesScaled <- vocabulary
        .fact(Modular.DividesMul)
        .flatMap(rules.specAll(_, List(divisor, b, successorOfI)))
        .flatMap(rules.mp(_, dividesB))
      commuted <- vocabulary.product(b, successorOfI).flatMap(semiring.prove(_, scaled))
      dividesFirst <- vocabulary.carry(context, commuted, dividesScaled)

      dividesSum <- vocabulary.carry(context, shape, dividesLower)
      dividesUnit <- vocabulary
        .fact(Modular.DividesSummand)
        .flatMap(rules.specAll(_, List(divisor, scaled, one)))
        .flatMap(rules.mp(_, dividesFirst))
        .flatMap(rules.mp(_, dividesSum))
      result <- vocabulary.fact(Modular.DividesOne).flatMap(rules.spec(divisor, _)).flatMap(rules.mp(_, dividesUnit))
    } yield result
  }


  /**
   * `|- SUC x = NUM_ADD x (SUC ZERO)`.
   *
   * Two steps and neither is the semiring: `Peano.AddAtSuccessor` turns `x + SUC ZERO` into
   * `SUC (x + ZERO)` and `Peano.AddAtZero` removes the zero. `Semiring` cannot do this and the
   * refusal it gives is correct rather than a gap, because a successor added to something is an
   * atom there on purpose: opening it would turn every written bound in a goal into a sum.
   */
  private def successorAsSum(
    vocabulary: Vocabulary,
    subject: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      one <- vocabulary.one
      stepped <- vocabulary
        .fact(Peano.AddAtSuccessor)
        .flatMap(rules.specAll(_, List(subject, vocabulary.zero)))
      atZero <- vocabulary.fact(Peano.AddAtZero).flatMap(rules.spec(subject, _))
      inside <- Conv.apTerm(vocabulary.successor, atZero)
      forward <- Conv.trans(stepped, inside)
      result <- Conv.sym(forward)
    } yield result
  }


  /**
   * [[ProductDivides]], by induction on the length with the index fixed.
   *
   * Two cases at `SUC k` and they use the product's recurrence from opposite ends. Below `k` the
   * hypothesis gives the factor dividing the shorter product, and `Modular.DividesMul` carries that
   * through the extra factor; at `k` the new factor divides itself and the same lemma carries it
   * through the shorter product, which then has to be commuted because `NUM_PROD` puts the new
   * factor on the right and divisibility wants it on the left.
   */
  private def eachFactorDivides(
    vocabulary: Vocabulary,
    driver: Induct,
    semiring: Semiring,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- vocabulary.statement(ProductDivides)
      proved <- driver.proveBy(
        statement,
        goal => vacuousBelowZero(vocabulary, goal),
        step => factorStep(vocabulary, semiring, atSuccessor, step)
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(ProductDivides, proved)
    } yield result

  /** The step of [[ProductDivides]]: below the new index, or at it. */
  private def factorStep(
    vocabulary: Vocabulary,
    semiring: Semiring,
    atSuccessor: Kernel.Thm,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
      (below, conclusion) = parts
      assumedBelow <- LogicError.lift(Kernel.assume(below))
      index <- below match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a comparison", other))
      }
      sequence <- conclusion match {
        case App(App(_, App(candidate, _)), _) => Right(candidate)
        case other => Left(NotOfForm("a divisibility naming the sequence", other))
      }

      recurrence <- rules.specAll(atSuccessor, List(sequence, step.variable))
      shorter <- Term
        .destEq(recurrence.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", recurrence.conclusion))
      product <- Term
        .destEq(recurrence.conclusion)
        .map(_._1)
        .toRight(NotOfForm("an equation", recurrence.conclusion))
      head <- shorter match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a product", other))
      }
      newest <- shorter match {
        case App(App(_, _), right) => Right(right)
        case other => Left(NotOfForm("a product", other))
      }
      entry <- LogicError.lift(Term.app(sequence, index))
      context <- LogicError.lift(Term.app(vocabulary.divides, entry))

      cases <- vocabulary
        .fact(Peano.BelowSuccessorCases)
        .flatMap(rules.specAll(_, List(step.variable, index)))
        .flatMap(rules.mp(_, assumedBelow))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (strictly, exactly) = split

      fromHypothesis <- for {
        assumed <- LogicError.lift(Kernel.assume(strictly))
        shorterDivides <- rules.mp(step.hypothesis, assumed)
        carried <- vocabulary
          .fact(Modular.DividesMul)
          .flatMap(rules.specAll(_, List(entry, head, newest)))
          .flatMap(rules.mp(_, shorterDivides))
        back <- Conv.sym(recurrence)
        result <- vocabulary.carry(context, back, carried)
      } yield result

      fromEquality <- for {
        assumed <- LogicError.lift(Kernel.assume(exactly))
        atStep <- LogicError.lift(Term.app(sequence, step.variable))
        reflexive <- vocabulary.fact(Modular.DividesRefl).flatMap(rules.spec(atStep, _))
        swapped <- vocabulary.product(atStep, head)
        scaled <- vocabulary
          .fact(Modular.DividesMul)
          .flatMap(rules.specAll(_, List(atStep, atStep, head)))
          .flatMap(rules.mp(_, reflexive))
        commuted <- semiring.prove(swapped, shorter)
        atStepContext <- LogicError.lift(Term.app(vocabulary.divides, atStep))
        asProduct <- vocabulary.carry(atStepContext, commuted, scaled)
        back <- Conv.sym(recurrence)
        asWhole <- vocabulary.carry(atStepContext, back, asProduct)

        // `i = k`, so what has been proved about `m k` is what was wanted about `m i`.
        entryAt <- Conv.sym(assumed).flatMap(Conv.apTerm(sequence, _))
        result <- Conv
          .apTerm(vocabulary.divides, entryAt)
          .flatMap(Conv.apThm(_, product))
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, asWhole)))
      } yield result

      settled <- rules.disjElim(cases, fromHypothesis, fromEquality)
      result <- rules.disch(below, settled)
    } yield result
  }

  /**
   * [[ProductCongruent]], by induction on the length.
   *
   * The base is the empty product read at both families, which is `SUC ZERO` either way and needs
   * nothing of the agreement. The step spends the agreement twice and at different widths: below
   * `k` it is what the induction hypothesis asks for, and at `k` it is the equation between the two
   * new factors, so the recurrence's two halves are carried across by one congruence each.
   */
  private def productsOfAgreeingFamilies(
    vocabulary: Vocabulary,
    driver: Induct,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- vocabulary.statement(ProductCongruent)
      proved <- driver.proveBy(
        statement,
        goal => agreementBase(vocabulary, atZero, goal),
        step => agreementStep(vocabulary, atSuccessor, step)
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(ProductCongruent, proved)
    } yield result

  /** The family a `NUM_PROD` application is about, read off the application. */
  private def familyOf(term: Term): Either[LogicError, Term] = term match {
    case App(App(_, family), _) => Right(family)
    case other => Left(NotOfForm("a product over a family", other))
  }

  /** The base of [[ProductCongruent]]: both empty products are one, whatever the families are. */
  private def agreementBase(
    vocabulary: Vocabulary,
    atZero: Kernel.Thm,
    goal: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    for {
      parts <- vocabulary.logic.destImp(goal).toRight(NotOfForm("an implication", goal))
      (premise, equation) = parts
      sides <- Term.destEq(equation).toRight(NotOfForm("an equation", equation))
      first <- familyOf(sides._1)
      second <- familyOf(sides._2)
      left <- rules.spec(first, atZero)
      right <- rules.spec(second, atZero)
      both <- Conv.sym(right).flatMap(Conv.trans(left, _))
      result <- rules.disch(premise, both)
    } yield result
  }

  /** The step of [[ProductCongruent]]: the shorter products agree and so do the new factors. */
  private def agreementStep(
    vocabulary: Vocabulary,
    atSuccessor: Kernel.Thm,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    for {
      parts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
      (premise, equation) = parts
      sides <- Term.destEq(equation).toRight(NotOfForm("an equation", equation))
      first <- familyOf(sides._1)
      second <- familyOf(sides._2)
      agreement <- LogicError.lift(Kernel.assume(premise))

      successor <- LogicError.lift(Term.app(vocabulary.successor, step.variable))
      belowSuccessor <- vocabulary
        .fact(Peano.BelowSuccessor)
        .flatMap(rules.spec(step.variable, _))

      // The agreement below `k`, which is the hypothesis's own premise.
      index = Conv.freshVariable(
        "i", vocabulary.numbers, Term.freeVariables(step.goal) + step.variable)
      shorter <- LogicError.lift(Term.appAll(vocabulary.below, List(index, step.variable)))
      assumedShorter <- LogicError.lift(Kernel.assume(shorter))
      carried <- vocabulary
        .fact(Peano.StrictTransitive)
        .flatMap(rules.specAll(_, List(index, step.variable, successor)))
        .flatMap(implication =>
          rules.conjIntro(assumedShorter, belowSuccessor).flatMap(rules.mp(implication, _)))
      here <- rules.spec(index, agreement).flatMap(rules.mp(_, carried))
      restricted <- rules.disch(shorter, here).flatMap(rules.gen(index, _))
      shorterProducts <- rules.mp(step.hypothesis, restricted)

      newest <- rules.spec(step.variable, agreement).flatMap(rules.mp(_, belowSuccessor))
      factors <- Conv
        .apTerm(vocabulary.times, shorterProducts)
        .flatMap(scaled => LogicError.lift(Kernel.mkComb(scaled, newest)))

      leftRecurrence <- rules.specAll(atSuccessor, List(first, step.variable))
      rightRecurrence <- rules.specAll(atSuccessor, List(second, step.variable))
      reached <- Conv
        .sym(rightRecurrence)
        .flatMap(Conv.trans(factors, _))
        .flatMap(Conv.trans(leftRecurrence, _))
      result <- rules.disch(premise, reached)
    } yield result
  }

  /**
   * [[ProductPositive]], by induction on the length.
   *
   * The empty product is `SUC ZERO` and positive because it is a successor, which is the base and
   * is the reason the empty product is one rather than zero. At `SUC k` the hypothesis wants its
   * premise restricted to indices below `k`, which `Peano.BelowSuccessor` and transitivity supply,
   * and `Peano.MulPositive` puts the two positives together.
   */
  private def productOfPositives(
    vocabulary: Vocabulary,
    driver: Induct,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- vocabulary.statement(ProductPositive)
      proved <- driver.proveBy(
        statement,
        goal => positiveAtZero(vocabulary, atZero, goal),
        step => positiveStep(vocabulary, atSuccessor, step)
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(ProductPositive, proved)
    } yield result

  /** The empty product is one, and one is a successor. */
  private def positiveAtZero(
    vocabulary: Vocabulary,
    atZero: Kernel.Thm,
    goal: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
      (premise, conclusion) = parts
      sequence <- conclusion match {
        case App(App(_, _), App(App(_, candidate), _)) => Right(candidate)
        case other => Left(NotOfForm("a claim about a product", other))
      }
      recurrence <- rules.spec(sequence, atZero)
      positive <- vocabulary.fact(Peano.SuccessorPositive).flatMap(rules.spec(vocabulary.zero, _))
      belowZero <- LogicError.lift(Term.app(vocabulary.below, vocabulary.zero))
      back <- Conv.sym(recurrence)
      carried <- Conv.apTerm(belowZero, back)
      reached <- LogicError.lift(Kernel.eqMp(carried, positive))
      result <- rules.disch(premise, reached)
    } yield result
  }

  /** The step of [[ProductPositive]]: the shorter product and the new factor are both positive. */
  private def positiveStep(
    vocabulary: Vocabulary,
    atSuccessor: Kernel.Thm,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
      (premise, conclusion) = parts
      assumed <- LogicError.lift(Kernel.assume(premise))
      sequence <- conclusion match {
        case App(App(_, _), App(App(_, candidate), _)) => Right(candidate)
        case other => Left(NotOfForm("a claim about a product", other))
      }

      // The hypothesis wants its premise at indices below `k`, which the goal's gives through
      // `i < k ==> i < SUC k`.
      innerParts <- logic
        .destImp(step.hypothesis.conclusion)
        .toRight(NotOfForm("an implication", step.hypothesis.conclusion))
      innerPremise = innerParts._1
      stripped <- Logic.stripForall(innerPremise)
      index <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", innerPremise))
      innerBody <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (belowK, positiveAt) = innerBody
      assumedBelowK <- LogicError.lift(Kernel.assume(belowK))
      reaches <- vocabulary.fact(Peano.BelowSuccessor).flatMap(rules.spec(step.variable, _))
      belowSuccessor <- rules
        .conjIntro(assumedBelowK, reaches)
        .flatMap(pair =>
          vocabulary
            .fact(Peano.StrictTransitive)
            .flatMap(rules.specAll(_, List(index, step.variable, Term.app(vocabulary.successor, step.variable).getOrElse(step.variable))))
            .flatMap(rules.mp(_, pair))
        )
      positiveThere <- rules.spec(index, assumed).flatMap(rules.mp(_, belowSuccessor))
      restricted <- rules.disch(belowK, positiveThere).flatMap(rules.gen(index, _))
      shorterPositive <- rules.mp(step.hypothesis, restricted)

      // The new factor is positive, at `k`, which is below its own successor.
      atStep <- LogicError.lift(Term.app(sequence, step.variable))
      newestPositive <- rules.spec(step.variable, assumed).flatMap(rules.mp(_, reaches))

      recurrence <- rules.specAll(atSuccessor, List(sequence, step.variable))
      shorter <- Term
        .destEq(recurrence.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", recurrence.conclusion))
      head <- shorter match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a product", other))
      }
      together <- vocabulary
        .fact(Peano.MulPositive)
        .flatMap(rules.specAll(_, List(head, atStep)))
        .flatMap(rules.mp(_, shorterPositive))
        .flatMap(rules.mp(_, newestPositive))

      belowZero <- LogicError.lift(Term.app(vocabulary.below, vocabulary.zero))
      back <- Conv.sym(recurrence)
      carried <- Conv.apTerm(belowZero, back)
      reached <- LogicError.lift(Kernel.eqMp(carried, together))
      result <- rules.disch(premise, reached)
    } yield result
  }

  /** The `NUM_GCD` of this signature, which the coprimality derivations below need as a term. */
  private def greatestCommonDivisor(vocabulary: Vocabulary): Either[LogicError, Term] =
    LogicError.lift(
      vocabulary.theory.constant(
        Modular.GcdName,
        Type.fun(vocabulary.numbers, Type.fun(vocabulary.numbers, vocabulary.numbers))
      )
    )

  /** The `NUM_CONG` of this signature, the same way. */
  private def congruenceRelation(vocabulary: Vocabulary): Either[LogicError, Term] =
    LogicError.lift(
      vocabulary.theory.constant(
        Modular.CongruenceName,
        Type.fun(
          vocabulary.numbers,
          Type.fun(vocabulary.numbers, Type.fun(vocabulary.numbers, Type.Bool))
        )
      )
    )

  /** The `NUM_PROD` of this signature, which the family theorems build their modulus from. */
  private def productOverAFamily(vocabulary: Vocabulary): Either[LogicError, Term] =
    LogicError.lift(
      vocabulary.theory.constant(
        ProductName,
        Type.fun(
          Type.fun(vocabulary.numbers, vocabulary.numbers),
          Type.fun(vocabulary.numbers, vocabulary.numbers)
        )
      )
    )

  /**
   * `~(d = ZERO)` from `d | n` and `~(n = ZERO)`.
   *
   * Zero divides only zero, so a divisor of something that does not vanish cannot be zero. Used
   * wherever a guard of the form "not both zero" has to be discharged on the left, which is every
   * place the greatest common divisor of a term is itself put into another one.
   */
  private def dividesNotZero(
    vocabulary: Vocabulary,
    divisor: Term,
    dividend: Term,
    divides: Kernel.Thm,
    dividendNotZero: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val isZero = zeroOf(vocabulary, divisor)

    for {
      assumed <- LogicError.lift(Kernel.assume(isZero))
      carried <- Conv.apTerm(vocabulary.divides, assumed).flatMap(Conv.apThm(_, dividend))
      byZero <- LogicError.lift(Kernel.eqMp(carried, divides))
      collapsed <- vocabulary.fact(Modular.ZeroDivides).flatMap(rules.spec(dividend, _))
      absurd <- LogicError.lift(Kernel.eqMp(collapsed, byZero))
      contradiction <- rules.notElim(dividendNotZero, absurd)
      result <- rules.notIntro(isZero, contradiction)
    } yield result
  }

  /**
   * `d = SUC ZERO` from `d | x`, `d | y` and `NUM_GCD x y = SUC ZERO`.
   *
   * `Modular.GcdDivides` is what makes this two steps rather than an argument: a common divisor
   * divides the greatest one, and here the greatest one is one. It is [[dividesBothIsOne]]'s
   * statement over an arbitrary pair rather than over the beta function's own modulus, and the two
   * are not merged because that one proves its coprimality inline from the shape of the modulus.
   */
  private def dividesBothCoprime(
    vocabulary: Vocabulary,
    divisor: Term,
    left: Term,
    right: Term,
    guard: Kernel.Thm,
    dividesLeft: Kernel.Thm,
    dividesRight: Kernel.Thm,
    coprime: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      pair <- rules.conjIntro(dividesLeft, dividesRight)
      dividesGreatest <- vocabulary
        .fact(Modular.GcdDivides)
        .flatMap(rules.specAll(_, List(left, right, divisor)))
        .flatMap(rules.mp(_, guard))
        .flatMap(rules.mp(_, pair))
      context <- LogicError.lift(Term.app(vocabulary.divides, divisor))
      dividesUnit <- vocabulary.carry(context, coprime, dividesGreatest)
      result <- vocabulary
        .fact(Modular.DividesOne)
        .flatMap(rules.spec(divisor, _))
        .flatMap(rules.mp(_, dividesUnit))
    } yield result
  }

  /**
   * [[CoprimeToProduct]], which is [[Gauss]] spent on the thing Gauss exists for.
   *
   * Let `d` be `NUM_GCD (a * b) c`. It divides `a * b` and it divides `c`, and it is not zero
   * because `c` is not. `NUM_GCD d a` divides `a`, and divides `c` through `d`, so it divides
   * `NUM_GCD a c` and the first hypothesis makes it one: `d` is coprime to `a`. Gauss then puts `d`
   * into `b`, and the same two steps run against the second hypothesis make `d` itself one.
   *
   * The guard is discharged five times from one fact, `~(c = ZERO)`, and that is the whole reason
   * `NUM_LT ZERO c` is in the statement rather than something weaker.
   */
  private def coprimeToProduct(
    vocabulary: Vocabulary,
    gauss: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules
    val numbers = vocabulary.numbers
    val a = Term.variable("a", numbers)
    val b = Term.variable("b", numbers)
    val c = Term.variable("c", numbers)

    for {
      one <- vocabulary.one
      gcd <- greatestCommonDivisor(vocabulary)

      positive <- LogicError.lift(Term.appAll(vocabulary.below, List(vocabulary.zero, c)))
      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      notZeroC <- notZero(vocabulary, assumedPositive, c)

      greatestWithA <- LogicError.lift(Term.appAll(gcd, List(a, c)))
      coprimeA <- LogicError.lift(Term.eq(greatestWithA, one))
      assumedA <- LogicError.lift(Kernel.assume(coprimeA))
      greatestWithB <- LogicError.lift(Term.appAll(gcd, List(b, c)))
      coprimeB <- LogicError.lift(Term.eq(greatestWithB, one))
      assumedB <- LogicError.lift(Kernel.assume(coprimeB))

      product <- vocabulary.product(a, b)
      divisor <- LogicError.lift(Term.appAll(gcd, List(product, c)))

      guardProduct <- logic
        .mkNot(zeroOf(vocabulary, product))
        .flatMap(rules.disjIntro2(_, notZeroC))
      guardA <- logic.mkNot(zeroOf(vocabulary, a)).flatMap(rules.disjIntro2(_, notZeroC))
      guardB <- logic.mkNot(zeroOf(vocabulary, b)).flatMap(rules.disjIntro2(_, notZeroC))

      dividesProduct <- vocabulary
        .fact(Modular.GcdDividesLeft)
        .flatMap(rules.specAll(_, List(product, c)))
        .flatMap(rules.mp(_, guardProduct))
      dividesC <- vocabulary
        .fact(Modular.GcdDividesRight)
        .flatMap(rules.specAll(_, List(product, c)))
        .flatMap(rules.mp(_, guardProduct))

      notZeroDivisor <- dividesNotZero(vocabulary, divisor, c, dividesC, notZeroC)
      guardDivisor <- logic
        .mkNot(zeroOf(vocabulary, a))
        .flatMap(rules.disjIntro1(_, notZeroDivisor))

      inner <- LogicError.lift(Term.appAll(gcd, List(divisor, a)))
      innerDividesDivisor <- vocabulary
        .fact(Modular.GcdDividesLeft)
        .flatMap(rules.specAll(_, List(divisor, a)))
        .flatMap(rules.mp(_, guardDivisor))
      innerDividesA <- vocabulary
        .fact(Modular.GcdDividesRight)
        .flatMap(rules.specAll(_, List(divisor, a)))
        .flatMap(rules.mp(_, guardDivisor))
      innerDividesC <- vocabulary
        .fact(Modular.DividesTrans)
        .flatMap(rules.specAll(_, List(inner, divisor, c)))
        .flatMap(rules.mp(_, innerDividesDivisor))
        .flatMap(rules.mp(_, dividesC))
      innerIsOne <- dividesBothCoprime(
        vocabulary, inner, a, c, guardA, innerDividesA, innerDividesC, assumedA)

      dividesB <- rules
        .specAll(gauss, List(divisor, a, b))
        .flatMap(rules.mp(_, guardDivisor))
        .flatMap(rules.mp(_, innerIsOne))
        .flatMap(rules.mp(_, dividesProduct))

      isOne <- dividesBothCoprime(
        vocabulary, divisor, b, c, guardB, dividesB, dividesC, assumedB)

      dischargedB <- rules.disch(coprimeB, isOne)
      dischargedA <- rules.disch(coprimeA, dischargedB)
      discharged <- rules.disch(positive, dischargedA)
      general <- rules.genAll(discharged, List(a, b, c))
      result <- vocabulary.checked(CoprimeToProduct, general)
    } yield result
  }

  /**
   * `!i. NUM_LT i k ==> P i` from `!i. NUM_LT i (SUC k) ==> P i`.
   *
   * What every step of an induction over a length does to its own premise before the hypothesis
   * will take it. Written once here rather than four times inline, which is how many places in this
   * file wanted it by the time the Chinese remainder theorem landed.
   */
  private def restrictBelow(
    vocabulary: Vocabulary,
    family: Kernel.Thm,
    k: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      stripped <- Logic.stripForall(family.conclusion)
      index <- stripped._1.headOption
        .toRight(NotOfForm("a claim about every index", family.conclusion))
      // Checked and discarded: what this reads off is the index, and the shape of the body is
      // asserted here so a family of the wrong form is a refusal. `Rules.mp` below would not
      // refuse it, for the reason `ModularSpec` records: it leaves the antecedent standing as a
      // hypothesis and returns a theorem that looks right.
      _ <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      successor <- LogicError.lift(Term.app(vocabulary.successor, k))
      below <- LogicError.lift(Term.appAll(vocabulary.below, List(index, k)))
      assumed <- LogicError.lift(Kernel.assume(below))
      reaches <- vocabulary.fact(Peano.BelowSuccessor).flatMap(rules.spec(k, _))
      further <- rules
        .conjIntro(assumed, reaches)
        .flatMap(pair =>
          vocabulary
            .fact(Peano.StrictTransitive)
            .flatMap(rules.specAll(_, List(index, k, successor)))
            .flatMap(rules.mp(_, pair))
        )
      there <- rules.spec(index, family).flatMap(rules.mp(_, further))
      result <- rules.disch(below, there).flatMap(rules.gen(index, _))
    } yield result
  }

  /** `~(i = k)` from `NUM_LT i k`, which the pairwise premise asks for and the order does not give. */
  private def belowIsNotEqual(
    vocabulary: Vocabulary,
    lower: Term,
    upper: Term,
    below: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      equal <- LogicError.lift(Term.eq(lower, upper))
      assumed <- LogicError.lift(Kernel.assume(equal))
      carried <- Conv.apTerm(vocabulary.below, assumed).flatMap(Conv.apThm(_, upper))
      absurdly <- LogicError.lift(Kernel.eqMp(carried, below))
      never <- vocabulary.fact(Peano.StrictIrreflexive).flatMap(rules.spec(upper, _))
      contradiction <- rules.notElim(never, absurdly)
      result <- rules.notIntro(equal, contradiction)
    } yield result
  }

  /** [[CoprimeToFamily]], by induction on the length with [[CoprimeToProduct]] as the step. */
  private def coprimeToFamily(
    vocabulary: Vocabulary,
    driver: Induct,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm,
    forProduct: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- vocabulary.statement(CoprimeToFamily)
      proved <- driver.proveBy(
        statement,
        goal => coprimeAtZero(vocabulary, atZero, goal),
        step => coprimeAtSuccessor(vocabulary, atSuccessor, forProduct, step)
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(CoprimeToFamily, proved)
    } yield result

  /** The empty product is one, and `NUM_GCD (SUC ZERO) c` divides one, so it is one. */
  private def coprimeAtZero(
    vocabulary: Vocabulary,
    atZero: Kernel.Thm,
    goal: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
      (positive, rest) = parts
      inner <- logic.destImp(rest).toRight(NotOfForm("an implication", rest))
      (family, conclusion) = inner
      subject <- Term.destEq(conclusion).map(_._1).toRight(NotOfForm("an equation", conclusion))
      pieces <- subject match {
        case App(App(_, App(App(_, sequence), _)), modulus) => Right((sequence, modulus))
        case other => Left(NotOfForm("a greatest common divisor of a product", other))
      }
      (sequence, modulus) = pieces

      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      notZeroModulus <- notZero(vocabulary, assumedPositive, modulus)
      one <- vocabulary.one
      gcd <- greatestCommonDivisor(vocabulary)

      guard <- logic.mkNot(zeroOf(vocabulary, one)).flatMap(rules.disjIntro2(_, notZeroModulus))
      unit <- LogicError.lift(Term.appAll(gcd, List(one, modulus)))
      dividesUnit <- vocabulary
        .fact(Modular.GcdDividesLeft)
        .flatMap(rules.specAll(_, List(one, modulus)))
        .flatMap(rules.mp(_, guard))
      unitIsOne <- vocabulary
        .fact(Modular.DividesOne)
        .flatMap(rules.spec(unit, _))
        .flatMap(rules.mp(_, dividesUnit))

      recurrence <- rules.spec(sequence, atZero)
      carried <- Conv.apTerm(gcd, recurrence).flatMap(Conv.apThm(_, modulus))
      reached <- Conv.trans(carried, unitIsOne)
      _ <-
        if (reached.conclusion == conclusion) Right(())
        else Left(NotOfForm("the base case as it is written", reached.conclusion))
      dischargedFamily <- rules.disch(family, reached)
      result <- rules.disch(positive, dischargedFamily)
    } yield result
  }

  /** The step of [[CoprimeToFamily]]: the shorter product and the new factor are each coprime. */
  private def coprimeAtSuccessor(
    vocabulary: Vocabulary,
    atSuccessor: Kernel.Thm,
    forProduct: Kernel.Thm,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
      (positive, rest) = parts
      inner <- logic.destImp(rest).toRight(NotOfForm("an implication", rest))
      (family, conclusion) = inner
      subject <- Term.destEq(conclusion).map(_._1).toRight(NotOfForm("an equation", conclusion))
      pieces <- subject match {
        case App(App(_, App(App(_, sequence), _)), modulus) => Right((sequence, modulus))
        case other => Left(NotOfForm("a greatest common divisor of a product", other))
      }
      (sequence, modulus) = pieces

      assumedPositive <- LogicError.lift(Kernel.assume(positive))
      assumedFamily <- LogicError.lift(Kernel.assume(family))

      restricted <- restrictBelow(vocabulary, assumedFamily, step.variable)
      shorter <- rules
        .mp(step.hypothesis, assumedPositive)
        .flatMap(rules.mp(_, restricted))

      reaches <- vocabulary.fact(Peano.BelowSuccessor).flatMap(rules.spec(step.variable, _))
      newest <- rules.spec(step.variable, assumedFamily).flatMap(rules.mp(_, reaches))

      recurrence <- rules.specAll(atSuccessor, List(sequence, step.variable))
      opened <- Term
        .destEq(recurrence.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", recurrence.conclusion))
      halves <- opened match {
        case App(App(_, left), right) => Right((left, right))
        case other => Left(NotOfForm("a product", other))
      }
      (shorterProduct, newestFactor) = halves

      together <- rules
        .specAll(forProduct, List(shorterProduct, newestFactor, modulus))
        .flatMap(rules.mp(_, assumedPositive))
        .flatMap(rules.mp(_, shorter))
        .flatMap(rules.mp(_, newest))

      gcd <- greatestCommonDivisor(vocabulary)
      carried <- Conv.apTerm(gcd, recurrence).flatMap(Conv.apThm(_, modulus))
      reached <- Conv.trans(carried, together)
      _ <-
        if (reached.conclusion == conclusion) Right(())
        else Left(NotOfForm("what the step has to reach", reached.conclusion))
      dischargedFamily <- rules.disch(family, reached)
      result <- rules.disch(positive, dischargedFamily)
    } yield result
  }

  /**
   * Open `?x. body` with a fresh name and hand the instance to the caller.
   *
   * [[withTwoWitnesses]]'s half, and it is not the two-witness version called once: that one opens
   * a nested pair in the order the discharges have to happen, and this one is the single
   * elimination the Chinese remainder theorem does twice at different depths.
   */
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
      variable = Conv.freshVariable(
        name,
        vocabulary.numbers,
        avoid ++ Term.freeVariables(existential.conclusion)
      )
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

  /**
   * `!i. NUM_LT i k ==> NUM_GCD (m i) (m k) = SUC ZERO`, from the pairwise premise at `SUC k`.
   *
   * Three things to hand [[RemaindersFamily]]'s premise: `i` reaches past `k` by transitivity, `k`
   * reaches past itself, and `i` differs from `k` because it is below it. The third is the one that
   * is not free: `NUM_LT` is irreflexive and that is what says so.
   */
  private def coprimeToNewest(
    vocabulary: Vocabulary,
    pairwise: Kernel.Thm,
    k: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      stripped <- Logic.stripForall(pairwise.conclusion)
      index <- stripped._1.headOption
        .toRight(NotOfForm("a claim about every index", pairwise.conclusion))
      successor <- LogicError.lift(Term.app(vocabulary.successor, k))
      below <- LogicError.lift(Term.appAll(vocabulary.below, List(index, k)))
      assumed <- LogicError.lift(Kernel.assume(below))
      reaches <- vocabulary.fact(Peano.BelowSuccessor).flatMap(rules.spec(k, _))
      further <- rules
        .conjIntro(assumed, reaches)
        .flatMap(pair =>
          vocabulary
            .fact(Peano.StrictTransitive)
            .flatMap(rules.specAll(_, List(index, k, successor)))
            .flatMap(rules.mp(_, pair))
        )
      distinct <- belowIsNotEqual(vocabulary, index, k, assumed)
      widened <- rules.conjIntro(reaches, distinct).flatMap(rules.conjIntro(further, _))
      there <- rules.specAll(pairwise, List(index, k)).flatMap(rules.mp(_, widened))
      result <- rules.disch(below, there).flatMap(rules.gen(index, _))
    } yield result
  }

  /** The pairwise premise restricted to the first `k` indices, which the hypothesis wants. */
  private def restrictPairwiseBelow(
    vocabulary: Vocabulary,
    pairwise: Kernel.Thm,
    k: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    def widen(index: FVar, successor: Term, reaches: Kernel.Thm, at: Kernel.Thm) =
      rules
        .conjIntro(at, reaches)
        .flatMap(pair =>
          vocabulary
            .fact(Peano.StrictTransitive)
            .flatMap(rules.specAll(_, List(index, k, successor)))
            .flatMap(rules.mp(_, pair))
        )

    for {
      stripped <- Logic.stripForall(pairwise.conclusion)
      first <- stripped._1.headOption
        .toRight(NotOfForm("a claim about every pair of indices", pairwise.conclusion))
      second <- stripped._1
        .drop(1)
        .headOption
        .toRight(NotOfForm("a claim about every pair of indices", pairwise.conclusion))

      successor <- LogicError.lift(Term.app(vocabulary.successor, k))
      belowFirst <- LogicError.lift(Term.appAll(vocabulary.below, List(first, k)))
      belowSecond <- LogicError.lift(Term.appAll(vocabulary.below, List(second, k)))
      distinct <- LogicError.lift(Term.eq(first, second)).flatMap(logic.mkNot)
      tail <- logic.mkConj(belowSecond, distinct)
      premise <- logic.mkConj(belowFirst, tail)
      assumed <- LogicError.lift(Kernel.assume(premise))
      reaches <- vocabulary.fact(Peano.BelowSuccessor).flatMap(rules.spec(k, _))

      firstFurther <- rules.conjElim1(assumed).flatMap(widen(first, successor, reaches, _))
      rest <- rules.conjElim2(assumed)
      secondFurther <- rules.conjElim1(rest).flatMap(widen(second, successor, reaches, _))
      notEqual <- rules.conjElim2(rest)

      widened <- rules.conjIntro(secondFurther, notEqual).flatMap(rules.conjIntro(firstFurther, _))
      there <- rules.specAll(pairwise, List(first, second)).flatMap(rules.mp(_, widened))
      result <- rules
        .disch(premise, there)
        .flatMap(rules.gen(second, _))
        .flatMap(rules.gen(first, _))
    } yield result
  }

  /** [[RemaindersFamily]], by induction on the number of moduli. */
  private def remaindersOverAFamily(
    vocabulary: Vocabulary,
    driver: Induct,
    pair: Kernel.Thm,
    productDivides: Kernel.Thm,
    productPositive: Kernel.Thm,
    coprimeFamily: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- vocabulary.statement(RemaindersFamily)
      proved <- driver.proveBy(
        statement,
        goal => noModuliAtAll(vocabulary, goal),
        step =>
          oneMoreModulus(
            vocabulary, pair, productDivides, productPositive, coprimeFamily, step)
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(RemaindersFamily, proved)
    } yield result

  /**
   * No moduli at all: zero solves the empty system, because nothing is below zero.
   *
   * The witness is arbitrary and that is the point of writing it out rather than reaching for a
   * choice: the claim at length zero is vacuous, and a reader who sees `ZERO` handed in here can
   * see that nothing about it was used.
   */
  private def noModuliAtAll(vocabulary: Vocabulary, goal: Term): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(goal).toRight(NotOfForm("an implication", goal))
      (positives, rest) = parts
      inner <- logic.destImp(rest).toRight(NotOfForm("an implication", rest))
      (pairwise, conclusion) = inner
      predicate <- logic
        .destExistsPredicate(conclusion)
        .toRight(NotOfForm("an existential", conclusion))
      applied <- LogicError.lift(Term.app(predicate, vocabulary.zero))
      contraction <- Conv.betaRoot(applied)
      instance <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      stripped <- Logic.stripForall(instance)
      index <- stripped._1.headOption
        .toRight(NotOfForm("a claim about every index", instance))
      vacuous <- vacuousBelowZero(vocabulary, stripped._2)
      everywhere <- rules.gen(index, vacuous)
      witnessed <- rules.existsIntro(predicate, vocabulary.zero, everywhere)
      dischargedPairwise <- rules.disch(pairwise, witnessed)
      result <- rules.disch(positives, dischargedPairwise)
    } yield result
  }

  /**
   * One more modulus: the shorter system's answer and the new residue, joined by [[Remainders]].
   *
   * The hypothesis solves the first `k` congruences with some `y`. [[Remainders]] is then applied
   * to the pair `NUM_PROD m k` and `m k`, which are coprime by [[CoprimeToFamily]] and positive by
   * [[ProductPositive]], and what comes back is a `z` congruent to `y` **modulo the whole product**
   * and to `a k` modulo the new one. `Modular.CongDivisor` walks the first of those down to each
   * earlier modulus through [[ProductDivides]], and transitivity finishes it.
   *
   * That is the step the usual textbook strengthening exists to make possible, and it needs no
   * strengthening here because [[Remainders]] was stated as two congruences rather than as a
   * residue below the modulus.
   */
  private def oneMoreModulus(
    vocabulary: Vocabulary,
    pair: Kernel.Thm,
    productDivides: Kernel.Thm,
    productPositive: Kernel.Thm,
    coprimeFamily: Kernel.Thm,
    step: Induct.Step
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      parts <- logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
      (positives, rest) = parts
      inner <- logic.destImp(rest).toRight(NotOfForm("an implication", rest))
      (pairwise, conclusion) = inner
      predicate <- logic
        .destExistsPredicate(conclusion)
        .toRight(NotOfForm("an existential", conclusion))

      // The two sequences, read off the goal rather than rebuilt: the driver freshened them.
      strippedPositives <- Logic.stripForall(positives)
      positiveBody <- logic
        .destImp(strippedPositives._2)
        .toRight(NotOfForm("an implication", strippedPositives._2))
      moduli <- positiveBody._2 match {
        case App(App(_, _), App(candidate, _)) => Right(candidate)
        case other => Left(NotOfForm("a claim about a sequence of moduli", other))
      }
      probe <- LogicError.lift(Term.app(predicate, vocabulary.zero))
      probeContraction <- Conv.betaRoot(probe)
      probeInstance <- Term
        .destEq(probeContraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", probeContraction.conclusion))
      strippedProbe <- Logic.stripForall(probeInstance)
      probeBody <- logic
        .destImp(strippedProbe._2)
        .toRight(NotOfForm("an implication", strippedProbe._2))
      residues <- probeBody._2 match {
        case App(App(App(_, _), _), App(candidate, _)) => Right(candidate)
        case other => Left(NotOfForm("a claim about a sequence of residues", other))
      }

      assumedPositives <- LogicError.lift(Kernel.assume(positives))
      assumedPairwise <- LogicError.lift(Kernel.assume(pairwise))

      reaches <- vocabulary.fact(Peano.BelowSuccessor).flatMap(rules.spec(step.variable, _))
      restrictedPositives <- restrictBelow(vocabulary, assumedPositives, step.variable)
      restrictedPairwise <- restrictPairwiseBelow(vocabulary, assumedPairwise, step.variable)
      shorter <- rules
        .mp(step.hypothesis, restrictedPositives)
        .flatMap(rules.mp(_, restrictedPairwise))

      productConstant <- productOverAFamily(vocabulary)
      product <- LogicError.lift(Term.appAll(productConstant, List(moduli, step.variable)))
      productIsPositive <- rules
        .specAll(productPositive, List(moduli, step.variable))
        .flatMap(rules.mp(_, restrictedPositives))
      newestModulus <- LogicError.lift(Term.app(moduli, step.variable))
      newestResidue <- LogicError.lift(Term.app(residues, step.variable))
      newestPositive <- rules.spec(step.variable, assumedPositives).flatMap(rules.mp(_, reaches))
      coprimeEach <- coprimeToNewest(vocabulary, assumedPairwise, step.variable)
      productCoprime <- rules
        .specAll(coprimeFamily, List(moduli, newestModulus, step.variable))
        .flatMap(rules.mp(_, newestPositive))
        .flatMap(rules.mp(_, coprimeEach))
      premise <- rules
        .conjIntro(productIsPositive, newestPositive)
        .flatMap(rules.conjIntro(productCoprime, _))

      found <- withWitness(vocabulary, shorter, "y", Set(step.variable)) { (y, solvesShorter) =>
        for {
          solved <- rules
            .specAll(pair, List(product, newestModulus, y, newestResidue))
            .flatMap(rules.mp(_, premise))
          joined <- withWitness(vocabulary, solved, "z", Set(step.variable, y)) { (z, both) =>
            for {
              toShorter <- rules.conjElim1(both)
              toNewest <- rules.conjElim2(both)
              everywhere <- eachModulusInTurn(
                vocabulary,
                productDivides,
                predicate,
                moduli,
                residues,
                product,
                step.variable,
                y,
                z,
                toShorter,
                toNewest,
                solvesShorter
              )
              introduced <- rules.existsIntro(predicate, z, everywhere)
            } yield introduced
          }
        } yield joined
      }

      dischargedPairwise <- rules.disch(pairwise, found)
      result <- rules.disch(positives, dischargedPairwise)
    } yield result
  }

  /**
   * `!i. NUM_LT i (SUC k) ==> NUM_CONG (m i) z (a i)`, the two cases of the step.
   *
   * Below `k` the modulus divides the product, so the congruence to `y` descends to it and
   * transitivity carries it to `a i`; at `k` the congruence is the one [[Remainders]] handed back,
   * and what is done to it is a congruence under a fixed context rather than a rewrite, because `i`
   * and `k` both occur elsewhere in the goal.
   */
  private def eachModulusInTurn(
    vocabulary: Vocabulary,
    productDivides: Kernel.Thm,
    predicate: Term,
    moduli: Term,
    residues: Term,
    product: Term,
    k: FVar,
    y: FVar,
    z: FVar,
    toShorter: Kernel.Thm,
    toNewest: Kernel.Thm,
    solvesShorter: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      congruence <- congruenceRelation(vocabulary)
      applied <- LogicError.lift(Term.app(predicate, z))
      contraction <- Conv.betaRoot(applied)
      instance <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
      stripped <- Logic.stripForall(instance)
      index <- stripped._1.headOption
        .toRight(NotOfForm("a claim about every index", instance))
      body <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (below, goal) = body
      assumedBelow <- LogicError.lift(Kernel.assume(below))
      cases <- vocabulary
        .fact(Peano.BelowSuccessorCases)
        .flatMap(rules.specAll(_, List(k, index)))
        .flatMap(rules.mp(_, assumedBelow))
      split <- logic
        .destDisj(cases.conclusion)
        .toRight(NotOfForm("a disjunction", cases.conclusion))
      (belowK, atK) = split
      modulusAtIndex <- LogicError.lift(Term.app(moduli, index))
      residueAtIndex <- LogicError.lift(Term.app(residues, index))

      // Below `k`: the modulus divides the product, so the congruence descends to it.
      fromHypothesis <- for {
        assumed <- LogicError.lift(Kernel.assume(belowK))
        dividesProduct <- rules
          .specAll(productDivides, List(moduli, index, k))
          .flatMap(rules.mp(_, assumed))
        descended <- vocabulary
          .fact(Modular.CongDivisor)
          .flatMap(rules.specAll(_, List(product, modulusAtIndex, z, y)))
          .flatMap(rules.mp(_, dividesProduct))
          .flatMap(rules.mp(_, toShorter))
        there <- rules.spec(index, solvesShorter).flatMap(rules.mp(_, assumed))
        result <- vocabulary
          .fact(Modular.CongTrans)
          .flatMap(rules.specAll(_, List(modulusAtIndex, z, y, residueAtIndex)))
          .flatMap(rules.mp(_, descended))
          .flatMap(rules.mp(_, there))
      } yield result

      // At `k`: the congruence the pair theorem returned, carried backwards along `i = k`.
      fromEquality <- for {
        assumed <- LogicError.lift(Kernel.assume(atK))
        backwards <- Conv.sym(assumed)
        modulusAt <- Conv.apTerm(moduli, backwards)
        residueAt <- Conv.apTerm(residues, backwards)
        newestResidue <- LogicError.lift(Term.app(residues, k))
        overModulus <- Conv
          .apTerm(congruence, modulusAt)
          .flatMap(Conv.apThm(_, z))
          .flatMap(Conv.apThm(_, newestResidue))
        head <- LogicError.lift(Term.appAll(congruence, List(modulusAtIndex, z)))
        overResidue <- Conv.apTerm(head, residueAt)
        bridge <- Conv.trans(overModulus, overResidue)
        result <- LogicError.lift(Kernel.eqMp(bridge, toNewest))
      } yield result

      settled <- rules.disjElim(cases, fromHypothesis, fromEquality)
      _ <-
        if (settled.conclusion == goal) Right(())
        else Left(NotOfForm("what the step has to reach at each index", settled.conclusion))
      result <- rules.disch(below, settled).flatMap(rules.gen(index, _))
    } yield result
  }

  /* --------------------------------------------------------------------- the beta function */

  /** [[FactorialPositive]], by induction: one is a successor, and a product of positives is. */
  private def factorialNeverVanishes(
    vocabulary: Vocabulary,
    driver: Induct,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    def carryBack(recurrence: Kernel.Thm, positive: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        belowZero <- LogicError.lift(Term.app(vocabulary.below, vocabulary.zero))
        back <- Conv.sym(recurrence)
        carried <- Conv.apTerm(belowZero, back)
        result <- LogicError.lift(Kernel.eqMp(carried, positive))
      } yield result

    for {
      statement <- vocabulary.statement(FactorialPositive)
      proved <- driver.proveBy(
        statement,
        _ =>
          for {
            positive <- vocabulary
              .fact(Peano.SuccessorPositive)
              .flatMap(rules.spec(vocabulary.zero, _))
            result <- carryBack(atZero, positive)
          } yield result,
        step =>
          for {
            recurrence <- rules.spec(step.variable, atSuccessor)
            opened <- Term
              .destEq(recurrence.conclusion)
              .map(_._2)
              .toRight(NotOfForm("an equation", recurrence.conclusion))
            halves <- opened match {
              case App(App(_, left), right) => Right((left, right))
              case other => Left(NotOfForm("a product", other))
            }
            (shorter, newest) = halves
            newestPositive <- vocabulary
              .fact(Peano.SuccessorPositive)
              .flatMap(rules.spec(step.variable, _))
            together <- vocabulary
              .fact(Peano.MulPositive)
              .flatMap(rules.specAll(_, List(shorter, newest)))
              .flatMap(rules.mp(_, step.hypothesis))
              .flatMap(rules.mp(_, newestPositive))
            result <- carryBack(recurrence, together)
          } yield result
      )
      _ <-
        if (proved.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
      result <- vocabulary.checked(FactorialPositive, proved)
    } yield result
  }

  /**
   * [[PowerBelowFactorial]], by the ordinary induction on the shifted claim and one case split.
   *
   * The shape is forced and is written out in the docstring of the name: the step of the direct
   * induction asks for `2 <= SUC k`, which fails at zero, so what is inducted on is
   * `Q k := P (SUC k)`, whose step asks for `2 <= SUC (SUC k)` and gets it for every `k`. `P ZERO`
   * is derived beside it, and `Natural.NUM_CASES` puts the two together.
   *
   * == The three places the derivation is longer than the argument ==
   *
   * `NUM_MUL_MONOTONE` is monotone in the **right** factor with the left one fixed, and every
   * inequality here needs it in the other direction: the induction hypothesis is multiplied by two
   * on the right, and the factorial by its own new index. Each of those is the lemma plus one
   * instance of `NUM_MUL_SYM` carried into the comparison, which is what `onLeft` is for.
   *
   * `two <= SUC (SUC k)` has no lemma of its own and is not an instance of one. What gives it is
   * `NUM_LE_ADD`, `x <= x + y`, at `x := SUC (SUC ZERO)` and `y := k`, with the sum rewritten to
   * `SUC (SUC k)` by two instances of `NUM_SUC_ADD` over `NUM_ZERO_ADD`. It is three lines and
   * they are arithmetic rather than order.
   *
   * And a two is `SUC (SUC ZERO)` throughout rather than the numeral `2`, which is what `Peano`
   * does at `NUM_MUL_TWO` and for the same reason: a numeral reaches a recurrence only through
   * `Successor`, `NUM_POW_SUC` recurses on the exponent, and this file has no need of the numeral
   * anywhere. A consumer over the reals crosses by `Series.NUM_REAL_POW` and the embedding, where
   * the two becomes a real numeral in one step that `Linarith` decides.
   */
  private def powerBelowFactorial(
    vocabulary: Vocabulary,
    driver: Induct,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules
    val logic = vocabulary.logic
    val numbers = vocabulary.numbers

    /** `|- NUM_LE left' right` from `|- left = left'` and `|- NUM_LE left right`. */
    def onLeft(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      theorem.conclusion match {
        case App(App(_, _), right) =>
          for {
            congruence <- Conv.apTerm(vocabulary.atMost, equation)
            applied <- Conv.apThm(congruence, right)
            result <- LogicError.lift(Kernel.eqMp(applied, theorem))
          } yield result
        case other => Left(NotOfForm("a comparison", other))
      }

    /** `|- NUM_LE left right'` from `|- right = right'` and `|- NUM_LE left right`. */
    def onRight(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      theorem.conclusion match {
        case App(App(_, left), _) =>
          for {
            context <- LogicError.lift(Term.app(vocabulary.atMost, left))
            result <- vocabulary.carry(context, equation, theorem)
          } yield result
        case other => Left(NotOfForm("a comparison", other))
      }

    /** `|- left * tail = right * tail` from `|- left = right`. */
    def overProduct(equation: Kernel.Thm, tail: Term): Either[LogicError, Kernel.Thm] =
      Conv.apTerm(vocabulary.times, equation).flatMap(Conv.apThm(_, tail))

    for {
      one <- vocabulary.one
      two <- LogicError.lift(Term.app(vocabulary.successor, one))
      power <- LogicError.lift(
        vocabulary.theory
          .constant(Peano.Exponentiation, Type.fun(numbers, Type.fun(numbers, numbers)))
      )

      powAtZero <- vocabulary.fact(Peano.PowAtZero)
      powAtSuccessor <- vocabulary.fact(Peano.PowAtSuccessor)
      timesOne <- vocabulary.fact(Peano.TimesOne)
      mulSym <- vocabulary.fact(Peano.MulCommutative)
      monotone <- vocabulary.fact(Peano.MulMonotone)
      reflexive <- vocabulary.fact(Peano.Reflexive)
      atMostSuccessor <- vocabulary.fact(Peano.AtMostSuccessor)
      atMostSum <- vocabulary.fact(Peano.AtMostSum)
      successorPlus <- vocabulary.fact(Peano.SuccessorPlus)
      zeroPlus <- vocabulary.fact(Peano.ZeroPlus)
      cases <- vocabulary.peano.naturals.fact(Natural.ZeroOrSuccessor)

      result <- {
        def powerAt(exponent: Term): Either[LogicError, Term] =
          LogicError.lift(Term.appAll(power, List(two, exponent)))

        def successorOf(argument: Term): Either[LogicError, Term] =
          LogicError.lift(Term.app(vocabulary.successor, argument))

        /** `|- two <= SUC (SUC k)`, which is `NUM_LE_ADD` with the sum rewritten. */
        def twoBelowTwoSuccessors(k: Term): Either[LogicError, Kernel.Thm] =
          for {
            innerShift <- rules.specAll(successorPlus, List(vocabulary.zero, k))
            zeroAt <- rules.spec(k, zeroPlus)
            inner <- Conv.apTerm(vocabulary.successor, zeroAt)
            oneShift <- Conv.trans(innerShift, inner)
            outerShift <- rules.specAll(successorPlus, List(one, k))
            outer <- Conv.apTerm(vocabulary.successor, oneShift)
            shifted <- Conv.trans(outerShift, outer)
            bounded <- rules.specAll(atMostSum, List(two, k))
            result <- onRight(shifted, bounded)
          } yield result

        /** `|- NUM_POW two (SUC ZERO) <= NUM_MUL two (NUM_FACT (SUC ZERO))`, both sides being two. */
        def shiftedBase(goal: Term): Either[LogicError, Kernel.Thm] =
          for {
            opened <- rules.specAll(powAtSuccessor, List(two, vocabulary.zero))
            atZeroPower <- rules.spec(two, powAtZero)
            reduced <- overProduct(atZeroPower, two)
            asOneTimes <- Conv.trans(opened, reduced)
            commuted <- rules.specAll(mulSym, List(one, two))
            twoTimesOne <- rules.spec(two, timesOne)
            leftIsTwo <- Conv.trans(asOneTimes, commuted).flatMap(Conv.trans(_, twoTimesOne))

            factorialStep <- rules.spec(vocabulary.zero, atSuccessor)
            factorialReduced <- overProduct(atZero, one)
            oneTimesOne <- rules.spec(one, timesOne)
            factorialIsOne <- Conv
              .trans(factorialStep, factorialReduced)
              .flatMap(Conv.trans(_, oneTimesOne))
            underTwo <- vocabulary.underProduct(two, factorialIsOne)
            rightIsTwo <- Conv.trans(underTwo, twoTimesOne)

            refl <- rules.spec(two, reflexive)
            leftBack <- Conv.sym(leftIsTwo).flatMap(onLeft(_, refl))
            settled <- Conv.sym(rightIsTwo).flatMap(onRight(_, leftBack))
            _ <-
              if (settled.conclusion == goal) Right(())
              else Left(NotOfForm("the base of the shifted claim", settled.conclusion))
          } yield settled

        /** The step of the shifted claim, where the two the factorial has to beat is `SUC (SUC k)`. */
        def shiftedStep(step: Induct.Step): Either[LogicError, Kernel.Thm] =
          for {
            successorOfK <- successorOf(step.variable)
            twice <- successorOf(successorOfK)
            powerOfK <- powerAt(successorOfK)
            factorialOfK <- LogicError.lift(Term.app(vocabulary.factorial, successorOfK))

            twiceFactorial <- vocabulary.product(two, factorialOfK)
            byHypothesis <- rules
              .specAll(monotone, List(two, powerOfK, twiceFactorial))
              .flatMap(rules.mp(_, step.hypothesis))
            commutedPower <- rules.specAll(mulSym, List(powerOfK, two))
            fromHypothesis <- Conv.sym(commutedPower).flatMap(onLeft(_, byHypothesis))

            bigger <- twoBelowTwoSuccessors(step.variable)
            grown <- rules
              .specAll(monotone, List(factorialOfK, two, twice))
              .flatMap(rules.mp(_, bigger))
            commutedFactorial <- rules.specAll(mulSym, List(two, factorialOfK))
            shifted <- Conv.sym(commutedFactorial).flatMap(onLeft(_, grown))

            grownFactorial <- vocabulary.product(factorialOfK, twice)
            underTwo <- rules
              .specAll(monotone, List(two, twiceFactorial, grownFactorial))
              .flatMap(rules.mp(_, shifted))

            leftEnd <- vocabulary.product(powerOfK, two)
            middle <- vocabulary.product(two, twiceFactorial)
            rightEnd <- vocabulary.product(two, grownFactorial)
            chained <- transitively(vocabulary, leftEnd, middle, rightEnd, fromHypothesis, underTwo)

            openedPower <- rules.specAll(powAtSuccessor, List(two, successorOfK))
            openedFactorial <- rules.spec(successorOfK, atSuccessor)
            leftBack <- Conv.sym(openedPower).flatMap(onLeft(_, chained))
            rightBack <- Conv
              .sym(openedFactorial)
              .flatMap(vocabulary.underProduct(two, _))
              .flatMap(onRight(_, leftBack))
            _ <-
              if (rightBack.conclusion == step.goal) Right(())
              else Left(NotOfForm("the step of the shifted claim", rightBack.conclusion))
          } yield rightBack

        for {
          shiftedText <- Right(
            "!k:num. NUM_LE (NUM_POW (SUC (SUC ZERO)) (SUC k)) " +
              "(NUM_MUL (SUC (SUC ZERO)) (NUM_FACT (SUC k)))"
          )
          shifted <- Parser.proposition(vocabulary.theory, vocabulary.notation, shiftedText)
          everyShift <- driver.proveBy(shifted, shiftedBase, shiftedStep)

          // `P ZERO`, which the shifted claim does not cover and which is true for its own reason:
          // one power of two is one, no factorial has been taken, and `SUC 0 <= SUC (SUC 0)`.
          atZeroPower <- rules.spec(two, powAtZero)
          underTwo <- vocabulary.underProduct(two, atZero)
          twoTimesOne <- rules.spec(two, timesOne)
          rightIsTwo <- Conv.trans(underTwo, twoTimesOne)
          below <- rules.spec(one, atMostSuccessor)
          leftBack <- Conv.sym(atZeroPower).flatMap(onLeft(_, below))
          atZeroCase <- Conv.sym(rightIsTwo).flatMap(onRight(_, leftBack))

          statement <- vocabulary.statement(PowerBelowFactorial)
          stripped <- Logic.stripForall(statement)
          subject <- stripped._1.lastOption.toRight(
            NotOfForm("a claim about every number", statement)
          )
          template <- LogicError.lift(Term.abs(subject, stripped._2))

          split <- rules.spec(subject, cases)
          disjuncts <- logic
            .destDisj(split.conclusion)
            .toRight(NotOfForm("a disjunction", split.conclusion))
          (isZero, isSuccessor) = disjuncts

          fromZero <- for {
            assumed <- LogicError.lift(Kernel.assume(isZero))
            congruence <- Conv.apTerm(template, assumed)
            reduced <- Conv.betaSides(congruence)
            flipped <- Conv.sym(reduced)
            moved <- LogicError.lift(Kernel.eqMp(flipped, atZeroCase))
          } yield moved

          predicate <- logic
            .destExistsPredicate(isSuccessor)
            .toRight(NotOfForm("an existential quantification", isSuccessor))
          witness = Conv.freshVariable(
            "y",
            numbers,
            Term.freeVariables(statement) ++ Term.freeVariables(isSuccessor)
          )
          applied <- LogicError.lift(Term.app(predicate, witness))
          contraction <- Conv.betaRoot(applied)
          inner <- Term
            .destEq(contraction.conclusion)
            .map(_._2)
            .toRight(NotOfForm("an equation", contraction.conclusion))

          fromSuccessor <- for {
            assumedExists <- LogicError.lift(Kernel.assume(isSuccessor))
            assumedInner <- LogicError.lift(Kernel.assume(inner))
            atWitness <- rules.spec(witness, everyShift)
            congruence <- Conv.apTerm(template, assumedInner)
            reduced <- Conv.betaSides(congruence)
            flipped <- Conv.sym(reduced)
            moved <- LogicError.lift(Kernel.eqMp(flipped, atWitness))
            eliminated <- rules.existsElim(assumedExists, witness, moved)
          } yield eliminated

          settled <- rules.disjElim(split, fromZero, fromSuccessor)
          proved <- rules.gen(subject, settled)
          _ <-
            if (proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm("a theorem with nothing assumed", proved.conclusion))
          checked <- vocabulary.checked(PowerBelowFactorial, proved)
        } yield checked
      }
    } yield result
  }

  /** `NUM_LE x z` from `NUM_LE x y` and `NUM_LE y z`, which this construction does five times. */
  private def transitively(
    vocabulary: Vocabulary,
    first: Term,
    middle: Term,
    last: Term,
    below: Kernel.Thm,
    above: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    vocabulary.rules
      .conjIntro(below, above)
      .flatMap(pair =>
        vocabulary
          .fact(Peano.Transitive)
          .flatMap(vocabulary.rules.specAll(_, List(first, middle, last)))
          .flatMap(vocabulary.rules.mp(_, pair))
      )

  /**
   * `NUM_LT ZERO x` from `~(x = ZERO)`, by trichotomy against zero.
   *
   * The two branches that are not the answer are the equation, which the hypothesis denies, and
   * `x < ZERO`, which nothing satisfies.
   */
  private def positiveFromNotZero(
    vocabulary: Vocabulary,
    subject: Term,
    notZeroThm: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      wanted <- LogicError.lift(Term.appAll(vocabulary.below, List(vocabulary.zero, subject)))
      cases <- vocabulary
        .fact(Peano.Trichotomy)
        .flatMap(rules.specAll(_, List(vocabulary.zero, subject)))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (positive, rest) = split
      restSplit <- logic.destDisj(rest).toRight(NotOfForm("a disjunction", rest))
      (equal, negative) = restSplit

      fromPositive <- LogicError.lift(Kernel.assume(positive))
      fromEqual <- for {
        assumed <- LogicError.lift(Kernel.assume(equal))
        reversed <- Conv.sym(assumed)
        contradiction <- rules.notElim(notZeroThm, reversed)
        anything <- rules.falsityElim(wanted, contradiction)
      } yield anything
      fromNegative <- for {
        assumed <- LogicError.lift(Kernel.assume(negative))
        never <- vocabulary.fact(Peano.NotBelowZero).flatMap(rules.spec(subject, _))
        contradiction <- rules.notElim(never, assumed)
        anything <- rules.falsityElim(wanted, contradiction)
      } yield anything

      assumedRest <- LogicError.lift(Kernel.assume(rest))
      tail <- rules.disjElim(assumedRest, fromEqual, fromNegative)
      result <- rules.disjElim(cases, fromPositive, tail)
    } yield result
  }

  /**
   * `NUM_LT ZERO (NUM_SUB upper lower)` from `NUM_LT lower upper`.
   *
   * The gap between two indices, which [[FactorialDivides]] asks to be positive before it will make
   * it a divisor of a factorial. `Peano.MinusThenPlus` puts the gap back where it came from, and a
   * gap of zero would put `lower` on top of `upper`.
   */
  private def gapIsPositive(
    vocabulary: Vocabulary,
    lower: Term,
    upper: Term,
    below: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = vocabulary.rules

    for {
      subtraction <- truncatedDifference(vocabulary)
      gap <- LogicError.lift(Term.appAll(subtraction, List(upper, lower)))
      atMost <- vocabulary
        .fact(Peano.AtMostFromBelow)
        .flatMap(rules.specAll(_, List(lower, upper)))
        .flatMap(rules.mp(_, below))
      restored <- vocabulary
        .fact(Peano.MinusThenPlus)
        .flatMap(rules.specAll(_, List(upper, lower)))
        .flatMap(rules.mp(_, atMost))

      isZero <- LogicError.lift(Term.eq(gap, vocabulary.zero))
      assumed <- LogicError.lift(Kernel.assume(isZero))
      shifted <- Conv.apTerm(vocabulary.plus, assumed).flatMap(Conv.apThm(_, lower))
      zeroSum <- vocabulary.fact(Peano.ZeroPlus).flatMap(rules.spec(lower, _))

      // `upper = (upper - lower) + lower = ZERO + lower = lower`, read backwards.
      restoredBack <- Conv.sym(restored)
      throughShift <- Conv.trans(restoredBack, shifted)
      upperIsLower <- Conv.trans(throughShift, zeroSum)
      sameNumber <- Conv.sym(upperIsLower)
      absurdly <- Conv
        .apTerm(vocabulary.below, sameNumber)
        .flatMap(Conv.apThm(_, upper))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, below)))
      never <- vocabulary.fact(Peano.StrictIrreflexive).flatMap(rules.spec(upper, _))
      contradiction <- rules.notElim(never, absurdly)
      notZero <- rules.notIntro(isZero, contradiction)
      result <- positiveFromNotZero(vocabulary, gap, notZero)
    } yield result
  }

  /** The theorem again with its conclusion beta-normalised, which every specialisation here wants. */
  private def reduced(theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      contraction <- Conv.betaNormalise(theorem.conclusion)
      result <- LogicError.lift(Kernel.eqMp(contraction, theorem))
    } yield result

  /** The right-hand side of what `Conv.betaNormalise` makes of a term. */
  private def normalised(goal: Term): Either[LogicError, (Kernel.Thm, Term)] =
    for {
      contraction <- Conv.betaNormalise(goal)
      right <- Term
        .destEq(contraction.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", contraction.conclusion))
    } yield (contraction, right)

  /** `NUM_SUB` at this signature, which the gap between two indices is written with. */
  private def truncatedDifference(vocabulary: Vocabulary): Either[LogicError, Term] =
    LogicError.lift(
      vocabulary.theory.constant(
        Peano.Subtraction,
        Type.fun(vocabulary.numbers, Type.fun(vocabulary.numbers, vocabulary.numbers))
      )
    )

  /**
   * [[BetaSequence]], the construction rather than an induction.
   *
   * Every step is named in the lemma's own docstring; what is here is the order they have to happen
   * in. The two existentials are introduced last, because the witnesses are `a`, which the Chinese
   * remainder theorem produces, and `b`, which is `k!` and is fixed the moment the bound is opened.
   */
  private def sequenceOfResidues(
    vocabulary: Vocabulary,
    bound: Kernel.Thm,
    factorialDivides: Kernel.Thm,
    factorialPositive: Kernel.Thm,
    coprime: Kernel.Thm,
    remaindersFamily: Kernel.Thm,
    betaDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      statement <- vocabulary.statement(BetaSequence)
      stripped <- Logic.stripForall(statement)
      sequence <- stripped._1.headOption
        .toRight(NotOfForm("a claim about every sequence", statement))
      length <- stripped._1.drop(1).headOption
        .toRight(NotOfForm("a claim about every length", statement))
      outer = stripped._2

      bounded <- rules.specAll(bound, List(sequence, length))
      found <- withWitness(vocabulary, bounded, "M", Set(sequence, length)) { (cap, entriesBounded) =>
        for {
          total <- vocabulary.sum(cap, length)
          k <- LogicError.lift(Term.app(vocabulary.successor, total))
          b <- LogicError.lift(Term.app(vocabulary.factorial, k))

          capAtMostTotal <- atMostSum(vocabulary, cap, length)
          lengthAtMostTotal <- atMostSumRight(vocabulary, cap, length)
          totalAtMostK <- vocabulary.fact(Peano.AtMostSuccessor).flatMap(rules.spec(total, _))
          capAtMostK <- transitively(vocabulary, cap, total, k, capAtMostTotal, totalAtMostK)
          lengthAtMostK <- transitively(vocabulary, length, total, k, lengthAtMostTotal, totalAtMostK)
          positiveK <- vocabulary.fact(Peano.SuccessorPositive).flatMap(rules.spec(total, _))

          kAtMostB <- factorialIsAtLeastItsArgument(
            vocabulary, factorialDivides, factorialPositive, k, b, positiveK)

          index = Conv.freshVariable("i", vocabulary.numbers, Set(sequence, length, cap))
          moduliBody <- modulus(vocabulary, index, b)
          moduli <- LogicError.lift(Term.abs(index, moduliBody))

          instance <- rules.specAll(remaindersFamily, List(moduli, sequence, length))
          firstHalf <- logic
            .destImp(instance.conclusion)
            .toRight(NotOfForm("an implication", instance.conclusion))
          (positives, rest) = firstHalf
          secondHalf <- logic.destImp(rest).toRight(NotOfForm("an implication", rest))
          (pairwise, _) = secondHalf

          provedPositives <- everyModulusIsPositive(vocabulary, positives)
          provedPairwise <- everyPairIsCoprime(
            vocabulary, pairwise, coprime, factorialDivides, b, k, lengthAtMostK)
          solved <- rules.mp(instance, provedPositives).flatMap(rules.mp(_, provedPairwise))

          predicate <- logic.destExistsPredicate(outer).toRight(NotOfForm("an existential", outer))
          result <- withWitness(vocabulary, solved, "a", Set(sequence, length, cap)) { (witness, solves) =>
            for {
              inner <- LogicError.lift(Term.app(predicate, witness))
              innerBody <- normalised(inner).map(_._2)
              innerPredicate <- logic
                .destExistsPredicate(innerBody)
                .toRight(NotOfForm("an existential", innerBody))
              atB <- LogicError.lift(Term.app(innerPredicate, b)).flatMap(normalised).map(_._2)
              readBack <- everyEntryIsRead(
                vocabulary, betaDefinition, atB, sequence, witness, b, cap, k,
                solves, entriesBounded, capAtMostK, kAtMostB)
              withB <- rules.existsIntro(innerPredicate, b, readBack)
              withA <- rules.existsIntro(predicate, witness, withB)
            } yield withA
          }
        } yield result
      }
      general <- rules.genAll(found, List(sequence, length))
      _ <-
        if (general.hypotheses.isEmpty) Right(())
        else Left(NotOfForm("a theorem with nothing assumed", general.conclusion))
      result <- vocabulary.checked(BetaSequence, general)
    } yield result
  }

  /**
   * `NUM_LE k (NUM_FACT k)` for positive `k`, which is `k | k!` read as a bound.
   *
   * `Modular.DividesBound` concludes a disjunction whose other half is that the dividend vanishes,
   * because zero is divided by everything. [[FactorialPositive]] is what closes that half, and it
   * is the only place in this file that lemma is spent.
   */
  private def factorialIsAtLeastItsArgument(
    vocabulary: Vocabulary,
    factorialDivides: Kernel.Thm,
    factorialPositive: Kernel.Thm,
    k: Term,
    b: Term,
    positiveK: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      wanted <- LogicError.lift(Term.appAll(vocabulary.atMost, List(k, b)))
      reflexive <- vocabulary.fact(Peano.Reflexive).flatMap(rules.spec(k, _))
      divides <- rules
        .conjIntro(positiveK, reflexive)
        .flatMap(pair => rules.specAll(factorialDivides, List(k, k)).flatMap(rules.mp(_, pair)))
      cases <- vocabulary
        .fact(Modular.DividesBound)
        .flatMap(rules.specAll(_, List(k, b)))
        .flatMap(rules.mp(_, divides))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (bounded, vanishes) = split

      fromBound <- LogicError.lift(Kernel.assume(bounded))
      fromVanishing <- for {
        assumed <- LogicError.lift(Kernel.assume(vanishes))
        positive <- rules.spec(k, factorialPositive)
        context <- LogicError.lift(Term.app(vocabulary.below, vocabulary.zero))
        absurdly <- vocabulary.carry(context, assumed, positive)
        never <- vocabulary
          .fact(Peano.StrictIrreflexive)
          .flatMap(rules.spec(vocabulary.zero, _))
        contradiction <- rules.notElim(never, absurdly)
        anything <- rules.falsityElim(wanted, contradiction)
      } yield anything

      result <- rules.disjElim(cases, fromBound, fromVanishing)
    } yield result
  }

  /** Each modulus is a successor, so the Chinese remainder theorem's positivity premise is free. */
  private def everyModulusIsPositive(
    vocabulary: Vocabulary,
    positives: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      stripped <- Logic.stripForall(positives)
      index <- stripped._1.headOption
        .toRight(NotOfForm("a claim about every index", positives))
      body <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (below, claim) = body
      reduction <- normalised(claim)
      (contraction, reducedClaim) = reduction
      inside <- reducedClaim match {
        case App(App(_, _), App(_, argument)) => Right(argument)
        case other => Left(NotOfForm("a claim about a successor", other))
      }
      positive <- vocabulary.fact(Peano.SuccessorPositive).flatMap(rules.spec(inside, _))
      back <- Conv.sym(contraction)
      carried <- LogicError.lift(Kernel.eqMp(back, positive))
      result <- rules.disch(below, carried).flatMap(rules.gen(index, _))
    } yield result
  }

  /**
   * The moduli are pairwise coprime, which is [[ModuliCoprime]] under a trichotomy.
   *
   * That lemma is stated for `i < j`, and the Chinese remainder theorem asks for every ordered pair
   * with the two indices distinct. So the case below is the lemma, the case above is the lemma with
   * the indices exchanged and `Modular.GcdSym` to put the answer back in the order the premise
   * wants, and the case of equality is refused by the premise itself.
   */
  private def everyPairIsCoprime(
    vocabulary: Vocabulary,
    pairwise: Term,
    coprime: Kernel.Thm,
    factorialDivides: Kernel.Thm,
    b: Term,
    k: Term,
    lengthAtMostK: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    def coprimeAt(lower: Term, upper: Term, below: Kernel.Thm, upperBelowLength: Kernel.Thm) =
      for {
        positiveGap <- gapIsPositive(vocabulary, lower, upper, below)
        subtraction <- truncatedDifference(vocabulary)
        gap <- LogicError.lift(Term.appAll(subtraction, List(upper, lower)))
        gapAtMostUpper <- vocabulary
          .fact(Peano.SubBelow)
          .flatMap(rules.specAll(_, List(upper, lower)))
        upperAtMostLength <- vocabulary
          .fact(Peano.AtMostFromBelow)
          .flatMap(argument =>
            upperBelowLength.conclusion match {
              case App(App(_, left), right) =>
                rules.specAll(argument, List(left, right)).flatMap(rules.mp(_, upperBelowLength))
              case other => Left(NotOfForm("a comparison", other))
            }
          )
        lengthTerm <- upperBelowLength.conclusion match {
          case App(App(_, _), right) => Right(right)
          case other => Left(NotOfForm("a comparison", other))
        }
        gapAtMostLength <- transitively(
          vocabulary, gap, upper, lengthTerm, gapAtMostUpper, upperAtMostLength)
        gapAtMostK <- transitively(
          vocabulary, gap, lengthTerm, k, gapAtMostLength, lengthAtMostK)
        dividesB <- rules
          .conjIntro(positiveGap, gapAtMostK)
          .flatMap(pair =>
            rules.specAll(factorialDivides, List(gap, k)).flatMap(rules.mp(_, pair))
          )
        result <- rules
          .conjIntro(below, dividesB)
          .flatMap(pair =>
            rules.specAll(coprime, List(b, lower, upper)).flatMap(rules.mp(_, pair))
          )
      } yield result

    for {
      stripped <- Logic.stripForall(pairwise)
      first <- stripped._1.headOption
        .toRight(NotOfForm("a claim about every pair of indices", pairwise))
      second <- stripped._1.drop(1).headOption
        .toRight(NotOfForm("a claim about every pair of indices", pairwise))
      body <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (premise, claim) = body
      assumed <- LogicError.lift(Kernel.assume(premise))
      firstBelow <- rules.conjElim1(assumed)
      rest <- rules.conjElim2(assumed)
      secondBelow <- rules.conjElim1(rest)
      distinct <- rules.conjElim2(rest)

      reduction <- normalised(claim)
      (contraction, reducedClaim) = reduction

      cases <- vocabulary
        .fact(Peano.Trichotomy)
        .flatMap(rules.specAll(_, List(first, second)))
      split <- logic.destDisj(cases.conclusion).toRight(NotOfForm("a disjunction", cases.conclusion))
      (ascending, tailCases) = split
      tailSplit <- logic.destDisj(tailCases).toRight(NotOfForm("a disjunction", tailCases))
      (equal, descending) = tailSplit

      fromAscending <- LogicError
        .lift(Kernel.assume(ascending))
        .flatMap(coprimeAt(first, second, _, secondBelow))

      fromEqual <- for {
        assumedEqual <- LogicError.lift(Kernel.assume(equal))
        contradiction <- rules.notElim(distinct, assumedEqual)
        anything <- rules.falsityElim(reducedClaim, contradiction)
      } yield anything

      fromDescending <- for {
        assumedDescending <- LogicError.lift(Kernel.assume(descending))
        other <- coprimeAt(second, first, assumedDescending, firstBelow)
        lowerModulus <- modulus(vocabulary, second, b)
        upperModulus <- modulus(vocabulary, first, b)
        swap <- vocabulary
          .fact(Modular.GcdSym)
          .flatMap(rules.specAll(_, List(upperModulus, lowerModulus)))
        settled <- Conv.trans(swap, other)
      } yield settled

      assumedTail <- LogicError.lift(Kernel.assume(tailCases))
      tail <- rules.disjElim(assumedTail, fromEqual, fromDescending)
      settled <- rules.disjElim(cases, fromAscending, tail)
      back <- Conv.sym(contraction)
      carried <- LogicError.lift(Kernel.eqMp(back, settled))
      result <- rules
        .disch(premise, carried)
        .flatMap(rules.gen(second, _))
        .flatMap(rules.gen(first, _))
    } yield result
  }

  /**
   * Each entry is the beta function at its index, which is where every bound above is spent.
   *
   * Two facts meet. The Chinese remainder theorem made `a` congruent to `s i` modulo the `i`th
   * modulus, and the chain of bounds puts `s i` strictly below that modulus:
   * `s i <= M <= k <= k! = b <= (i + 1) * b < 1 + (i + 1) * b`. `Modular.ModOfCong` needs exactly
   * those two and gives the remainder, and the remainder is what `NUM_BETA` unfolds to.
   */
  private def everyEntryIsRead(
    vocabulary: Vocabulary,
    betaDefinition: Kernel.Thm,
    goal: Term,
    sequence: Term,
    witness: Term,
    b: Term,
    cap: Term,
    k: Term,
    solves: Kernel.Thm,
    entriesBounded: Kernel.Thm,
    capAtMostK: Kernel.Thm,
    kAtMostB: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = vocabulary.logic
    val rules = vocabulary.rules

    for {
      stripped <- Logic.stripForall(goal)
      index <- stripped._1.headOption.toRight(NotOfForm("a claim about every index", goal))
      body <- logic.destImp(stripped._2).toRight(NotOfForm("an implication", stripped._2))
      (below, claim) = body
      assumedBelow <- LogicError.lift(Kernel.assume(below))

      congruent <- rules.spec(index, solves).flatMap(rules.mp(_, assumedBelow)).flatMap(reduced)
      modulusTerm <- modulus(vocabulary, index, b)
      entry <- LogicError.lift(Term.app(sequence, index))

      // `s i` is below its own modulus, by five steps of the order and one of the semiring.
      entryAtMostCap <- rules.spec(index, entriesBounded).flatMap(rules.mp(_, assumedBelow))
      entryAtMostK <- transitively(vocabulary, entry, cap, k, entryAtMostCap, capAtMostK)
      entryAtMostB <- transitively(vocabulary, entry, k, b, entryAtMostK, kAtMostB)
      successorOfIndex <- LogicError.lift(Term.app(vocabulary.successor, index))
      scaled <- vocabulary.product(successorOfIndex, b)
      opened <- vocabulary
        .fact(Peano.SuccessorTimes)
        .flatMap(rules.specAll(_, List(index, b)))
      shorter <- Term
        .destEq(opened.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", opened.conclusion))
      head <- shorter match {
        case App(App(_, left), _) => Right(left)
        case other => Left(NotOfForm("a sum", other))
      }
      bAtMostShorter <- atMostSumRight(vocabulary, head, b)
      backwards <- Conv.sym(opened)
      atMostB <- LogicError.lift(Term.app(vocabulary.atMost, b))
      bAtMostScaled <- Conv
        .apTerm(atMostB, backwards)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, bAtMostShorter)))
      entryAtMostScaled <- transitively(vocabulary, entry, b, scaled, entryAtMostB, bAtMostScaled)
      scaledBelowModulus <- vocabulary.fact(Peano.BelowSuccessor).flatMap(rules.spec(scaled, _))
      entryBelowModulus <- rules
        .conjIntro(entryAtMostScaled, scaledBelowModulus)
        .flatMap(pair =>
          vocabulary
            .fact(Peano.AtMostThenBelow)
            .flatMap(rules.specAll(_, List(entry, scaled, modulusTerm)))
            .flatMap(rules.mp(_, pair))
        )

      asRemainder <- vocabulary
        .fact(Modular.ModOfCong)
        .flatMap(rules.specAll(_, List(modulusTerm, witness, entry)))
        .flatMap(rules.mp(_, congruent))
        .flatMap(rules.mp(_, entryBelowModulus))

      unfolded <- Conv.unfold(betaDefinition, List(witness, b, index))
      reachedClaim <- Conv.trans(unfolded, asRemainder)
      _ <-
        if (reachedClaim.conclusion == claim) Right(())
        else Left(NotOfForm("the entry as the goal writes it", reachedClaim.conclusion))
      result <- rules.disch(below, reachedClaim).flatMap(rules.gen(index, _))
    } yield result
  }
}
