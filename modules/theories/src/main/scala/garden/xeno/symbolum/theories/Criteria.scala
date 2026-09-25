package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The convergence criteria for a series, in both directions: what makes one converge and what makes
 * one fail to, derived for [[Limit]] and published there under the names it gives them.
 *
 * == Why this file exists beside `Limit.scala` rather than inside it ==
 *
 * `Limit.scala` is the vocabulary and the algebra of limits; what is here is a **decision**, the
 * half of it that answers "diverges" as well as the half that answers "converges". Until these
 * landed the answer set was {converges, silence}, and silence is not a negative answer: nothing in
 * the proof side could say a series fails to converge. The names, the statements a reader checks
 * and the docstrings are in [[Limit]], where a reader of the library looks; the derivations are
 * here, because they share a vocabulary of their own (the kit below) and none of the other
 * derivations in `Limit.scala` wants it.
 *
 * == What the ratio test is and is not for ==
 *
 * [[Limit.RatioTest]] is published with the geometric criteria it rests on, and it is **not** what
 * the procedure in `Convergence` applies: that one reads a summand against closed forms, because
 * proving the ratio inequality at a symbolic index is a derivation per shape and the closed forms
 * need none. The test is here because it is the theorem a reader reaches for by hand, at a summand
 * no closed form covers, and `CriteriaSpec` detaches it at one with every hypothesis discharged.
 */
private[theories] object Criteria {

  private val values: Type = TyApp(Real.TypeName, Nil)
  private val numbers: Type = TyApp(Natural.TypeName, Nil)
  private val sequences: Type = Type.fun(numbers, values)

  /**
   * Everything the derivations here take from below, named, so that a derivation says what it uses.
   *
   * One record rather than a parameter list per derivation, for the reason `Limit`'s own bundles
   * give: a positional read of thirty theorems of one type is how a derivation gets assembled out of
   * the wrong pieces, and here seven derivations share most of it.
   */
  final case class Kit(
    logic: Logic,
    ring: Ring,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    induct: Induct,
    convergesDefinition: Kernel.Thm,
    divergesDefinition: Kernel.Thm,
    orderDefinition: Kernel.Thm,
    constant: Kernel.Thm,
    unique: Kernel.Thm,
    eventually: Kernel.Thm,
    shifted: Kernel.Thm,
    monotoneConverges: Kernel.Thm,
    comparison: Kernel.Thm,
    aboveBound: Kernel.Thm,
    added: Kernel.Thm,
    negated: Kernel.Thm,
    multiplied: Kernel.Thm,
    absolute: Kernel.Thm,
    belowLimit: Kernel.Thm,
    squeezed: Kernel.Thm,
    powerOfAMagnitude: Kernel.Thm,
    sumAtSuccessor: Kernel.Thm,
    powerAtZero: Kernel.Thm,
    powerAtSuccessor: Kernel.Thm,
    powerPositive: Kernel.Thm,
    geometricSum: Kernel.Thm,
    reindex: Kernel.Thm,
    scaled: Kernel.Thm,
    scaledRight: Kernel.Thm,
    congruence: Kernel.Thm,
    absNonNegative: Kernel.Thm,
    absAbove: Kernel.Thm,
    absOfNonNegative: Kernel.Thm,
    absMultiplicative: Kernel.Thm,
    absZero: Kernel.Thm,
    leOfLt: Kernel.Thm,
    leOfEq: Kernel.Thm,
    leOfNotLt: Kernel.Thm,
    antisymmetric: Kernel.Thm,
    positiveNotZero: Kernel.Thm,
    mulInverse: Kernel.Thm,
    multiplyLe: Kernel.Thm,
    productPositive: Kernel.Thm,
    total: Kernel.Thm,
    addAtZero: Kernel.Thm,
    addAtSuccessor: Kernel.Thm,
    atMostSum: Kernel.Thm,
    associative: Kernel.Thm,
    commutative: Kernel.Thm
  ) {
    def rules: Rules = logic.rules

    def term(text: String, ty: Type): Either[LogicError, Term] =
      Parser.term(theory, notation, text, ty)

    def proposition(text: String): Either[LogicError, Term] =
      Parser.proposition(theory, notation, text)

    def assume(text: String): Either[LogicError, (Term, Kernel.Thm)] =
      proposition(text).flatMap(p => LogicError.lift(Kernel.assume(p)).map(p -> _))

    /** `template`, a lambda written as text, applied to `argument` and reduced. */
    def at(template: String, argument: Term): Either[LogicError, Term] =
      for {
        lambda <- Parser.term(theory, notation, template)
        applied <- LogicError.lift(Term.app(lambda, argument))
        reduced <- Conv.betaNormalise(applied)
        right <- Limit.rightOf(reduced)
      } yield right

    /** `body` packed under the existential `text` at `witness`. */
    def exists(text: String, witness: Term, body: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        claim <- proposition(text)
        predicate <- logic.destExistsPredicate(claim).toRight(NotOfForm("an existential", claim))
        packed <- rules.existsIntro(predicate, witness, body)
      } yield packed

    /** `x = y` carried to `x <= y`. */
    def weakened(equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Limit.destructEquation(equation).flatMap(sides =>
        rules.specAll(leOfEq, List(sides._1, sides._2)).flatMap(rules.mp(_, equation)))

    /** Refuse naming both statements where a derivation and its target have drifted apart. */
    def landsOn(theorem: Kernel.Thm, target: Term): Either[LogicError, Kernel.Thm] =
      if (theorem.conclusion == target) Right(theorem)
      else Left(NotOfForm(s"a proof of ${Show.show(notation, target)}", theorem.conclusion))
  }

  /**
   * [[Limit.Offset]], `|- !s l N. converges (\n. s (NUM_ADD N n)) l ==> converges s l`.
   *
   * A sequence converges where its tail from `N` does. [[Limit.Shifted]] goes the other way and one
   * place at a time; this one comes back from any distance, which is what the ratio test needs,
   * since its hypothesis holds from an index on and what it can sum is the tail from there.
   *
   * The index that answers for `s` is `N + M`, where `M` answers for the tail, and no subtraction
   * is needed to get back: `NUM_LE (N + M) n` **is** `?d. (N + M) + d = n`, so the witness puts
   * `n` at `N + (M + d)` by associativity and the tail's own bound applies at `M + d`.
   */
  def offset(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val s = Term.variable("s", sequences)
    val l = Term.variable("l", values)
    val bound = Term.variable("N", numbers)
    val e = Term.variable("e", values)
    val n = Term.variable("n", numbers)
    val m = Term.variable("m", numbers)
    val d = Term.variable("d", numbers)

    for {
      tail <- kit.term("\\n:num. (s:num -> real) (NUM_ADD (N:num) n)", sequences)
      assumedTail <- kit.assume("converges (\\n:num. (s:num -> real) (NUM_ADD (N:num) n)) (l:real)")
      (premise, assumed) = assumedTail
      unfolded <- Conv.unfold(kit.convergesDefinition, List(tail, l)).flatMap(Limit.normaliseRight)
      body <- LogicError.lift(Kernel.eqMp(unfolded, assumed))
      assumedPositive <- kit.assume("0 < e:real")
      (positive, isPositive) = assumedPositive
      near <- rules.spec(e, body).flatMap(rules.mp(_, isPositive))
      assumedInside <- kit.assume(
        "!n:num. NUM_LE (m:num) n ==> abs ((s:num -> real) (NUM_ADD (N:num) n) - (l:real)) < e:real")
      (_, inside) = assumedInside

      index <- kit.term("NUM_ADD (N:num) (m:num)", numbers)
      assumedGuard <- kit.assume("NUM_LE (NUM_ADD (N:num) (m:num)) (n:num)")
      (guard, past) = assumedGuard
      guardUnfolded <- Conv.unfold(kit.orderDefinition, List(index, n)).flatMap(Limit.normaliseRight)
      gap <- LogicError.lift(Kernel.eqMp(guardUnfolded, past))
      assumedInner <- kit.assume("NUM_ADD (NUM_ADD (N:num) (m:num)) (d:num) = n:num")
      (_, inner) = assumedInner
      regrouped <- rules.specAll(kit.associative, List(bound, m, d))
      landed <- Conv.sym(regrouped).flatMap(Conv.trans(_, inner))
      further <- kit.term("NUM_ADD (m:num) (d:num)", numbers)
      pastM <- rules.specAll(kit.atMostSum, List(m, d))
      close <- rules.spec(further, inside).flatMap(rules.mp(_, pastM))
      moved <- Limit.rewriteInProposition(landed, close)
      atN <- rules.existsElim(gap, d, moved)

      guarded <- rules.disch(guard, atN).flatMap(rules.gen(n, _))
      witnessed <- kit.exists(
        "?M:num. !n:num. NUM_LE M n ==> abs ((s:num -> real) n - (l:real)) < e:real", index, guarded)
      eliminated <- rules.existsElim(near, m, witnessed)
      whole <- rules.disch(positive, eliminated).flatMap(rules.gen(e, _))
      unfoldedS <- Conv.unfold(kit.convergesDefinition, List(s, l)).flatMap(Limit.normaliseRight)
      folded <- Conv.sym(unfoldedS).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, whole)))
      result <- rules.disch(premise, folded).flatMap(rules.genAll(_, List(s, l, bound)))
    } yield result
  }

  /**
   * [[Limit.TermsVanish]], `|- !f l. converges (Sum f) l ==> converges f 0`.
   *
   * The terms of a convergent series go to zero. It is four facts in one order: the partial sums
   * read one place later converge to the same limit ([[Limit.Shifted]]), the partial sums negated
   * converge to `-l`, the two added converge to `l + -l`, and at every index that sum **is** the
   * term, by `SUM_SUC`. So the value is `0` by the ring and the sequence is `f` by
   * [[Limit.Eventually]] at index zero. No epsilon is taken here.
   */
  def termsVanish(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val f = Term.variable("f", sequences)
    val l = Term.variable("l", values)
    val n = Term.variable("n", numbers)

    for {
      assumedSeries <- kit.assume("converges (Sum (f:num -> real)) (l:real)")
      (premise, assumed) = assumedSeries
      partial <- kit.term("Sum (f:num -> real)", sequences)
      later <- rules.specAll(kit.shifted, List(partial, l)).flatMap(rules.mp(_, assumed))
      laterParts <- Limit.convergenceOf(later)
      turned <- rules.specAll(kit.negated, List(partial, l)).flatMap(rules.mp(_, assumed))
      turnedParts <- Limit.convergenceOf(turned)
      together <- rules
        .specAll(kit.added, List(laterParts._1, turnedParts._1, l, turnedParts._2))
        .flatMap(rules.mp(_, later))
        .flatMap(rules.mp(_, turned))
        .flatMap(Limit.normalised)
      togetherParts <- Limit.convergenceOf(together)
      zero <- kit.term("0:real", values)
      vanishes <- LogicError.lift(Term.eq(togetherParts._2, zero)).flatMap(kit.ring.prove)
      atZero <- Limit.rewriteWith(vanishes, together)

      step <- rules.specAll(kit.sumAtSuccessor, List(f, n))
      sides <- Limit.destructEquation(step)
      peel <- kit.linarith.prove("!a:real. !b:real. !c:real. a = b + c ==> a + -b = c")
      atN <- sides._2 match {
        case App(App(_, shorter), term) =>
          rules.specAll(peel, List(sides._1, shorter, term)).flatMap(rules.mp(_, step))
        case other => Left(NotOfForm("a sum of two", other))
      }
      guard <- kit.proposition("NUM_LE ZERO (n:num)")
      agreeing <- rules.disch(guard, atN).flatMap(rules.gen(n, _))
      indexZero <- kit.term("ZERO", numbers)
      carried <- rules
        .specAll(kit.eventually, List(togetherParts._1, f, zero, indexZero))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, agreeing))
        .flatMap(rules.mp(_, atZero))
      result <- rules.disch(premise, carried).flatMap(rules.genAll(_, List(f, l)))
    } yield result
  }

  /**
   * [[Limit.TermTest]], `|- !f b N. 0 < b ==> (!n. NUM_LE N n ==> b <= abs (f n)) ==> diverges (Sum f)`.
   *
   * The contrapositive of [[termsVanish]], stated with the bound a caller has rather than with a
   * failure of `converges f 0`, which nobody holds: terms that stay a fixed distance from zero past
   * an index cannot vanish, so the series cannot converge. The distance is the tolerance, and the
   * index where the vanishing and the bound meet is `M + N`, a sum rather than a maximum for the
   * reason `Limit.Unique` gives.
   *
   * The conclusion is reached by refuting the convergence, since `diverges` is a negation, and it
   * takes no supremum: `CriteriaSpec` asserts that `COMPLETENESS` is not among what it rests on,
   * which is the difference between reading a divergence off the terms and obtaining a limit.
   */
  def termTest(kit: Kit, vanishing: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val f = Term.variable("f", sequences)
    val b = Term.variable("b", values)
    val l = Term.variable("l", values)
    val bound = Term.variable("N", numbers)
    val m = Term.variable("m", numbers)

    for {
      assumedPositive <- kit.assume("0 < b:real")
      (positive, isPositive) = assumedPositive
      assumedAway <- kit.assume("!n:num. NUM_LE (N:num) n ==> b:real <= abs ((f:num -> real) n)")
      (away, isAway) = assumedAway
      assumedConverging <- kit.assume("?l:real. converges (Sum (f:num -> real)) l")
      (converging, isConverging) = assumedConverging
      assumedAtL <- kit.assume("converges (Sum (f:num -> real)) (l:real)")
      (_, atL) = assumedAtL

      toZero <- rules.specAll(vanishing, List(f, l)).flatMap(rules.mp(_, atL))
      zero <- kit.term("0:real", values)
      unfolded <- Conv.unfold(kit.convergesDefinition, List(f, zero)).flatMap(Limit.normaliseRight)
      body <- LogicError.lift(Kernel.eqMp(unfolded, toZero))
      near <- rules.spec(b, body).flatMap(rules.mp(_, isPositive))
      assumedInside <- kit.assume("!n:num. NUM_LE (m:num) n ==> abs ((f:num -> real) n - 0) < b:real")
      (_, inside) = assumedInside

      index <- kit.term("NUM_ADD (m:num) (N:num)", numbers)
      pastM <- rules.specAll(kit.atMostSum, List(m, bound))
      pastN <- for {
        other <- rules.specAll(kit.atMostSum, List(bound, m))
        swap <- rules.specAll(kit.commutative, List(bound, m))
        carried <- Limit.rewriteWith(swap, other)
      } yield carried
      close <- rules.spec(index, inside).flatMap(rules.mp(_, pastM))
      far <- rules.spec(index, isAway).flatMap(rules.mp(_, pastN))

      // `abs (x - 0)` and `abs x` are two atoms to LINARITH, so the subtraction goes first.
      term <- kit.term("(f:num -> real) (NUM_ADD (m:num) (N:num))", values)
      difference <- kit.term("(f:num -> real) (NUM_ADD (m:num) (N:num)) - 0", values)
      plain <- LogicError.lift(Term.eq(difference, term)).flatMap(kit.ring.prove)
      closePlain <- Limit.rewriteInProposition(plain, close)
      size <- kit.term("abs ((f:num -> real) (NUM_ADD (m:num) (N:num)))", values)
      denial <- kit.linarith
        .prove("!a:real. !c:real. a < c ==> ~(c <= a)")
        .flatMap(rules.specAll(_, List(size, b)))
        .flatMap(rules.mp(_, closePlain))
      absurd <- rules.notElim(denial, far)
      overM <- rules.existsElim(near, m, absurd)
      overL <- rules.existsElim(isConverging, l, overM)
      refuted <- rules.notIntro(converging, overL)

      series <- kit.term("Sum (f:num -> real)", sequences)
      folded <- Conv
        .unfold(kit.divergesDefinition, List(series))
        .flatMap(Limit.normaliseRight)
        .flatMap(Conv.sym)
        .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, refuted)))
      result <- rules
        .disch(away, folded)
        .flatMap(rules.disch(positive, _))
        .flatMap(rules.genAll(_, List(f, b, bound)))
    } yield result
  }

  /**
   * `|- !c. 0 < c ==> c < 1 ==> converges (\n. Power c n) 0`, which [[powersVanish]] spends.
   *
   * **No Archimedean step and no logarithm**, which is the route worth knowing. The powers of `c`
   * decrease and stay positive, so they converge, by monotone convergence applied to their
   * negations; and a limit `L` of `c^n` is also a limit of `c^(n + 1) = c * c^n`, so `L = c * L` by
   * uniqueness, and with `c < 1` and `L >= 0` that leaves `L = 0`. The textbook route bounds
   * `c^n` by `1 / (n * (1/c - 1))` through Bernoulli's inequality and then needs the naturals to be
   * unbounded in the reals, which `Peano.NUM_ARCHIMEDES` provides and this does not need.
   *
   * Two products are formed by hand with `LT_MUL` before LINARITH is asked anything, and that is a
   * measurement rather than caution: asked `0 < p ==> c < 1 ==> q = c * p ==> -p <= -q` directly,
   * LINARITH ran out of its fact budget (64 against 48), and asked `x = c * x ==> ~(0 < (1 - c) * x)`
   * it refused with a message about RING, which is the defect named where it is used below.
   */
  private def powerOfAFraction(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val c = Term.variable("c", values)
    val n = Term.variable("n", numbers)
    val big = Term.variable("L", values)

    for {
      assumedPositive <- kit.assume("0 < c:real")
      (positive, isPositive) = assumedPositive
      assumedBelow <- kit.assume("c:real < 1")
      (below, isBelow) = assumedBelow
      powers <- kit.term("\\n:num. Power (c:real) n", sequences)
      turned <- kit.term("\\n:num. -(Power (c:real) n)", sequences)
      powerAt <- kit.term("Power (c:real) (n:num)", values)
      nextAt <- kit.term("Power (c:real) (SUC (n:num))", values)
      zero <- kit.term("0:real", values)
      gap <- kit.term("1 - (c:real)", values)

      everyPositive <- rules.spec(c, kit.powerPositive).flatMap(rules.mp(_, isPositive))
      positiveAt <- rules.spec(n, everyPositive)
      gapPositive <- kit.linarith
        .prove("!c:real. c < 1 ==> 0 < 1 - c")
        .flatMap(rules.spec(c, _))
        .flatMap(rules.mp(_, isBelow))

      /* ---- the negated powers increase and are bounded, so they converge ---- */

      next <- rules.specAll(kit.powerAtSuccessor, List(c, n))
      shrinkage <- rules
        .conjIntro(gapPositive, positiveAt)
        .flatMap(both => rules.specAll(kit.productPositive, List(gap, powerAt)).flatMap(rules.mp(_, both)))
      increasingAt <- kit.linarith
        .prove("!c:real. !p:real. !q:real. 0 < (1 - c) * p ==> q = c * p ==> -p <= -q")
        .flatMap(rules.specAll(_, List(c, powerAt, nextAt)))
        .flatMap(rules.mp(_, shrinkage))
        .flatMap(rules.mp(_, next))
      increasing <- rules.gen(n, increasingAt)
      capped <- kit.linarith
        .prove("!p:real. 0 < p ==> -p <= 0")
        .flatMap(rules.spec(powerAt, _))
        .flatMap(rules.mp(_, positiveAt))
        .flatMap(rules.gen(n, _))
      boundedAbove <- kit.exists("?b:real. !n:num. -(Power (c:real) n) <= b", zero, capped)
      somewhere <- rules
        .spec(turned, kit.monotoneConverges)
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, increasing))
        .flatMap(rules.mp(_, boundedAbove))

      assumedAtL <- kit.assume("converges (\\n:num. -(Power (c:real) n)) (L:real)")
      (_, atL) = assumedAtL
      back <- rules
        .specAll(kit.negated, List(turned, big))
        .flatMap(rules.mp(_, atL))
        .flatMap(Limit.normalised)
      backParts <- Limit.convergenceOf(back)
      limitValue = backParts._2
      indexZero <- kit.term("ZERO", numbers)
      guard <- kit.proposition("NUM_LE ZERO (n:num)")
      doubled <- kit.term("--(Power (c:real) (n:num))", values)
      undone <- LogicError.lift(Term.eq(doubled, powerAt)).flatMap(kit.ring.prove)
      agree <- rules.disch(guard, undone).flatMap(rules.gen(n, _))
      plain <- rules
        .specAll(kit.eventually, List(backParts._1, powers, limitValue, indexZero))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, agree))
        .flatMap(rules.mp(_, back))

      /* ---- the limit is its own multiple by c ---- */

      later <- rules
        .specAll(kit.shifted, List(powers, limitValue))
        .flatMap(rules.mp(_, plain))
        .flatMap(Limit.normalised)
      laterParts <- Limit.convergenceOf(later)
      steady <- rules.spec(c, kit.constant)
      steadyParts <- Limit.convergenceOf(steady)
      scaled <- rules
        .specAll(kit.multiplied, List(steadyParts._1, powers, c, limitValue))
        .flatMap(rules.mp(_, steady))
        .flatMap(rules.mp(_, plain))
        .flatMap(Limit.normalised)
      scaledParts <- Limit.convergenceOf(scaled)
      movedAgree <- rules.disch(guard, next).flatMap(rules.gen(n, _))
      scaledToL <- rules
        .specAll(kit.eventually, List(laterParts._1, scaledParts._1, limitValue, indexZero))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, movedAgree))
        .flatMap(rules.mp(_, later))
      same <- rules
        .specAll(kit.unique, List(scaledParts._1, limitValue, scaledParts._2))
        .flatMap(rules.mp(_, scaledToL))
        .flatMap(rules.mp(_, scaled))

      /* ---- and it is not negative and not positive ---- */

      nonNegativeAt <- rules.specAll(kit.leOfLt, List(zero, powerAt)).flatMap(rules.mp(_, positiveAt))
      nonNegativeFrom <- rules.disch(guard, nonNegativeAt).flatMap(rules.gen(n, _))
      atLeastZero <- rules
        .specAll(kit.aboveBound, List(powers, limitValue, zero, indexZero))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, plain))
        .flatMap(rules.mp(_, nonNegativeFrom))
      positiveLimit <- rules.specAll(kit.leOfLt, List(zero, limitValue)).flatMap(instance =>
        kit.logic.destImp(instance.conclusion).map(_._1).toRight(NotOfForm("an implication", instance.conclusion)))
      assumedPositiveLimit <- LogicError.lift(Kernel.assume(positiveLimit))
      wouldShrink <- rules
        .conjIntro(gapPositive, assumedPositiveLimit)
        .flatMap(both => rules.specAll(kit.productPositive, List(gap, limitValue)).flatMap(rules.mp(_, both)))
      // The multiple is named `y` rather than written `x = c * x`. Measured on 2026-09-25: LINARITH
      // refuses an equation whose left side occurs inside its right side, with a message about RING
      // that names neither the goal nor the cause, and it takes the same content in this form.
      multiple <- Limit.rightOf(same)
      impossible <- kit.linarith
        .prove("!c:real. !x:real. !y:real. y = c * x ==> x = y ==> ~(0 < (1 - c) * x)")
        .flatMap(rules.specAll(_, List(c, limitValue, multiple)))
        .flatMap(rules.mp(_, Conv.refl(multiple)))
        .flatMap(rules.mp(_, same))
      absurd <- rules.notElim(impossible, wouldShrink)
      notPositive <- rules.notIntro(positiveLimit, absurd)
      notAbove <- rules.specAll(kit.leOfNotLt, List(zero, limitValue)).flatMap(rules.mp(_, notPositive))
      isZero <- rules
        .specAll(kit.antisymmetric, List(limitValue, zero))
        .flatMap(rules.mp(_, notAbove))
        .flatMap(rules.mp(_, atLeastZero))
      atZero <- Limit.rewriteWith(isZero, plain)
      settled <- rules.existsElim(somewhere, big, atZero)
      result <- rules
        .disch(below, settled)
        .flatMap(rules.disch(positive, _))
        .flatMap(rules.gen(c, _))
    } yield result
  }

  /**
   * [[Limit.PowersVanish]], `|- !q. abs q < 1 ==> converges (\n. Power q n) 0`.
   *
   * [[powerOfAFraction]] at `(1 + abs q) / 2`, which is positive where `abs q` need not be, and a
   * squeeze under it: `Limit.ABS_POWER_LE` puts `abs (q^n)` under that number's powers. Going
   * through a positive stand-in is what spares a case split on `q = 0`, where the powers are `1`
   * and then `0` and `POWER_POSITIVE` has nothing to say.
   */
  def powersVanish(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val q = Term.variable("q", values)
    val n = Term.variable("n", numbers)

    for {
      fraction <- powerOfAFraction(kit)
      assumedSmall <- kit.assume("abs (q:real) < 1")
      (small, isSmall) = assumedSmall
      size <- kit.term("abs (q:real)", values)
      middle <- kit.term("(1 + abs (q:real)) / 2", values)
      sizeNonNegative <- rules.spec(q, kit.absNonNegative)
      positive <- kit.linarith
        .prove("!a:real. 0 <= a ==> 0 < (1 + a) / 2")
        .flatMap(rules.spec(size, _))
        .flatMap(rules.mp(_, sizeNonNegative))
      belowOne <- kit.linarith
        .prove("!a:real. a < 1 ==> (1 + a) / 2 < 1")
        .flatMap(rules.spec(size, _))
        .flatMap(rules.mp(_, isSmall))
      under <- kit.linarith
        .prove("!a:real. a < 1 ==> a <= (1 + a) / 2")
        .flatMap(rules.spec(size, _))
        .flatMap(rules.mp(_, isSmall))
      dominating <- rules.spec(middle, fraction).flatMap(rules.mp(_, positive)).flatMap(rules.mp(_, belowOne))
      pointwise <- rules
        .specAll(kit.powerOfAMagnitude, List(q, middle, n))
        .flatMap(rules.mp(_, under))
        .flatMap(rules.gen(n, _))
      powers <- kit.term("\\n:num. Power (q:real) n", sequences)
      bound <- kit.term("\\n:num. Power ((1 + abs (q:real)) / 2) n", sequences)
      vanishing <- rules
        .specAll(kit.squeezed, List(powers, bound))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, pointwise))
        .flatMap(rules.mp(_, dominating))
      result <- rules.disch(small, vanishing).flatMap(rules.gen(q, _))
    } yield result
  }

  /**
   * [[Limit.GeometricConverges]], `|- !q. abs q < 1 ==> converges (Sum (\i. Power q i)) (inv (1 - q))`.
   *
   * **With its value**, which is the first limit of a series this repository names rather than
   * obtains. `SUM_GEOMETRIC` says `(q - 1) * S n = q^n - 1`, so every partial sum is
   * `k + -(k * q^n)` with `k = inv (1 - q)`, and that sequence converges to `k` because the powers
   * vanish. So the comparison test is not used at all: the partial sums are written down and their
   * limit is read off the algebra of limits.
   *
   * Clearing the denominator is the one step with a condition in it, and the condition is paid
   * rather than carried: `1 - q` is positive because `q <= abs q < 1`, so `MUL_INVERSE` applies and
   * `k * ((1 - q) * S) = S` is RING's identity with `(1 - q) * k` rewritten to `1`.
   */
  def geometricConverges(kit: Kit, vanishing: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val q = Term.variable("q", values)
    val n = Term.variable("n", numbers)

    for {
      assumedSmall <- kit.assume("abs (q:real) < 1")
      (small, isSmall) = assumedSmall
      gap <- kit.term("1 - (q:real)", values)
      reciprocal <- kit.term("inv (1 - (q:real))", values)
      size <- kit.term("abs (q:real)", values)
      above <- rules.spec(q, kit.absAbove)
      gapPositive <- kit.linarith
        .prove("!x:real. !a:real. x <= a ==> a < 1 ==> 0 < 1 - x")
        .flatMap(rules.specAll(_, List(q, size)))
        .flatMap(rules.mp(_, above))
        .flatMap(rules.mp(_, isSmall))
      nonZero <- rules.spec(gap, kit.positiveNotZero).flatMap(rules.mp(_, gapPositive))
      cancels <- rules.spec(gap, kit.mulInverse).flatMap(rules.mp(_, nonZero))

      /* ---- the sequence the partial sums are, and its limit ---- */

      powersVanish <- rules.spec(q, vanishing).flatMap(rules.mp(_, isSmall))
      powers <- kit.term("\\n:num. Power (q:real) n", sequences)
      steady <- rules.spec(reciprocal, kit.constant)
      steadyParts <- Limit.convergenceOf(steady)
      zero <- kit.term("0:real", values)
      scaled <- rules
        .specAll(kit.multiplied, List(steadyParts._1, powers, reciprocal, zero))
        .flatMap(rules.mp(_, steady))
        .flatMap(rules.mp(_, powersVanish))
        .flatMap(Limit.normalised)
      scaledParts <- Limit.convergenceOf(scaled)
      turned <- rules
        .specAll(kit.negated, List(scaledParts._1, scaledParts._2))
        .flatMap(rules.mp(_, scaled))
        .flatMap(Limit.normalised)
      turnedParts <- Limit.convergenceOf(turned)
      together <- rules
        .specAll(kit.added, List(steadyParts._1, turnedParts._1, reciprocal, turnedParts._2))
        .flatMap(rules.mp(_, steady))
        .flatMap(rules.mp(_, turned))
        .flatMap(Limit.normalised)
      togetherParts <- Limit.convergenceOf(together)
      valued <- LogicError.lift(Term.eq(togetherParts._2, reciprocal)).flatMap(kit.ring.prove)
      atValue <- Limit.rewriteWith(valued, together)

      /* ---- and it is the partial sums, at every index ---- */

      sumAt <- kit.term("Sum (\\i:num. Power (q:real) i) (n:num)", values)
      powerAt <- kit.term("Power (q:real) (n:num)", values)
      closed <- rules.specAll(kit.geometricSum, List(q, n))
      cleared <- kit.linarith
        .prove("!q:real. !s:real. !p:real. (q - 1) * s = p - 1 ==> (1 - q) * s = 1 - p")
        .flatMap(rules.specAll(_, List(q, sumAt, powerAt)))
        .flatMap(rules.mp(_, closed))
      regrouped <- kit
        .proposition(
          "inv (1 - (q:real)) * ((1 - q) * Sum (\\i:num. Power q i) (n:num)) = " +
            "((1 - q) * inv (1 - q)) * Sum (\\i:num. Power q i) n")
        .flatMap(kit.ring.prove)
      unit <- Limit.rewriteInProposition(cancels, regrouped)
      oneTimes <- kit
        .proposition("1 * Sum (\\i:num. Power (q:real) i) (n:num) = Sum (\\i:num. Power q i) n")
        .flatMap(kit.ring.prove)
      recovered <- Conv.trans(unit, oneTimes)
      substituted <- Limit.rewriteInProposition(cleared, recovered)
      expanded <- kit
        .proposition(
          "inv (1 - (q:real)) * (1 - Power q (n:num)) = inv (1 - q) + -(inv (1 - q) * Power q n)")
        .flatMap(kit.ring.prove)
      pointwise <- Conv.sym(substituted).flatMap(Conv.trans(_, expanded)).flatMap(Conv.sym)
      guard <- kit.proposition("NUM_LE ZERO (n:num)")
      agree <- rules.disch(guard, pointwise).flatMap(rules.gen(n, _))
      series <- kit.term("Sum (\\i:num. Power (q:real) i)", sequences)
      indexZero <- kit.term("ZERO", numbers)
      carried <- rules
        .specAll(kit.eventually, List(togetherParts._1, series, reciprocal, indexZero))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, agree))
        .flatMap(rules.mp(_, atValue))
      result <- rules.disch(small, carried).flatMap(rules.gen(q, _))
    } yield result
  }

  /** `abs (f x) = abs (f y)` from `x = y`, for the sequence `f` of the derivation it is used in. */
  private def magnitudesOf(kit: Kit, indices: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      template <- kit.term("\\x:num. abs ((f:num -> real) x)", Type.fun(numbers, values))
      carried <- Conv.apTerm(template, indices)
      reduced <- Conv.betaSides(carried)
    } yield reduced

  /**
   * `|- !f c N. 0 <= c ==> (!n. NUM_LE N n ==> abs (f (SUC n)) <= c * abs (f n))
   * ==> !k. abs (f (NUM_ADD N k)) <= Power c k * abs (f N)`
   *
   * The ratio bound iterated, which is the whole of what the ratio test knows about a summand. Not
   * published: its one consumer is [[ratioTest]], and a caller holding a ratio bound wants the
   * convergence rather than the estimate.
   */
  private def ratioBound(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val f = Term.variable("f", sequences)
    val c = Term.variable("c", values)
    val bound = Term.variable("N", numbers)

    for {
      assumedNonNegative <- kit.assume("0 <= c:real")
      (nonNegative, isNonNegative) = assumedNonNegative
      assumedRatio <- kit.assume(
        "!n:num. NUM_LE (N:num) n ==> abs ((f:num -> real) (SUC n)) <= c:real * abs (f n)")
      (ratio, hasRatio) = assumedRatio
      statement <- kit.proposition(
        "!k:num. abs ((f:num -> real) (NUM_ADD (N:num) k)) <= Power (c:real) k * abs (f N)")
      chained <- kit.linarith.prove(
        "!a:real. !b:real. !d:real. !c:real. !p:real. " +
          "a <= c * b ==> b * c <= (p * d) * c ==> a <= (c * p) * d")
      unitStatement <- kit.proposition("1 * abs ((f:num -> real) (N:num)) = abs (f N)")

      // The variables are read off the goals the driver hands over, for the reason
      // `Limit.monotoneOrder` gives: a step written with this function's own names proves a
      // statement about two other terms of the same name.
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            collapsed <- rules.spec(bound, kit.addAtZero)
            sameSize <- magnitudesOf(kit, collapsed)
            unit <- kit.ring.prove(unitStatement)
            zeroPower <- rules.spec(c, kit.powerAtZero).flatMap(Conv.sym)
            powered <- Limit.rewriteInProposition(zeroPower, unit).flatMap(Conv.sym)
            joined <- Conv.trans(sameSize, powered)
            result <- kit.weakened(joined).flatMap(kit.landsOn(_, base))
          } yield result,
        step => {
          val k = step.variable
          for {
            opened <- rules.specAll(kit.addAtSuccessor, List(bound, k))
            here <- kit.at("\\x:num. NUM_ADD (N:num) x", k)
            past <- rules.specAll(kit.atMostSum, List(bound, k))
            atStep <- rules.spec(here, hasRatio).flatMap(rules.mp(_, past))
            ahead <- kit.at("\\x:num. abs ((f:num -> real) (SUC x))", here)
            current <- kit.at("\\x:num. abs ((f:num -> real) x)", here)
            first <- kit.at("\\x:num. abs ((f:num -> real) x)", bound)
            power <- kit.at("\\x:num. Power (c:real) x", k)
            product <- kit.at("\\x:num. Power (c:real) x * abs ((f:num -> real) (N:num))", k)
            scaledUp <- rules
              .specAll(kit.multiplyLe, List(c, current, product))
              .flatMap(rules.mp(_, isNonNegative))
              .flatMap(rules.mp(_, step.hypothesis))
            combined <- rules
              .specAll(chained, List(ahead, current, first, c, power))
              .flatMap(rules.mp(_, atStep))
              .flatMap(rules.mp(_, scaledUp))
            nextPower <- rules.specAll(kit.powerAtSuccessor, List(c, k)).flatMap(Conv.sym)
            powered <- Limit.rewriteInProposition(nextPower, combined)
            back <- Conv.sym(opened)
            result <- Limit.rewriteInProposition(back, powered).flatMap(kit.landsOn(_, step.goal))
          } yield result
        }
      )
      result <- rules
        .disch(ratio, proved)
        .flatMap(rules.disch(nonNegative, _))
        .flatMap(rules.genAll(_, List(f, c, bound)))
    } yield result
  }

  /**
   * [[Limit.RatioTest]],
   * `|- !f r N. 0 <= r ==> r < 1 ==> (!n. NUM_LE N n ==> abs (f (SUC n)) <= r * abs (f n))
   * ==> ?l. converges (Sum f) l`.
   *
   * The route, in the order the derivation takes it:
   *
   *  - the ratio is widened from `r` to `c = (1 + r) / 2`, which is positive where `r` need not be,
   *    so that `POWER_POSITIVE` applies to its powers;
   *  - [[ratioBound]] puts every term of the tail from `N` under `c^k * abs (f N)`;
   *  - the tail's magnitudes are therefore under a scaled geometric series, whose partial sums sit
   *    under `inv (1 - c) * abs (f N)` by [[geometricConverges]] and `SUM_BELOW_LIMIT`, so the
   *    comparison test makes the tail absolutely convergent and `CONVERGES_ABSOLUTE` makes it
   *    convergent;
   *  - the series is its head plus its tail, `SUM_REINDEX`, so the partial sums from `N` on
   *    converge, and [[offset]] carries that to the whole series.
   *
   * The hypothesis is from an index on and not everywhere, which is what makes it usable: a ratio
   * that settles below one only past a point is the ordinary case, and the exponential's is.
   */
  def ratioTest(kit: Kit, geometric: Kernel.Thm, offsetFact: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val f = Term.variable("f", sequences)
    val r = Term.variable("r", values)
    val bound = Term.variable("N", numbers)
    val n = Term.variable("n", numbers)
    val i = Term.variable("i", numbers)
    val l = Term.variable("l", values)
    val m = Term.variable("m", values)

    for {
      bounded <- ratioBound(kit)
      assumedNonNegative <- kit.assume("0 <= r:real")
      (nonNegative, isNonNegative) = assumedNonNegative
      assumedBelow <- kit.assume("r:real < 1")
      (below, isBelow) = assumedBelow
      assumedRatio <- kit.assume(
        "!n:num. NUM_LE (N:num) n ==> abs ((f:num -> real) (SUC n)) <= r:real * abs (f n)")
      (ratio, hasRatio) = assumedRatio
      zero <- kit.term("0:real", values)

      /* ---- the ratio at c ---- */

      c <- kit.term("(1 + (r:real)) / 2", values)
      cPositive <- kit.linarith
        .prove("!r:real. 0 <= r ==> 0 < (1 + r) / 2")
        .flatMap(rules.spec(r, _))
        .flatMap(rules.mp(_, isNonNegative))
      cNonNegative <- rules.specAll(kit.leOfLt, List(zero, c)).flatMap(rules.mp(_, cPositive))
      cBelow <- kit.linarith
        .prove("!r:real. r < 1 ==> (1 + r) / 2 < 1")
        .flatMap(rules.spec(r, _))
        .flatMap(rules.mp(_, isBelow))
      rUnder <- kit.linarith
        .prove("!r:real. r < 1 ==> r <= (1 + r) / 2")
        .flatMap(rules.spec(r, _))
        .flatMap(rules.mp(_, isBelow))

      assumedGuard <- kit.assume("NUM_LE (N:num) (n:num)")
      (guard, isPast) = assumedGuard
      atR <- rules.spec(n, hasRatio).flatMap(rules.mp(_, isPast))
      termAt <- kit.term("(f:num -> real) (n:num)", values)
      size <- kit.term("abs ((f:num -> real) (n:num))", values)
      ahead <- kit.term("abs ((f:num -> real) (SUC (n:num)))", values)
      sizeNonNegative <- rules.spec(termAt, kit.absNonNegative)
      widened <- rules
        .specAll(kit.multiplyLe, List(size, r, c))
        .flatMap(rules.mp(_, sizeNonNegative))
        .flatMap(rules.mp(_, rUnder))
      atC <- kit.linarith
        .prove("!a:real. !b:real. !r:real. !c:real. a <= r * b ==> r * b <= c * b ==> a <= c * b")
        .flatMap(rules.specAll(_, List(ahead, size, r, c)))
        .flatMap(rules.mp(_, atR))
        .flatMap(rules.mp(_, widened))
      ratioAtC <- rules.disch(guard, atC).flatMap(rules.gen(n, _))
      pointwise <- rules
        .specAll(bounded, List(f, c, bound))
        .flatMap(rules.mp(_, cNonNegative))
        .flatMap(rules.mp(_, ratioAtC))

      /* ---- the geometric series at c bounds the tail's magnitudes ---- */

      cSize <- rules.spec(c, kit.absOfNonNegative).flatMap(rules.mp(_, cNonNegative)).flatMap(Conv.sym)
      cSmall <- Limit.rewriteInProposition(cSize, cBelow)
      geometricAtC <- rules.spec(c, geometric).flatMap(rules.mp(_, cSmall))
      powers <- kit.term("\\i:num. Power ((1 + (r:real)) / 2) i", sequences)
      reciprocal <- kit.term("inv (1 - (1 + (r:real)) / 2)", values)
      powerAt <- kit.term("Power ((1 + (r:real)) / 2) (i:num)", values)
      powersNonNegative <- rules
        .spec(c, kit.powerPositive)
        .flatMap(rules.mp(_, cPositive))
        .flatMap(rules.spec(i, _))
        .flatMap(p => rules.specAll(kit.leOfLt, List(zero, powerAt)).flatMap(rules.mp(_, p)))
        .flatMap(rules.gen(i, _))
      underLimit <- rules
        .specAll(kit.belowLimit, List(powers, reciprocal))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, powersNonNegative))
        .flatMap(rules.mp(_, geometricAtC))

      first <- kit.term("abs ((f:num -> real) (N:num))", values)
      firstTerm <- kit.term("(f:num -> real) (N:num)", values)
      firstNonNegative <- rules.spec(firstTerm, kit.absNonNegative)
      partial <- kit.term("Sum (\\i:num. Power ((1 + (r:real)) / 2) i) (n:num)", values)
      scaledBound <- rules
        .spec(n, underLimit)
        .flatMap(atN =>
          rules
            .specAll(kit.multiplyLe, List(first, partial, reciprocal))
            .flatMap(rules.mp(_, firstNonNegative))
            .flatMap(rules.mp(_, atN)))
      scaleBack <- rules.specAll(kit.scaledRight, List(first, powers, n)).flatMap(Limit.normalised).flatMap(Conv.sym)
      tailBound <- Limit.rewriteInProposition(scaleBack, scaledBound).flatMap(rules.gen(n, _))
      witness <- kit.term("inv (1 - (1 + (r:real)) / 2) * abs ((f:num -> real) (N:num))", values)
      boundedTail <- kit.exists(
        "?b:real. !n:num. Sum (\\i:num. Power ((1 + (r:real)) / 2) i * abs ((f:num -> real) (N:num))) n <= b",
        witness,
        tailBound)
      magnitudes <- kit.term("\\i:num. abs ((f:num -> real) (NUM_ADD (N:num) i))", sequences)
      dominating <- kit.term(
        "\\i:num. Power ((1 + (r:real)) / 2) i * abs ((f:num -> real) (N:num))", sequences)
      tailTerm <- kit.term("(f:num -> real) (NUM_ADD (N:num) (i:num))", values)
      magnitudesNonNegative <- rules.spec(tailTerm, kit.absNonNegative).flatMap(rules.gen(i, _))
      compared <- rules
        .specAll(kit.comparison, List(magnitudes, dominating))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, magnitudesNonNegative))
        .flatMap(rules.mp(_, pointwise))
        .flatMap(rules.mp(_, boundedTail))

      /* ---- so the tail converges, and the series is its head plus its tail ---- */

      tail <- kit.term("\\i:num. (f:num -> real) (NUM_ADD (N:num) i)", sequences)
      assumedAbs <- kit.assume("converges (Sum (\\i:num. abs ((f:num -> real) (NUM_ADD (N:num) i)))) (l:real)")
      (_, absAt) = assumedAbs
      tailConverges <- rules.specAll(kit.absolute, List(tail, l)).flatMap(Limit.normalised).flatMap(rules.mp(_, absAt))
      assumedTail <- kit.assume("converges (Sum (\\i:num. (f:num -> real) (NUM_ADD (N:num) i))) (m:real)")
      (_, tailAt) = assumedTail
      head <- kit.term("Sum (f:num -> real) (N:num)", values)
      steady <- rules.spec(head, kit.constant)
      steadyParts <- Limit.convergenceOf(steady)
      tailSeries <- kit.term("Sum (\\i:num. (f:num -> real) (NUM_ADD (N:num) i))", sequences)
      together <- rules
        .specAll(kit.added, List(steadyParts._1, tailSeries, head, m))
        .flatMap(rules.mp(_, steady))
        .flatMap(rules.mp(_, tailAt))
        .flatMap(Limit.normalised)
      togetherParts <- Limit.convergenceOf(together)
      reindexed <- rules.specAll(kit.reindex, List(f, bound, n))
      sides <- Limit.destructEquation(reindexed)
      difference <- sides._2 match {
        case App(App(_, whole), shorter) => Right((whole, shorter))
        case other => Left(NotOfForm("a difference", other))
      }
      split <- kit.linarith
        .prove("!s:real. !t:real. !a:real. s = t - a ==> a + s = t")
        .flatMap(rules.specAll(_, List(sides._1, difference._1, difference._2)))
        .flatMap(rules.mp(_, reindexed))
      guardZero <- kit.proposition("NUM_LE ZERO (n:num)")
      agree <- rules.disch(guardZero, split).flatMap(rules.gen(n, _))
      indexZero <- kit.term("ZERO", numbers)
      fromN <- kit.term("\\n:num. Sum (f:num -> real) (NUM_ADD (N:num) n)", sequences)
      carried <- rules
        .specAll(kit.eventually, List(togetherParts._1, fromN, togetherParts._2, indexZero))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, agree))
        .flatMap(rules.mp(_, together))
      series <- kit.term("Sum (f:num -> real)", sequences)
      whole <- rules
        .specAll(offsetFact, List(series, togetherParts._2, bound))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, carried))
      claim <- kit.exists("?l:real. converges (Sum (f:num -> real)) l", togetherParts._2, whole)
      overM <- rules.existsElim(tailConverges, m, claim)
      overL <- rules.existsElim(compared, l, overM)
      result <- rules
        .disch(ratio, overL)
        .flatMap(rules.disch(below, _))
        .flatMap(rules.disch(nonNegative, _))
        .flatMap(rules.genAll(_, List(f, r, bound)))
    } yield result
  }

  /**
   * [[Limit.RatioDiverges]],
   * `|- !f N. ~(f N = 0) ==> (!n. NUM_LE N n ==> abs (f n) <= abs (f (SUC n))) ==> diverges (Sum f)`.
   *
   * The other side of the ratio test, stated at ratio one rather than at a ratio `r >= 1`, because
   * one is the weakest: a caller holding `r * abs (f n) <= abs (f (SUC n))` with `1 <= r` has this
   * hypothesis by one linear step. The magnitudes never shrink past `N`, so they stay at
   * `abs (f N)`, which is positive, and [[termTest]] closes it.
   *
   * The positivity is the one place a case split happens, on the three cases of the order: LINARITH
   * does not read a denied equation among its hypotheses, so `0 <= a` with `~(a = 0)` is not a
   * goal it takes, and the trichotomy is.
   */
  def ratioDiverges(kit: Kit, termTestFact: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val f = Term.variable("f", sequences)
    val bound = Term.variable("N", numbers)
    val n = Term.variable("n", numbers)
    val d = Term.variable("d", numbers)

    for {
      assumedNonZero <- kit.assume("~((f:num -> real) (N:num) = 0)")
      (nonZero, isNonZero) = assumedNonZero
      assumedGrowing <- kit.assume("!n:num. NUM_LE (N:num) n ==> abs ((f:num -> real) n) <= abs (f (SUC n))")
      (growing, isGrowing) = assumedGrowing
      statement <- kit.proposition("!k:num. abs ((f:num -> real) (N:num)) <= abs (f (NUM_ADD N k))")
      transitive <- kit.linarith.prove("!a:real. !b:real. !c:real. a <= b ==> b <= c ==> a <= c")

      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            collapsed <- rules.spec(bound, kit.addAtZero)
            sameSize <- magnitudesOf(kit, collapsed).flatMap(Conv.sym)
            result <- kit.weakened(sameSize).flatMap(kit.landsOn(_, base))
          } yield result,
        step => {
          val k = step.variable
          for {
            opened <- rules.specAll(kit.addAtSuccessor, List(bound, k))
            here <- kit.at("\\x:num. NUM_ADD (N:num) x", k)
            past <- rules.specAll(kit.atMostSum, List(bound, k))
            grows <- rules.spec(here, isGrowing).flatMap(rules.mp(_, past))
            first <- kit.at("\\x:num. abs ((f:num -> real) x)", bound)
            current <- kit.at("\\x:num. abs ((f:num -> real) x)", here)
            ahead <- kit.at("\\x:num. abs ((f:num -> real) (SUC x))", here)
            chained <- rules
              .specAll(transitive, List(first, current, ahead))
              .flatMap(rules.mp(_, step.hypothesis))
              .flatMap(rules.mp(_, grows))
            back <- Conv.sym(opened)
            result <- Limit.rewriteInProposition(back, chained).flatMap(kit.landsOn(_, step.goal))
          } yield result
        }
      )

      /* ---- so every magnitude past N is at least the first ---- */

      assumedGuard <- kit.assume("NUM_LE (N:num) (n:num)")
      (guard, isPast) = assumedGuard
      unfolded <- Conv.unfold(kit.orderDefinition, List(bound, n)).flatMap(Limit.normaliseRight)
      gap <- LogicError.lift(Kernel.eqMp(unfolded, isPast))
      assumedInner <- kit.assume("NUM_ADD (N:num) (d:num) = n:num")
      (_, inner) = assumedInner
      landed <- rules.spec(d, proved).flatMap(Limit.rewriteInProposition(inner, _))
      away <- rules.existsElim(gap, d, landed).flatMap(rules.disch(guard, _)).flatMap(rules.gen(n, _))

      /* ---- and the first is positive ---- */

      first <- kit.term("abs ((f:num -> real) (N:num))", values)
      atN <- kit.term("(f:num -> real) (N:num)", values)
      assumedZeroSize <- kit.assume("abs ((f:num -> real) (N:num)) = 0")
      (zeroSize, isZeroSize) = assumedZeroSize
      sizeNonZero <- rules
        .spec(atN, kit.absZero)
        .flatMap(rules.mp(_, isZeroSize))
        .flatMap(rules.notElim(isNonZero, _))
        .flatMap(rules.notIntro(zeroSize, _))
      sizeNonNegative <- rules.spec(atN, kit.absNonNegative)
      zero <- kit.term("0:real", values)
      cases <- rules.specAll(kit.total, List(zero, first))
      goal <- kit.proposition("0 < abs ((f:num -> real) (N:num))")
      assumedEqual <- kit.assume("0 = abs ((f:num -> real) (N:num))")
      (_, isEqual) = assumedEqual
      assumedBelowZero <- kit.assume("abs ((f:num -> real) (N:num)) < 0")
      (_, isBelowZero) = assumedBelowZero
      fromEqual <- Conv
        .sym(isEqual)
        .flatMap(rules.notElim(sizeNonZero, _))
        .flatMap(rules.falsityElim(goal, _))
      fromBelow <- kit.linarith
        .prove("!a:real. 0 <= a ==> ~(a < 0)")
        .flatMap(rules.spec(first, _))
        .flatMap(rules.mp(_, sizeNonNegative))
        .flatMap(rules.notElim(_, isBelowZero))
        .flatMap(rules.falsityElim(goal, _))
      assumedGoal <- LogicError.lift(Kernel.assume(goal))
      otherCases <- kit.assume("0 = abs ((f:num -> real) (N:num)) \\/ abs (f N) < 0")
      (_, isOther) = otherCases
      absurdCases <- rules.disjElim(isOther, fromEqual, fromBelow)
      positive <- rules.disjElim(cases, assumedGoal, absurdCases)

      series <- rules
        .specAll(termTestFact, List(f, first, bound))
        .flatMap(rules.mp(_, positive))
        .flatMap(rules.mp(_, away))
      result <- rules
        .disch(growing, series)
        .flatMap(rules.disch(nonZero, _))
        .flatMap(rules.genAll(_, List(f, bound)))
    } yield result
  }

  /**
   * [[Limit.GeometricDiverges]], `|- !q. 1 <= abs q ==> diverges (Sum (\i. Power q i))`.
   *
   * [[ratioDiverges]] at index zero: the first term is `1`, and each magnitude is `abs q` times the
   * one before, which is at least the one before. With [[geometricConverges]] it decides the
   * geometric series at every ratio, and that pair is what the procedure in `Convergence` reads a
   * geometric summand against.
   */
  def geometricDiverges(kit: Kit, growing: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val q = Term.variable("q", values)
    val n = Term.variable("n", numbers)

    for {
      assumedLarge <- kit.assume("1 <= abs (q:real)")
      (large, isLarge) = assumedLarge
      powers <- kit.term("\\i:num. Power (q:real) i", sequences)
      indexZero <- kit.term("ZERO", numbers)
      instance <- rules.specAll(growing, List(powers, indexZero)).flatMap(Limit.normalised)
      zeroPower <- rules.spec(q, kit.powerAtZero).flatMap(Conv.sym)
      startNonZero <- kit.linarith
        .prove("~((1:real) = 0)")
        .flatMap(Limit.rewriteInProposition(zeroPower, _))

      powerAt <- kit.term("Power (q:real) (n:num)", values)
      size <- kit.term("abs (Power (q:real) (n:num))", values)
      qSize <- kit.term("abs (q:real)", values)
      one <- kit.term("1:real", values)
      product <- kit.term("abs (q:real) * abs (Power (q:real) (n:num))", values)
      sizeNonNegative <- rules.spec(powerAt, kit.absNonNegative)
      scaled <- rules
        .specAll(kit.multiplyLe, List(size, one, qSize))
        .flatMap(rules.mp(_, sizeNonNegative))
        .flatMap(rules.mp(_, isLarge))
      grown <- kit.linarith
        .prove("!a:real. !b:real. 1 * a <= b ==> a <= b")
        .flatMap(rules.specAll(_, List(size, product)))
        .flatMap(rules.mp(_, scaled))
      asProduct <- rules
        .specAll(kit.absMultiplicative, List(q, powerAt))
        .flatMap(Conv.sym)
        .flatMap(Limit.rewriteInProposition(_, grown))
      asPower <- rules
        .specAll(kit.powerAtSuccessor, List(q, n))
        .flatMap(Conv.sym)
        .flatMap(Limit.rewriteInProposition(_, asProduct))
      guard <- kit.proposition("NUM_LE ZERO (n:num)")
      growth <- rules.disch(guard, asPower).flatMap(rules.gen(n, _))
      series <- rules.mp(instance, startNonZero).flatMap(rules.mp(_, growth))
      result <- rules.disch(large, series).flatMap(rules.gen(q, _))
    } yield result
  }

  /**
   * [[Limit.ScaleConverges]], `|- !f c l. converges (Sum f) l ==> converges (Sum (\i. c * f i)) (c * l)`.
   *
   * A constant factor comes out of a series and out of its limit. It is `CONVERGES_MUL` at the
   * constant sequence with `SUM_SCALE` turning the product of `c` and a partial sum into a partial
   * sum of the products, and it is published because the procedure in `Convergence` reads a
   * summand as a constant times a shape it knows, and needs to put the constant back.
   */
  def scaleConverges(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val f = Term.variable("f", sequences)
    val c = Term.variable("c", values)
    val l = Term.variable("l", values)
    val n = Term.variable("n", numbers)

    for {
      assumedSeries <- kit.assume("converges (Sum (f:num -> real)) (l:real)")
      (premise, assumed) = assumedSeries
      steady <- rules.spec(c, kit.constant)
      steadyParts <- Limit.convergenceOf(steady)
      partial <- kit.term("Sum (f:num -> real)", sequences)
      product <- rules
        .specAll(kit.multiplied, List(steadyParts._1, partial, c, l))
        .flatMap(rules.mp(_, steady))
        .flatMap(rules.mp(_, assumed))
        .flatMap(Limit.normalised)
      productParts <- Limit.convergenceOf(product)
      pointwise <- rules.specAll(kit.scaled, List(c, f, n)).flatMap(Limit.normalised).flatMap(Conv.sym)
      guard <- kit.proposition("NUM_LE ZERO (n:num)")
      agree <- rules.disch(guard, pointwise).flatMap(rules.gen(n, _))
      series <- kit.term("Sum (\\i:num. (c:real) * (f:num -> real) i)", sequences)
      indexZero <- kit.term("ZERO", numbers)
      carried <- rules
        .specAll(kit.eventually, List(productParts._1, series, productParts._2, indexZero))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, agree))
        .flatMap(rules.mp(_, product))
      result <- rules.disch(premise, carried).flatMap(rules.genAll(_, List(f, c, l)))
    } yield result
  }

  /**
   * [[Limit.ScaleDiverges]], `|- !f c. ~(c = 0) ==> diverges (Sum f) ==> diverges (Sum (\i. c * f i))`.
   *
   * The other direction, and the condition is the one it needs: were the scaled series to converge,
   * [[scaleConverges]] at `inv c` would give back a convergence of `Sum f`, since
   * `inv c * (c * f i) = f i` wherever `c` is not zero. At `c = 0` the scaled series is the zero
   * series, which converges, so the hypothesis is not a convenience.
   */
  def scaleDiverges(kit: Kit, scaling: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val f = Term.variable("f", sequences)
    val c = Term.variable("c", values)
    val l = Term.variable("l", values)
    val i = Term.variable("i", numbers)
    val n = Term.variable("n", numbers)

    for {
      assumedNonZero <- kit.assume("~((c:real) = 0)")
      (nonZero, isNonZero) = assumedNonZero
      assumedDivergent <- kit.assume("diverges (Sum (f:num -> real))")
      (divergent, isDivergent) = assumedDivergent
      series <- kit.term("Sum (f:num -> real)", sequences)
      denied <- Conv
        .unfold(kit.divergesDefinition, List(series))
        .flatMap(Limit.normaliseRight)
        .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, isDivergent)))

      assumedConverging <- kit.assume("?l:real. converges (Sum (\\i:num. (c:real) * (f:num -> real) i)) l")
      (converging, isConverging) = assumedConverging
      assumedAtL <- kit.assume("converges (Sum (\\i:num. (c:real) * (f:num -> real) i)) (l:real)")
      (_, atL) = assumedAtL
      scaledTerms <- kit.term("\\i:num. (c:real) * (f:num -> real) i", sequences)
      inverse <- kit.term("inv (c:real)", values)
      undone <- rules
        .specAll(scaling, List(scaledTerms, inverse, l))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, atL))
      undoneParts <- Limit.convergenceOf(undone)

      cancels <- rules.spec(c, kit.mulInverse).flatMap(rules.mp(_, isNonZero))
      regrouped <- kit
        .proposition("inv (c:real) * (c * (f:num -> real) (i:num)) = (c * inv c) * f i")
        .flatMap(kit.ring.prove)
      unit <- Limit.rewriteInProposition(cancels, regrouped)
      oneTimes <- kit.proposition("1 * (f:num -> real) (i:num) = f i").flatMap(kit.ring.prove)
      pointwise <- Conv.trans(unit, oneTimes).flatMap(rules.gen(i, _))
      back <- kit.term("\\i:num. inv (c:real) * ((c:real) * (f:num -> real) i)", sequences)
      sums <- rules
        .specAll(kit.congruence, List(back, f))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, pointwise))
      guard <- kit.proposition("NUM_LE ZERO (n:num)")
      agree <- rules.spec(n, sums).flatMap(rules.disch(guard, _)).flatMap(rules.gen(n, _))
      indexZero <- kit.term("ZERO", numbers)
      recovered <- rules
        .specAll(kit.eventually, List(undoneParts._1, series, undoneParts._2, indexZero))
        .flatMap(Limit.normalised)
        .flatMap(rules.mp(_, agree))
        .flatMap(rules.mp(_, undone))
      witnessed <- kit.exists("?l:real. converges (Sum (f:num -> real)) l", undoneParts._2, recovered)
      absurd <- rules.notElim(denied, witnessed)
      overL <- rules.existsElim(isConverging, l, absurd)
      refuted <- rules.notIntro(converging, overL)
      scaledSeries <- kit.term("Sum (\\i:num. (c:real) * (f:num -> real) i)", sequences)
      folded <- Conv
        .unfold(kit.divergesDefinition, List(scaledSeries))
        .flatMap(Limit.normaliseRight)
        .flatMap(Conv.sym)
        .flatMap(eq => LogicError.lift(Kernel.eqMp(eq, refuted)))
      result <- rules
        .disch(divergent, folded)
        .flatMap(rules.disch(nonZero, _))
        .flatMap(rules.genAll(_, List(f, c)))
    } yield result
  }
}
