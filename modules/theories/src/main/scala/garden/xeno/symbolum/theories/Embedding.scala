package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The half of `Peano` that cannot be stated without the real numbers.
 *
 * `real_of_num` and the seventeen facts about it: that it is a homomorphism for both operations,
 * that it carries the order and the integrality with it, that it is injective, the Archimedean
 * property, and the floor and the ceiling. They are here and the other seventy-four are in
 * `Peano.scala`, and the line between the two files is the line `docs/adr/0016` draws.
 *
 * == Why this is a file and not yet a development ==
 *
 * The record says the seventeen "become a development above `Order`", and that is phase 5's work
 * rather than this one's. Splitting the class as well as the file would move 78 call sites from
 * `peano.fact(Peano.EmbedsSum)` to a second development, and every one of them would move **again**
 * when the chain is reordered and this is constructed after `Ring` instead of inside `Peano`. A
 * split done twice is not twice as good, so what is split here is the code, which pays at once: a
 * reader opening `Peano.scala` now meets `num` and nothing else, and a lemma about the reals added
 * to the wrong half is visible in the diff rather than buried in six thousand lines.
 *
 * What already makes the boundary a fact rather than a convention is not this file. It is that
 * `Peano.arithmetic` builds the seventy-four over a theory in which the type operator `real` is not
 * declared, which `ArithmeticBelowTheRealsSpec` asserts and which nothing here changes.
 *
 * == What everything in it has in common ==
 *
 * Every one of these stages needs something the naturals cannot supply. `embedding` needs `RING`
 * for the two homomorphism inductions and `LINARITH` for the three that carry a bound across;
 * `archimedean` is the one place `COMPLETENESS` is spent; `floors` needs the trichotomy of the
 * reals and a case split. That is the same list read from the other side: these are the facts whose
 * derivations reach the sixteen axioms, and `Peano`'s other seventy-four reach none of them.
 *
 * The functions are `private[theories]` and `Peano.construct` is their only caller. They are not a
 * surface: a caller wanting these facts asks `peano.fact` for them by name, exactly as before this
 * file existed.
 */
private[theories] object Embedding {

  import Peano.*

  /**
   * `real_of_num`, and the two homomorphism lemmas that make it worth having.
   *
   * The definition is the same recursion the operations were built by, at the reals rather than at
   * the naturals: zero goes to zero and a successor adds one. What that buys is the two lemmas
   * below, and they are what lets a development state an index over `num` and still hand the
   * arithmetic to a tactic that decides the reals:
   *
   * {{{
   *   |- !m n. real_of_num (NUM_ADD m n) = real_of_num m + real_of_num n
   *   |- !m n. real_of_num (NUM_MUL m n) = real_of_num m * real_of_num n
   * }}}
   *
   * Both are one induction whose step is a **ring** identity, so they go through `Induct`'s own
   * driver rather than through the rewriting one used above: the goal is an equation between reals,
   * `Ring` closes it, and `real_of_num m` is an atom it cannot take apart, which is the right
   * reading of the image of a variable. The product needs the sum lemma as a rewrite on the way,
   * because `m * SUC n` is a sum before it is anything else.
   */
  private[theories] def embedding(
    logic: Logic,
    driver: Induct,
    linarith: Linarith,
    naturals: Natural,
    base: Theory,
    notation: Notation,
    recursion: Kernel.Thm,
    arithmetic: Map[String, Kernel.Thm],
    orderDefinitions: Map[String, Kernel.Thm],
    trichotomy: Kernel.Thm
  ): Either[LogicError, (Theory, Kernel.Thm, Map[String, Kernel.Thm])] = {
    val values = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)
    val rules = logic.rules
    val m: FVar = Term.variable("m", numbers)
    val n: FVar = Term.variable("n", numbers)
    val gap: FVar = Term.variable("d", numbers)

    for {
      defined <- Recursion.define(
        logic,
        naturals,
        base,
        notation,
        recursion,
        Peano.EmbeddingName,
        values,
        "0",
        "\\v:real. \\i:num. v + 1",
        None
      )
      (theory, definition, atZero, atSuccessor) = defined

      embedsZero <- checked(theory, notation, EmbedsZero, atZero)
      embedsSuccessor <- checked(theory, notation, EmbedsSuccessor, atSuccessor)

      sumStatement <- stated(theory, notation, EmbedsSum)
      embedsSum <- driver.prove(
        sumStatement,
        Vector(
          embedsZero,
          embedsSuccessor,
          arithmetic(AddAtZero),
          arithmetic(AddAtSuccessor)
        )
      )

      productStatement <- stated(theory, notation, EmbedsProduct)
      embedsProduct <- driver.prove(
        productStatement,
        Vector(
          embedsZero,
          embedsSuccessor,
          embedsSum,
          arithmetic(MulAtZero),
          arithmetic(MulAtSuccessor)
        )
      )
      // The three that carry the order across, and the only place in this file where a decision
      // procedure closes a step. Everything above is an equation and the rewriter settles it; these
      // are inequalities, and there is no `RING` for an order.
      nonNegativeStatement <- stated(theory, notation, EmbedsNonNegative)
      embedsNonNegative <- driver.proveAssuming(
        nonNegativeStatement,
        Vector(embedsZero, embedsSuccessor)
      )(linarith.prove)

      embedsOrder <- crossesOrder(
        logic,
        linarith,
        theory,
        notation,
        orderDefinitions,
        embedsSum,
        embedsNonNegative,
        m,
        n,
        gap
      )

      strictStatement <- stated(theory, notation, EmbedsStrictOrder)
      embedsStrictOrder <- crossesStrictly(
        logic,
        theory,
        orderDefinitions,
        embedsSuccessor,
        embedsOrder,
        strictStatement,
        m,
        n
      )

      embedsInjectively <- crossesBack(
        logic,
        linarith,
        theory,
        notation,
        trichotomy,
        embedsStrictOrder,
        m,
        n
      )
    } yield (
      theory,
      definition,
      Map(
        EmbedsZero -> embedsZero,
        EmbedsSuccessor -> embedsSuccessor,
        EmbedsSum -> embedsSum,
        EmbedsProduct -> embedsProduct,
        EmbedsNonNegative -> embedsNonNegative,
        EmbedsOrder -> embedsOrder,
        EmbedsStrictOrder -> embedsStrictOrder,
        EmbedsInjectively -> embedsInjectively
      )
    )
  }

  /**
   * `|- !m n. real_of_num m = real_of_num n ==> m = n`.
   *
   * [[EmbedsStrictOrder]] carries a strict bound across as a **gap of one**, and that is what makes
   * this provable rather than merely plausible: two distinct naturals are a whole unit apart on the
   * reals, so their images cannot coincide. Trichotomy supplies the three cases, the middle one is
   * the conclusion, and the outer two are closed by `LINARITH` against the assumed equation.
   *
   * The linear step is asked for once, as a fact about two arbitrary reals, and specialised twice.
   * Asking it twice at the images would be the same work and a second place for the shape to drift.
   */
  private[theories] def crossesBack(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    trichotomy: Kernel.Thm,
    strictly: Kernel.Thm,
    m: FVar,
    n: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val values = TyApp(Real.TypeName, Nil)

    for {
      embedding <- LogicError.lift(theory.constant(Peano.EmbeddingName, Type.fun(numbers, values)))

      // `x = y` and a gap of one between them cannot both hold, which is linear in two unknowns.
      impossible <- Parser
        .proposition(theory, notation, "!x:real y:real. x = y /\\ x + 1 <= y ==> F")
        .flatMap(linarith.prove)

      embeddedM <- LogicError.lift(Term.app(embedding, m))
      embeddedN <- LogicError.lift(Term.app(embedding, n))
      premise <- LogicError.lift(Term.eq(embeddedM, embeddedN))
      assumed <- LogicError.lift(Kernel.assume(premise))
      goal <- LogicError.lift(Term.eq(m, n))

      split <- rules.specAll(trichotomy, List(m, n))
      branches <- logic
        .destDisj(split.conclusion)
        .toRight(NotOfForm("a disjunction", split.conclusion))
      (isBelow, rest) = branches
      tail <- logic.destDisj(rest).toRight(NotOfForm("a disjunction", rest))
      (isEqual, isAbove) = tail

      belowCase <- refutedByTheGap(logic, theory, impossible, strictly, isBelow, m, n, goal, assumed)
      equalCase <- LogicError.lift(Kernel.assume(isEqual))

      flipped <- Conv.sym(assumed)
      aboveCase <- refutedByTheGap(logic, theory, impossible, strictly, isAbove, n, m, goal, flipped)

      upper <- LogicError
        .lift(Kernel.assume(rest))
        .flatMap(rules.disjElim(_, equalCase, aboveCase))
      decided <- rules.disjElim(split, belowCase, upper)

      discharged <- rules.disch(premise, decided)
      general <- rules.genAll(discharged, List(m, n))
      result <- checked(theory, notation, EmbedsInjectively, general)
    } yield result
  }

  /**
   * One of the two outer cases of [[crossesBack]]: a strict bound, refuted by the equation.
   *
   * The two differ only in which way round the pair goes and which orientation of the assumed
   * equation is handed over, which is why they are one function called twice rather than a copy.
   */
  private[theories] def refutedByTheGap(
    logic: Logic,
    theory: Theory,
    impossible: Kernel.Thm,
    strictly: Kernel.Thm,
    disjunct: Term,
    lower: Term,
    upper: Term,
    goal: Term,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val values = TyApp(Real.TypeName, Nil)

    for {
      embedding <- LogicError.lift(theory.constant(Peano.EmbeddingName, Type.fun(numbers, values)))
      assumed <- LogicError.lift(Kernel.assume(disjunct))
      bound <- rules.specAll(strictly, List(lower, upper)).flatMap(rules.mp(_, assumed))

      embeddedLower <- LogicError.lift(Term.app(embedding, lower))
      embeddedUpper <- LogicError.lift(Term.app(embedding, upper))
      instance <- rules.specAll(impossible, List(embeddedLower, embeddedUpper))
      pair <- rules.conjIntro(equation, bound)
      absurd <- rules.mp(instance, pair)
      result <- rules.falsityElim(goal, absurd)
    } yield result
  }

  /**
   * `NUM_REAL_SUB`, the one fact of the subtraction that cannot be stated without the reals.
   *
   * Split out of [[subtraction]] on 2026-09-15, which is `docs/adr/0016`'s phase 0: what is left
   * above is thirteen facts about `PRE` and `NUM_SUB` that name no real, and this is the
   * fourteenth, which does. The seam was already there and was not visible: `ring` and `embedsSum`
   * were parameters of the whole stage and were read by these two lines alone.
   */
  private[theories] def subtractionEmbedded(
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    embedsSum: Kernel.Thm,
    minusThenPlus: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      differenceStatement <- stated(theory, notation, EmbedsDifference)
      embedsDifference <- crossesDifference(
        logic,
        ring,
        theory,
        notation,
        embedsSum,
        minusThenPlus,
        differenceStatement
      )
    } yield embedsDifference

  /**
   * `|- !m n. NUM_LE n m ==> real_of_num (NUM_SUB m n) = real_of_num m - real_of_num n`.
   *
   * [[MinusThenPlus]] under the same hypothesis says `(m - n) + n = m` over the naturals;
   * [[EmbedsSum]] carries that to `A + B = C` over the reals, where `A` is the image of the
   * difference and the other two are the images of `m` and `n`. What is left is `A = C - B`, and it
   * is reached by rewriting `C` back into `A + B` and handing `(A + B) - B = A` to `RING`.
   *
   * `RING` rather than `LINARITH`, which is the procedure the three order lemmas above use. The
   * residue here is an **equation** between ring expressions in three atoms, which is what `RING`
   * decides; sending it to `LINARITH` would be asking a procedure for inequalities to settle an
   * identity, and the three atoms are applications of `real_of_num` that neither takes apart.
   */
  private[theories] def crossesDifference(
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    embedsSum: Kernel.Thm,
    minusThenPlus: Kernel.Thm,
    statement: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val values = TyApp(Real.TypeName, Nil)
    val m = Term.variable("m", numbers)
    val n = Term.variable("n", numbers)

    for {
      below <- Parser.proposition(theory, notation, "NUM_LE (n:num) (m:num)")
      assumed <- LogicError.lift(Kernel.assume(below))
      reaches <- rules.specAll(minusThenPlus, List(m, n)).flatMap(rules.mp(_, assumed))

      embedding <- LogicError.lift(theory.constant(Peano.EmbeddingName, Type.fun(numbers, values)))
      minus <- LogicError.lift(
        theory.constant(Subtraction, Type.fun(numbers, Type.fun(numbers, numbers)))
      )
      realPlus <- LogicError.lift(
        theory.constant(Real.Addition, Type.fun(values, Type.fun(values, values)))
      )
      realMinus <- LogicError.lift(
        theory.constant(Real.Subtraction, Type.fun(values, Type.fun(values, values)))
      )

      taken <- LogicError.lift(Term.appAll(minus, List(m, n)))
      carried <- Conv.apTerm(embedding, reaches)
      homomorphism <- rules.specAll(embedsSum, List(taken, n))
      equation <- Conv.sym(homomorphism).flatMap(Conv.trans(_, carried))

      left <- LogicError.lift(Term.app(embedding, taken))
      subtracted <- LogicError.lift(Term.app(embedding, n))
      whole <- LogicError.lift(Term.app(embedding, m))
      sum <- LogicError.lift(Term.appAll(realPlus, List(left, subtracted)))
      shrunk <- LogicError.lift(Term.appAll(realMinus, List(sum, subtracted)))
      identity <- LogicError.lift(Term.eq(shrunk, left)).flatMap(ring.prove)

      back <- Conv.sym(equation)
      asDifference <- Conv.apTerm(realMinus, back).flatMap(Conv.apThm(_, subtracted))
      reached <- Conv.trans(asDifference, identity).flatMap(Conv.sym)

      result <- rules.disch(below, reached).flatMap(rules.genAll(_, List(m, n)))

      // The statement as the table writes it rather than something that follows from it, for the
      // reason `crossesStrictly` gives: `RING` decides the shape of what comes back and the table
      // decides what this file claims.
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm("the statement as the table writes it", result.conclusion))
    } yield result
  }

  /**
   * The three lemmas that carry a numeral of `num` across `real_of_num`.
   *
   * The other half of [[numerals]], split from it on 2026-09-15 for `docs/adr/0016`'s phase 0. The
   * encoding above is three definitions and three doubling lemmas and names no real; these three
   * are what make it worth having on a goal about the reals, and they cannot be stated below them.
   */
  private[theories] def numeralsEmbedded(
    logic: Logic,
    ring: Ring,
    theory: Theory,
    spelled: Notation,
    embedding: Map[String, Kernel.Thm],
    oneIsSuccessor: Kernel.Thm,
    bit0Doubles: Kernel.Thm,
    bit1Doubles: Kernel.Thm
  ): Either[LogicError, Map[String, Kernel.Thm]] =
    for {
      // `real_of_num NUM_ONE` rewrites to `0 + 1` and stops: the rules here are recurrences and
      // `0 + 1 = 1` is not one of them, it is an identity of the field. So the rewrite settles the
      // left side and `RING` settles what is left, which is the same division of labour
      // `EmbedsDifference` above already uses.
      embedsZero <- embedding.get(EmbedsZero).toRight(MissingDefinition(EmbedsZero))
      embedsSuccessor <- embedding.get(EmbedsSuccessor).toRight(MissingDefinition(EmbedsSuccessor))
      embedsSum <- embedding.get(EmbedsSum).toRight(MissingDefinition(EmbedsSum))

      bit0Real <- ring.reals.definition(Real.Bit0)
      bit1Real <- ring.reals.definition(Real.Bit1)

      embedsOne <- carriedAcross(
        logic,
        ring,
        theory,
        spelled,
        EmbedsNumeralOne,
        Vector(oneIsSuccessor, embedsSuccessor, embedsZero)
      )
      embedsBit0 <- byRewriting(
        logic, theory, spelled, EmbedsNumeralBit0, Vector(bit0Doubles, embedsSum, bit0Real))
      embedsBit1 <- byRewriting(
        logic,
        theory,
        spelled,
        EmbedsNumeralBit1,
        Vector(bit1Doubles, embedsSuccessor, embedsSum, bit1Real)
      )
    } yield Map(
      EmbedsNumeralOne -> embedsOne,
      EmbedsNumeralBit0 -> embedsBit0,
      EmbedsNumeralBit1 -> embedsBit1
    )

  /**
   * An unquantified equation whose left side rewrites to something `RING` can finish against.
   *
   * [[byRewriting]] is the usual route and it is the one the two bit lemmas take: both sides
   * normalise to the same term and there is nothing left to decide. [[EmbedsNumeralOne]] does not,
   * and the reason is worth the separate method rather than a fallback that hides it. Its left side
   * normalises to `0 + 1` and its right side is `1`; the rules here are recurrences and `0 + 1 = 1`
   * is not one of them, it is an identity of the field. So the rewriting settles what it can and
   * `RING` decides the residue, which is the same division of labour [[EmbedsDifference]] already
   * uses and is a decision procedure rather than a second guess.
   *
   * Asking `RING` the **original** statement instead would fail and is worth recording as the first
   * thing tried: `real_of_num NUM_ONE` is an atom to a procedure that decides the reals, so the
   * question it would answer is whether an unknown equals one, and the answer to that is no.
   */
  private[theories] def carriedAcross(
    logic: Logic,
    ring: Ring,
    theory: Theory,
    notation: Notation,
    name: String,
    rewrites: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      statement <- stated(theory, notation, name)
      sides <- Term.destEq(statement).toRight(NotOfForm("an equation", statement))
      rules <- Rewrite.Rule.all(logic, rewrites)
      normalised <- Rewrite.rewrite(rules, sides._1)
      residue <- rightOf(normalised)
      closing <- LogicError.lift(Term.eq(residue, sides._2)).flatMap(ring.prove)
      proved <- Conv.trans(normalised, closing)
      result <- checked(theory, notation, name, proved)
    } yield result

  /**
   * `|- !x:real. ?n:num. x < real_of_num n`, and it is where `COMPLETENESS` is spent.
   *
   * The plan is in [[Archimedean]]'s comment. What the code adds is the bookkeeping: the predicate
   * is `\x. ?n. x = real_of_num n`, which is the image of `num` written as a set, and the three
   * things `COMPLETENESS` wants of it are that it is inhabited, that the assumed `y` bounds it, and
   * then that `s - 1` bounds it too.
   *
   * Each of the four arithmetic steps is `LINARITH`'s and is asked for once as a fact about
   * arbitrary reals, then specialised. Asking at the images instead would be the same work and a
   * second place for the shape to drift, which is the arrangement [[crossesBack]] already uses.
   */
  private[theories] def archimedean(
    logic: Logic,
    classical: Classical,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    trichotomy: Kernel.Thm,
    completeness: Kernel.Thm,
    embedsSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val values = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)

    val n: FVar = Term.variable("n", numbers)
    val k: FVar = Term.variable("k", numbers)
    val x: FVar = Term.variable("x", values)
    val y: FVar = Term.variable("y", values)
    val s: FVar = Term.variable("s", values)

    def proposition(text: String): Either[LogicError, Term] =
      Parser.proposition(theory, notation, text)

    def expression(text: String, ty: Type): Either[LogicError, Term] =
      Parser.term(theory, notation, text, ty)

    def predicateOf(term: Term): Either[LogicError, Term] =
      logic.destExistsPredicate(term).toRight(NotOfForm("an existential", term))

    for {
      // The assumption everything below is under, and the one `Classical.contradiction` discharges.
      goal <- proposition("?n:num. y < real_of_num n")
      negation <- logic.mkNot(goal)
      assumed <- LogicError.lift(Kernel.assume(negation))

      // Under it, no embedded natural passes `y`, so every one of them is at most `y`. The
      // trichotomy supplies the three cases and the first is closed by the assumption itself.
      belowStatement <- proposition("y < real_of_num n")
      below <- LogicError.lift(Kernel.assume(belowStatement))
      goalPredicate <- predicateOf(goal)
      witnessed <- rules.existsIntro(goalPredicate, n, below)
      clash <- rules.notElim(assumed, witnessed)
      notBelow <- rules.notIntro(belowStatement, clash)

      embedded <- expression("real_of_num n", values)
      cases <- rules.specAll(trichotomy, List(y, embedded))
      atMostStatement <- proposition("real_of_num n <= y")

      fromBelow <- LogicError
        .lift(Kernel.assume(belowStatement))
        .flatMap(rules.notElim(notBelow, _))
        .flatMap(rules.falsityElim(atMostStatement, _))

      fromEqual <- for {
        linear <- proposition("!a:real b:real. a = b ==> b <= a").flatMap(linarith.prove)
        equality <- proposition("y = real_of_num n").flatMap(t => LogicError.lift(Kernel.assume(t)))
        instance <- rules.specAll(linear, List(y, embedded))
        applied <- rules.mp(instance, equality)
      } yield applied

      fromAbove <- for {
        linear <- proposition("!a:real b:real. b < a ==> b <= a").flatMap(linarith.prove)
        strict <- proposition("real_of_num n < y").flatMap(t => LogicError.lift(Kernel.assume(t)))
        instance <- rules.specAll(linear, List(y, embedded))
        applied <- rules.mp(instance, strict)
      } yield applied

      tail <- proposition("y = real_of_num n \\/ real_of_num n < y")
        .flatMap(t => LogicError.lift(Kernel.assume(t)))
      fromTail <- rules.disjElim(tail, fromEqual, fromAbove)
      atMost <- rules.disjElim(cases, fromBelow, fromTail)
      boundedByY <- rules.gen(n, atMost)

      // The image is inhabited, by zero and nothing cleverer.
      inhabitedStatement <- proposition("?x:real. ?y:num. x = real_of_num y")
      inhabitedPredicate <- predicateOf(inhabitedStatement)
      zero <- expression("real_of_num 0", values)
      atZeroStatement <- proposition("?y:num. real_of_num 0 = real_of_num y")
      atZeroPredicate <- predicateOf(atZeroStatement)
      zeroIndex <- expression("0", numbers)
      atZero <- rules.existsIntro(atZeroPredicate, zeroIndex, Kernel.refl(zero))
      inhabited <- rules.existsIntro(inhabitedPredicate, zero, atZero)

      // `y` bounds it: a member is an embedded natural, and those are all below `y`.
      memberStatement <- proposition("?z:num. x = real_of_num z")
      member <- LogicError.lift(Kernel.assume(memberStatement))
      witnessEquation <- proposition("x = real_of_num k")
      embeddedK <- expression("real_of_num k", values)
      carry <- proposition("!a:real b:real c:real. a = b /\\ b <= c ==> a <= c")
        .flatMap(linarith.prove)
      atK <- rules.spec(k, boundedByY)
      carriedAtK <- for {
        equation <- LogicError.lift(Kernel.assume(witnessEquation))
        instance <- rules.specAll(carry, List(x, embeddedK, y))
        both <- rules.conjIntro(equation, atK)
        applied <- rules.mp(instance, both)
      } yield applied
      carried <- rules.existsElim(member, k, carriedAtK)
      bounds <- rules.disch(memberStatement, carried).flatMap(rules.gen(x, _))
      boundedStatement <- proposition("?x:real. !y:real. (?z:num. y = real_of_num z) ==> y <= x")
      boundedPredicate <- predicateOf(boundedStatement)
      boundedAbove <- rules.existsIntro(boundedPredicate, y, bounds)

      // So there is a least upper bound. `spec` leaves the predicate applied rather than
      // substituted, which is what `Rules.spec` documents, so the instance is normalised before
      // anything is read off it.
      image <- expression("\\x:real. ?n:num. x = real_of_num n", Type.fun(values, Type.Bool))
      atImage <- rules.spec(image, completeness)
      reduction <- Conv.betaNormalise(atImage.conclusion)
      instance <- LogicError.lift(Kernel.eqMp(reduction, atImage))
      premises <- rules.conjIntro(inhabited, boundedAbove)
      supremum <- rules.mp(instance, premises)

      // And `s - 1` bounds the image too, which is the step that avoids the missing lemma: every
      // member has a successor in the image, and the successor is at most `s`.
      supremumStatement <- proposition(
        "(!y:real. (?z:num. y = real_of_num z) ==> y <= s) /\\ " +
          "(!y:real. (!z:real. (?u:num. z = real_of_num u) ==> z <= y) ==> s <= y)"
      )
      supremumBody <- LogicError.lift(Kernel.assume(supremumStatement))
      isUpperBound <- rules.conjElim1(supremumBody)
      isLeast <- rules.conjElim2(supremumBody)

      successorStatement <- proposition("?z:num. real_of_num (SUC k) = real_of_num z")
      successorPredicate <- predicateOf(successorStatement)
      embeddedSuccessor <- expression("real_of_num (SUC k)", values)
      successorIndex <- expression("SUC k", numbers)
      successorInImage <- rules.existsIntro(
        successorPredicate,
        successorIndex,
        Kernel.refl(embeddedSuccessor)
      )
      successorAtMost <- rules
        .spec(embeddedSuccessor, isUpperBound)
        .flatMap(rules.mp(_, successorInImage))
      atKSuccessor <- rules.spec(k, embedsSuccessor)
      shifted <- Rewrite.Rule
        .of(logic, atKSuccessor)
        .flatMap(rule => Rewrite.inTheorem(Vector(rule), successorAtMost))

      step <- proposition("!a:real b:real c:real. a + 1 <= b /\\ c = a ==> c <= b - 1")
        .flatMap(linarith.prove)
      loweredAtK <- for {
        equation <- LogicError.lift(Kernel.assume(witnessEquation))
        instance2 <- rules.specAll(step, List(embeddedK, s, x))
        both <- rules.conjIntro(shifted, equation)
        applied <- rules.mp(instance2, both)
      } yield applied
      lowered <- rules.existsElim(member, k, loweredAtK)
      lowerBound <- rules.disch(memberStatement, lowered).flatMap(rules.gen(x, _))

      // Leastness then says `s <= s - 1`, and that is falsity in one linear step.
      lessOne <- expression("s - 1", values)
      atLessOne <- rules.spec(lessOne, isLeast).flatMap(rules.mp(_, lowerBound))
      impossible <- proposition("!a:real. a <= a - 1 ==> F").flatMap(linarith.prove)
      falsity <- rules.spec(s, impossible).flatMap(rules.mp(_, atLessOne))

      withoutSupremum <- rules.existsElim(supremum, s, falsity)
      reached <- classical.contradiction(goal, withoutSupremum)
      result <- rules.gen(y, reached)
    } yield result
  }

  /**
   * The floor and the ceiling, named by choice, with the two facts each one is for.
   *
   * == The existence proof, which is the whole of it ==
   *
   * [[Archimedean]] puts a natural past `x` and [[LeastNumber]] takes the first one. That first one
   * is not zero, because `x` is not below zero, so it is a successor, and its predecessor is the
   * floor: nothing below the first passes `x`, so the predecessor does not, and the trichotomy
   * turns that into `real_of_num p <= x`. The other half is the first one itself, written as one
   * more by [[EmbedsSuccessor]]. The ceiling then comes from the floor by a case split on whether
   * the floor is exactly `x`, which is `Classical.cases` and two linear steps.
   *
   * == Why `select` and not a definition by recursion ==
   *
   * Between a proof that something exists and a term naming it stands the choice operator and
   * nothing else, which is the argument `Magnitude` makes for `max` and it is the same here.
   * `Kernel.defineConstant` wants a closed term; a witness pulled out of an existential is a
   * variable. So the bill is choice, which this development already pays through `Natural`, and it
   * is **no new axiom**: both constants are definitions and the count stays at nineteen.
   *
   * == What the condition costs, and where it goes when the integers arrive ==
   *
   * Both characterisations carry `0 <= x`, for the reason [[FloorAtMost]] gives: `num` has no
   * negative numbers and a constant that answered anyway would be silently wrong below zero. The
   * hypothesis is written rather than avoided, and `select` leaves the term denoting something
   * unspecified there rather than leaving it undefined.
   */
  private[theories] def floors(
    logic: Logic,
    classical: Classical,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    archimedes: Kernel.Thm,
    leastNumber: Kernel.Thm,
    zeroOrSuccessor: Kernel.Thm,
    belowSuccessor: Kernel.Thm,
    embedsZero: Kernel.Thm,
    embedsSuccessor: Kernel.Thm,
    trichotomy: Kernel.Thm,
    leCases: Kernel.Thm
  ): Either[LogicError, (Theory, Map[String, Kernel.Thm], Map[String, Kernel.Thm])] = {
    val rules = logic.rules
    val values = TyApp(Real.TypeName, Nil)
    val numbers = TyApp(Natural.TypeName, Nil)

    val x: FVar = Term.variable("x", values)
    val m: FVar = Term.variable("m", numbers)
    val p: FVar = Term.variable("p", numbers)

    def proposition(at: Theory, text: String): Either[LogicError, Term] =
      Parser.proposition(at, notation, text)

    def expression(at: Theory, text: String, ty: Type): Either[LogicError, Term] =
      Parser.term(at, notation, text, ty)

    def assume(term: Term): Either[LogicError, Kernel.Thm] = LogicError.lift(Kernel.assume(term))

    def carrying(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Rewrite.Rule.of(logic, equation).flatMap(rule => Rewrite.inTheorem(Vector(rule), theorem))

    def folding(equation: Kernel.Thm, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Conv.sym(equation).flatMap(carrying(_, theorem))

    for {
      nonNegative <- proposition(theory, "0 <= x")
      assumed <- assume(nonNegative)

      /* ------------------------------------------------- a natural the floor could be */
      target <- proposition(theory, "?n:num. real_of_num n <= x /\\ x < real_of_num n + 1")
      targetPredicate <- logic
        .destExistsPredicate(target)
        .toRight(NotOfForm("an existential", target))

      passes <- rules.spec(x, archimedes)
      passing <- expression(theory, "\\n:num. x < real_of_num n", Type.fun(numbers, Type.Bool))
      atPassing <- rules.spec(passing, leastNumber)
      reduction <- Conv.betaNormalise(atPassing.conclusion)
      reduced <- LogicError.lift(Kernel.eqMp(reduction, atPassing))
      first <- rules.mp(reduced, passes)

      firstBodyStatement <- proposition(
        theory,
        "x < real_of_num m /\\ (!k:num. NUM_LT k m ==> ~(x < real_of_num k))"
      )
      firstBody <- assume(firstBodyStatement)
      passesAtFirst <- rules.conjElim1(firstBody)
      noneBelowFirst <- rules.conjElim2(firstBody)

      // The first one is not zero: `x` is not below zero and `real_of_num 0` is zero.
      isZeroStatement <- proposition(theory, "m = 0:num")
      fromZero <- for {
        isZero <- assume(isZeroStatement)
        carried <- carrying(isZero, passesAtFirst)
        grounded <- carrying(embedsZero, carried)
        impossible <- proposition(theory, "!a:real. 0 <= a ==> a < 0 ==> F")
          .flatMap(linarith.prove)
        falsity <- rules
          .spec(x, impossible)
          .flatMap(rules.mp(_, assumed))
          .flatMap(rules.mp(_, grounded))
        anything <- rules.falsityElim(target, falsity)
      } yield anything

      // So it is a successor, and the predecessor is the floor.
      isSuccessorStatement <- proposition(theory, "m = SUC p")
      fromSuccessor <- for {
        isSuccessor <- assume(isSuccessorStatement)
        passesAtSuccessor <- carrying(isSuccessor, passesAtFirst)
        noneBelowSuccessor <- carrying(isSuccessor, noneBelowFirst)

        atPredecessor <- rules.spec(p, belowSuccessor)
        notPassing <- rules.spec(p, noneBelowSuccessor).flatMap(rules.mp(_, atPredecessor))

        embedded <- expression(theory, "real_of_num p", values)
        three <- rules.specAll(trichotomy, List(x, embedded))
        atMostStatement <- proposition(theory, "real_of_num p <= x")
        fromBelow <- proposition(theory, "x < real_of_num p")
          .flatMap(assume)
          .flatMap(rules.notElim(notPassing, _))
          .flatMap(rules.falsityElim(atMostStatement, _))
        fromEqual <- for {
          linear <- proposition(theory, "!a:real b:real. a = b ==> b <= a").flatMap(linarith.prove)
          equality <- proposition(theory, "x = real_of_num p").flatMap(assume)
          instance <- rules.specAll(linear, List(x, embedded))
          applied <- rules.mp(instance, equality)
        } yield applied
        fromAbove <- for {
          linear <- proposition(theory, "!a:real b:real. b < a ==> b <= a").flatMap(linarith.prove)
          strict <- proposition(theory, "real_of_num p < x").flatMap(assume)
          instance <- rules.specAll(linear, List(x, embedded))
          applied <- rules.mp(instance, strict)
        } yield applied
        tail <- proposition(theory, "x = real_of_num p \\/ real_of_num p < x").flatMap(assume)
        fromTail <- rules.disjElim(tail, fromEqual, fromAbove)
        atMost <- rules.disjElim(three, fromBelow, fromTail)

        atPredecessorSuccessor <- rules.spec(p, embedsSuccessor)
        shifted <- carrying(atPredecessorSuccessor, passesAtSuccessor)
        both <- rules.conjIntro(atMost, shifted)
        witnessed <- rules.existsIntro(targetPredicate, p, both)
        closed <- rules.disch(isSuccessorStatement, witnessed)
      } yield closed

      successorExistsStatement <- proposition(theory, "?p:num. m = SUC p")
      successorExists <- assume(successorExistsStatement)
      fromSuccessorClosed <- assume(isSuccessorStatement)
        .flatMap(rules.mp(fromSuccessor, _))
        .flatMap(rules.existsElim(successorExists, p, _))

      atFirst <- rules.spec(m, zeroOrSuccessor)
      split <- rules.disjElim(atFirst, fromZero, fromSuccessorClosed)
      exists <- rules.existsElim(first, m, split)

      /* ------------------------------------------------------- the floor, named */
      floorBody <- expression(
        theory,
        "\\x:real. select (\\n:num. real_of_num n <= x /\\ x < real_of_num n + 1)",
        Type.fun(values, numbers)
      )
      floorDefined <- LogicError.lift(Kernel.defineConstant(theory, Floor, floorBody))
      (withFloor, floorDefinition) = floorDefined
      floorUnfolded <- Conv.unfold(floorDefinition, List(x))
      floorChosen <- classical.witness(exists)
      floorReduced <- Conv
        .betaRoot(floorChosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, floorChosen)))
      floorFolded <- folding(floorUnfolded, floorReduced)
      floorAtMostAtX <- rules.conjElim1(floorFolded)
      floorAboveAtX <- rules.conjElim2(floorFolded)
      floorAtMost <- rules
        .disch(nonNegative, floorAtMostAtX)
        .flatMap(rules.gen(x, _))
        .flatMap(checked(withFloor, notation, FloorAtMost, _))
      floorAbove <- rules
        .disch(nonNegative, floorAboveAtX)
        .flatMap(rules.gen(x, _))
        .flatMap(checked(withFloor, notation, FloorAbove, _))

      /* ---------------------------------------------------- the ceiling, from it */
      ceilingTarget <- proposition(
        withFloor,
        "?n:num. x <= real_of_num n /\\ real_of_num n < x + 1"
      )
      ceilingPredicate <- logic
        .destExistsPredicate(ceilingTarget)
        .toRight(NotOfForm("an existential", ceilingTarget))
      floorIndex <- expression(withFloor, "NUM_FLOOR x", numbers)
      successorIndex <- expression(withFloor, "SUC (NUM_FLOOR x)", numbers)
      embeddedFloor <- expression(withFloor, "real_of_num (NUM_FLOOR x)", values)
      exactStatement <- proposition(withFloor, "real_of_num (NUM_FLOOR x) = x")

      whenExact <- for {
        exact <- assume(exactStatement)
        linear <- proposition(withFloor, "!a:real b:real. a = b ==> b <= a /\\ a < b + 1")
          .flatMap(linarith.prove)
        instance <- rules.specAll(linear, List(embeddedFloor, x))
        both <- rules.mp(instance, exact)
        witnessed <- rules.existsIntro(ceilingPredicate, floorIndex, both)
      } yield witnessed

      exactNegation <- logic.mkNot(exactStatement)
      whenNotExact <- for {
        notExact <- assume(exactNegation)
        strictStatement <- proposition(withFloor, "real_of_num (NUM_FLOOR x) < x")
        cases <- rules.specAll(leCases, List(embeddedFloor, x)).flatMap(rules.mp(_, floorAtMostAtX))
        fromStrict <- assume(strictStatement)
        fromExact <- assume(exactStatement)
          .flatMap(rules.notElim(notExact, _))
          .flatMap(rules.falsityElim(strictStatement, _))
        strict <- rules.disjElim(cases, fromStrict, fromExact)
        linear <- proposition(
          withFloor,
          "!a:real b:real. a < b ==> b < a + 1 ==> b <= a + 1 /\\ a + 1 < b + 1"
        ).flatMap(linarith.prove)
        instance <- rules.specAll(linear, List(embeddedFloor, x))
        both <- rules.mp(instance, strict).flatMap(rules.mp(_, floorAboveAtX))
        atSuccessor <- rules.spec(floorIndex, embedsSuccessor)
        written <- folding(atSuccessor, both)
        witnessed <- rules.existsIntro(ceilingPredicate, successorIndex, written)
      } yield witnessed

      ceilingExists <- classical.cases(exactStatement, whenExact, whenNotExact)
      ceilingBody <- expression(
        withFloor,
        "\\x:real. select (\\n:num. x <= real_of_num n /\\ real_of_num n < x + 1)",
        Type.fun(values, numbers)
      )
      ceilingDefined <- LogicError.lift(Kernel.defineConstant(withFloor, Ceiling, ceilingBody))
      (withCeiling, ceilingDefinition) = ceilingDefined
      ceilingUnfolded <- Conv.unfold(ceilingDefinition, List(x))
      ceilingChosen <- classical.witness(ceilingExists)
      ceilingReduced <- Conv
        .betaRoot(ceilingChosen.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, ceilingChosen)))
      ceilingFolded <- folding(ceilingUnfolded, ceilingReduced)
      ceilingAtLeast <- rules
        .conjElim1(ceilingFolded)
        .flatMap(rules.disch(nonNegative, _))
        .flatMap(rules.gen(x, _))
        .flatMap(checked(withCeiling, notation, CeilingAtLeast, _))
      ceilingBelow <- rules
        .conjElim2(ceilingFolded)
        .flatMap(rules.disch(nonNegative, _))
        .flatMap(rules.gen(x, _))
        .flatMap(checked(withCeiling, notation, CeilingBelow, _))
    } yield (
      withCeiling,
      Map(Floor -> floorDefinition, Ceiling -> ceilingDefinition),
      Map(
        FloorAtMost -> floorAtMost,
        FloorAbove -> floorAbove,
        CeilingAtLeast -> ceilingAtLeast,
        CeilingBelow -> ceilingBelow
      )
    )
  }

  /**
   * `|- !m n. NUM_LE m n ==> real_of_num m <= real_of_num n`, from the definition of the order.
   *
   * `NUM_LE m n` **is** `?d. NUM_ADD m d = n`, which is why this is not an induction: open the
   * existential, embed the witness equation with [[EmbedsSum]], and what is left is
   * `a + b = c` with `0 <= b`, which is linear in three atoms and goes to `LINARITH`.
   *
   * The three atoms are applications of `real_of_num`, and that they are usable as atoms at all is
   * a fact about the procedure rather than about this file: it reads an applied constant of type
   * `real` as an unknown and decides over it. A development that had to abstract each one to a
   * fresh variable first would be working around a restriction that is not there.
   */
  private def crossesOrder(
    logic: Logic,
    linarith: Linarith,
    theory: Theory,
    notation: Notation,
    orderDefinitions: Map[String, Kernel.Thm],
    embedsSum: Kernel.Thm,
    embedsNonNegative: Kernel.Thm,
    m: FVar,
    n: FVar,
    gap: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)
    val values = TyApp(Real.TypeName, Nil)

    for {
      definition <- orderDefinitions
        .get(NonStrictOrder)
        .toRight(MissingDefinition(NonStrictOrder))
      unfolded <- Conv.unfold(definition, List(m, n))

      order <- LogicError.lift(
        theory
          .constant(NonStrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
          .flatMap(constant => Term.appAll(constant, List(m, n)))
      )
      assumed <- LogicError.lift(Kernel.assume(order))
      existential <- LogicError.lift(Kernel.eqMp(unfolded, assumed))

      plus <- LogicError.lift(theory.constant(Addition, Type.fun(numbers, Type.fun(numbers, numbers))))
      reaching <- LogicError.lift(Term.appAll(plus, List(m, gap)).flatMap(Term.eq(_, n)))
      reaches <- LogicError.lift(Kernel.assume(reaching))

      embedding <- LogicError.lift(theory.constant(Peano.EmbeddingName, Type.fun(numbers, values)))
      carried <- Conv.apTerm(embedding, reaches)
      homomorphism <- rules.specAll(embedsSum, List(m, gap))
      equation <- Conv.sym(homomorphism).flatMap(Conv.trans(_, carried))

      atGap <- rules.spec(gap, embedsNonNegative)
      shape <- Parser.proposition(theory, notation, "!a:real b:real c:real. 0 <= b /\\ a + b = c ==> a <= c")
      linear <- linarith.prove(shape)
      instances <- LogicError.lift(
        List(m, gap, n).foldLeft[Either[KernelError, List[Term]]](Right(Nil)) { (acc, argument) =>
          for {
            done <- acc
            applied <- Term.app(embedding, argument)
          } yield done :+ applied
        }
      )
      instanced <- rules.specAll(linear, instances)
      both <- rules.conjIntro(atGap, equation)
      bounded <- rules.mp(instanced, both)

      withoutWitness <- rules.existsElim(existential, gap, bounded)
      discharged <- rules.disch(order, withoutWitness)
      result <- rules.genAll(discharged, List(m, n))
    } yield result
  }

  /**
   * `|- !m n. NUM_LT m n ==> real_of_num m + 1 <= real_of_num n`, one step from the other one.
   *
   * `NUM_LT m n` is `NUM_LE (SUC m) n` by definition, so the non-strict lemma at `(SUC m, n)` is
   * already the answer with the left-hand side written as `real_of_num (SUC m)`; rewriting it with
   * [[EmbedsSuccessor]] is the whole of the rest. That the gap is exactly one, rather than merely
   * positive, is the fact worth having and is what defining `<` through `<=` bought.
   */
  private def crossesStrictly(
    logic: Logic,
    theory: Theory,
    orderDefinitions: Map[String, Kernel.Thm],
    embedsSuccessor: Kernel.Thm,
    embedsOrder: Kernel.Thm,
    statement: Term,
    m: FVar,
    n: FVar
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val numbers = TyApp(Natural.TypeName, Nil)

    for {
      definition <- orderDefinitions.get(StrictOrder).toRight(MissingDefinition(StrictOrder))
      unfolded <- Conv.unfold(definition, List(m, n))

      strict <- LogicError.lift(
        theory
          .constant(StrictOrder, Type.fun(numbers, Type.fun(numbers, Type.Bool)))
          .flatMap(constant => Term.appAll(constant, List(m, n)))
      )
      assumed <- LogicError.lift(Kernel.assume(strict))
      asNonStrict <- LogicError.lift(Kernel.eqMp(unfolded, assumed))

      successor <- LogicError.lift(theory.constant(Natural.NumberSuccessor, Type.fun(numbers, numbers)))
      next <- LogicError.lift(Term.app(successor, m))
      crossed <- rules.specAll(embedsOrder, List(next, n)).flatMap(rules.mp(_, asNonStrict))

      rule <- Rewrite.Rule.of(logic, embedsSuccessor)
      rewritten <- Rewrite.rewrite(Vector(rule), crossed.conclusion)
      opened <- LogicError.lift(Kernel.eqMp(rewritten, crossed))

      discharged <- rules.disch(strict, opened)
      result <- rules.genAll(discharged, List(m, n))

      // The statement as it is written down, rather than something that follows from it: the
      // rewriter decides the shape of the left-hand side and the table decides what this file
      // claims, and the two have to be the same claim.
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm("the statement as the table writes it", result.conclusion))
    } yield result
  }
}
