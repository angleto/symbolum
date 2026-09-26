package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * FRACTRAN read as a register machine: a step on the number is a step on its prime registers, in
 * both directions.
 *
 * Not a development: `Fractran` defines `FRACTRAN_REGISTER_STEP` and publishes what this file
 * derives, the arrangement `Freshman` has with `Primes`.
 *
 * == The register machine, and why it is the same fold ==
 *
 * {{{
 *   FRACTRAN_REGISTER_STEP P n m =
 *     LIST_FOLD (\f r. COND (~(SND f = 0) /\ (!p. prime p ==> v_p (SND f) <= v_p n + v_p (FST f)))
 *                           (0 < m /\ (!p. prime p ==> v_p m + v_p (SND f) = v_p n + v_p (FST f)))
 *                           r)
 *               F P
 * }}}
 *
 * The same walk over the program as `FRACTRAN_STEP`, with each fraction's test and effect written
 * on the registers `v_p` instead of on the number: a fraction applies when the state's and the
 * numerator's registers together cover the denominator's, and it adds the numerator's registers
 * and takes the denominator's away. Keeping the fold identical is the point, since "the first
 * fraction that applies" is then the same clause on both sides and the proof is an induction on the
 * program whose step compares one fraction.
 *
 * The effect is written with the denominator's register on the left, `v_p m + v_p q = v_p n +
 * v_p a`, because `num`'s subtraction is truncated and this form needs no side condition. And the
 * register machine says `0 < m`, because the registers of nought are the valuation's unnamed value
 * and no set of registers names it.
 *
 * == What the theorem asks of the program and of the state ==
 *
 * `0 < n`, and every numerator positive. At `n = 0` every fraction applies, since everything
 * divides nought, and the state stays nought, which has no registers. A numerator of nought sends
 * every state it applies to to nought, for the same reason. Neither is a restriction on a program
 * anybody runs: Conway's programs have positive numerators and start above nought, and once above
 * nought such a program stays there. The denominators need nothing: a denominator of nought is
 * refused by both machines in the same clause.
 */
private[theories] object FractranRegisters {
  import Steps.*

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Pairs: Type = TyApp(Product.TypeName, List(Num, Num))
  private val Programs: Type = TyApp(Word.TypeName, List(Pairs))

  private def at(theorem: Kernel.Thm, element: Type, values: Type): Kernel.Thm =
    Kernel.instType(Map(Classical.TypeVariable -> element, Classical.CodomainVariable -> values), theorem)

  private def normal(thm: Kernel.Thm): R[Kernel.Thm] =
    Conv.betaNormalise(thm.conclusion).flatMap(e => LogicError.lift(Kernel.eqMp(e, thm)))

  /** `LIST_FOLD g F P` taken apart. */
  private def folded(term: Term): R[(Term, Term, Term)] = term match {
    case App(App(App(_, g), start), list) => Right((g, start, list))
    case other => Left(NotOfForm("a fold", other))
  }

  /** `t = F` from `~t`. */
  private def equalsFalsity(kit: Kit, t: Term, refuted: Kernel.Thm): R[Kernel.Thm] =
    for {
      falsity <- kit.term("F", Type.Bool)
      h <- assume(t)
      absurd <- kit.rules.notElim(refuted, h)
      back <- assume(falsity)
      anything <- kit.rules.falsityElim(t, back)
    } yield Kernel.deductAntisym(anything, absurd)

  /**
   * `|- !P n m. NUM_LT 0 n ==> LIST_FOLD (\f r. NUM_LT 0 (FST f) /\ r) T P ==>
   *     (FRACTRAN_STEP P n m = FRACTRAN_REGISTER_STEP P n m)`
   */
  def simulation(
    kit: Kit,
    registerStep: Kernel.Thm,
    stepEmpty: Kernel.Thm,
    stepCons: Kernel.Thm,
    applies: Kernel.Thm,
    lands: Kernel.Thm
  ): R[Kernel.Thm] = {
    val n = Term.variable("n", Num)
    val m = Term.variable("m", Num)
    val f = Term.variable("f", Pairs)
    val program = Term.variable("P", Programs)
    val tail = Term.variable("Q", Programs)
    val rules = kit.rules
    val empty = kit.term("WORD_EMPTY", Programs)

    for {
      nPositive <- kit.assume("NUM_LT 0 (n:num)")
      claim <- kit.at(
        "\\n:num. \\m:num. \\P:word(prod(num,num)). " +
          "LIST_FOLD (\\f:prod(num,num). \\r:bool. NUM_LT 0 (FST f) /\\ r) T P ==> " +
          "(FRACTRAN_STEP P n m = FRACTRAN_REGISTER_STEP P n m)", n, m)
      induction <- kit.fact("LIST_INDUCT").map(Kernel.instType(Map(Classical.TypeVariable -> Pairs), _))
        .flatMap(rules.spec(claim, _)).flatMap(normal)
      parts <- imp(kit, induction.conclusion)
      (premise, _) = parts
      halves <- conj(kit, premise)
      (baseGoal, stepGoal) = halves

      // the empty program: neither machine steps
      emptyTerm <- empty
      base <- for {
        p <- imp(kit, baseGoal)
        (positive, goal) = p
        sides0 <- sides(goal)
        (stepTerm, registerTerm) = sides0
        refused <- rules.specAll(stepEmpty, List(n, m))
        stepFalse <- equalsFalsity(kit, stepTerm, refused)
        unfolded <- Conv.unfold(registerStep, List(emptyTerm, n, m))
        body <- Limit.rightOf(unfolded)
        pieces <- folded(body)
        (g, start, _) = pieces
        emptyFold <- kit.fact("LIST_FOLD_EMPTY").map(at(_, Pairs, Type.Bool)).flatMap(rules.specAll(_, List(g, start)))
        registerFalse <- Conv.trans(unfolded, emptyFold)
        back <- Conv.sym(registerFalse)
        both <- Conv.trans(stepFalse, back)
        r <- rules.disch(positive, both)
      } yield r

      // a program with a head f: the head decides on both sides alike
      step <- for {
        tailBody <- open(kit, stepGoal, f).flatMap(open(kit, _, tail))
        p <- imp(kit, tailBody)
        (hypothesisTerm, goalTerm) = p
        hypothesis <- assume(hypothesisTerm)
        p2 <- imp(kit, goalTerm)
        (positiveTerm, goal) = p2
        positives <- assume(positiveTerm)
        every <- kit.at("\\f:prod(num,num). \\r:bool. NUM_LT 0 (FST f) /\\ r")
        truth <- kit.term("T", Type.Bool)
        consEvery <- kit.fact("LIST_FOLD_CONS").map(at(_, Pairs, Type.Bool))
          .flatMap(rules.specAll(_, List(every, truth, f, tail))).flatMap(normal)
        split0 <- LogicError.lift(Kernel.eqMp(consEvery, positives))
        numeratorPositive <- rules.conjElim1(split0)
        tailPositive <- rules.conjElim2(split0)
        ih <- rules.mp(hypothesis, tailPositive)

        consTerm <- kit.at("\\f:prod(num,num). \\Q:word(prod(num,num)). LIST_CONS f Q", f, tail)
        onNumbers <- rules.specAll(stepCons, List(f, tail, n, m))
        unfolded <- Conv.unfold(registerStep, List(consTerm, n, m))
        body <- Limit.rightOf(unfolded)
        pieces <- folded(body)
        (g, start, _) = pieces
        consFold <- kit.fact("LIST_FOLD_CONS").map(at(_, Pairs, Type.Bool))
          .flatMap(rules.specAll(_, List(g, start, f, tail))).flatMap(normal)
        onRegisters <- Conv.trans(unfolded, consFold)
        tailUnfolded <- Conv.unfold(registerStep, List(tail, n, m))
        tailBack <- Conv.sym(tailUnfolded)

        numbersRight <- Limit.rightOf(onNumbers)
        c3 <- conditional(numbersRight)
        (test, lands0, numbersElse) = c3
        registersRight <- Limit.rightOf(onRegisters)
        r3 <- conditional(registersRight)
        (registerTest, registerLands, registerElse) = r3

        a <- kit.at("\\f:prod(num,num). FST f", f)
        q <- kit.at("\\f:prod(num,num). SND f", f)

        equal <- split(kit, test)(
          holds =>
            for {
              qNonZero <- rules.conjElim1(holds)
              dividesNA <- rules.conjElim2(holds)
              qPositive <- positive(kit, q, qNonZero)
              read <- kit.applyTo(applies, List(n, a, q), nPositive._2, numeratorPositive, qPositive)
              dominated <- LogicError.lift(Kernel.eqMp(read, dividesNA))
              registerHolds <- rules.conjIntro(qNonZero, dominated)
              chosen1 <- kit.fact("COND_TRUE").map(Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), _))
              numbersIs <- kit.applyTo(chosen1, List(test, lands0, numbersElse), holds)
              registersIs <- kit.applyTo(chosen1, List(registerTest, registerLands, registerElse), registerHolds)
              landing <- kit.applyTo(lands, List(n, a, q, m), nPositive._2, numeratorPositive, qPositive, dividesNA)
              left <- transAll(onNumbers, numbersIs, landing)
              right <- Conv.trans(onRegisters, registersIs)
              back <- Conv.sym(right)
              r <- Conv.trans(left, back)
            } yield r,
          fails =>
            for {
              registerFails <- for {
                h <- assume(registerTest)
                qNonZero <- rules.conjElim1(h)
                dominated <- rules.conjElim2(h)
                qPositive <- positive(kit, q, qNonZero)
                read <- kit.applyTo(applies, List(n, a, q), nPositive._2, numeratorPositive, qPositive)
                dividesNA <- Conv.sym(read).flatMap(e => LogicError.lift(Kernel.eqMp(e, dominated)))
                numbersHold <- rules.conjIntro(qNonZero, dividesNA)
                absurd <- rules.notElim(fails, numbersHold)
                r <- rules.notIntro(registerTest, absurd)
              } yield r
              chosen0 <- kit.fact("COND_FALSE").map(Kernel.instType(Map(Classical.TypeVariable -> Type.Bool), _))
              numbersIs <- kit.applyTo(chosen0, List(test, lands0, numbersElse), fails)
              registersIs <- kit.applyTo(chosen0, List(registerTest, registerLands, registerElse), registerFails)
              left <- transAll(onNumbers, numbersIs, ih)
              right <- transAll(onRegisters, registersIs, tailBack)
              back <- Conv.sym(right)
              r <- Conv.trans(left, back)
            } yield r
        )
        _ <- kit.landsOn(equal, goal)
        r <- rules.disch(positiveTerm, equal).flatMap(rules.disch(hypothesisTerm, _)).flatMap(rules.genAll(_, List(f, tail)))
      } yield r

      both <- rules.conjIntro(base, step)
      all <- rules.mp(induction, both)
      atP <- rules.spec(program, all)
      result <- rules.disch(nPositive._1, atP).flatMap(rules.genAll(_, List(program, n, m)))
    } yield result
  }
}
