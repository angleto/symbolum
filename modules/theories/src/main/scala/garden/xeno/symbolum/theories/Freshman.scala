package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Fermat's little theorem on `num`, and the binomial theorem on `num` it needs, derived for
 * `Primes` and published there.
 *
 * == The binomial theorem is derived here and not carried over from the reals ==
 *
 * `Series.POWER_BINOMIAL` is the binomial theorem over the reals, and the obvious route is to carry
 * it across `real_of_num`, which is injective and commutes with sums, products and powers. That
 * route was built first and works, and it charges the sixteen axioms of a complete ordered field to
 * a theorem about the naturals: `NothingOverNumRestsOnTheRealsSpec` holds `Primes` to resting on no
 * axiom of the reals, and the reason it gives is that a theorem about arithmetic resting on the
 * reals is a theorem about something else. So the binomial theorem is proved by Pascal's rule
 * instead, by induction on the exponent, over two facts about finite sums on `num` that were not
 * there either: a sum of two families and a family times a constant. Everything here costs the
 * naturals' two axioms and no other.
 *
 * == The route to Fermat ==
 *
 *  - `p` divides `C(p, k)` for `0 < k < p`: `C(p, k) * (k! * (p - k)!) = p!`, `p` divides `p!`, and by
 *    Euclid's lemma `p` divides one of the three factors; it divides neither factorial, because a
 *    prime divides no factorial of a number below it.
 *  - So in the binomial expansion of `(a + 1)^p` every term but the first and the last is a
 *    multiple of `p`, and `(a + 1)^p` is congruent to `a^p + 1`.
 *  - And `a^p` is congruent to `a` by induction on `a`, the step being that congruence.
 *
 * == One instrument that was measured ==
 *
 * SEMIRING reads `SUC 0` as an atom, so `SUC 0 * SUC 0` is not reduced and an identity whose two
 * sides differ by that is refused. `byRewriting` turns every `SUC 0` into the numeral `1` in a
 * second pass, after the equations that open a sum at `SUC 0` have fired, which is why the pass is
 * separate.
 */
private[theories] object Freshman {

  /**
   * What the derivations below read: the connectives and the signature of `Primes`, the
   * natural-number normaliser, the induction driver, and every fact they use, by the name the
   * library publishes it under, so a derivation reads as the argument it is.
   */
  final case class Kit(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    semiring: Semiring,
    induct: Induct,
    fact: String => Either[LogicError, Kernel.Thm]
  ) {
    val rules: Rules = logic.rules
    val numbers: Type = TyApp(Natural.TypeName, Nil)
    val values: Type = TyApp(Real.TypeName, Nil)

    def term(text: String, ty: Type): Either[LogicError, Term] = Parser.term(theory, notation, text, ty)
    def proposition(text: String): Either[LogicError, Term] = Parser.proposition(theory, notation, text)
    def assume(text: String): Either[LogicError, (Term, Kernel.Thm)] =
      proposition(text).flatMap(p => LogicError.lift(Kernel.assume(p)).map(p -> _))
    def at(template: String, arguments: Term*): Either[LogicError, Term] =
      for {
        lambda <- Parser.term(theory, notation, template)
        applied <- LogicError.lift(Term.appAll(lambda, arguments.toList))
        reduced <- Conv.betaNormalise(applied)
        right <- Limit.rightOf(reduced)
      } yield right
    /** `name` specialised at `args` and detached from `premises` in order. */
    def use(name: String, args: List[Term], premises: Kernel.Thm*): Either[LogicError, Kernel.Thm] =
      fact(name).flatMap(applyTo(_, args, premises*))
    def applyTo(theorem: Kernel.Thm, args: List[Term], premises: Kernel.Thm*): Either[LogicError, Kernel.Thm] =
      premises.foldLeft(rules.specAll(theorem, args).flatMap(Limit.normalised))((acc, p) => acc.flatMap(rules.mp(_, p)))
    def landsOn(theorem: Kernel.Thm, target: Term): Either[LogicError, Kernel.Thm] =
      if (theorem.conclusion == target) Right(theorem)
      else Left(NotOfForm(s"a proof of ${Show.show(notation, target)}", theorem.conclusion))
    /** An equation `f x = f y` from `x = y`, for `f` a lambda written as text. */
    def congruence(template: String, equation: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      Parser.term(theory, notation, template).flatMap(Conv.apTerm(_, equation)).flatMap(Conv.betaSides)
  }


  /**
   * `goal`, an equation of naturals, by rewriting each side with ground equations and then with
   * `SUC 0 = 1`, and SEMIRING on what is left. Two passes because the numeral rule would otherwise
   * turn a `NUM_SUM f (SUC 0)` into `NUM_SUM f 1` before the equation that opens it could fire.
   */
  private def byRewriting(kit: Kit, goal: Term, leftEquations: Vector[Kernel.Thm], rightEquations: Vector[Kernel.Thm]): Either[LogicError, Kernel.Thm] =
    for {
      sides <- Term.destEq(goal).toRight(NotOfForm("an equation", goal))
      toNumeral <- kit.fact("NUM_ONE_SUC").flatMap(Conv.sym)
      numeralRules <- Rewrite.Rule.all(kit.logic, Vector(toNumeral))
      leftRules <- Rewrite.Rule.all(kit.logic, leftEquations)
      rightRules <- Rewrite.Rule.all(kit.logic, rightEquations)
      leftMoved <- Rewrite.rewrite(leftRules, sides._1)
      rightMoved <- Rewrite.rewrite(rightRules, sides._2)
      leftTerm <- Limit.rightOf(leftMoved)
      rightTerm <- Limit.rightOf(rightMoved)
      leftNumeral <- Rewrite.rewrite(numeralRules, leftTerm)
      rightNumeral <- Rewrite.rewrite(numeralRules, rightTerm)
      leftFinal <- Limit.rightOf(leftNumeral)
      rightFinal <- Limit.rightOf(rightNumeral)
      middle <- LogicError.lift(Term.eq(leftFinal, rightFinal)).flatMap(kit.semiring.prove)
      leftAll <- Conv.trans(leftMoved, leftNumeral)
      rightAll <- Conv.trans(rightMoved, rightNumeral)
      result <- Conv.trans(leftAll, middle).flatMap(t => Conv.sym(rightAll).flatMap(Conv.trans(t, _)))
      landed <- kit.landsOn(result, goal)
    } yield landed

  /** `|- !f g n. NUM_SUM (\k. f k + g k) n = NUM_SUM f n + NUM_SUM g n` */
  private def sumAdd(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val fn = Type.fun(kit.numbers, kit.numbers)
    val f = Term.variable("f", fn)
    val g = Term.variable("g", fn)
    for {
      statement <- kit.proposition("!n:num. NUM_SUM (\\k:num. (f:num -> num) k + (g:num -> num) k) n = NUM_SUM f n + NUM_SUM g n")
      both <- kit.term("\\k:num. (f:num -> num) k + (g:num -> num) k", fn)
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            z1 <- kit.use("NUM_SUM_ZERO", List(both))
            z2 <- kit.use("NUM_SUM_ZERO", List(f))
            z3 <- kit.use("NUM_SUM_ZERO", List(g))
            result <- byRewriting(kit, base, Vector(z1), Vector(z2, z3))
          } yield result,
        step => {
          val k = step.variable
          for {
            s1 <- kit.use("NUM_SUM_SUC", List(both, k))
            s2 <- kit.use("NUM_SUM_SUC", List(f, k))
            s3 <- kit.use("NUM_SUM_SUC", List(g, k))
            result <- byRewriting(kit, step.goal, Vector(s1, step.hypothesis), Vector(s2, s3))
          } yield result
        }
      )
      result <- kit.rules.genAll(proved, List(f, g))
    } yield result
  }

  /** `|- !f c n. NUM_SUM (\k. f k * c) n = NUM_SUM f n * c` */
  private def sumTimes(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val fn = Type.fun(kit.numbers, kit.numbers)
    val f = Term.variable("f", fn)
    val c = Term.variable("c", kit.numbers)
    for {
      statement <- kit.proposition("!n:num. NUM_SUM (\\k:num. (f:num -> num) k * (c:num)) n = NUM_SUM f n * c")
      scaled <- kit.term("\\k:num. (f:num -> num) k * (c:num)", fn)
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            z1 <- kit.use("NUM_SUM_ZERO", List(scaled))
            z2 <- kit.use("NUM_SUM_ZERO", List(f))
            result <- byRewriting(kit, base, Vector(z1), Vector(z2))
          } yield result,
        step => {
          val k = step.variable
          for {
            s1 <- kit.use("NUM_SUM_SUC", List(scaled, k))
            s2 <- kit.use("NUM_SUM_SUC", List(f, k))
            result <- byRewriting(kit, step.goal, Vector(s1, step.hypothesis), Vector(s2))
          } yield result
        }
      )
      result <- kit.rules.genAll(proved, List(f, c))
    } yield result
  }

  /** `SUC 0 + x = SUC x`, at the term `x`. */
  private def onePlus(kit: Kit, x: Term): Either[LogicError, Kernel.Thm] =
    for {
      zero <- kit.term("0", kit.numbers)
      shifted <- kit.use("NUM_SUC_ADD", List(zero, x))
      swapped <- kit.use("NUM_ADD_SYM", List(zero, x))
      unit <- kit.use("NUM_ADD_ZERO", List(x))
      inner <- Conv.trans(swapped, unit).flatMap(kit.congruence("\\y:num. SUC y", _))
      result <- Conv.trans(shifted, inner)
    } yield result

  /** `|- !a n. NUM_POW (SUC a) n = NUM_SUM (\k. NUM_CHOOSE n k * NUM_POW a k) (SUC n)`, by Pascal. */
  private def binomial(kit: Kit, add: Kernel.Thm, times: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val fn = Type.fun(kit.numbers, kit.numbers)
    val a = Term.variable("a", kit.numbers)
    val u = Term.variable("u", kit.numbers)
    for {
      statement <- kit.proposition("!n:num. NUM_POW (SUC (a:num)) n = NUM_SUM (\\k:num. NUM_CHOOSE n k * NUM_POW a k) (SUC n)")
      zero <- kit.term("0", kit.numbers)
      sucZero <- kit.term("SUC 0", kit.numbers)
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            terms <- kit.term("\\k:num. NUM_CHOOSE 0 k * NUM_POW (a:num) k", fn)
            sucA <- kit.term("SUC (a:num)", kit.numbers)
            p0 <- kit.use("NUM_POW_ZERO", List(sucA))
            s1 <- kit.use("NUM_SUM_SUC", List(terms, zero))
            s2 <- kit.use("NUM_SUM_ZERO", List(terms))
            c0 <- kit.use("NUM_CHOOSE_ZERO", List(zero))
            a0 <- kit.use("NUM_POW_ZERO", List(a))
            result <- byRewriting(kit, base, Vector(p0), Vector(s1, s2, c0, a0))
          } yield result,
        step => {
          val n = step.variable
          for {
            sucN <- kit.at("\\n:num. SUC n", n)
            sucA <- kit.term("SUC (a:num)", kit.numbers)
            f <- kit.at("\\n:num. \\k:num. NUM_CHOOSE n k * NUM_POW (a:num) k", n)
            fNext <- kit.at("\\n:num. \\k:num. NUM_CHOOSE (SUC n) k * NUM_POW (a:num) k", n)
            h <- kit.at("\\n:num. \\k:num. NUM_CHOOSE n k * NUM_POW (a:num) (SUC k)", n)
            g <- kit.at("\\n:num. \\k:num. NUM_CHOOSE n (SUC k) * NUM_POW (a:num) (SUC k)", n)
            sumF <- kit.at("\\n:num. NUM_SUM (\\k:num. NUM_CHOOSE n k * NUM_POW (a:num) k) (SUC n)", n)

            // (SUC a)^n * a = the sum of the H terms: the power moves inside, one index along
            timesA <- rules.specAll(times, List(f, a, sucN)).flatMap(Limit.normalised)
            k = Term.variable("k", kit.numbers)
            fTimesA <- kit.at("\\f:num -> num. \\k:num. f k * (a:num)", f)
            pointGoal <- LogicError.lift(Term.app(fTimesA, k)).flatMap(t => LogicError.lift(Term.app(h, k)).flatMap(t2 =>
              Conv.betaNormalise(t).flatMap(Limit.rightOf).flatMap(l => Conv.betaNormalise(t2).flatMap(Limit.rightOf).flatMap(r => LogicError.lift(Term.eq(l, r)))))
            )
            powerStep <- kit.use("NUM_POW_SUC", List(a, k))
            point <- byRewriting(kit, pointGoal, Vector.empty, Vector(powerStep))
            guardK <- kit.at("\\k:num. \\m:num. NUM_LT k m", k, sucN)
            everyK <- rules.disch(guardK, point).flatMap(rules.gen(k, _))
            toH <- kit.use("NUM_SUM_CONGRUENCE_BELOW", List(fTimesA, h, sucN), everyK)
            e4 <- Conv.sym(timesA).flatMap(Conv.trans(_, toH))

            // the sum of the F terms is its first term plus the sum of the G terms
            split <- kit.use("NUM_SUM_SPLIT", List(f, sucZero, n))
            oneN <- onePlus(kit, n)
            splitAtSuc <- Limit.rewriteInProposition(oneN, split)
            middleF <- kit.at("\\f:num -> num. \\u:num. f (NUM_ADD (SUC 0) u)", f)
            oneU <- onePlus(kit, u)
            pointF <- LogicError.lift(Term.app(middleF, u)).flatMap(Conv.betaNormalise).flatMap(Limit.rightOf).flatMap(l =>
              LogicError.lift(Term.app(g, u)).flatMap(Conv.betaNormalise).flatMap(Limit.rightOf).flatMap(r => LogicError.lift(Term.eq(l, r))))
            pointFProved <- byRewriting(kit, pointF, Vector(oneU), Vector.empty)
            guardU <- kit.at("\\u:num. \\m:num. NUM_LT u m", u, n)
            everyU <- rules.disch(guardU, pointFProved).flatMap(rules.gen(u, _))
            toG <- kit.use("NUM_SUM_CONGRUENCE_BELOW", List(middleF, g, n), everyU)
            firstPeeled <- kit.use("NUM_SUM_SUC", List(f, zero))
            firstEmpty <- kit.use("NUM_SUM_ZERO", List(f))
            chooseZero <- kit.use("NUM_CHOOSE_ZERO", List(n))
            powerZero <- kit.use("NUM_POW_ZERO", List(a))

            // the left side: (SUC a)^(SUC n) = (SUC a)^n * SUC a = S * a + S
            powerSuc <- kit.use("NUM_POW_SUC", List(sucA, n))
            timesSuc <- kit.use("NUM_MUL_SUC", List(sumF, a))
            e1 <- Limit.rewriteInProposition(step.hypothesis, powerSuc)
            e2 <- Conv.trans(e1, timesSuc)
            e3 <- Limit.rewriteInProposition(e4, e2)

            // the right side, by Pascal
            splitNext <- kit.use("NUM_SUM_SPLIT", List(fNext, sucZero, sucN))
            oneSucN <- onePlus(kit, sucN)
            splitNextAtSuc <- Limit.rewriteInProposition(oneSucN, splitNext)
            middleNext <- kit.at("\\f:num -> num. \\u:num. f (NUM_ADD (SUC 0) u)", fNext)
            both <- kit.at("\\h:num -> num. \\g:num -> num. \\k:num. h k + g k", h, g)
            chooseSuc <- kit.use("NUM_CHOOSE_SUC", List(n, u))
            pointNext <- LogicError.lift(Term.app(middleNext, u)).flatMap(Conv.betaNormalise).flatMap(Limit.rightOf).flatMap(l =>
              LogicError.lift(Term.app(both, u)).flatMap(Conv.betaNormalise).flatMap(Limit.rightOf).flatMap(r => LogicError.lift(Term.eq(l, r))))
            pointNextProved <- byRewriting(kit, pointNext, Vector(oneU, chooseSuc), Vector.empty)
            guardNext <- kit.at("\\u:num. \\m:num. NUM_LT u m", u, sucN)
            everyNext <- rules.disch(guardNext, pointNextProved).flatMap(rules.gen(u, _))
            toBoth <- kit.use("NUM_SUM_CONGRUENCE_BELOW", List(middleNext, both, sucN), everyNext)
            added <- rules.specAll(add, List(h, g, sucN)).flatMap(Limit.normalised)
            gPeeled <- kit.use("NUM_SUM_SUC", List(g, n))
            above <- kit.use("NUM_LT_SUC", List(n))
            chooseAbove <- kit.use("NUM_CHOOSE_ABOVE", List(n, sucN), above)
            powerAtSucN <- kit.at("\\n:num. NUM_POW (a:num) (SUC n)", n)
            zeroTimes <- kit.use("NUM_ZERO_MUL", List(powerAtSucN))
            nextPeeled <- kit.use("NUM_SUM_SUC", List(fNext, zero))
            nextEmpty <- kit.use("NUM_SUM_ZERO", List(fNext))
            chooseZeroNext <- kit.use("NUM_CHOOSE_ZERO", List(sucN))

            result <- byRewriting(
              kit,
              step.goal,
              Vector(e3, splitAtSuc, toG, firstPeeled, firstEmpty, chooseZero, powerZero),
              Vector(splitNextAtSuc, toBoth, added, gPeeled, chooseAbove, zeroTimes, nextPeeled, nextEmpty, chooseZeroNext, powerZero)
            )
          } yield result
        }
      )
      result <- rules.gen(a, proved)
    } yield result
  }


  /** `|- !d g n. (!u. NUM_LT u n ==> NUM_DIVIDES d (g u)) ==> NUM_DIVIDES d (NUM_SUM g n)` */
  private def dividesSum(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val d = Term.variable("d", kit.numbers)
    val g = Term.variable("g", Type.fun(kit.numbers, kit.numbers))
    val u = Term.variable("u", kit.numbers)
    for {
      statement <- kit.proposition(
        "!n:num. (!u:num. NUM_LT u n ==> NUM_DIVIDES (d:num) ((g:num -> num) u)) ==> NUM_DIVIDES d (NUM_SUM g n)")
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            parts <- kit.logic.destImp(base).toRight(NotOfForm("an implication", base))
            empty <- kit.use("NUM_SUM_ZERO", List(g)).flatMap(Conv.sym)
            divides <- kit.use("NUM_DIVIDES_ZERO", List(d))
            atZero <- Limit.rewriteWith(empty, divides)
            result <- rules.disch(parts._1, atZero).flatMap(kit.landsOn(_, base))
          } yield result,
        step => {
          val k = step.variable
          for {
            parts <- kit.logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
            assumed <- LogicError.lift(Kernel.assume(parts._1))
            guard <- kit.at("\\u:num. \\k:num. NUM_LT u k", u, k)
            assumedGuard <- LogicError.lift(Kernel.assume(guard))
            sucK <- kit.at("\\k:num. SUC k", k)
            below <- kit.use("NUM_LT_SUC", List(k))
            further <- rules.conjIntro(assumedGuard, below).flatMap(both => kit.use("NUM_LT_TRANS", List(u, k, sucK), both))
            earlier <- rules.spec(u, assumed).flatMap(rules.mp(_, further))
            narrowed <- rules.disch(guard, earlier).flatMap(rules.gen(u, _))
            upToK <- rules.mp(step.hypothesis, narrowed)
            last <- rules.spec(k, assumed).flatMap(rules.mp(_, below))
            sumK <- kit.at("\\k:num. NUM_SUM (g:num -> num) k", k)
            termK <- kit.at("\\k:num. (g:num -> num) k", k)
            added <- rules.conjIntro(upToK, last).flatMap(both => kit.use("NUM_DIVIDES_ADD", List(d, sumK, termK), both))
            peeled <- kit.use("NUM_SUM_SUC", List(g, k)).flatMap(Conv.sym)
            atSuc <- Limit.rewriteWith(peeled, added)
            result <- rules.disch(parts._1, atSuc).flatMap(kit.landsOn(_, step.goal))
          } yield result
        }
      )
      result <- rules.genAll(proved, List(d, g))
    } yield result
  }

  /** `|- !p n. NUM_PRIME p ==> NUM_LT n p ==> ~(NUM_DIVIDES p (NUM_FACT n))` */
  private def notDividesFactorial(kit: Kit): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val p = Term.variable("p", kit.numbers)
    for {
      assumedPrime <- kit.assume("NUM_PRIME (p:num)")
      (prime, isPrime) = assumedPrime
      aboveOne <- kit.use("NUM_PRIME_ABOVE_ONE", List(p), isPrime)
      statement <- kit.proposition("!n:num. NUM_LT n (p:num) ==> ~(NUM_DIVIDES p (NUM_FACT n))")
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            parts <- kit.logic.destImp(base).toRight(NotOfForm("an implication", base))
            denied <- kit.logic.destNot(parts._2).toRight(NotOfForm("a denial", parts._2))
            assumedDivides <- LogicError.lift(Kernel.assume(denied))
            one <- kit.fact("NUM_FACT_ZERO")
            dividesOne <- Limit.rewriteWith(one, assumedDivides)
            isOne <- kit.use("NUM_DIVIDES_ONE", List(p), dividesOne)
            collapsed <- Limit.rewriteInProposition(isOne, aboveOne)
            sucZero <- kit.term("SUC 0", kit.numbers)
            irreflexive <- kit.use("NUM_LT_IRREFL", List(sucZero))
            absurd <- rules.notElim(irreflexive, collapsed)
            refuted <- rules.notIntro(denied, absurd)
            result <- rules.disch(parts._1, refuted).flatMap(kit.landsOn(_, base))
          } yield result,
        step => {
          val k = step.variable
          for {
            parts <- kit.logic.destImp(step.goal).toRight(NotOfForm("an implication", step.goal))
            assumedBelow <- LogicError.lift(Kernel.assume(parts._1))
            denied <- kit.logic.destNot(parts._2).toRight(NotOfForm("a denial", parts._2))
            assumedDivides <- LogicError.lift(Kernel.assume(denied))
            factK <- kit.at("\\k:num. NUM_FACT k", k)
            sucK <- kit.at("\\k:num. SUC k", k)
            opened <- kit.use("NUM_FACT_SUC", List(k))
            dividesProduct <- Limit.rewriteWith(opened, assumedDivides)
            cases <- kit.use("NUM_EUCLID", List(p, factK, sucK), isPrime, dividesProduct)
            // the factorial: k < p, so the hypothesis refuses it
            factCase <- for {
              caseTerm <- kit.at("\\k:num. NUM_DIVIDES (p:num) (NUM_FACT k)", k)
              assumedCase <- LogicError.lift(Kernel.assume(caseTerm))
              below <- kit.use("NUM_LT_SUC", List(k))
              kBelowP <- rules.conjIntro(below, assumedBelow).flatMap(both => kit.use("NUM_LT_TRANS", List(k, sucK, p), both))
              refusal <- rules.mp(step.hypothesis, kBelowP)
              absurd <- rules.notElim(refusal, assumedCase)
            } yield absurd
            // the successor: p would be at most SUC k, which is below p
            sucCase <- for {
              caseTerm <- kit.at("\\k:num. NUM_DIVIDES (p:num) (SUC k)", k)
              assumedCase <- LogicError.lift(Kernel.assume(caseTerm))
              sizes <- kit.use("NUM_DIVIDES_LE", List(p, sucK), assumedCase)
              notAtMost <- kit.use("NUM_LT_NOT_LE", List(sucK, p), assumedBelow)
              atMostCase <- kit.at("\\k:num. NUM_LE (p:num) (SUC k)", k)
              assumedAtMost <- LogicError.lift(Kernel.assume(atMostCase))
              first <- rules.notElim(notAtMost, assumedAtMost)
              zeroCase <- kit.at("\\k:num. SUC k = 0", k)
              assumedZero <- LogicError.lift(Kernel.assume(zeroCase))
              notZero <- kit.use("NUM_SUC_NOT_ZERO", List(k))
              second <- rules.notElim(notZero, assumedZero)
              absurd <- rules.disjElim(sizes, first, second)
            } yield absurd
            absurd <- rules.disjElim(cases, factCase, sucCase)
            refuted <- rules.notIntro(denied, absurd)
            result <- rules.disch(parts._1, refuted).flatMap(kit.landsOn(_, step.goal))
          } yield result
        }
      )
      n = Term.variable("n", kit.numbers)
      result <- rules.spec(n, proved).flatMap(rules.disch(prime, _)).flatMap(rules.genAll(_, List(p, n)))
    } yield result
  }

  /** `|- !p k. NUM_PRIME p ==> NUM_LT 0 k ==> NUM_LT k p ==> NUM_DIVIDES p (NUM_CHOOSE p k)` */
  private def dividesChoose(kit: Kit, notDivides: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val p = Term.variable("p", kit.numbers)
    val k = Term.variable("k", kit.numbers)
    for {
      a1 <- kit.assume("NUM_PRIME (p:num)"); (prime, isPrime) = a1
      a2 <- kit.assume("NUM_LT 0 (k:num)"); (positive, isPositive) = a2
      a3 <- kit.assume("NUM_LT (k:num) (p:num)"); (below, isBelow) = a3
      zero <- kit.term("0", kit.numbers)
      rest <- kit.term("NUM_SUB (p:num) (k:num)", kit.numbers)
      atMost <- kit.use("NUM_LE_OF_LT", List(k, p), isBelow)
      restPlusK <- kit.use("NUM_SUB_ADD", List(p, k), atMost)
      swapped <- kit.use("NUM_ADD_SYM", List(k, rest))
      kPlusRest <- Conv.trans(swapped, restPlusK)
      identity <- kit.use("NUM_CHOOSE_FACTORIAL", List(rest, k))
      atP <- Limit.rewriteInProposition(kPlusRest, identity)
      pPositive <- rules.conjIntro(isPositive, isBelow).flatMap(both => kit.use("NUM_LT_TRANS", List(zero, k, p), both))
      reflexive <- kit.use("NUM_LE_REFL", List(p))
      dividesFactorial <- rules.conjIntro(pPositive, reflexive).flatMap(both => kit.use("NUM_FACT_DIVIDES", List(p, p), both))
      dividesProduct <- Conv.sym(atP).flatMap(Limit.rewriteWith(_, dividesFactorial))
      choose <- kit.term("NUM_CHOOSE (p:num) (k:num)", kit.numbers)
      factorials <- kit.term("NUM_FACT (k:num) * NUM_FACT (NUM_SUB p k)", kit.numbers)
      factK <- kit.term("NUM_FACT (k:num)", kit.numbers)
      factRest <- kit.term("NUM_FACT (NUM_SUB (p:num) (k:num))", kit.numbers)
      firstSplit <- kit.use("NUM_EUCLID", List(p, choose, factorials), isPrime, dividesProduct)
      goal <- kit.proposition("NUM_DIVIDES (p:num) (NUM_CHOOSE p (k:num))")
      atChoose <- LogicError.lift(Kernel.assume(goal))
      factorialsCase <- for {
        assumedCase <- kit.assume("NUM_DIVIDES (p:num) (NUM_FACT (k:num) * NUM_FACT (NUM_SUB p k))")
        (_, isCase) = assumedCase
        secondSplit <- kit.use("NUM_EUCLID", List(p, factK, factRest), isPrime, isCase)
        kCase <- for {
          a <- kit.assume("NUM_DIVIDES (p:num) (NUM_FACT (k:num))"); (_, isK) = a
          refusal <- kit.applyTo(notDivides, List(p, k), isPrime, isBelow)
          absurd <- rules.notElim(refusal, isK)
        } yield absurd
        restCase <- for {
          a <- kit.assume("NUM_DIVIDES (p:num) (NUM_FACT (NUM_SUB p (k:num)))"); (_, isRest) = a
          shifted <- kit.use("NUM_ADD_LT_MONOTONE", List(rest, zero, k), isPositive)
          unit <- kit.use("NUM_ADD_ZERO", List(rest))
          left <- Limit.rewriteInProposition(unit, shifted)
          restBelow <- Limit.rewriteInProposition(restPlusK, left)
          refusal <- kit.applyTo(notDivides, List(p, rest), isPrime, restBelow)
          absurd <- rules.notElim(refusal, isRest)
        } yield absurd
        absurd <- rules.disjElim(secondSplit, kCase, restCase)
        result <- rules.falsityElim(goal, absurd)
      } yield result
      result0 <- rules.disjElim(firstSplit, atChoose, factorialsCase)
      result <- rules.disch(below, result0).flatMap(rules.disch(positive, _)).flatMap(rules.disch(prime, _)).flatMap(rules.genAll(_, List(p, k)))
    } yield result
  }


  /** From `NUM_PRIME p`, `?r. p = SUC r`: a prime is not zero. */
  private def predecessor(kit: Kit, p: Term, isPrime: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    for {
      cases <- kit.use("NUM_CASES", List(p))
      goal <- kit.at("\\p:num. ?r:num. p = SUC r", p)
      zeroCase <- for {
        caseTerm <- kit.at("\\p:num. p = 0", p)
        assumed <- LogicError.lift(Kernel.assume(caseTerm))
        aboveOne <- kit.use("NUM_PRIME_ABOVE_ONE", List(p), isPrime)
        atZero <- Limit.rewriteInProposition(assumed, aboveOne)
        zero <- kit.term("0", kit.numbers)
        sucZero <- kit.term("SUC 0", kit.numbers)
        positive <- kit.use("NUM_ZERO_LT_SUC", List(zero))
        circle <- rules.conjIntro(positive, atZero).flatMap(both => kit.use("NUM_LT_TRANS", List(zero, sucZero, zero), both))
        irreflexive <- kit.use("NUM_LT_IRREFL", List(zero))
        absurd <- rules.notElim(irreflexive, circle)
        result <- rules.falsityElim(goal, absurd)
      } yield result
      assumedSuc <- LogicError.lift(Kernel.assume(goal))
      result <- rules.disjElim(cases, zeroCase, assumedSuc)
    } yield result
  }

  /** `|- !p a. NUM_PRIME p ==> NUM_CONG p (NUM_POW (SUC a) p) (NUM_ADD (NUM_POW a p) (SUC 0))` */
  private def freshman(kit: Kit, binomialFact: Kernel.Thm, dividesSumFact: Kernel.Thm, dividesChooseFact: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val p = Term.variable("p", kit.numbers)
    val a = Term.variable("a", kit.numbers)
    val r = Term.variable("r", kit.numbers)
    val u = Term.variable("u", kit.numbers)
    val m = Term.variable("m", kit.numbers)
    for {
      a1 <- kit.assume("NUM_PRIME (p:num)"); (prime, isPrime) = a1
      nonZero <- predecessor(kit, p, isPrime)
      a2 <- kit.assume("(p:num) = SUC (r:num)"); (_, isSuc) = a2
      zero <- kit.term("0", kit.numbers)
      sucZero <- kit.term("SUC 0", kit.numbers)

      // SUC 0 + r = p
      shiftedSum <- kit.use("NUM_SUC_ADD", List(zero, r))
      zeroPlus <- kit.use("NUM_ADD_SYM", List(zero, r)).flatMap(e => kit.use("NUM_ADD_ZERO", List(r)).flatMap(Conv.trans(e, _)))
      inner <- kit.congruence("\\x:num. SUC x", zeroPlus)
      oneRest <- Conv.trans(shiftedSum, inner).flatMap(e => Conv.sym(isSuc).flatMap(Conv.trans(e, _)))

      expanded <- kit.applyTo(binomialFact, List(a, p))
      summands <- kit.term("\\k:num. NUM_CHOOSE (p:num) k * NUM_POW (a:num) k", Type.fun(kit.numbers, kit.numbers))
      lastPeeled <- kit.use("NUM_SUM_SUC", List(summands, p))
      split <- kit.use("NUM_SUM_SPLIT", List(summands, sucZero, r))
      splitAtP <- Limit.rewriteInProposition(oneRest, split)
      firstPeeled <- kit.use("NUM_SUM_SUC", List(summands, zero))
      emptyFirst <- kit.use("NUM_SUM_ZERO", List(summands))
      whole <- Conv.trans(expanded, lastPeeled)
      withMiddle <- Limit.rewriteInProposition(splitAtP, whole)
      withFirst <- Limit.rewriteInProposition(firstPeeled, withMiddle)
      withEmpty <- Limit.rewriteInProposition(emptyFirst, withFirst)

      // the middle terms are multiples of p
      middleTerms <- kit.term("\\u:num. NUM_CHOOSE (p:num) (NUM_ADD (SUC 0) u) * NUM_POW (a:num) (NUM_ADD (SUC 0) u)", Type.fun(kit.numbers, kit.numbers))
      a3 <- kit.assume("NUM_LT (u:num) (r:num)"); (guard, isGuard) = a3
      index <- kit.term("NUM_ADD (SUC 0) (u:num)", kit.numbers)
      zeroPlusU <- kit.use("NUM_ADD_SYM", List(zero, u)).flatMap(e => kit.use("NUM_ADD_ZERO", List(u)).flatMap(Conv.trans(e, _)))
      positiveInner <- kit.term("NUM_ADD 0 (u:num)", kit.numbers).flatMap(t => kit.use("NUM_ZERO_LT_SUC", List(t)))
      sucShift <- kit.use("NUM_SUC_ADD", List(zero, u)).flatMap(Conv.sym)
      indexPositive <- Limit.rewriteInProposition(sucShift, positiveInner)
      indexBelow <- kit.use("NUM_ADD_LT_MONOTONE", List(sucZero, u, r), isGuard).flatMap(Limit.rewriteInProposition(oneRest, _))
      chooseDivides <- kit.applyTo(dividesChooseFact, List(p, index), isPrime, indexPositive, indexBelow)
      chooseAt <- kit.term("NUM_CHOOSE (p:num) (NUM_ADD (SUC 0) (u:num))", kit.numbers)
      powerAt <- kit.term("NUM_POW (a:num) (NUM_ADD (SUC 0) (u:num))", kit.numbers)
      termDivides <- kit.use("NUM_DIVIDES_MUL", List(p, chooseAt, powerAt), chooseDivides)
      everyTerm <- rules.disch(guard, termDivides).flatMap(rules.gen(u, _))
      middleDivides <- kit.applyTo(dividesSumFact, List(p, middleTerms, r), everyTerm)
      middle <- kit.term("NUM_SUM (\\u:num. NUM_CHOOSE (p:num) (NUM_ADD (SUC 0) u) * NUM_POW (a:num) (NUM_ADD (SUC 0) u)) (r:num)", kit.numbers)
      multiple <- kit.use("NUM_DIVIDES_ELIM", List(p, middle), middleDivides)
      a4 <- kit.assume("NUM_SUM (\\u:num. NUM_CHOOSE (p:num) (NUM_ADD (SUC 0) u) * NUM_POW (a:num) (NUM_ADD (SUC 0) u)) (r:num) = p * (m:num)")
      (_, isMultiple) = a4
      withMultiple <- Limit.rewriteInProposition(isMultiple, withEmpty)
      chooseZero <- kit.use("NUM_CHOOSE_ZERO", List(p))
      chooseAll <- kit.use("NUM_CHOOSE_ALL", List(p))
      powerZero <- kit.use("NUM_POW_ZERO", List(a))
      c1 <- Limit.rewriteInProposition(chooseZero, withMultiple)
      c2 <- Limit.rewriteInProposition(chooseAll, c1)
      clean <- Limit.rewriteInProposition(powerZero, c2)
      // `SUC 0` is an atom to SEMIRING, so `SUC 0 * SUC 0` would not reduce; the numeral `1` is not.
      toNumeral <- kit.fact("NUM_ONE_SUC").flatMap(Conv.sym)
      cleanOnes <- Limit.rewriteInProposition(toNumeral, clean)
      powerSide <- Limit.rightOf(cleanOnes)
      lhs <- kit.at("\\x:num. x + (p:num) * 0", powerSide)
      rhs <- kit.term("NUM_POW (a:num) (p:num) + 1 + p * (m:num)", kit.numbers)
      identity <- LogicError.lift(Term.eq(lhs, rhs)).flatMap(kit.semiring.prove)
      carried <- Conv.sym(cleanOnes).flatMap(Limit.rewriteInProposition(_, identity))
      target <- kit.term("NUM_POW (SUC (a:num)) (p:num)", kit.numbers)
      plusOne <- kit.term("NUM_POW (a:num) (p:num) + 1", kit.numbers)
      congruent <- kit.use("NUM_CONG_INTRO", List(p, target, plusOne, zero, m), carried)
      backToSuc <- kit.fact("NUM_ONE_SUC")
      cong <- Limit.rewriteInProposition(backToSuc, congruent)
      overM <- rules.existsElim(multiple, m, cong)
      overR <- rules.existsElim(nonZero, r, overM)
      result <- rules.disch(prime, overR).flatMap(rules.genAll(_, List(p, a)))
    } yield result
  }


  /** `|- !p a. NUM_PRIME p ==> NUM_CONG p (NUM_POW a p) a` */
  private def fermat(kit: Kit, freshmanFact: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
    val rules = kit.rules
    val p = Term.variable("p", kit.numbers)
    val r = Term.variable("r", kit.numbers)
    for {
      a1 <- kit.assume("NUM_PRIME (p:num)"); (prime, isPrime) = a1
      statement <- kit.proposition("!a:num. NUM_CONG (p:num) (NUM_POW a p) a")
      zero <- kit.term("0", kit.numbers)
      sucZero <- kit.term("SUC 0", kit.numbers)
      proved <- kit.induct.proveBy(
        statement,
        base =>
          for {
            nonZero <- predecessor(kit, p, isPrime)
            a2 <- kit.assume("(p:num) = SUC (r:num)"); (_, isSuc) = a2
            peeled <- kit.use("NUM_POW_SUC", List(zero, r))
            smaller <- kit.term("NUM_POW 0 (r:num)", kit.numbers)
            vanishes <- kit.use("NUM_MUL_ZERO", List(smaller))
            atSuc <- Conv.trans(peeled, vanishes)
            atP <- Conv.sym(isSuc).flatMap(Limit.rewriteInProposition(_, atSuc))
            power <- Limit.destructEquation(atP).map(_._1)
            reflexive <- kit.use("NUM_CONG_REFL", List(p, power))
            landed <- Limit.rewriteWith(atP, reflexive)
            result <- rules.existsElim(nonZero, r, landed).flatMap(kit.landsOn(_, base))
          } yield result,
        step => {
          val k = step.variable
          for {
            fresh <- kit.applyTo(freshmanFact, List(p, k), isPrime)
            powerK <- kit.at("\\k:num. NUM_POW k (p:num)", k)
            reflexive <- kit.use("NUM_CONG_REFL", List(p, sucZero))
            added <- kit.use("NUM_CONG_ADD", List(p, powerK, k, sucZero, sucZero), step.hypothesis, reflexive)
            powerSuc <- kit.at("\\k:num. NUM_POW (SUC k) (p:num)", k)
            middle <- kit.at("\\k:num. NUM_ADD (NUM_POW k (p:num)) (SUC 0)", k)
            end <- kit.at("\\k:num. NUM_ADD k (SUC 0)", k)
            chained <- kit.use("NUM_CONG_TRANS", List(p, powerSuc, middle, end), fresh, added)
            shifted <- kit.use("NUM_ADD_SUC", List(k, zero))
            unit <- kit.use("NUM_ADD_ZERO", List(k)).flatMap(kit.congruence("\\x:num. SUC x", _))
            successor <- Conv.trans(shifted, unit)
            result <- Limit.rewriteWith(successor, chained).flatMap(kit.landsOn(_, step.goal))
          } yield result
        }
      )
      a = Term.variable("a", kit.numbers)
      result <- rules.spec(a, proved).flatMap(rules.disch(prime, _)).flatMap(rules.genAll(_, List(p, a)))
    } yield result
  }

  /** The eight facts `Primes` publishes from this file, under the names it gives them. */
  def derive(kit: Kit): Either[LogicError, Map[String, Kernel.Thm]] =
    for {
      add <- sumAdd(kit)
      times <- sumTimes(kit)
      expansion <- binomial(kit, add, times)
      sums <- dividesSum(kit)
      factorials <- notDividesFactorial(kit)
      chooses <- dividesChoose(kit, factorials)
      dream <- freshman(kit, expansion, sums, chooses)
      little <- fermat(kit, dream)
    } yield Map(
      Primes.SumAdd -> add,
      Primes.SumTimes -> times,
      Primes.Binomial -> expansion,
      Primes.DividesSum -> sums,
      Primes.NotDividesFactorial -> factorials,
      Primes.DividesChoose -> chooses,
      Primes.Freshman -> dream,
      Primes.Fermat -> little
    )
}
