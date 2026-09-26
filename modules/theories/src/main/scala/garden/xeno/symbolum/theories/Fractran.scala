package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Conway's FRACTRAN, as a relation on `num` and runs the kernel checks.
 *
 * A program is a list of fractions and the state is one natural number: from `n`, multiply by the
 * first fraction `p/q` for which `n * p/q` is a natural number, and stop when there is none.
 * `docs/adr/0054` is the decision this file implements, and the alternatives it rejected.
 *
 * == The step is a fold into `bool` ==
 *
 * {{{
 *   FRACTRAN_STEP P n m =
 *     LIST_FOLD (\f r. COND (~(SND f = 0) /\ NUM_DIVIDES (SND f) (n * FST f))
 *                           (m = NUM_DIV (n * FST f) (SND f))
 *                           r)
 *               F P
 * }}}
 *
 * A program is a `word (prod(num, num))` read as a list, each pair a numerator and a denominator,
 * and nothing reduces them. The fold is what says "first": the fraction at the head decides when it
 * applies, and the rest of the list is read only when it does not. The empty list is `F`, so a state
 * no fraction applies to has no successor, and that is [[Fractran.HaltsName]]. A pair with denominator
 * zero never applies, which keeps `NUM_DIV x 0`, a value nothing determines, out of every statement.
 *
 * == A run is `REACH`, with the step counted ==
 *
 * `FRACTRAN_REACHES P n k m` is `Reaching`'s closure with the counted relation equal to the step, so
 * the counter is the length of the run. No second closure is defined.
 *
 * == The interpreter proposes, the kernel decides ==
 *
 * [[Fractran.trace]] runs a program on `BigInt` and is believed by nothing. [[certify]] hands
 * each state of a trace to the kernel: the product through `Digits.multiply`, the quotient through
 * `Value`, and every fraction that is passed over refused by a remainder that is not zero. A trace
 * the program does not produce comes back as a refusal and never as a theorem, and `FractranSpec`
 * feeds it such traces.
 *
 * == What is not here ==
 *
 * What a program computes on the exponents of its primes, which is card `626ad37f` and wants the
 * valuation at a prime first; and whether Conway's generalised Collatz maps meet `Collatz`, which is
 * card `b0d2ada9`. Until the first lands, `3/2` sending `72` to `243` in three steps is a fact here and
 * "it adds the exponents" is not.
 *
 * It sits beside the chain, like `Collatz` and `EuclidAlgorithm`: nothing below needs its constants,
 * and making it a link moves `Chain.widest`, the reading register and the guide's map.
 */
final class Fractran private (
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm],
  kit: Freshman.Kit,
  value: Value,
  modZero: Kernel.Thm
) extends Signature {
  import Fractran.*
  import Steps.*

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /** The equation defining `name`. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact, by name. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))

  private val rules: Rules = logic.rules
  private val digits: Digits = value.digits

  /** The program as a term, `LIST_CONS (PAIR p q) (...)` down to the empty word. */
  def program(fractions: Vector[(BigInt, BigInt)]): Either[LogicError, Term] =
    for {
      empty <- LogicError.lift(theory.constant(Concatenation.Empty, Programs))
      cons <- LogicError.lift(theory.constant(Listing.Cons, Type.fun(Pairs, Type.fun(Programs, Programs))))
      pairing <- LogicError.lift(theory.constant(Product.Pairing, Type.fun(Num, Type.fun(Num, Pairs))))
      built <- fractions.foldRight[Either[LogicError, Term]](Right(empty)) { case ((p, q), rest) =>
        for {
          tail <- rest
          numerator <- digits.numeral(p)
          denominator <- digits.numeral(q)
          pair <- app(pairing, numerator, denominator)
          result <- app(cons, pair, tail)
        } yield result
      }
    } yield built

  /**
   * `|- FRACTRAN_STEP P n m`, where `m` is what the first applicable fraction makes of `n`, or a
   * refusal when none applies. The value is computed here and then proved; the computation decides
   * only which theorem to ask for.
   */
  def step(fractions: Vector[(BigInt, BigInt)], n: BigInt): Either[LogicError, Kernel.Thm] =
    next(fractions, n) match {
      case None => Left(NotOfForm(s"a state some fraction applies to, and none applies to $n", Term.variable("n", Num)))
      case Some(m) => stepTo(fractions, n, m)
    }

  /** `|- FRACTRAN_HALTS P n`, or a refusal when some fraction applies to `n`. */
  def halts(fractions: Vector[(BigInt, BigInt)], n: BigInt): Either[LogicError, Kernel.Thm] = {
    val m = Term.variable("m", Num)
    for {
      programTerm <- program(fractions)
      nTerm <- digits.numeral(n)
      walked <- passing(fractions, n, m, 0)
      _ <- walked match {
        case Passed(_) => Right(())
        case Landed(_, p, q) => Left(NotOfForm(s"a state no fraction applies to; $p/$q applies to $n", nTerm))
      }
      stepTerm <- Datatype.leftOf(walked.equation)
      assumed <- assume(stepTerm)
      atEmpty <- LogicError.lift(Kernel.eqMp(walked.equation, assumed))
      none <- rules.specAll(published(StepEmpty), List(nTerm, m))
      absurd <- rules.notElim(none, atEmpty)
      refused <- rules.notIntro(stepTerm, absurd)
      general <- rules.gen(m, refused)
      unfolded <- Conv.unfold(definitions(HaltsName), List(programTerm, nTerm))
      result <- Conv.sym(unfolded).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, general)))
    } yield result
  }

  /**
   * `|- FRACTRAN_REACHES P start k m`, with `k` the length of `states` less one and `m` its last
   * element, each step certified. `states` is a proposal and is checked, not believed: it is what
   * [[Fractran.trace]] returns, or anything else a caller wants the kernel to rule on.
   */
  def certifyTrace(fractions: Vector[(BigInt, BigInt)], states: Vector[BigInt]): Either[LogicError, Kernel.Thm] =
    states.headOption match {
      case None => Left(NotOfForm("a trace with a first state", Term.variable("n", Num)))
      case Some(start) =>
        for {
          programTerm <- program(fractions)
          startTerm <- digits.numeral(start)
          initial <- rules.specAll(published(ReachesStart), List(programTerm, startTerm))
          reaches <- LogicError.lift(theory.constant(ReachesName, ReachesType))
          result <- states.indices.drop(1).foldLeft[Either[LogicError, Kernel.Thm]](Right(initial)) { (acc, i) =>
            val j = Term.variable("j", Num)
            for {
              reached <- acc
              before <- digits.numeral(states(i - 1))
              after <- digits.numeral(states(i))
              count <- digits.numeral(BigInt(i - 1))
              stepped <- stepTo(fractions, states(i - 1), states(i))
              both <- rules.conjIntro(reached, stepped)
              further <- rules.specAll(published(ReachesStep), List(programTerm, startTerm, count, before, after))
                .flatMap(rules.mp(_, both))
              counted <- digits.successor(BigInt(i - 1))
              body <- app(reaches, programTerm, startTerm, j, after)
              lambda <- LogicError.lift(Term.absAll(List(j), body))
              moved <- transport(lambda, counted, further)
            } yield moved
          }
        } yield result
    }

  /** [[Fractran.trace]] for `steps` steps, or until it halts, and then [[certifyTrace]]. */
  def certify(fractions: Vector[(BigInt, BigInt)], start: BigInt, steps: Int): Either[LogicError, Kernel.Thm] =
    certifyTrace(fractions, trace(fractions, start, steps))

  /**
   * `|- FRACTRAN_STEP P n m`, for the `m` the caller names: the program is walked to the first
   * fraction that applies, and that fraction has to send `n` to `m`. A different `m`, or no fraction
   * applying, is a refusal naming what the program does instead.
   */
  private def stepTo(fractions: Vector[(BigInt, BigInt)], n: BigInt, m: BigInt): Either[LogicError, Kernel.Thm] =
    for {
      target <- digits.numeral(m)
      walked <- passing(fractions, n, target, 0)
      landing <- walked match {
        case Landed(_, p, q) if n * p / q == m => Right((p, q))
        case Landed(_, p, q) =>
          Left(NotOfForm(s"a step from $n to $m; the first fraction applying is $p/$q, which gives ${n * p / q}", target))
        case Passed(_) => Left(NotOfForm(s"a step from $n to $m; no fraction applies to $n", target))
      }
      (p, q) = landing
      qTerm <- digits.numeral(q)
      product <- digits.multiply(n, p)
      quotient <- value.of(Modular.DivName, Vector(n * p, q))
      divide <- LogicError.lift(theory.constant(Modular.DivName, Type.fun(Num, Type.fun(Num, Num))))
      y = Term.variable("y", Num)
      divideBy <- app(divide, y, qTerm).flatMap(t => LogicError.lift(Term.absAll(List(y), t)))
      moved <- cong(divideBy, product)
      valued <- Conv.trans(moved, quotient).flatMap(Conv.sym)
      result <- Conv.sym(walked.equation).flatMap(e => LogicError.lift(Kernel.eqMp(e, valued)))
    } yield result

  /**
   * `|- FRACTRAN_STEP P_i n t = E`, `P_i` the program from fraction `i` on, across every fraction
   * that does not apply to `n`. `E` is `t = NUM_DIV (n * p) q` at the first fraction that applies,
   * which is `Landed`, or `FRACTRAN_STEP WORD_EMPTY n t` when none does, which is
   * `Passed`.
   */
  private def passing(fractions: Vector[(BigInt, BigInt)], n: BigInt, target: Term, i: Int): Either[LogicError, Walk] =
    if (i == fractions.size)
      for {
        empty <- program(Vector.empty)
        nTerm <- digits.numeral(n)
        stepConst <- LogicError.lift(theory.constant(StepName, StepType))
        atEmpty <- app(stepConst, empty, nTerm, target)
      } yield Passed(Conv.refl(atEmpty))
    else {
      val (p, q) = fractions(i)
      for {
        rest <- program(fractions.drop(i + 1))
        pTerm <- digits.numeral(p)
        qTerm <- digits.numeral(q)
        nTerm <- digits.numeral(n)
        instance <- rules.specAll(published(StepPair), List(pTerm, qTerm, rest, nTerm, target))
        pieces <- sides(instance.conclusion).flatMap { case (_, right) => conditional(right) }
        (test, landed, passed) = pieces
        product <- digits.multiply(n, p)
        result <-
          if (q != 0 && (n * p) % q == 0)
            for {
              holds <- testHolds(test, n, p, q)
              chosen <- condTrue(kit, test, landed, passed, holds)
              equation <- Conv.trans(instance, chosen)
            } yield Landed(equation, p, q)
          else
            for {
              fails <- testFails(test, n, p, q, product)
              chosen <- condFalse(kit, test, landed, passed, fails)
              equation <- Conv.trans(instance, chosen)
              further <- passing(fractions, n, target, i + 1)
              joined <- Conv.trans(equation, further.equation)
            } yield further match {
              case Landed(_, lp, lq) => Landed(joined, lp, lq)
              case Passed(_) => Passed(joined)
            }
      } yield result
    }

  /** `|- ~(q = 0) /\ NUM_DIVIDES q (n * p)` at numerals, `q` dividing `n * p`. */
  private def testHolds(test: Term, n: BigInt, p: BigInt, q: BigInt): Either[LogicError, Kernel.Thm] =
    for {
      parts <- conj(kit, test)
      (nonZeroTerm, dividesTerm) = parts
      nonZero <- apart(q)
      _ <- kit.landsOn(nonZero, nonZeroTerm)
      qTerm <- digits.numeral(q)
      nTerm <- digits.numeral(n)
      pTerm <- digits.numeral(p)
      quotient <- digits.numeral(n * p / q)
      product <- mul(kit, nTerm, pTerm)
      left <- digits.multiply(n, p)
      right <- digits.multiply(q, n * p / q)
      factored <- Conv.sym(right).flatMap(Conv.trans(left, _))
      divides <- kit.use("NUM_DIVIDES_INTRO", List(qTerm, product, quotient), factored)
      _ <- kit.landsOn(divides, dividesTerm)
      result <- rules.conjIntro(nonZero, divides)
    } yield result

  /**
   * `|- ~(~(q = 0) /\ NUM_DIVIDES q (n * p))` at numerals: at `q = 0` by the first conjunct, and
   * otherwise because a remainder that is not zero refuses the second.
   */
  private def testFails(test: Term, n: BigInt, p: BigInt, q: BigInt, product: Kernel.Thm): Either[LogicError, Kernel.Thm] =
    for {
      assumed <- assume(test)
      nonZero <- rules.conjElim1(assumed)
      absurd <-
        if (q == 0)
          for {
            zeroTerm <- digits.numeral(BigInt(0))
            f <- rules.notElim(nonZero, Conv.refl(zeroTerm))
          } yield f
        else
          for {
            divides <- rules.conjElim2(assumed)
            qTerm <- digits.numeral(q)
            productTerm <- sides(product.conclusion).map(_._1)
            both <- rules.conjIntro(nonZero, divides)
            atZero <- rules.specAll(modZero, List(qTerm, productTerm)).flatMap(rules.mp(_, both))
            remainder <- value.of(Modular.ModName, Vector(n * p, q))
            modulo <- LogicError.lift(theory.constant(Modular.ModName, Type.fun(Num, Type.fun(Num, Num))))
            y = Term.variable("y", Num)
            modBy <- app(modulo, y, qTerm).flatMap(t => LogicError.lift(Term.absAll(List(y), t)))
            moved <- cong(modBy, product)
            valued <- Conv.trans(moved, remainder)
            isZero <- Conv.sym(valued).flatMap(Conv.trans(_, atZero))
            positive <- digits.below(BigInt(0), (n * p) % q)
            zeroTerm <- digits.numeral(BigInt(0))
            rTerm <- digits.numeral((n * p) % q)
            notZero <- neqOfLt(kit, zeroTerm, rTerm, positive)
            f <- rules.notElim(notZero, isZero)
          } yield f
      result <- rules.notIntro(test, absurd)
    } yield result

  /** `|- ~(q = 0)` for a numeral `q` above zero, by the digits rather than by spelling successors. */
  private def apart(q: BigInt): Either[LogicError, Kernel.Thm] =
    for {
      positive <- digits.below(BigInt(0), q)
      zeroTerm <- digits.numeral(BigInt(0))
      qTerm <- digits.numeral(q)
      result <- neqOfLt(kit, zeroTerm, qTerm, positive)
    } yield result
}

object Fractran {
  import Steps.*

  /** `FRACTRAN_STEP P n m`: the first fraction of `P` that applies to `n` sends it to `m`. */
  val StepName: String = "FRACTRAN_STEP"

  /** `FRACTRAN_HALTS P n`: no fraction of `P` applies to `n`, so `n` has no successor. */
  val HaltsName: String = "FRACTRAN_HALTS"

  /** `FRACTRAN_REACHES P n k m`: `P` takes `n` to `m` in exactly `k` steps. */
  val ReachesName: String = "FRACTRAN_REACHES"

  /** The definitions, in the order they are made: each names only what is above it. */
  val Bodies: Vector[(String, String)] = Vector(
    StepName ->
      ("\\P:word(prod(num,num)). \\n:num. \\m:num. LIST_FOLD (\\f:prod(num,num). \\r:bool. " +
        "COND (~(SND f = 0) /\\ NUM_DIVIDES (SND f) (n * FST f)) (m = NUM_DIV (n * FST f) (SND f)) r) F P"),
    HaltsName -> "\\P:word(prod(num,num)). \\n:num. !m:num. ~FRACTRAN_STEP P n m",
    ReachesName ->
      "\\P:word(prod(num,num)). \\n:num. \\k:num. \\m:num. REACH (FRACTRAN_STEP P) (FRACTRAN_STEP P) n (PAIR m k)"
  )

  /** `|- !n m. ~FRACTRAN_STEP WORD_EMPTY n m`: the empty program halts everywhere. */
  val StepEmpty: String = "FRACTRAN_STEP_EMPTY"

  /** The step at a program with a head: the head decides if it applies, the tail otherwise. */
  val StepCons: String = "FRACTRAN_STEP_CONS"

  /** [[StepCons]] with the head written as a pair, which is the form a program is written in. */
  val StepPair: String = "FRACTRAN_STEP_PAIR"

  /** The step is functional: two successors of one state are one number. */
  val StepFunctional: String = "FRACTRAN_STEP_FUNCTIONAL"

  /** A run of length zero stays where it started. */
  val ReachesStart: String = "FRACTRAN_REACHES_START"

  /** A run followed by a step is a run one longer. */
  val ReachesStep: String = "FRACTRAN_REACHES_STEP"

  /** Everything published here, as the text a person checks it by. */
  val Statements: Vector[(String, String)] = Vector(
    StepEmpty -> "!n:num. !m:num. ~FRACTRAN_STEP (WORD_EMPTY:word(prod(num,num))) n m",
    StepCons ->
      ("!f:prod(num,num). !P:word(prod(num,num)). !n:num. !m:num. FRACTRAN_STEP (LIST_CONS f P) n m = " +
        "COND (~(SND f = 0) /\\ NUM_DIVIDES (SND f) (n * FST f)) (m = NUM_DIV (n * FST f) (SND f)) (FRACTRAN_STEP P n m)"),
    StepPair ->
      ("!p:num. !q:num. !P:word(prod(num,num)). !n:num. !m:num. FRACTRAN_STEP (LIST_CONS (PAIR p q) P) n m = " +
        "COND (~(q = 0) /\\ NUM_DIVIDES q (n * p)) (m = NUM_DIV (n * p) q) (FRACTRAN_STEP P n m)"),
    StepFunctional ->
      "!P:word(prod(num,num)). !n:num. !a:num. !b:num. FRACTRAN_STEP P n a /\\ FRACTRAN_STEP P n b ==> a = b",
    ReachesStart -> "!P:word(prod(num,num)). !n:num. FRACTRAN_REACHES P n 0 n",
    ReachesStep ->
      ("!P:word(prod(num,num)). !n:num. !k:num. !x:num. !m:num. " +
        "FRACTRAN_REACHES P n k x /\\ FRACTRAN_STEP P x m ==> FRACTRAN_REACHES P n (SUC k) m")
  )

  /**
   * Conway's PRIMEGAME, as OEIS A007542 lists it. Started at `2` it passes through `2^p` for every
   * prime `p` in order and through no other power of two; the first is at step 19. `docs/adr/0054`
   * says where the fractions were taken from and how they were checked.
   */
  val PrimeGame: Vector[(BigInt, BigInt)] = Vector(
    17 -> 91, 78 -> 85, 19 -> 51, 23 -> 38, 29 -> 33, 77 -> 29, 95 -> 23,
    77 -> 19, 1 -> 17, 11 -> 13, 13 -> 11, 15 -> 2, 1 -> 7, 55 -> 1
  ).map { case (p, q) => BigInt(p) -> BigInt(q) }

  /**
   * The successor of `n`, computed on `BigInt` and believed by nothing: this is the proposal
   * `certify` hands the kernel, and it is the whole interpreter.
   */
  def next(fractions: Vector[(BigInt, BigInt)], n: BigInt): Option[BigInt] =
    fractions.collectFirst { case (p, q) if q != 0 && (n * p) % q == 0 => n * p / q }

  /** The states from `start`, for `steps` steps or until the program halts. */
  def trace(fractions: Vector[(BigInt, BigInt)], start: BigInt, steps: Int): Vector[BigInt] =
    Iterator.iterate(Option(start))(_.flatMap(next(fractions, _))).take(steps + 1).takeWhile(_.isDefined).flatten.toVector

  /** Where walking a program over one state ended, with the equation that walked it. */
  private sealed trait Walk { def equation: Kernel.Thm }

  /** At the first fraction that applies, `p/q`. */
  private final case class Landed(equation: Kernel.Thm, p: BigInt, q: BigInt) extends Walk

  /** Past every fraction, none applying. */
  private final case class Passed(equation: Kernel.Thm) extends Walk

  private val Num: Type = TyApp(Natural.TypeName, Nil)
  private val Pairs: Type = TyApp(Product.TypeName, List(Num, Num))
  private val Programs: Type = TyApp(Word.TypeName, List(Pairs))
  private val StepType: Type = Type.fun(Programs, Type.fun(Num, Type.fun(Num, Type.Bool)))
  private val ReachesType: Type = Type.fun(Programs, Type.fun(Num, Type.fun(Num, Type.fun(Num, Type.Bool))))

  /** The development over the chain it is handed. */
  def construct(chain: Chain): Either[LogicError, Fractran] = {
    val base = chain.widest
    val notation = base.notation
    val introduced = Bodies.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](Right((base.theory, Map.empty))) {
      case (accumulated, (name, text)) =>
        for {
          state <- accumulated
          (theory, defined) = state
          body <- Parser.term(theory, notation, text)
          made <- LogicError.lift(Kernel.defineConstant(theory, name, body))
          (extended, definition) = made
        } yield (extended, defined + (name -> definition))
    }
    for {
      state <- introduced
      (theory, definitions) = state
      logic <- chain.classical.logic.over(theory)
      semiring <- Semiring.construct(chain.peano)
      value <- Value.construct(chain)
      lookup = (name: String) =>
        chain.modular.fact(name)
          .orElse(chain.peano.fact(name))
          .orElse(chain.peano.naturals.fact(name))
          .orElse(chain.classical.fact(name))
          .orElse(chain.product.fact(name))
          .orElse(chain.folding.fact(name))
          .orElse(chain.listing.fact(name))
          .orElse(chain.reaching.fact(name))
      kit = Freshman.Kit(logic, theory, notation, semiring, chain.induct, lookup)
      step = definitions(StepName)
      reaches = definitions(ReachesName)
      empty <- Proofs.stepEmpty(kit, step)
      cons <- Proofs.stepCons(kit, step)
      pair <- Proofs.stepPair(kit, cons)
      functional <- Proofs.functional(kit, empty, cons)
      start <- Proofs.reachesStart(kit, reaches)
      further <- Proofs.reachesStep(kit, reaches)
      modZero <- Proofs.modZero(kit)
      facts = Map(
        StepEmpty -> empty,
        StepCons -> cons,
        StepPair -> pair,
        StepFunctional -> functional,
        ReachesStart -> start,
        ReachesStep -> further
      )
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { case (acc, (name, text)) =>
        for {
          _ <- acc
          expected <- Parser.proposition(theory, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Fractran(theory, notation, logic, definitions, facts, kit, value, modZero)
  }

  /** The development over the standard chain. */
  lazy val standard: Fractran =
    construct(Chain.standard).fold(error => throw new IllegalStateException(error.message), identity)

  /** The derivations `construct` runs, over the `Steps` every hand derivation here shares. */
  private object Proofs {

    private def at(theorem: Kernel.Thm, element: Type, values: Type): Kernel.Thm =
      Kernel.instType(Map(Classical.TypeVariable -> element, Classical.CodomainVariable -> values), theorem)

    /** `LIST_FOLD g F P` taken apart, for the `g` the definition put there. */
    private def folded(term: Term): R[(Term, Term, Term)] = term match {
      case App(App(App(_, g), start), list) => Right((g, start, list))
      case other => Left(NotOfForm("a fold", other))
    }

    /** `|- !n m. ~FRACTRAN_STEP WORD_EMPTY n m` */
    def stepEmpty(kit: Kit, definition: Kernel.Thm): R[Kernel.Thm] = {
      val n = Term.variable("n", Num)
      val m = Term.variable("m", Num)
      for {
        empty <- kit.term(Concatenation.Empty, Programs)
        unfolded <- Conv.unfold(definition, List(empty, n, m))
        body <- Limit.rightOf(unfolded)
        pieces <- folded(body)
        (g, start, _) = pieces
        atEmpty <- kit.fact(Folding.FoldOfEmpty).map(at(_, Pairs, Type.Bool)).flatMap(kit.rules.specAll(_, List(g, start)))
        equation <- Conv.trans(unfolded, atEmpty)
        stepTerm <- Datatype.leftOf(unfolded)
        assumed <- assume(stepTerm)
        absurd <- LogicError.lift(Kernel.eqMp(equation, assumed))
        refused <- kit.rules.notIntro(stepTerm, absurd)
        result <- kit.rules.genAll(refused, List(n, m))
      } yield result
    }

    /** `|- !f P n m. FRACTRAN_STEP (LIST_CONS f P) n m = COND (...) (m = ...) (FRACTRAN_STEP P n m)` */
    def stepCons(kit: Kit, definition: Kernel.Thm): R[Kernel.Thm] = {
      val f = Term.variable("f", Pairs)
      val list = Term.variable("P", Programs)
      val n = Term.variable("n", Num)
      val m = Term.variable("m", Num)
      for {
        cons <- kit.term(Listing.Cons, Type.fun(Pairs, Type.fun(Programs, Programs)))
        whole <- app(cons, f, list)
        unfolded <- Conv.unfold(definition, List(whole, n, m))
        body <- Limit.rightOf(unfolded)
        pieces <- folded(body)
        (g, start, _) = pieces
        atCons <- kit.fact(Folding.FoldOfCons).map(at(_, Pairs, Type.Bool))
          .flatMap(kit.rules.specAll(_, List(g, start, f, list)))
        opened <- Limit.rightOf(atCons).flatMap(Conv.betaNormalise)
        tail <- Conv.unfold(definition, List(list, n, m)).flatMap(Conv.sym)
        reduced <- Limit.rightOf(opened)
        parts <- conditional(reduced)
        (test, landed, _) = parts
        hole = Term.variable("hole_", Type.Bool)
        conditionalConst <- kit.term("COND", Type.fun(Type.Bool, Type.fun(Type.Bool, Type.fun(Type.Bool, Type.Bool))))
        template <- app(conditionalConst, test, landed, hole).flatMap(t => LogicError.lift(Term.absAll(List(hole), t)))
        named <- cong(template, tail)
        equation <- transAll(unfolded, atCons, opened, named)
        result <- kit.rules.genAll(equation, List(f, list, n, m))
      } yield result
    }

    /** [[StepCons]] at `PAIR p q`, with the projections read off the pair. */
    def stepPair(kit: Kit, cons: Kernel.Thm): R[Kernel.Thm] = {
      val p = Term.variable("p", Num)
      val q = Term.variable("q", Num)
      val list = Term.variable("P", Programs)
      val n = Term.variable("n", Num)
      val m = Term.variable("m", Num)
      for {
        pair <- kit.at("\\p:num. \\q:num. PAIR p q", p, q)
        instance <- kit.rules.specAll(cons, List(pair, list, n, m))
        first <- kit.fact(Product.FirstOfPair).map(at(_, Num, Num)).flatMap(kit.rules.specAll(_, List(p, q)))
        second <- kit.fact(Product.SecondOfPair).map(at(_, Num, Num)).flatMap(kit.rules.specAll(_, List(p, q)))
        once <- Limit.rewriteInProposition(first, instance)
        twice <- Limit.rewriteInProposition(second, once)
        result <- kit.rules.genAll(twice, List(p, q, list, n, m))
      } yield result
    }

    /** `|- !P n a b. FRACTRAN_STEP P n a /\ FRACTRAN_STEP P n b ==> a = b`, by induction on `P`. */
    def functional(kit: Kit, empty: Kernel.Thm, cons: Kernel.Thm): R[Kernel.Thm] = {
      val rules = kit.rules
      val n = Term.variable("n", Num)
      val a = Term.variable("a", Num)
      val b = Term.variable("b", Num)
      val f = Term.variable("f", Pairs)
      val list = Term.variable("P", Programs)
      for {
        predicate <- Parser.term(kit.theory, kit.notation,
          "\\P:word(prod(num,num)). !n:num. !a:num. !b:num. FRACTRAN_STEP P n a /\\ FRACTRAN_STEP P n b ==> a = b")
        induction <- kit.fact(Listing.Induct).map(at(_, Pairs, Pairs)).flatMap(kit.applyTo(_, List(predicate)))
        premises <- imp(kit, induction.conclusion).map(_._1)
        halves <- conj(kit, premises)
        (baseT, stepT) = halves

        base <- for {
          claim <- open(kit, baseT, n).flatMap(open(kit, _, a)).flatMap(open(kit, _, b))
          opened <- imp(kit, claim)
          (bothT, goal) = opened
          both <- assume(bothT)
          first <- rules.conjElim1(both)
          refused <- rules.specAll(empty, List(n, a))
          absurd <- rules.notElim(refused, first)
          closed <- rules.falsityElim(goal, absurd)
          result <- rules.disch(bothT, closed).flatMap(rules.genAll(_, List(n, a, b)))
        } yield result

        inductive <- for {
          claim <- open(kit, stepT, f).flatMap(open(kit, _, list))
          opened <- imp(kit, claim)
          (hypothesisT, conclusionT) = opened
          hypothesis <- assume(hypothesisT)
          goal <- open(kit, conclusionT, n).flatMap(open(kit, _, a)).flatMap(open(kit, _, b))
          goalSplit <- imp(kit, goal)
          (bothT, target) = goalSplit
          both <- assume(bothT)
          atA <- rules.conjElim1(both)
          atB <- rules.conjElim2(both)
          eqA <- rules.specAll(cons, List(f, list, n, a))
          eqB <- rules.specAll(cons, List(f, list, n, b))
          condA <- LogicError.lift(Kernel.eqMp(eqA, atA))
          condB <- LogicError.lift(Kernel.eqMp(eqB, atB))
          partsA <- conditional(condA.conclusion)
          (test, landedA, passedA) = partsA
          partsB <- conditional(condB.conclusion)
          (_, landedB, passedB) = partsB
          proved <- split(kit, test)(
            holds =>
              for {
                toA <- condTrue(kit, test, landedA, passedA, holds)
                toB <- condTrue(kit, test, landedB, passedB, holds)
                valueA <- LogicError.lift(Kernel.eqMp(toA, condA))
                valueB <- LogicError.lift(Kernel.eqMp(toB, condB))
                same <- Conv.sym(valueB).flatMap(Conv.trans(valueA, _))
              } yield same,
            fails =>
              for {
                toA <- condFalse(kit, test, landedA, passedA, fails)
                toB <- condFalse(kit, test, landedB, passedB, fails)
                tailA <- LogicError.lift(Kernel.eqMp(toA, condA))
                tailB <- LogicError.lift(Kernel.eqMp(toB, condB))
                together <- rules.conjIntro(tailA, tailB)
                same <- rules.specAll(hypothesis, List(n, a, b)).flatMap(rules.mp(_, together))
              } yield same
          )
          _ <- kit.landsOn(proved, target)
          result <- rules.disch(bothT, proved)
            .flatMap(rules.genAll(_, List(n, a, b)))
            .flatMap(rules.disch(hypothesisT, _))
            .flatMap(rules.genAll(_, List(f, list)))
        } yield result

        premise <- rules.conjIntro(base, inductive)
        all <- rules.mp(induction, premise)
        atList <- rules.spec(list, all).flatMap(Limit.normalised)
        result <- rules.genAll(atList, List(list))
      } yield result
    }

    /** `REACH (FRACTRAN_STEP P) (FRACTRAN_STEP P)`, the relation a run is. */
    private def relation(kit: Kit, list: Term): R[Term] =
      kit.term(StepName, StepType).flatMap(app(_, list))

    /** `|- !P n. FRACTRAN_REACHES P n 0 n` */
    def reachesStart(kit: Kit, definition: Kernel.Thm): R[Kernel.Thm] = {
      val list = Term.variable("P", Programs)
      val n = Term.variable("n", Num)
      for {
        r <- relation(kit, list)
        started <- kit.fact(Reaching.Start).map(at(_, Num, Num)).flatMap(kit.rules.specAll(_, List(r, r, n)))
        z <- zero(kit)
        unfolded <- Conv.unfold(definition, List(list, n, z, n))
        result <- Conv.sym(unfolded).flatMap(e => LogicError.lift(Kernel.eqMp(e, started)))
        out <- kit.rules.genAll(result, List(list, n))
      } yield out
    }

    /** `|- !P n k x m. FRACTRAN_REACHES P n k x /\ FRACTRAN_STEP P x m ==> FRACTRAN_REACHES P n (SUC k) m` */
    def reachesStep(kit: Kit, definition: Kernel.Thm): R[Kernel.Thm] = {
      val rules = kit.rules
      val list = Term.variable("P", Programs)
      val n = Term.variable("n", Num)
      val k = Term.variable("k", Num)
      val x = Term.variable("x", Num)
      val m = Term.variable("m", Num)
      val y = Term.variable("y", Num)
      for {
        r <- relation(kit, list)
        hypothesisT <- kit.proposition(
          "FRACTRAN_REACHES (P:word(prod(num,num))) (n:num) (k:num) (x:num) /\\ FRACTRAN_STEP P x (m:num)")
        hypothesis <- assume(hypothesisT)
        reached <- rules.conjElim1(hypothesis)
        stepped <- rules.conjElim2(hypothesis)
        asReach <- Conv.unfold(definition, List(list, n, k, x)).flatMap(e => LogicError.lift(Kernel.eqMp(e, reached)))
        pair <- kit.at("\\x:num. \\k:num. PAIR x k", x, k)
        first <- kit.fact(Product.FirstOfPair).map(at(_, Num, Num)).flatMap(rules.specAll(_, List(x, k)))
        second <- kit.fact(Product.SecondOfPair).map(at(_, Num, Num)).flatMap(rules.specAll(_, List(x, k)))
        stepAt <- app(r, y, m).flatMap(t => LogicError.lift(Term.absAll(List(y), t)))
        fromFirst <- Conv.sym(first).flatMap(transport(stepAt, _, stepped))
        premise <- rules.conjIntro(fromFirst, fromFirst).flatMap(rules.conjIntro(asReach, _))
        counted <- kit.fact(Reaching.CountedStep).map(at(_, Num, Num))
          .flatMap(rules.specAll(_, List(r, r, n, pair, m)))
          .flatMap(rules.mp(_, premise))
        reachConst <- kit.term(Reaching.Name, Type.fun(Type.fun(Num, Type.fun(Num, Type.Bool)),
          Type.fun(Type.fun(Num, Type.fun(Num, Type.Bool)), Type.fun(Num, Type.fun(TyApp(Product.TypeName, List(Num, Num)), Type.Bool)))))
        landedAt <- kit.at("\\m:num. \\j:num. PAIR m (SUC j)", m, y)
        reachAt <- app(reachConst, r, r, n, landedAt).flatMap(t => LogicError.lift(Term.absAll(List(y), t)))
        moved <- transport(reachAt, second, counted)
        sk <- succ(kit, k)
        folded <- Conv.unfold(definition, List(list, n, sk, m)).flatMap(Conv.sym)
          .flatMap(e => LogicError.lift(Kernel.eqMp(e, moved)))
        result <- rules.disch(hypothesisT, folded).flatMap(rules.genAll(_, List(list, n, k, x, m)))
      } yield result
    }

    /**
     * `|- !q x. ~(q = 0) /\ NUM_DIVIDES q x ==> NUM_MOD x q = 0`, which is what lets a remainder
     * that is not zero refuse a fraction. `x = q * k + 0` with `0 < q`, and `NUM_DIV_MOD_UNIQUE` reads
     * the remainder off. It is a fact about `num` rather than about FRACTRAN and belongs in
     * `Modular`; it is private here because publishing it there moves the generated library, which is
     * a change of its own.
     */
    def modZero(kit: Kit): R[Kernel.Thm] = {
      val rules = kit.rules
      val q = Term.variable("q", Num)
      val x = Term.variable("x", Num)
      val k = Term.variable("k", Num)
      for {
        hypothesisT <- kit.proposition("~((q:num) = 0) /\\ NUM_DIVIDES q (x:num)")
        hypothesis <- assume(hypothesisT)
        nonZero <- rules.conjElim1(hypothesis)
        divides <- rules.conjElim2(hypothesis)
        exists <- kit.use("NUM_DIVIDES_ELIM", List(q, x), divides)
        predicate <- kit.logic.destExistsPredicate(exists.conclusion).toRight(NotOfForm("an existential", exists.conclusion))
        witnessT <- instantiate(predicate, k)
        witness <- assume(witnessT)
        product <- mul(kit, q, k)
        plusZero <- kit.use("NUM_ADD_ZERO", List(product)).flatMap(Conv.sym)
        decomposed <- Conv.trans(witness, plusZero)
        above <- positive(kit, q, nonZero)
        z <- zero(kit)
        unique <- rules.conjIntro(decomposed, above)
          .flatMap(c => kit.use("NUM_DIV_MOD_UNIQUE", List(x, q, k, z), c))
        remainder <- rules.conjElim2(unique).flatMap(Conv.sym)
        eliminated <- rules.existsElim(exists, k, remainder)
        result <- rules.disch(hypothesisT, eliminated).flatMap(rules.genAll(_, List(q, x)))
      } yield result
    }
  }
}
