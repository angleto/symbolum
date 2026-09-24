package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * A claim about every number below a concrete bound, proved by proving the instances.
 *
 * `!i:num. NUM_LT i k ==> P i`, with `k` written out as `SUC (SUC ... ZERO)` and not as the
 * numeral `4`, which `Successor.spell` converts for a caller who has one, is decidable here in
 * the only sense this system recognises: prove `P ZERO`, `P (SUC ZERO)`, ... `P (k-1)` and put them
 * together. The audit that asked for this wrote the gap as *"a bounded universal is not discharged
 * by computation. There is no reflection: a consumer checks twelve forms by enumeration and that
 * fact has no route into the kernel"*, and the missing half was the assembly rather than the
 * instances: a caller could prove each of the twelve and had nothing to join them with.
 *
 * == It does not compute, and that is the shape `docs/adr/0010` forces ==
 *
 * There is no computing rule in the kernel and there will not be one, so nothing here shortcuts a
 * proof by evaluating. The bound is read as a **term** and walked as a term; the arithmetic that
 * decides `i < k` for a particular `i` is not done at all. What is done instead is one case split
 * per step, `Peano.BelowSuccessorCases`, which turns `i < SUC n` into `i < n \/ i = n` and so
 * peels one instance off the front. The `Int` this file carries is the **length of the walk**, used
 * to index the caller's instances and to compare against the budget, and no theorem rests on it:
 * every numeral it builds is built from `ZERO` and `SUC` and every step is an inference.
 *
 * That is why the cost is what it is, and the measurement is worth reading because it is not where
 * a reader would guess. `BoundedSpec` walks bounds 1, 2, 4 and 8 over an instance that costs
 * nothing, and read 6625, 6771, 7063 and 7647 inferences on 2026-09-24: **146 per instance, and
 * linear**, on a base of about 6480 which is the two order lemmas it rests on, and which every
 * claim it proves shares. The driver is therefore not what a bounded universal costs here. What the
 * spec asserts is the linearity; the four figures are its printout of that day and move whenever a
 * lemma under them does, which is why they carry a date. They read 9129 to 10340 before 2026-09-14
 * and nothing noticed the change.
 *
 * What it costs is the caller's, and that grows faster than the bound for a reason that is the
 * mathematics rather than this file. The same claim closed by LINARITH over the embedding, `!i. i <
 * k ==> real_of_num i < k`, read 14216 inferences at `k = 1`, 20409 at 8, 82783 at 32 and 340388 at
 * 64 when [[Bounded.Instances]] was chosen, before 2026-09-14: the instances get **larger** as the
 * bound does, `real_of_num 63 < 64` being a bigger problem than `real_of_num 0 < 1`. A reader
 * wanting the arithmetic decided cheaply instead wants the thing `docs/adr/0010` refused.
 *
 * == The bound is read off the statement rather than passed beside it ==
 *
 * The card proposed `bounded(claim, bound)(at)`. It is one argument here, and the reason is the
 * mistake the second argument makes possible: a caller that passes a bound which is not the bound
 * its claim states gets a theorem about a different claim, and nothing in the types notices. The
 * statement already says what `k` is; reading it there means the driver and the caller cannot
 * disagree about it. [[Bounded.prove]] then checks the theorem it assembled **is** the statement it
 * was given, which is the guard `Induct.proveBy` ends with and for the same reason.
 *
 * == Where it lives, and why not in `modules/tactics` ==
 *
 * Everything it uses is in the proof half: the two definitions of the order, three facts of
 * `Peano`, three of `Natural`, and the derived rules. Nothing here asks the algebra system
 * anything, so putting it in `modules/tactics` would put it out of reach of a development in
 * `theories` for no gain. Same argument `Induct` makes one file over, and the same answer.
 *
 * == The two lemmas it rests on are `Peano`'s ==
 *
 * `NUM_NOT_LT_ZERO` and `NUM_LT_SUC_CASES` are facts about `NUM_LT` and nothing about them is about
 * enumeration. They were derived here on 2026-09-11 because `Peano` was being changed elsewhere the
 * hour this was written, and they moved the same day. They are in `docs/lemmas.md` now, which a
 * fact held here still is not, and for a reason that changed on 2026-09-12: this development **is**
 * one of the chain's now, and it holds no `facts` map to collect. What it produces is a proof of a
 * caller's statement, so there is nothing of its own for `Library.of` to list.
 *
 * The measurement above is left as it was read and did not move: `Derivation.size` counts the whole
 * acyclic graph of a proof, and the two lemmas are in it whether this file derived them or took
 * them from `Peano`. What did move is who **pays** for deriving them, which is now `Peano`, once,
 * for every consumer rather than once per driver constructed.
 */
final class Bounded private (
  val peano: Peano,
  /**
   * The most instances this will ask for, beyond which it refuses by name.
   *
   * A field rather than a constant read from the companion, because the only way to find out what a
   * limit cuts is to build the same procedure with the limit somewhere else and ask the same
   * claims, which is what `BoundedSpec` does and what `Linarith`'s own limits are set by.
   * [[Bounded.Instances]] is the number a caller gets who does not choose.
   */
  val limit: Int,
  private val notBelowZero: Kernel.Thm,
  private val belowSuccessorCases: Kernel.Thm,
  private val zero: Term,
  private val successor: Term,
  private val lessThan: Term
) {

  private val logic: Logic = peano.logic
  private val rules: Rules = logic.rules

  /**
   * `|- !i. NUM_LT i k ==> P i`, from the caller's proof of each of the `k` instances.
   *
   * The statement is the whole claim as it is to be read back, so the bound is in it. Any leading
   * universals other than the last are stripped and put back, the way `Induct.prove` does: the
   * **last** quantifier is the bounded index, because that is where a claim about every number
   * below something puts it.
   *
   * `at` is called once per index, from `ZERO` upwards, and is handed a [[Bounded.Instance]]
   * carrying the goal already instantiated, the numeral as a term, and its position as an `Int`.
   * The goal is not something the caller reconstructs: it is the right-hand side of the very
   * equation the driver will use to transport the answer back, so a caller that proves what it was
   * handed cannot have proved the wrong thing.
   *
   * == The three refusals, and why they are three ==
   *
   *  - `NotOfForm`, when the bound is not a numeral of `num`. `!i. NUM_LT i n ==> P i` over a
   *    variable `n` is not false and is not provable this way; the refusal says what shape it
   *    needed, and a caller reading it goes to `Induct` rather than raising anything.
   *  - `BoundReached`, when the bound is larger than [[limit]]. Nothing has been asked and
   *    nothing has been decided, which is the distinction that case exists for.
   *  - `InstanceRefused`, when the caller's own procedure could not settle one index. It names
   *    **which** index and carries the caller's reason underneath, so a driver that walked eight
   *    instances and stopped at the sixth says so rather than reporting the sixth's message as if
   *    it were about the claim.
   *
   * A fourth arrives inside the third: a caller that returns a theorem of some other shape gets an
   * `InstanceRefused` whose reason is a `NotOfForm`, because what went wrong is the caller's
   * step either way and the reason field is what tells the two apart.
   */
  def prove(statement: Term)(
    at: Bounded.Instance => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      stripped <- Logic.stripForall(statement)
      (variables, body) = stripped
      index <- variables.lastOption
        .toRight(NotOfForm("a claim about every number below a bound", statement))
      _ <-
        if (index.ty == Bounded.Numbers) Right(())
        else Left(NotOfForm("a claim about a number of num", statement))
      others = variables.dropRight(1)

      parts <- logic.destImp(body).toRight(NotOfForm("an implication under the quantifier", body))
      (guard, consequent) = parts
      bound <- boundOf(guard, index)
      size <- Bounded
        .lengthOf(zero, successor, bound)
        .toRight(NotOfForm("a bound written as ZERO or SUC applied to a numeral of num", bound))

      _ <-
        if (size <= limit) Right(())
        else Left(BoundReached(Bounded.LimitName, size, limit, statement))

      predicate <- LogicError.lift(Term.abs(index, consequent))
      proved <- upTo(size, index, consequent, predicate, at)
      result <- rules.genAll(proved, others.toList)

      // The statement as written, not merely something that follows. The same guard `Induct`
      // ends with, and here it is what makes reading the bound off the statement safe: if the
      // walk built a claim about a different bound, this is where it stops.
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm("the statement as it is written", result.conclusion))
    } yield result

  /** The `k` of `NUM_LT index k`, refusing anything else under the quantifier. */
  private def boundOf(guard: Term, index: FVar): Either[LogicError, Term] = guard match {
    case App(App(relation, subject), bound) if relation == lessThan && subject == index =>
      Right(bound)
    case other =>
      Left(NotOfForm(s"${Natural.TypeName} bound of the form NUM_LT ${index.name} k", other))
  }

  /**
   * The walk, from the empty range upwards.
   *
   * Upwards rather than downwards, and it is not only the natural reading: each step needs the
   * theorem for the range one shorter, so a downward recursion would build the same chain and hold
   * every frame of it open while doing so. It also fixes the order the caller's instances are
   * asked for, which is the order a caller building on its own earlier work needs.
   */
  private def upTo(
    size: Int,
    index: FVar,
    consequent: Term,
    predicate: Term,
    at: Bounded.Instance => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    (0 until size).foldLeft(atZero(index, consequent)) { (accumulated, position) =>
      accumulated.flatMap(prior => oneMore(position, prior, index, consequent, predicate, at))
    }

  /**
   * `|- !i. NUM_LT i ZERO ==> P i`, which holds because nothing is below zero.
   *
   * The base of the walk and the one place a bounded universal is vacuous. It is a theorem about
   * whatever `P` is, including a false one, which is the correct reading: no `i` satisfies the
   * guard, so the caller is asked for nothing.
   */
  private def atZero(index: FVar, consequent: Term): Either[LogicError, Kernel.Thm] =
    for {
      guard <- LogicError.lift(Term.appAll(lessThan, List(index, zero)))
      assumed <- LogicError.lift(Kernel.assume(guard))
      refuted <- rules.spec(index, notBelowZero)
      absurd <- rules.notElim(refuted, assumed)
      anything <- rules.falsityElim(consequent, absurd)
      implied <- rules.disch(guard, anything)
      result <- rules.gen(index, implied)
    } yield result

  /**
   * `|- !i. NUM_LT i (SUC n) ==> P i` from the same for `n` and the caller's proof of `P n`.
   *
   * One case split and two branches. The split is `Peano.BelowSuccessorCases`, and the reason it
   * is that lemma rather than trichotomy is that trichotomy answers a different question: it
   * compares two numbers and says which way they go, where this peels the top index off a range.
   *
   * The second branch is where the caller's theorem is transported. `i = n` is applied to the
   * predicate and both roots contracted, which gives `P i = P n` **as terms the driver built**; the
   * right-hand side of that equation is what the caller was handed as its goal, so the transport
   * back cannot be a transport of something else.
   */
  private def oneMore(
    position: Int,
    prior: Kernel.Thm,
    index: FVar,
    consequent: Term,
    predicate: Term,
    at: Bounded.Instance => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      below <- Bounded.numeral(zero, successor, position)
      above <- LogicError.lift(Term.app(successor, below))
      guard <- LogicError.lift(Term.appAll(lessThan, List(index, above)))
      assumed <- LogicError.lift(Kernel.assume(guard))
      decided <- rules
        .specAll(belowSuccessorCases, List(below, index))
        .flatMap(rules.mp(_, assumed))

      // Strictly below the number one down: the theorem already built says everything about that.
      strictly <- LogicError.lift(Term.appAll(lessThan, List(index, below)))
      assumedStrictly <- LogicError.lift(Kernel.assume(strictly))
      fromPrior <- rules.spec(index, prior).flatMap(rules.mp(_, assumedStrictly))

      // Equal to it: the one index this step asks the caller about.
      equation <- LogicError.lift(Term.eq(index, below))
      assumedEqual <- LogicError.lift(Kernel.assume(equation))
      carried <- Conv.apTerm(predicate, assumedEqual)
      transport <- Conv.betaSides(carried)
      goal <- Term
        .destEq(transport.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", transport.conclusion))

      instance <- at(Bounded.Instance(goal, below, position)).left
        .map(InstanceRefused(position, goal, _))
      _ <-
        if (instance.conclusion == goal) Right(())
        else
          Left(
            InstanceRefused(
              position,
              goal,
              NotOfForm(s"a proof of the instance at $position", instance.conclusion)
            )
          )
      backwards <- Conv.sym(transport)
      fromInstance <- LogicError.lift(Kernel.eqMp(backwards, instance))

      joined <- rules.disjElim(decided, fromPrior, fromInstance)
      implied <- rules.disch(guard, joined)
      result <- rules.gen(index, implied)
    } yield result
}

object Bounded {

  /** The type the bound and the index live in. */
  private val Numbers: Type = TyApp(Natural.TypeName, Nil)

  /**
   * What the driver opened for one index.
   *
   * A record rather than three arguments, for the reason `Induct.Step` gives: a caller cannot see
   * inside the driver, and the next thing a step turns out to need should be added here rather than
   * by changing the shape of every caller a second time.
   *
   * `goal` is the claim at this index, already instantiated and beta-contracted. `index` is the
   * numeral as a term, which is what a caller building a term of its own needs and cannot rebuild
   * without knowing how this file spells a numeral. `position` is the same number as an `Int`, for
   * a caller that dispatches on it; it is a convenience and nothing is proved from it.
   */
  final case class Instance(goal: Term, index: Term, position: Int)

  /** The name `BoundReached` carries, so that a caller reading a refusal can find the number. */
  val LimitName: String = "Bounded.Instances"

  /**
   * The most instances a bounded universal is enumerated over before this refuses.
   *
   * The number says what the procedure is for rather than tuning it, and it is **not** set by this
   * driver's own cost, which is 146 inferences per instance on 2026-09-24 and would not be worth a
   * limit. It is set by what a caller pays, which is the thing a bound multiplies.
   *
   * Measured on the consumer `!i. i < k ==> real_of_num i < k`, closed by LINARITH after the
   * embedding is rewritten, over one process on a machine at load 135, before 2026-09-14 (the wall
   * clock here is worthless as an absolute and the ratios are not, and the inference counts have
   * moved since, as the next paragraph shows):
   *
   * {{{
   *   k     8      16      32      64
   *   inf   20409  32776   82783   340388
   *   ms    432    1493    8906    44453
   * }}}
   *
   * It is superlinear, and that is the mathematics rather than the assembly: the instances get
   * larger with the bound, `real_of_num 63 < 64` being a bigger problem than `real_of_num 0 < 1`.
   * The line is where that turns: 32 is the last bound at which a claim of this shape is settled in
   * one round of thinking, and 64 is four times the price for twice the range.
   *
   * **Measured in both directions**, because a limit calibrated against nothing is calibrated on
   * nothing. `BoundedSpec` builds the same driver at 4 and at 32 and asks the same claim:
   *
   *  - what the line cuts: at 4, the eight-instance consumer comes back refused, naming the bound
   *    and the limit, and it is provable. At 32 it is proved, in 15486 inferences on 2026-09-24,
   *    where the table read 20409.
   *  - what it buys: that a bound of ten thousand, which is a term a translator produces without
   *    anybody intending it, is a refusal naming the limit rather than a walk nobody watches
   *    finish. At the rate above that claim is on the order of a day.
   *
   * A caller who means a larger bound passes one to [[Bounded.construct]], which is a change a
   * caller can make and waiting is not.
   */
  val Instances: Int = 32

  /** The standard development, over the chain that has the naturals and the reals in one signature. */
  lazy val standard: Bounded =
    construct(Chain.standard.peano).fold(
      error =>
        throw new IllegalStateException(s"the bounded-universal driver does not build: ${error.message}"),
      identity
    )

  /** The driver over a development of one's own, at the standard limit. */
  def construct(peano: Peano): Either[LogicError, Bounded] = construct(peano, Instances)

  /**
   * The same, at a limit the caller chooses.
   *
   * Public because the limit is measured rather than argued, and measuring it means building the
   * same procedure with the line somewhere else and asking the same claims. A limit that could only
   * be changed by editing this file is a limit nobody measures.
   */
  def construct(peano: Peano, limit: Int): Either[LogicError, Bounded] =
    for {
      zero <- LogicError.lift(peano.theory.constant(Natural.NumberZero, Numbers))
      successor <- LogicError.lift(
        peano.theory.constant(Natural.NumberSuccessor, Type.fun(Numbers, Numbers))
      )
      lessThan <- LogicError.lift(
        peano.theory.constant(Peano.StrictOrder, Type.fun(Numbers, Type.fun(Numbers, Type.Bool)))
      )

      // Taken from `Peano` by name. Both were derived in this file until 2026-09-11 and neither
      // was ever about enumeration; a driver that derived its own copy of a fact the chain already
      // holds would also be a second place for that fact's statement to drift.
      none <- peano.fact(Peano.NotBelowZero)
      split <- peano.fact(Peano.BelowSuccessorCases)
    } yield new Bounded(peano, limit, none, split, zero, successor, lessThan)

  /* ------------------------------------------------------------------ numerals */

  /**
   * `SUC` applied `count` times to `ZERO`.
   *
   * Built rather than parsed, and the reason for it changed on 2026-09-12 without this comment
   * changing with it. `num` has numerals since then, so `4:num` is a term; what it is not is `SUC`
   * applied to anything, and everything below walks successors. A caller holding a numeral converts
   * its claim across `Successor.spell`, which is two lines and needs nothing from this file; this
   * is for a caller holding an `Int`.
   */
  private[theories] def numeral(
    zero: Term,
    successor: Term,
    count: Int
  ): Either[LogicError, Term] =
    (0 until count).foldLeft(Right(zero): Either[LogicError, Term]) { (accumulated, _) =>
      accumulated.flatMap(term => LogicError.lift(Term.app(successor, term)))
    }

  /**
   * How many successors a term is away from zero, or nothing if it is not a numeral.
   *
   * Iterative rather than recursive, and the reason is not style: the term arrives from a caller
   * and a numeral is as deep as it is large, so a recursion here would exhaust the stack on exactly
   * the input the budget exists to refuse. Nothing is decided from the answer except which
   * instances to ask for; the proof walks the same term through the kernel.
   */
  private[theories] def lengthOf(zero: Term, successor: Term, bound: Term): Option[Int] = {
    @annotation.tailrec
    def walk(term: Term, count: Int): Option[Int] =
      if (term == zero) Some(count)
      else
        term match {
          case App(fn, argument) if fn == successor => walk(argument, count + 1)
          case _ => None
        }

    walk(bound, 0)
  }

}
