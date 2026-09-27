package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Counterpart, Natural, Prose, RealTheory, Signature}

/**
 * What a caller can do about a refusal, as a value rather than as prose.
 *
 * A session driving this system reads a refusal in order to decide what to try next, and until now
 * that decision was reconstructed from an error message each time. The messages are careful and
 * several of them say enough, but "could not certify x + 1 = 1 + x: rewriting stopped before
 * finishing" and "could not certify x + 1 = 1 + x: expected an equation, found ..." are the same
 * shape of sentence and imply opposite moves: raise a limit, or stop believing the identity.
 *
 * == Why this is a function and not a table in a comment ==
 *
 * The table existed already, in the comment on `Ledger.Verdict`, and it is the model for this file:
 * seven verdicts against the one question a ledger is asked, which is whether asking again could
 * give a different answer. What a comment cannot do is fail. A case added to [[TacticError]] with
 * no next step named is a case a session meets and cannot act on, and prose does not notice. Every
 * mapping below is a total match, so the compiler notices instead.
 *
 * == The one distinction this exists to preserve ==
 *
 * A refusal because the caller asked for something the system does not have, and a refusal because
 * something above the kernel built a malformed object, imply opposite next actions: change the
 * question, or report the defect. The second is [[ReportADefect]] and it is never something a
 * caller can fix by rewriting its input. Merging the two would tell a session to keep rephrasing a
 * question that will never be accepted, which is the failure mode this whole file is against.
 *
 * == What it is not ==
 *
 * Not a verdict about the mathematics. `Remedy.of` says what to try next, never whether a claim is
 * true: [[Settled]] means the answer does not depend on this system's strength, not that the answer
 * was yes.
 *
 * == Which refusal sets it covers, and one it cannot ==
 *
 * Everything `modules/tactics` hands a caller: `TacticError` with the `LogicError` and
 * `KernelError` underneath it, and the answers this module's own procedures give, which are
 * `Refutation.Outcome`, `Quantified.Verdict`, `CollatzScreen.Verdict`, `Discovery.Outcome`,
 * `Chaining.Outcome` and `Ledger.Verdict`.
 *
 * `Check.Verdict` is outside it, and not by choice. `modules/checker` reads a proof a second time
 * and depends on the kernel; `modules/tactics` depends on the theories and on the algebra system
 * and not on the checker, so that verdict cannot be named in this file at all. A caller that asks
 * for the second reading reads it where it arrives, and what a `Fails` there names is the step and
 * the rule rather than a move: a proof that does not check is not a question to ask differently.
 *
 * The rest of this module is in the census or named out of it, and that boundary is checked rather
 * than stated. The exhaustive matches below catch a new **case** of a type already mapped, as the
 * section above says, and nothing in the language catches a new **type**: that is how `Quantified`
 * and `CollatzScreen`, both of which landed on 2026-09-10 after this file, reached callers with a
 * verdict no arm here read. `RemedySpec` scans this module's sources for sealed verdicts and
 * outcomes and holds the list of the ones deliberately unmapped, with the reason each is out, so
 * the next one is a decision rather than an omission.
 */
sealed trait Remedy {

  /** What to do next, in a sentence a session can act on. */
  def message: String
}

/**
 * Nothing to try: the answer does not depend on how strong this system is.
 *
 * A proof, a refutation with a witness, and a decision over the linear fragment all land here. What
 * `what` carries is the answer, so that a caller logging a remedy logs something worth reading.
 */
final case class Settled(what: String) extends Remedy {
  def message: String = s"settled: $what; asking again cannot change it"
}

/**
 * The theory has no constant, type or definition for something the question mentions.
 *
 * The next step is not a rephrasing. Either the theory gains what it lacks, through
 * `RealTheory.extended`, or the question is asked without it.
 */
final case class ExtendTheTheory(what: String) extends Remedy {
  def message: String =
    s"the theory has nothing for $what: declare it, or ask the question without it"
}

/**
 * A named limit was reached, and the question is otherwise inside the fragment.
 *
 * The limit is named rather than described because there is more than one and they were separated
 * on purpose: the numeral budget and the rewriting step limit answer to different measurements, and
 * raising the wrong one changes nothing.
 */
final case class RaiseALimit(limit: String, reached: String) extends Remedy {
  def message: String = s"$limit was reached at $reached: raise it, or accept the wait"
}

/**
 * The question is the wrong shape, and the shape it has to be is named.
 *
 * Also where a premise set that cannot hold at once arrives. That is not a limit and not a defect:
 * a contradictory left-hand side makes every conclusion follow, so the problem is restated rather
 * than asked again.
 */
final case class RestateTheProblem(expected: String) extends Remedy {
  def message: String = s"restate it as $expected"
}

/** The text does not read. The position is where the reader stopped, when it knows. */
final case class RepairTheText(detail: String, position: Option[Int]) extends Remedy {
  def message: String =
    position.fold(s"the text does not read: $detail")(at =>
      s"the text does not read: $detail, at character $at"
    )
}

/**
 * The lemma fits and the goal does not say what one of its variables must be.
 *
 * Its own remedy rather than a [[RestateTheProblem]], and the distinction is the one
 * `LogicError.Undetermined` argues where it is raised: the goal is the right shape and nothing about
 * it needs changing. Transitivity applied to `a < c` is the standing example — the goal decides the
 * two ends and cannot decide the middle, which is not a defect in the goal, in the lemma, or in the
 * matcher. Somebody has to choose the middle, and that is a step in the proof rather than a repair
 * to the statement.
 */
final case class ChooseATerm(what: String) extends Remedy {
  def message: String = s"the goal does not fix $what: choose it, and apply the lemma at that"
}

/**
 * A hypothesis is missing, and the caller has to assume it rather than restate anything.
 *
 * Its own remedy rather than a [[RestateTheProblem]] because `LogicError.MissingHypothesis` already
 * argues the distinction where it is raised: what arrived was the right shape and the hypothesis
 * list was wrong, and the two repairs are different.
 */
final case class AssumeMore(what: String) extends Remedy {
  def message: String = s"nothing here assumes $what: assume it, or prove it first"
}

/**
 * The goal is provable, the proof costs a hypothesis, and accepting it is the caller's to do.
 *
 * Distinct from [[AssumeMore]], which arrives from `LogicError.MissingHypothesis`: there a rule was
 * handed a hypothesis list that was wrong, and supplying the hypothesis makes the same call
 * succeed. Here the goal **as written is not a theorem at all**, and accepting the condition
 * changes what is being claimed: the variable the condition names can no longer be generalised, so
 * what `Field` returns is about *a* `y` that is not zero rather than about every `y`.
 *
 * Distinct from [[AskDifferently]] for the opposite reason. That one says another address might
 * settle the question; this one says a named address did settle it, and reports what it charged.
 */
final case class AcceptTheConditions(conditions: Vector[String]) extends Remedy {
  def message: String =
    s"this is not a theorem as written; Field proves it assuming ${conditions.mkString(" and ")}: " +
      "ask Field and read what it assumed, or discharge that first and nothing is owed"
}

/**
 * The model had nothing to say, which is not the same as having said no.
 *
 * `Refutation.NeverAsked` and `Evaluate` returning nothing both land here. The next step is to
 * interpret what is uninterpreted, not to try more points: a constant nobody gave a value has the
 * same absence at every point.
 */
final case class InterpretMore(what: String) extends Remedy {
  def message: String = s"the model says nothing about $what: interpret it, or more points will not help"
}

/**
 * This procedure cannot settle a question of this shape, and something else might.
 *
 * Distinct from [[APersonLooks]]: the question has a known better address. Sampling declines a
 * premise forcing an equality between reals and the solver decides it; LINARITH declines a product
 * of two unknowns and nothing here decides it.
 */
final case class AskDifferently(what: String) extends Remedy {
  def message: String = s"this procedure cannot settle a question of that shape: $what"
}

/**
 * Nothing mechanical follows, and this is the outcome worth a person's attention.
 *
 * `Discovery.Why.NotProvableHere` is the case its own comment calls the only one of four worth
 * reading, and this is where it arrives: either the claim needs mathematics this system does not
 * have, or the agreement that produced the candidate was a coincidence.
 */
final case class APersonLooks(why: String) extends Remedy {
  def message: String = s"nothing mechanical follows: $why"
}

/**
 * The refusal is not about the input: something above the kernel built a malformed object.
 *
 * A session must not answer this by rephrasing, and telling it to would have it rephrase forever.
 * The kernel's side conditions are the clearest instance: a correct tactic never hands `eqMp` two
 * sides that differ, so a caller that sees `TermsDiffer` has found a defect in the layer between it
 * and the kernel rather than a limit of the theory.
 */
final case class ReportADefect(where: String) extends Remedy {
  def message: String =
    s"this is a defect above the kernel rather than a limit of the theory: $where"
}

/**
 * The claim is about `num` and is spelled with a symbol the reals own and `num` does not share.
 *
 * Its own remedy rather than a [[RepairTheText]], and that is the whole of why it is worth a case.
 * `RepairTheText` hands the reader's own complaint back, and the reader's complaint here is "real
 * and num cannot be the same type": true, the whole of what the reader knows, and it names neither
 * the owner of the symbol nor what to write instead. This names the constant.
 *
 * Reached from the claim's **text** rather than from the refusal, because there is no term to read
 * it off: the refusal exists precisely because nothing could be built.
 *
 * **The sentence said `num` has no operator notation of its own until 2026-09-16, and
 * `docs/adr/0018` made that false four symbols ago.** The table under it was pruned to subtraction
 * in the same change and `CounterpartSpec` asserts the new partition in both directions, so every
 * piece of the advice was correct while the sentence framing it denied the thing that had just
 * landed: a reader who wrote `!x:num. !y:num. x + y - y = x` was told `num` has no operator
 * notation, in a claim whose `+` had read. It was the one string in the chain no test read.
 */
final case class WriteTheConstant(spellings: Vector[Counterpart.Spelling]) extends Remedy {
  def message: String =
    s"${Natural.TypeName} shares the reals' operator symbols only where the operation is the " +
      "same one, and this claim uses something it does not share: " +
      spellings.map(_.instruction).mkString("; ")
}

object Remedy {

  /**
   * How a term is written into a remedy's message.
   *
   * A refusal carries terms and the surface renders them, which is the rule `LogicError.NotEqualTo`
   * exists to keep. Without a theory the kernel's printer is all there is, and it renders `3 * n + 1`
   * as `+ 1 (* (BIT1 1) n)`: correct, unreadable, and the defect measured on the frozen corpus of
   * 2026-09-07. With a theory the same term is written the way the reader wrote it.
   *
   * The theory is optional rather than required because the mapping is also used where none is at
   * hand, and a required argument would have every caller invent one.
   */
  private def write(term: Term, reals: Option[Signature]): String =
    reals.fold(term.toString)(_.show(term))

  /** What to do about a tactic's refusal, written in a theory's own notation. */
  def of(reals: Signature, error: TacticError): Remedy = of(error, Some(reals))

  /** The same for a derived rule's refusal. */
  def of(reals: Signature, error: LogicError): Remedy = of(error, Some(reals))

  /**
   * What the claim's own text says about a refusal to read it, or nothing.
   *
   * Beside the mappings rather than one of them, and it takes the text because a refusal does not
   * carry it: a `LogicError` is about a type or a position, and which symbols somebody wrote is a
   * fact about a string. It answers `None` wherever it has nothing to add, so a caller prints the
   * reader's own message and this underneath it, and never one in place of the other.
   *
   * **Only a `TypeError`**, which is the refusal `Peano`'s decision produces. A claim that does
   * not lex, or does not parse, has not reached the point where the owner of a symbol is the
   * question, and advice about `NUM_ADD` under a message about an unreadable character would be
   * sent to somebody with a different problem.
   */
  def spelling(reals: Signature, text: String, error: LogicError): Option[Remedy] =
    error match {
      case TypeError(_) =>
        val spellings = Counterpart.spellings(reals.notation, text)
        if (spellings.isEmpty) None else Some(WriteTheConstant(spellings))

      case _ => None
    }

  /**
   * What to do about a tactic's refusal.
   *
   * [[NotCertified]] is taken apart here rather than delegated to the logic's mapping, and the
   * reason is that the same `LogicError` means different things in the two places. A certification
   * is a claim the algebra system proposed and the kernel would not accept; the shapes not meeting
   * is what a false identity looks like, so it is a lead for a person. The same `NotOfForm` from a
   * goal a caller wrote is a goal written wrongly. `Discovery.why` already draws that line for the
   * screening loop, and `RemedySpec` asserts the two agree rather than leaving them to drift.
   */
  def of(error: TacticError): Remedy = of(error, None)

  private def of(error: TacticError, reals: Option[Signature]): Remedy = error match {
    case OutsideFragment(expression, reason) =>
      ExtendTheTheory(s"$expression ($reason)")

    case BeyondBudget(_, largest) =>
      RaiseALimit("Oracle.NumeralBudget", s"the numeral $largest")

    case NotCertified(claim, _: NotNormalised) =>
      RaiseALimit("the rewriting step limit", s"the normal form of $claim")

    case NotCertified(claim, reason) =>
      APersonLooks(
        s"the algebra system proposed $claim and the kernel would not certify it (${reason.message}): " +
          "either the proposal is wrong or this prover cannot see that it is right"
      )

    case ProvableOnlyUnder(_, conditions) =>
      AcceptTheConditions(conditions.map(write(_, reals)))

    case NotLegible(term, readBack) =>
      ReportADefect(
        readBack.fold(s"${write(term, reals)} prints as text this theory's reader cannot read back")(
          back => s"${write(term, reals)} prints as text that reads back as ${write(back, reals)}"
        )
      )

    case FromLogic(error) => of(error, reals)
  }

  /** What to do about a derived rule's refusal. */
  def of(error: LogicError): Remedy = of(error, None)

  private def of(error: LogicError, reals: Option[Signature]): Remedy = error match {
    case FromKernel(error) => of(error, reals)

    case NotOfForm(expected, _) => RestateTheProblem(expected)

    // The atoms are written here and nowhere else, which is the whole of the repair this case
    // arrived with. `Propositional` is in `modules/logic` and knows no notation, so while it wrote
    // the assignment into a sentence itself the reader got the kernel's encoding: `x = 99` came
    // back as `(x = (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 1)))))))`. It carries the pairs now, and
    // this is the only place that has a theory to render them against.
    //
    // `RestateTheProblem` and not `Settled`, which is where `DoesNotFollow` goes: the atoms are
    // uninterpreted, so what failed is the skeleton and restating the goal is exactly the move that
    // can change the answer. The refusal's own documentation carries why that is not a decision.
    case SkeletonFailsAt(_, assignment) =>
      RestateTheProblem(
        "a goal that holds; its propositional skeleton fails at " +
          assignment.map { case (atom, value) => s"${write(atom, reals)} := $value" }
            .mkString(", ")
      )

    // `Settled` rather than `RestateTheProblem`, which is what this arrived as while it was a
    // `NotOfForm`, and the difference is the whole of the case. Restating is how to find out
    // something nobody knows; here the procedure has been to the end of its fragment and the answer
    // does not depend on how the question is phrased. `Settled`'s own documentation named "a
    // decision over the linear fragment" as one of the three things that land here before anything
    // could reach it that way.
    //
    // The sentence keeps the procedure's own words rather than asserting the claim is false, for
    // the reason `DoesNotFollow` gives: decided over a fragment is not refuted.
    case DoesNotFollow(goal, procedure) =>
      Settled(
        s"no non-negative combination of the hypotheses gives ${write(goal, reals)}, and " +
          s"$procedure searched to the end of its fragment"
      )

    // `Settled`, and with more reason than the case above: the procedure holds a theorem denying
    // the goal, so no restatement of the goal's own shape can change the answer.
    case Denied(goal, proved, procedure) =>
      Settled(s"$procedure proved ${write(proved, reals)}, which denies ${write(goal, reals)}")

    // The two sides met a normal form each and the forms differ, which is what a false identity
    // looks like. It is a lead for a person rather than a shape to restate, and it is the one
    // refusal whose message has to print a term the reader recognises.
    case NotEqualTo(wanted, found) =>
      APersonLooks(
        s"${write(found, reals)} and ${write(wanted, reals)} both reached a normal form and the " +
          "forms differ: either the identity is false, or this prover cannot see that it is true"
      )

    // A person, for `NotEqualTo`'s reason, and without its verdict: the forms differ over atoms that
    // are not free, so the sentence names them and says the claim may hold all the same.
    case NotEqualAsRead(wanted, found, bound) =>
      APersonLooks(
        s"${write(found, reals)} and ${write(wanted, reals)} differ as polynomials over their " +
          s"atoms, and ${bound.map(write(_, reals)).mkString(", ")} is not a free variable, so the " +
          "identity may hold for a reason this prover does not read"
      )

    // A person rather than a restatement, for `NotEqualTo`'s reason, and without its verdict: the
    // two values were neither identified nor told apart, so the sentence says both are possible.
    case ValueUnidentified(wanted, found, _) =>
      APersonLooks(
        s"the value established is ${write(found, reals)}, and it was neither shown equal to " +
          s"${write(wanted, reals)} nor shown different from it"
      )

    case NotNormalised(term) =>
      RaiseALimit("the rewriting step limit", s"${write(term, reals)}, which still changes")

    // `ReportADefect` and NOT `RaiseALimit`, which is the whole of why `GrewPastCeiling` is its own
    // refusal rather than a `NotNormalised` with a number in it. Both say the rewriting did not
    // finish; raising the limit settles the one above and makes this one worse, because what
    // stopped it is a rule set that multiplies the term rather than one that has not got there yet.
    // Three runs were killed for memory before anything could say which of the two it was, and the
    // advice they would have been given is the advice that lengthens the run.
    // Both numbers reach one, for the reason `GrewPastCeiling` gives about itself: the ceiling is
    // a parameter and the guard is `width > ceiling`, so zero prints `reached` as one and one
    // prints `allowed` as one. The first goes through `Prose.count`; the second is written after
    // its noun, because `$allowed are allowed` disagrees with its own number and no counter
    // repairs a verb. The refusal one module down says the same thing in its own words.
    case GrewPastCeiling(term, reached, allowed) =>
      ReportADefect(
        s"a rule set took ${write(term, reals)} to ${Prose.count(reached, "node")} in one pass " +
          s"where the ceiling in nodes is $allowed: the rules multiply the term rather than " +
          "settle it, so the rule set is what to change and Rewrite.DefaultCeiling is not"
      )

    // A defect and not a limit, which is the whole reason `NoCloser` is its own refusal. The two
    // above are procedures that looked and could not; this one is a driver that was built with
    // nothing to look with, so no restatement of the goal and no raised limit reaches it. What is
    // wrong is the code that assembled the driver, and the message names it so that a reader
    // knows which of the two to go and change.
    case NoCloser(_, driver) =>
      ReportADefect(s"$driver was asked to finish a goal and holds no procedure that could")

    // A defect for `NoCloser`'s reason, from the other end: there a driver had nothing to look
    // with, here a procedure looked, found, and could not assemble what it found. No restatement
    // reaches it, since the search already said the goal follows, and no limit does either.
    case NotRebuilt(goal, procedure, reason) =>
      ReportADefect(
        s"$procedure found a certificate for ${write(goal, reals)} and its rebuilding was refused: " +
          reason.message
      )

    // The same shape one procedure over, and the reason `BoundReached` is its own case: a search
    // that stopped and a claim that does not follow look identical and imply opposite moves. The
    // limit is named because there is more than one of them and they are reached by different
    // goals.
    case BoundReached(limit, reached, allowed, goal) =>
      RaiseALimit(limit, s"${write(goal, reals)}, at $reached against $allowed")

    case SyntaxError(detail, position) => RepairTheText(detail, Some(position))

    case TypeError(detail) => RepairTheText(detail, None)

    case MissingDefinition(name) => ExtendTheTheory(name)

    case EscapingVariable(variable, where) =>
      RestateTheProblem(s"a statement in which ${variable.name} does not occur in $where")

    case MissingHypothesis(expected, _) => AssumeMore(write(expected, reals))

    case Undetermined(variable) => ChooseATerm(variable.name)

    // The same move as the case above, reached from the other side: there the goal does not fix a
    // variable, here the matcher cannot decide one, and in both the caller names the term and
    // specialises at it. Not a restatement, because the target may be an instance and nothing
    // about it needs changing.
    case BeyondMatching(_, _, refusal) => ChooseATerm(refusal.variable.name)

    // A shape to restate and not a term to choose, which is the line between this and the case
    // above: `Undetermined` says the goal is right and one quantity is unsaid, and this says the
    // call is wrong. Both numbers reach the message, because which of them is wrong is the caller's
    // to work out and usually means it reached a different lemma than it meant to.
    case PartialInstance(quantifiers, arguments, _) =>
      RestateTheProblem(
        s"a call with ${Prose.count(quantifiers, "argument")} rather than $arguments, " +
          "or specPrefix for a partial instance"
      )

    // Read off the caller's own reason rather than answered here, and that is the mapping rather
    // than a shortcut: the driver did its part, and what to try next is decided by why the one goal
    // failed. Which goal it was is in the refusal's message and is for a reader; it is not a move,
    // and a remedy that said "look at index 6" would be telling a session to do what it just did.
    case InstanceRefused(_, _, reason) => of(reason, reals)
  }

  /**
   * What to do about a kernel refusal.
   *
   * A kernel refusal names one of three things, and the three imply different moves. It names
   * something the theory does not have, and the theory is extended. It names a term that is not
   * well-typed, and the term is rewritten. Or it names a side condition on a primitive rule, and
   * those are the ones a caller cannot repair: the kernel is not driven directly from a session, so
   * a rule reaching one of them was handed something a correct tactic would never have built.
   *
   * The last group is [[ReportADefect]] for that reason and not because the condition is obscure.
   * Somebody driving the kernel by hand, which the tests do, would read the same refusal as their
   * own mistake; a session cannot, because it never chose the arguments.
   */
  def of(error: KernelError): Remedy = of(error, None)

  private def of(error: KernelError, reals: Option[Signature]): Remedy = error match {
    case UnknownConstant(name) => ExtendTheTheory(name)
    case UnknownTypeOperator(name) => ExtendTheTheory(name)

    case AlreadyDeclared(name) => RestateTheProblem(s"a declaration that does not repeat $name")
    // `argument(s)` until 2026-09-22, which reads at one and is a third mechanism for that in a
    // file whose other six counts go through `Prose.count`. It is not a defect the census finds,
    // the noun not being a bare plural, and it is a second name for what the counter already
    // does; the refusal it reads is `ArityMismatch`, whose own sentence moved on the same day.
    case ArityMismatch(name, expected, _) =>
      RestateTheProblem(s"$name applied to ${Prose.count(expected, "argument")}")
    case NotAnInstance(name, declared, _) =>
      RestateTheProblem(s"$name at an instance of ${Show.show(declared)}")
    case TypeMismatch(expected, _, context) =>
      RestateTheProblem(s"a term of type ${Show.show(expected)} in $context")
    case NotAFunction(found) =>
      RestateTheProblem(s"an application whose operator is a function, not ${Show.show(found)}")
    case NotAProposition(_, ty) =>
      RestateTheProblem(s"a proposition, where this is of type ${Show.show(ty)}")

    // Both arrive from `defineType` and both are about the witness the caller supplied, not about
    // anything a tactic built, so they are restated rather than reported: a caller defining a type
    // chose that theorem and can choose another.
    // `thing(s)` until 2026-09-22, and the third of this file's `(s)` forms to go: a theorem
    // reaching this branch assumes at least one, so the singular is the ordinary case rather than
    // an edge. `hypothesis` is the noun a reader wants and it is irregular, which is what
    // `Prose.count`'s two-form overload is for; writing the condition here instead would be a
    // fourth way of saying the same thing in a file that already has one.
    case TheoremHasHypotheses(hypotheses) =>
      RestateTheProblem(
        s"a theorem that holds outright, where this one assumes " +
          Prose.count(hypotheses.length, "hypothesis", "hypotheses")
      )
    case NotAnApplication(found) =>
      RestateTheProblem(s"a theorem concluding `P x`, where ${write(found, reals)} applies nothing")

    case NotLocallyClosed(found) =>
      ReportADefect(s"a rule was handed the open term ${write(found, reals)}")
    case NotAnEquation(found) =>
      ReportADefect(s"a rule was handed ${write(found, reals)} where an equation was needed")
    case NotABetaRedex(found) =>
      ReportADefect(s"a rule was handed ${write(found, reals)} where a redex was needed")
    case TermsDiffer(left, right, context) =>
      ReportADefect(
        s"a rule was handed ${write(left, reals)} and ${write(right, reals)} in $context, " +
          "which are not the same term"
      )
    case VariableIsFreeInHypotheses(variable, blocking) =>
      // The blocking hypotheses are named rather than counted, because which one mentions the
      // variable is what decides the repair: a recursion stated at one length is restated
      // universally, an assumption about one value is discharged, and the two look identical from
      // a message that says only that some hypothesis mentions it.
      ReportADefect(
        s"a rule generalised ${write(variable, reals)} while these hypotheses still mention it: " +
          blocking.map(write(_, reals)).mkString("; ")
      )
    case DefinitionIsNotClosed(free) =>
      ReportADefect(s"a definition was offered with ${free.mkString(", ")} free in it")
    case TypeVariablesEscape(names) =>
      ReportADefect(s"a definition was offered with ${names.mkString(", ")} escaping its type")
  }

  /**
   * What to do about a model search's outcome.
   *
   * Seven outcomes and seven is the point: `Refutation` keeps them apart because collapsing any two
   * turns "I could not ask" into "I asked and it was fine". They do not collapse here either, and
   * the three that are not answers get three different next steps.
   */
  def of(outcome: Refutation.Outcome): Remedy = outcome match {
    case Refutation.Found(witness, _) =>
      Settled(s"a point where the claim fails: ${point(witness)}")

    // The finite half is shown beside the rational one rather than dropped: a point over a sized
    // type is part of where the premises hold, and a message naming only the reals would say a set
    // about three agents is satisfied "at cost=1" and leave out which agent it was satisfied by.
    case Refutation.Solved(witness, finite) =>
      Settled(
        "a point satisfying the premises exactly: " +
          point(
            witness.map { case (name, value) => name -> value.toString } ++
              finite.map { case (name, value) => name -> Model.show(value) }
          )
      )

    // A count agreeing with a plural in both of these, a demonstrative in the first and a noun
    // behind a modifier in the second, and both reach one: a single premise can contradict itself,
    // and a claim with no premises puts one constraint to the search.
    case Refutation.Contradictory(premises) =>
      val which =
        if (premises == 1) "the one premise here cannot hold, so every conclusion follows from it"
        else s"these $premises cannot, so every conclusion follows from them"
      RestateTheProblem(s"premises that can hold at once; $which")

    case Refutation.NoCounterexample(constraints) =>
      Settled(s"no counterexample exists over ${Prose.count(constraints, "linear constraint")}")

    case Refutation.Survived(asked) =>
      APersonLooks(s"the claim survived ${Prose.count(asked, "point")}, which is evidence and not a decision")

    case Refutation.NeverAsked(offered) =>
      InterpretMore(s"none of ${Prose.count(offered, "point")} could be evaluated")

    case Refutation.Undecided(reason) => AskDifferently(reason)
  }

  /**
   * What to do about a decision on the propositional fragment.
   *
   * `Consistency` stands where `Refutation` and `Quantified` stand, under `docs/adr/0005`: it
   * decides and it certifies nothing. So [[Consistency.Verdict.Contradictory]] is [[Settled]] like
   * their decisions are, and the message says decided rather than proved.
   *
   * **The other answer is not settled and must not read as though it were.** Not contradictory is a
   * statement about propositional structure with the atoms uninterpreted, so premises it accepts can
   * still be unsatisfiable for a reason inside an atom. A caller told "settled" there would be told
   * the strong thing about the weak answer, which is the one way this file can mislead, so it is an
   * [[APersonLooks]]: somebody has to decide whether the atoms are as unrelated as the procedure
   * treated them.
   */
  def of(verdict: Consistency.Verdict): Remedy = verdict match {
    case Consistency.Verdict.Contradictory =>
      Settled("the premises cannot all hold, decided over their propositional structure")

    case Consistency.Verdict.NotContradictory(assignment) =>
      APersonLooks(
        "nothing in the propositional structure rules these out, which is weaker than consistent: " +
          s"the atoms are uninterpreted, and one reading that fits them is ${
            assignment.map { case (atom, value) => s"$atom = $value" }.mkString(", ")
          }"
      )

    case Consistency.Verdict.Refused(why) => AskDifferently(why)
  }

  /**
   * What to do about a decision over the quantifiers.
   *
   * `Quantified` stands where `Refutation` stands and under the same record, `docs/adr/0005`: a
   * model of the reals answers, nothing is certified, and no `Kernel.Thm` is built. So its two
   * decisions are [[Settled]] the way `NoCounterexample` is, and each message says the answer was
   * decided and not certified. A session that read `Holds` as a proof would be reading the one
   * claim that procedure never makes, and this is the sentence it would read it from.
   *
   * **Its refusals arrive as one string and get one next step.** An atom the linear reading cannot
   * range over, a quantifier it cannot open, a subterm `Linarith` cannot read as a linear form, and
   * an elimination that grows past `Quantified.Bound`, all come back as `Refused` carrying prose.
   * The last of those is a named budget and would be a [[RaiseALimit]]; the others are the shape of
   * the question. Telling them apart here would mean matching on the wording of a sentence written
   * one file over, which is what carrying values instead of sentences exists to prevent, so it
   * waits on `Quantified.Verdict` carrying its reason as a value.
   */
  def of(verdict: Quantified.Verdict): Remedy = verdict match {
    case Quantified.Holds => Settled("the claim holds over the reals, decided and not certified")

    case Quantified.Fails =>
      Settled("the claim does not hold over the reals, decided and not certified")

    // The reading `Refutation.Undecided` gets, for the reason it gets it: a procedure for the
    // linear fragment declining what is not in that fragment is a question for another address,
    // not a question a person has to think about. The reason it named travels with it, because it
    // is what says which address.
    case Quantified.Refused(why) => AskDifferently(why)
  }

  /**
   * What to do about a candidate closed form put through the screen.
   *
   * The screen refutes and never certifies, so its two answers are not two halves of one. A point
   * where the candidate and iteration differ settles the candidate, and agreement over the points
   * tried is evidence of the kind `Refutation.Survived` is: the message carries how many points
   * agreed, because that is the whole of what such an answer is worth.
   *
   * Its two absences stay apart here because they are apart there. A value past
   * `CollatzScreen.Exact` is a comparison a double cannot make, and the caller chooses the points,
   * so what is named is the screen it would have to be; exact arithmetic on a candidate would need
   * an evaluator this repository does not have, so [[AskDifferently]] would be naming an address
   * that is not there. A candidate with no value at a point is the absence `Evaluate` reports and
   * gets the answer that absence gets, and more points really will not help: the screen stops at
   * the first such point rather than skipping it.
   */
  /**
   * What to do about a goal put to the chaining search over the library.
   *
   * The three answers are three different next steps and that is why the outcome carries a value
   * rather than a sentence. A bound reached is a budget and reads as [[RaiseALimit]]; everything
   * inside the bounds tried and nothing reaching the goal is not a budget at all, and the honest
   * next step is that the development does not hold the lemma, which is [[ExtendTheTheory]].
   *
   * **The second of those is the one worth getting right.** A search that ran out of budget and a
   * search that finished and found nothing say opposite things about whether asking again could
   * help, and merging them would tell a caller to raise a limit that is not what stopped it. That
   * is the merge this file's comment about `Quantified.Verdict` describes from the other side: that
   * verdict carries prose, so its budget case cannot be told from its shape case here at all.
   */
  def of(outcome: Chaining.Outcome): Remedy = outcome match {
    case Chaining.Outcome.Proved(theorem, lemmas) =>
      Settled(s"proved by chaining ${lemmas.length} lemma(s): ${lemmas.mkString(", ")}")

    case Chaining.Outcome.Depleted(Chaining.Bound.Lemmas, at) =>
      RaiseALimit("lemmas chained", at.toString)

    case Chaining.Outcome.Depleted(Chaining.Bound.Expansions, at) =>
      RaiseALimit("lemma expansions in one question", at.toString)

    case Chaining.Outcome.NoRoute =>
      ExtendTheTheory(
        "a lemma this development holds whose conclusion is this goal, or which owes only what the " +
          "procedures decide; every one it holds was tried"
      )
  }

  def of(verdict: CollatzScreen.Verdict): Remedy = verdict match {
    case CollatzScreen.Disagrees(n, expected, got) =>
      Settled(
        s"the candidate and iteration differ at n = $n: iteration gives $expected, the candidate $got"
      )

    case CollatzScreen.Agreed(points) =>
      APersonLooks(
        s"the candidate agreed with iteration at ${Prose.count(points, "point")}, which is evidence and not a decision"
      )

    case CollatzScreen.NotExact(n, value) =>
      RestateTheProblem(
        s"a screen whose values stay inside CollatzScreen.Exact (${CollatzScreen.Exact}); " +
          s"at n = $n the candidate is $value"
      )

    case CollatzScreen.NotEvaluable(n) =>
      InterpretMore(s"the candidate at n = $n, where it has no value at all")
  }

  /**
   * What to do about a screening loop's outcome.
   *
   * `Discovery.Unsettled` already carries the refusal that produced it, so this defers to the
   * mapping for that refusal rather than re-deciding from `Why`. Keeping one decision site is what
   * makes the agreement between the two assertable at all.
   */
  /**
   * What to do about a claim's standing on the novelty scale, which is the question that scale
   * exists to answer.
   *
   * The scale ranks what a person will look at first, so every rung has a next step and the map is
   * the honest place to write them down. `Open` is the one that sends a person to look: a claim
   * that survived the screen and was certified by nothing here is what no decision procedure can
   * settle, which is `Discovery`'s `NotProvableHere` seen from the other side.
   */
  def of(standing: Novelty.Standing): Remedy = standing match {
    case Novelty.Standing.Open =>
      APersonLooks("it agreed at every point tried and no procedure here certified it")

    case Novelty.Standing.Earned =>
      Settled("certified, and by more than the cheapest procedure that could have been asked")

    case Novelty.Standing.Immediate =>
      Settled("the ring normalisation settles it; asking again cannot change it")

    case Novelty.Standing.Known =>
      Settled("it falls out of the lemmas already held, by rewriting alone: a corollary, not a result")

    case Novelty.Standing.Decided =>
      Settled("decided by quantifier elimination, which certifies nothing and cannot be asked twice")

    case Novelty.Standing.False =>
      Settled("decided false; the question is over")

    case Novelty.Standing.Unreadable =>
      RestateTheProblem("a claim one of these procedures can take, or a wider theory")
  }

  /**
   * What to do about a family the closed-form search was asked for.
   *
   * Four answers and four moves, and the reason they are not one: a family with no polynomial fit,
   * a family whose values cannot be computed, and a fit the prover refused send a reader to three
   * different places, and only the last of them is about the mathematics. `Found` is the fourth and
   * is settled, because what it carries is a theorem.
   */
  def of(outcome: Family.Outcome): Remedy = outcome match {
    case found: Family.Outcome.Found =>
      Settled(s"a closed form of degree ${found.degree}, certified")

    // Not a failure and not a claim that no closed form exists: a geometric sum has one and it is
    // not a polynomial. What would find it is a different fit, which is a different source.
    case Family.Outcome.NotPolynomial(_, sampled) =>
      AskDifferently(
        s"the values over ${Prose.count(sampled, "point")} are not a polynomial of any degree that fits them")

    // The interesting one, and the reason the fit is a screen rather than an answer: the values
    // agreed everywhere they were sampled and the claim did not hold. Nothing mechanical follows
    // from that; what a person does is look at the claim, which is why it is carried.
    case Family.Outcome.NotCertified(_, refusal) =>
      APersonLooks(s"the fit agreed at every point sampled and was not proved: $refusal")

    case Family.Outcome.Unreadable(why) => RestateTheProblem(s"a summand this can compute: $why")
  }

  /**
   * What to do about a request for the polynomial a sum of radicals satisfies.
   *
   * Five answers and four different moves, and the two that look alike are the ones to keep apart.
   * `NotCredible` is the search having found nothing the precision it was given supports, and the
   * move is **more digits**; `NotInTheIdeal` is the search having found something and the claim not
   * being true of every choice of sign, and no number of digits changes that. Sending both to
   * "raise a limit" would tell a reader to spend an afternoon on the second, which is settled.
   */
  def of(outcome: Algebraic.Outcome): Remedy = outcome match {
    case found: Algebraic.Outcome.Found =>
      Settled(s"a polynomial of degree ${found.coefficients.length - 1}, certified")

    // The digits are the limit and they are nameable, so this is the one case here that is a
    // limit rather than an answer. Not "there is no relation", which nothing here can say.
    case Algebraic.Outcome.NotCredible(_, confirmed, bound) =>
      RaiseALimit(
        s"the digits the values are known to, past ${Algebraic.Digits}",
        s"no relation up to degree $bound was confirmed by more than ${Prose.count(confirmed, "digit")}"
      )

    // Settled, and it is the interesting settlement: the value satisfies the polynomial and the
    // other reals with the same powers do not, so the claim a person would write is false. What
    // follows is a different claim, not a longer search.
    case Algebraic.Outcome.NotInTheIdeal(remainder, _) =>
      AskDifferently(
        s"the polynomial holds of the value and not of every root of the defining equations, " +
          s"which leaves $remainder"
      )

    case Algebraic.Outcome.NotCertified(why, _) =>
      APersonLooks(s"the certificate was built and the prover refused it: $why")

    case Algebraic.Outcome.Unusable(why) => RestateTheProblem(s"roots this can take: $why")
  }

  def of(outcome: Discovery.Outcome): Remedy = outcome match {
    case Discovery.Proved(left, right, _) => Settled(s"$left = $right, certified by the kernel")

    case Discovery.Disproved(left, right, witness, difference) =>
      Settled(s"$left = $right is false, by $difference at ${point(witness)}")

    // Settled, and the number of digits is what a reader does with it: a pair the first stage could
    // not separate and the second could is over as a candidate, and how far down it survived says
    // whether the shape was nearly right.
    case Discovery.Separated(left, right, _, agreement) =>
      Settled(s"$left = $right agreed to ${Prose.count(agreement, "digit")} and no further")

    case unsettled: Discovery.Unsettled => of(unsettled.reason)
  }

  /**
   * What to do about a ledger entry, which is the question the ledger was always asked.
   *
   * This replaces the table that used to live in a comment on `Ledger.Verdict`. A verdict carries
   * less than the outcome it was made from, so what comes back here is less specific than
   * `of(outcome)` on the same run: `TooLarge` knows a budget was reached and not which numeral
   * reached it. That is a property of the file rather than of this mapping, and a caller holding
   * the outcome should ask the outcome.
   */
  def of(verdict: Ledger.Verdict): Remedy = verdict match {
    case Ledger.Verdict.Proved => Settled("proved")
    case Ledger.Verdict.Disproved => Settled("disproved, with a witness")

    // The same words the standing gets, and it is the same fact: it holds, and nothing here has a
    // theorem for it. `Settled` rather than a route to a certificate, because there is none to
    // name: `docs/adr/0005` is the decision that a verdict is not a proof, and the thing to do
    // about one is know that, not ask again.
    case Ledger.Verdict.DecidedNotCertified =>
      Settled("decided by quantifier elimination, which certifies nothing and cannot be asked twice")
    case Ledger.Verdict.Outside => ExtendTheTheory("what the statement mentions")
    case Ledger.Verdict.TooLarge => RaiseALimit("Oracle.NumeralBudget", "a numeral in the statement")
    case Ledger.Verdict.Unfinished => RaiseALimit("the rewriting step limit", "the statement")
    case Ledger.Verdict.Open =>
      APersonLooks("both sides reached a normal form and the forms differ")
    case Ledger.Verdict.Unasked =>
      InterpretMore("what the statement mentions")
  }

  /**
   * A witness written out, whatever its values are.
   *
   * One implementation over three kinds of witness: sampled `Model.Value`s, exact `Rational`s from
   * the solver, and the doubles the screening loop carries. What a reader needs from all three is
   * the same, and three copies of a sort-and-join would be three chances to print one of them in a
   * different order from the others.
   */
  private def point[A](witness: Map[String, A]): String =
    witness.toVector.sortBy(_._1).map { case (name, value) => s"$name=$value" }.mkString(", ")
}
