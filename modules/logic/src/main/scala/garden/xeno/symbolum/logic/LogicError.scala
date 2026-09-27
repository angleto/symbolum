package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.{FVar, KernelError, Term}

/**
 * Why a derived rule refused.
 *
 * A separate type from the kernel's, rather than a case added to it, because the kernel's error
 * set is closed on purpose: everything that can go wrong inside the trusted base is enumerated
 * there, and a layer above must not be able to grow that enumeration. A kernel refusal reaching a
 * caller here arrives wrapped, so the boundary it crossed stays visible in the value.
 */
sealed trait LogicError {
  def message: String

  /**
   * What this refusal is about, which is the question a caller writing a negative check is asking.
   *
   * Abstract rather than defaulted, so a refusal added below does not compile until it says which
   * of the three it is. A default would make the next case's standing an omission rather than a
   * decision, and the omission anybody would fall into is the dangerous one.
   */
  def standing: LogicError.Standing
}

/** A rule of the kernel refused. */
final case class FromKernel(error: KernelError) extends LogicError {
  def message: String = error.message

  // The question was never put. A kernel rule refusing mid-derivation says the assembly above it
  // handed the kernel something a correct tactic would not have built, which is a defect in this
  // repository and never a fact about the goal.
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/** A term or a theorem was not of the shape the rule needed. */
final case class NotOfForm(expected: String, found: Term) extends LogicError {
  def message: String = s"expected $expected, found $found"
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * A procedure finished its search over the fragment it decides, and the goal is not in it.
 *
 * == The case that was missing, and what it used to arrive as ==
 *
 * This type had twelve refusals and none of them meant "from these premises this conclusion does
 * not follow". What that answer did was arrive as [[NotOfForm]], which is **also** the case for "I
 * cannot read this shape", so two opposite situations reached a caller as one constructor with a
 * different sentence inside. A consumer's harness counted every failure as a refutation and
 * published an exhausted search as one; it was careful, and careful was not enough, because the
 * distinction was in a string.
 *
 * == Why a case here, and not a three-way result out of `Linarith.prove` ==
 *
 * A sum type of the procedure's own is the shape the defect first suggests, and it is rejected for
 * three reasons that are about this layer rather than about that procedure.
 *
 * **The distinction is not one procedure's.** `Rewrite.proveEquation` already keeps all three
 * apart: [[NotEqualTo]] is two finished normal forms that differ, which is a decision;
 * [[NotNormalised]] is a rewriting that stopped, which is not; [[NotOfForm]] is a goal it never
 * read. `Ring` therefore gains the whole distinction **without a line changing in it**, because its
 * decided case already existed and now says so. A sum type belonging to `Linarith` would give one
 * procedure a vocabulary the ones beside it cannot speak, and a caller asking `Ring` the same
 * question would be back to reading sentences.
 *
 * **Its third arm would be a `LogicError` anyway**, so every caller would write a conversion, and a
 * conversion is where the merge comes back. `Linarith.prove` is called from inside `Linarith`
 * itself and from `Peano`, `Series`, `Prove`, `Abduce`, `Quantified` and `Provenance`: that is a
 * dozen hand-written arms mapping the decided case onto something, against none here.
 *
 * **And inattention already buys the right answer.** `.toOption`, `Try`, a `catch` and `isLeft` all
 * say "not proved", which is the weak and honest reading; [[LogicError.Standing.Decided]] is
 * reachable only by naming it. The old conflation was reachable *by* inattention, and that is the
 * property that had to go rather than the `Either`.
 *
 * == What it does not cover ==
 *
 * It is not a refutation, and `procedure` is carried so that nobody reads it as one. The decision
 * is over the fragment that procedure decides, with everything the fragment cannot read standing in
 * as an unknown, so a true claim outside the fragment lands here: `0 < x /\ 0 < y ==> 0 <= x * x +
 * y * y - 2 * (x * y)` holds and is not a non-negative combination of those two premises. What
 * refutes a claim is `Refutation`, which keeps seven answers apart, and what files one as decided
 * false is `Cost.Outcome.Fails`. This says a search finished and found nothing, which is a fact
 * about the question and never about the world.
 */
final case class DoesNotFollow(goal: Term, procedure: String) extends LogicError {
  def message: String =
    s"$procedure searched to the end: no non-negative combination of the hypotheses gives $goal, " +
      "and they are not contradictory either, so this is decided rather than merely unproved"

  def standing: LogicError.Standing = LogicError.Standing.Decided
}

/**
 * A search found a certificate for the goal and rebuilding it in the kernel was refused.
 *
 * The opposite of [[DoesNotFollow]] and the refusal most easily mistaken for it, which is why it is
 * its own case. The untrusted half finished and said the goal follows; the trusted half did not
 * accept the assembly, so nothing is established, and what failed is the procedure against its own
 * search rather than the goal against the fragment. Until 2026-09-25 this came out as whatever the
 * failing step said, a RING `NotEqualTo` at the first level, standing decided and naming neither
 * the goal nor the certificate; and inside an escalation it did not come out at all, because the
 * escalation reports the refusal from before it and that was `DoesNotFollow`. So a goal whose proof
 * had just been found was reported as decided not to follow, which is the one way this machinery
 * can mislead. Measured against `Linarith` at `57a2276d`, on
 * `!c x. c < 1 ==> 0 <= x ==> x = c * x ==> x <= 0`.
 *
 * `reason` is the step that refused, unchanged, so the defect can be found from the message.
 */
final case class NotRebuilt(goal: Term, procedure: String, reason: LogicError) extends LogicError {
  def message: String =
    s"$procedure found a combination of the hypotheses giving $goal and could not rebuild it in " +
      s"the kernel, so nothing about the goal is established either way: ${reason.message}"

  // Never decided, whatever the step that refused says of itself: a step deciding that the
  // assembled combination is not the goal's is a statement about the assembly. A step that stopped
  // on a bound keeps saying so, since "the rebuilding ran out" is still a search that stopped.
  def standing: LogicError.Standing = reason.standing match {
    case LogicError.Standing.Decided   => LogicError.Standing.Unread
    case LogicError.Standing.Exhausted => LogicError.Standing.Exhausted
    case LogicError.Standing.Unread    => LogicError.Standing.Unread
  }
}

/**
 * A classical propositional search finished and the goal's skeleton is falsifiable, with the
 * assignment that falsifies it.
 *
 * Its own case rather than a [[NotOfForm]] with the atoms written into the sentence, and the
 * argument is [[NotEqualTo]]'s in a second costume: an error carries values and the surface renders
 * them, because only the caller knows which notation its reader is using. `Propositional` lives in
 * `modules/logic`, which knows no notation at all, and rendered the atoms itself with the kernel's
 * printer, so somebody who asked about `x = 99` was shown
 * `(x = (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 1)))))))` and somebody who wrote `1 < x` was shown
 * `((< 1) x)`. What allowed it is that `expected` is a `String`: the field's type does not tell a
 * writer that a term does not belong there, and it was the second refusal in one day whose content
 * was prose where it should have been a value.
 *
 * == Why `Unread`, and why there is no fourth standing ==
 *
 * `Decided`, by analogy with [[DoesNotFollow]] and [[NotEqualTo]]: a procedure that searched its
 * own fragment to the end, with what lies outside the fragment standing in as unknown. The goal
 * that produced the defect refutes that reading. `!x:real. 1 < x ==> 0 < x \/ x = 99` is **true**,
 * and it is what arrives here, because the atoms are uninterpreted and the skeleton `A ==> B \/ C`
 * is falsifiable whatever the atoms mean. `Unread` is what it carries: the search ran on the
 * skeleton, the skeleton is not the goal, so about the goal nothing was learned.
 *
 * **This said until 2026-09-16 that a fourth standing was owed** -- one for "a procedure decided a
 * fragment too coarse to bear on the claim" -- and left it open. It is not owed, and what closed it
 * is a count rather than a rereading. Every library entry of the chain is a theorem and every one
 * is hypothesis-free, so each conclusion is **true**; put to the procedures with the library lookup
 * removed, so that no goal is answered by recognising the lemma it is, what reaches the
 * propositional address comes back refused here almost without exception, and what reaches the
 * order and equation addresses is filed `Decided` about half the time.
 *
 * So "this standing would make `LogicError.decided` answer yes about a theorem" does not separate
 * the two: `Decided` does exactly that, over half of this library's arithmetic statements,
 * deliberately, because decided over a fragment has never meant refuted and [[DoesNotFollow]] says
 * so in its own last section. What separates them is how often the fragment bears on the claim at
 * all, and that argues for filing this one **away** from `Decided`, which is where it already is.
 *
 * **Two readings, each with the revision it was taken at, because the population drifts.** The
 * ratio is the argument and the counts are not, so they carry their base rather than reading as a
 * property. This said "463 entries, 164 of 166" for four hours; nothing failed when the library
 * reached 477, which is how a figure of this shape rots with no gate noticing.
 *
 * {{{
 *   7.0 at fb3f45a   463 entries   propositional 164/166   arithmetic 62/112
 *   7.0 at 78b7b35   477 entries   propositional 172/174   arithmetic 62/112
 * }}}
 *
 * The fourteen between the two readings are twelve of the object language's syntax and two about
 * limits of sequences. **The arithmetic pair did not move at all**, and that is the half worth
 * keeping: that address receives the reals' own fragment, which is finished, while new development
 * lands at the propositional one. The gap does not close as the chain grows, it widens, and the
 * count that would have to be re-taken to overturn this is the arithmetic one.
 *
 * **What a fourth case would have cost was that nothing enforced it, and since 2026-09-16 something
 * does.** There was no exhaustive match on [[LogicError.Standing]] anywhere under `src/main`: the
 * readers were two `== Standing.Exhausted` comparisons in `Linarith` and the two `decided`
 * predicates, and those two have no production caller at all, every call site in the repository
 * being a spec. A fourth case compiled silently and every existing comparison answered `false`
 * about it, which was this enumeration's own defect one turn further out. The abstract `standing`
 * above makes a new **refusal** choose one; [[LogicError.Standing.answersTheGoal]] and
 * [[LogicError.Standing.stoppedShort]] are what now make a new **standing** answer for itself, and
 * the four readers go through them instead of comparing. It does not reopen the fourth case this
 * refusal was refused: it makes whichever case comes next a decision rather than an omission.
 *
 * And the distinction it would have carried is already carried, under a compiler check this enum
 * has not got. `Remedy` is a total match on `LogicError`: it sends [[DoesNotFollow]] to `Settled`
 * and this case to `RestateTheProblem`, so a caller asking what to do next is told two different
 * things already, and a case added there with no next step named stops compiling.
 *
 * `goal` is carried whole, before the leading quantifiers come off, because that is what the caller
 * asked and what it has to restate.
 */
final case class SkeletonFailsAt(goal: Term, assignment: Vector[(Term, Boolean)])
    extends LogicError {

  // The kernel's printer by way of `toString`, which is the last resort every case here falls back
  // to and is not the defect this case was split out of: a `message` is read where nobody supplied
  // a theory, and `Remedy` renders the same pairs in the reader's notation where somebody did.
  def message: String =
    s"the propositional skeleton of $goal fails at " +
      assignment.map { case (atom, value) => s"$atom := $value" }.mkString(", ") +
      ": the atoms are uninterpreted, so this is about the skeleton and not about the goal"

  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * The rewriter stopped before it had finished, so the two sides not meeting says nothing.
 *
 * Distinct from [[NotOfForm]] on purpose, and the distinction is the whole reason this exists. Two
 * different normal forms is what a false identity looks like and also what a rewriter that ran out
 * of steps looks like, and the reader's next move is opposite in the two cases: raise the limit, or
 * stop believing the identity. Until this was separated they produced the same `Left`.
 */
final case class NotNormalised(term: Term) extends LogicError {
  def message: String =
    s"rewriting stopped before finishing: $term still changes, so the two sides differing " +
      "is not evidence about the identity"

  def standing: LogicError.Standing = LogicError.Standing.Exhausted
}

/**
 * The rewriting stopped because the term was growing, which is the opposite advice to a limit.
 *
 * Its own case rather than a [[NotNormalised]], and the distinction is the one `docs/adr/0037`
 * exists for. Both say the rewriting did not finish, and the reader's next move is opposite: a
 * rewriting that ran out of steps is settled by raising the limit, and a rewriting that ran out of
 * **room** gets worse the higher the limit goes, because what stopped it was the rule set
 * multiplying the term. Reported as [[NotNormalised]] it reaches `Remedy` as `RaiseALimit`, which
 * is the advice that turns a four-minute heap exhaustion into a longer one.
 *
 * `reached` and `allowed` are the widths, in nodes, so that the message says how far past the
 * ceiling one pass took the term rather than only that it did. The term carried is the one the
 * caller was handed, which is the widest one **under** the ceiling: the one that crossed is not
 * kept, for the reason the ceiling exists.
 *
 * **Both numbers reach one and neither is a constant.** `Rewrite.repeatConv` takes its ceiling as
 * a parameter with a default, and `RewriteSpec` already passes one of its own; the guard is
 * `width > ceiling`, so a ceiling of zero prints `reached` as one and a ceiling of one prints
 * `allowed` as one. `reached` therefore goes through `Plural`, and `allowed` is written after
 * the noun rather than in front of it: `$allowed are allowed` would be a verb disagreeing with
 * its own number, which is the same defect one part of speech over and is not what a counter
 * repairs.
 */
final case class GrewPastCeiling(term: Term, reached: Int, allowed: Int) extends LogicError {
  def message: String =
    s"rewriting stopped because the term was growing: one pass took it to " +
      s"${Plural.count(reached, "node", "nodes")} where the ceiling in nodes is $allowed, " +
      s"so the rules multiply rather than settle and a higher " +
      s"limit makes this worse, not better. What was reached before that pass is $term"

  def standing: LogicError.Standing = LogicError.Standing.Exhausted
}

/**
 * A named bound stopped a search before it had looked at everything it would have looked at.
 *
 * The same argument as [[NotNormalised]] one procedure over, and it is the reason this is its own
 * case rather than a [[NotOfForm]] with a sentence in it. "No combination of the hypotheses gives
 * the goal" and "I stopped before building all the combinations" look identical to a caller and
 * imply opposite moves: stop believing the claim, or raise the line and wait. Until this existed
 * the second was reported as the first, so a goal that **is** a non-negative combination of its
 * hypotheses came back saying it is not.
 *
 * Measured on the family `0 < x1 /\ ... /\ 0 < xn ==> 0 < x1 * x2`, which the products settle for
 * every `n`: proved up to eight hypotheses, and from nine refused as not following. The goal did
 * not change and nothing about it stopped following.
 *
 * `limit` names the constant so that a caller can find it, `reached` and `allowed` are what makes
 * the message worth reading rather than a repetition of the name, and `goal` is carried as a term
 * for the reason [[NotEqualTo]] carries two: only the caller knows which notation its reader has.
 */
final case class BoundReached(limit: String, reached: Int, allowed: Int, goal: Term)
    extends LogicError {
  def message: String =
    s"$limit stopped the search at $reached, where it allows $allowed: this is not evidence " +
      s"about $goal either way"

  def standing: LogicError.Standing = LogicError.Standing.Exhausted
}

/**
 * A procedure proved the opposite of the goal: `proved` is a theorem, and it denies `goal`.
 *
 * The case `Convergence` needed on the day it landed, when a goal `?l. converges (Sum f) l` arrives
 * about a series the procedure proves divergent. That is the strongest answer a refusal can carry
 * and none of the others says it: [[NotOfForm]] would report that nothing was learned, which is
 * false, and [[DoesNotFollow]] speaks of a combination of hypotheses, which is LINARITH's fragment
 * and not this. Carried as terms for the reason [[NotEqualTo]] gives.
 *
 * `Decided`, and more than decided: unlike [[DoesNotFollow]] it does refute, because `proved` is a
 * theorem of the theory the goal was asked in. What it does not say is anything about a goal the
 * procedure did not read, and the procedure is named so a reader knows which fragment answered.
 */
final case class Denied(goal: Term, proved: Term, procedure: String) extends LogicError {
  def message: String = s"$procedure proved $proved, which denies $goal"
  def standing: LogicError.Standing = LogicError.Standing.Decided
}

/**
 * Two normal forms that do not meet, carried as terms rather than as a printed sentence.
 *
 * Its own case rather than a [[NotOfForm]] with the right-hand side interpolated, and the reason is
 * a defect that shipped: this layer knows the connectives and not the arithmetic, so printing a
 * term here used the logic's notation and rendered `3 * n + 1` as `+ 1 (* (BIT1 1) n)`. A session
 * reading an article of percentages was shown the binary encoding of the numerals.
 *
 * The rule the case exists to keep is that **an error carries values and the surface renders
 * them**. Only the caller knows which theory's notation the reader is using; `Remedy` takes one
 * when it has one.
 */
final case class NotEqualTo(wanted: Term, found: Term) extends LogicError {
  def message: String = s"$found is not equal to $wanted"

  // Decided, and it is the ring's half of [[DoesNotFollow]]. This is raised only where both sides
  // reached a fixed point of the same conversion, so the forms differing is a statement about the
  // identity; where the rewriting had not finished, [[NotNormalised]] is raised instead. It had two
  // other callers, in `Matrix`, checking that an assembled theorem was the goal, and they are
  // `NotOfForm("the goal as stated", ...)` since this classification existed to disagree with them.
  def standing: LogicError.Standing = LogicError.Standing.Decided
}

/**
 * Two finished normal forms differ over atoms that are not free variables, so the difference is a
 * fact about the procedure's reading and not about the claim.
 *
 * [[NotEqualTo]] is decided because a ring procedure reads everything it cannot take apart as an
 * atom, and two polynomials that differ over **independent** atoms differ as functions: choose the
 * atoms and the sides come apart. That argument needs the atoms to be free. `inv 0`, `exp 0` and
 * `inv x` are atoms of the reading and not free: `inv 0` has been a value the chain knows since the
 * reals were constructed, and `inv 0 = 0` is a theorem of it that RING refused as `Decided` until
 * 2026-09-27 (Mycelium card `7bf9d8a2`). What the refusal carries is the atoms that are not free,
 * because they are why nothing was decided, and a reader acts on them.
 *
 * Raised by the procedures that know which subterms of their normal form are coefficients, which a
 * rewriting in this module does not: `Rewrite` still raises [[NotEqualTo]] and they read it again.
 */
final case class NotEqualAsRead(wanted: Term, found: Term, bound: Vector[Term]) extends LogicError {
  def message: String =
    s"$found and $wanted differ as polynomials over their atoms, and ${bound.mkString(", ")} " +
      "is not a free variable, so the atoms need not be independent and the claim is not decided"

  // A search over a reading of the goal so coarse that what it settled was not the goal, which is
  // the last of `Unread`'s causes and the one this is.
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * A procedure established a value and could not say whether it is the one it was asked about.
 *
 * Its own case rather than [[NotEqualTo]], which is what it arrived as and what made it wrong.
 * `NotEqualTo` is decided because two finished normal forms differ, and that decides an identity
 * of the procedure's reading, which is a statement about two values only when nothing in them is
 * read as an atom. `Convergence` proved that a series converges to `exp 0` and was asked about
 * `1`; RING reads `exp 0` as an atom, found two forms that differ, and the refusal came out
 * decided about a claim that is true. `reason` is what the comparison said, unchanged.
 */
final case class ValueUnidentified(wanted: Term, found: Term, reason: LogicError) extends LogicError {
  def message: String =
    s"the value established is $found, and whether it is $wanted is not established either way: " +
      reason.message

  // Never decided, for `NotRebuilt`'s reason: whatever the comparison decided, it decided about
  // its own reading of the two terms. A comparison that stopped on a bound keeps saying so.
  def standing: LogicError.Standing = reason.standing match {
    case LogicError.Standing.Decided   => LogicError.Standing.Unread
    case LogicError.Standing.Exhausted => LogicError.Standing.Exhausted
    case LogicError.Standing.Unread    => LogicError.Standing.Unread
  }
}

/** The text could not be read as a term. */
final case class SyntaxError(detail: String, position: Int) extends LogicError {
  def message: String = s"$detail, at character $position"
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * The text is a term but not a well-typed one, or its type could not be determined.
 *
 * The second case is a refusal rather than a guess. A statement whose type the reader has to
 * work out is a statement nobody can check against a source, and the whole point of writing an
 * axiom in concrete syntax is that someone can.
 */
final case class TypeError(detail: String) extends LogicError {
  def message: String = detail
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/** A constant the standard theory should define was not there. */
final case class MissingDefinition(name: String) extends LogicError {
  def message: String = s"no definition of $name in this theory"
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * A variable that had to be arbitrary occurs somewhere it would be fixed.
 *
 * Distinct from the kernel's `VariableIsFreeInHypotheses`, which covers the side condition on
 * abstraction. This one covers the side conditions the kernel cannot see because they are about
 * the statement a rule is building rather than about the theorem it was handed. Eliminating an
 * existential has two of them, and `where` says which failed: a witness occurring in the conclusion
 * would prove that conclusion for the witness rather than from the existence of one, and a witness
 * occurring in the predicate would have the existential name the thing it exists to hide.
 */
final case class EscapingVariable(variable: FVar, where: String) extends LogicError {
  def message: String = s"${variable.name} must not occur in $where"
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * A rule was handed a theorem that does not carry a hypothesis the rule needs.
 *
 * Its own refusal rather than a `NotOfForm`, because the shape of what arrived is right and it is
 * the hypothesis list that is wrong, and because the two imply different repairs: a caller reading
 * this has to go back and assume something, not restate anything.
 */
final case class MissingHypothesis(expected: Term, rule: String) extends LogicError {
  def message: String = s"$rule needs a theorem assuming $expected"
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * A driver walked a finite family of goals and the caller's own procedure could not settle one.
 *
 * Its own refusal rather than the caller's reason passed straight up, and the argument is the one
 * [[BoundReached]] and [[NotNormalised]] are each separated for, one level further out. A driver
 * that enumerates has two ways to fail that look identical from outside: the assembly refused, or
 * one of the things it asked for was not forthcoming. Handing the caller's own `Left` back merges
 * them, and the caller then reads a message about the shape of a term as though the driver had
 * rejected the statement it was given.
 *
 * `index` says **which** of them, which is the part no other case carries and the part a reader
 * needs first: a walk of eight that stopped at the sixth is a different situation from one that
 * stopped at the first, and only the second suggests the method is wrong for the claim.
 *
 * `reason` is what the caller said, unchanged, so nothing is lost by the wrapping, and `Remedy`
 * reads the next step off it: what to do next is decided by why that one goal failed and not by its
 * having been reached from a walk. A caller that returns a theorem of some other shape arrives here
 * too, with a [[NotOfForm]] underneath, which is the honest reading rather than a fourth case: the
 * caller's step is wrong either way and `reason` is what tells the two apart.
 */
final case class InstanceRefused(index: Int, goal: Term, reason: LogicError) extends LogicError {
  def message: String = s"the instance at $index, $goal, was not settled: ${reason.message}"

  // The caller's own, for the reason `reason` is carried at all: a walk over a family adds nothing
  // to what is known about the claim, so what the instance settled is what the family settled. An
  // instance DECIDED not to follow is a family that does not follow; an instance whose search
  // stopped leaves the family open, and reading either off the wrapper rather than off the reason
  // would put the merge back one level out.
  def standing: LogicError.Standing = reason.standing
}

/**
 * A lemma was applied to a goal that does not say what one of its variables must be.
 *
 * Its own refusal rather than a `NotOfForm`, because the lemma is of the right form and the goal is
 * of the right form: what is missing is between them. `!x y. x < y ==> x <= y` applied to `a <= b`
 * decides `x` and `y` from the conclusion, and `!x y z. x < y /\ y < z ==> x < z` applied to
 * `a < c` decides `x` and `z` and says nothing about `y`, which is the case here and is not a
 * defect in either: a caller has to supply the middle, and this says which one it is.
 */
final case class Undetermined(variable: FVar) extends LogicError {
  def message: String = s"the goal does not say what ${variable.name} must be"
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * A lemma was not specialised at a target because deciding whether the target is an instance of it
 * is higher-order matching outside the fragment `Matching` decides.
 *
 * Its own refusal rather than a [[NotOfForm]], and the difference is what the caller is told.
 * `NotOfForm("an instance of ...")` says the target is not an instance, and here nothing was
 * decided about that: the target may be one. `P (SUC n)` under a binder for `n`, against
 * `SUC n < 3`, **is** an instance, at `P := \m. m < 3`, and the matcher turns it down, because `P`
 * is applied to `SUC n` with nothing earlier to decide it, and a variable applied to a term that
 * is not a binder is where the fragment stops: in general it has several answers. `LogicSpec`
 * holds that shape over a type variable, with the binder kept behind an implication so that
 * `specTo` does not strip it as a leading quantifier. A variable that an earlier occurrence has decided is not this case, and since
 * 2026-09-25 the matcher checks it instead of refusing it.
 *
 * `refusal` names the variable and the condition, and the repair is the caller's rather than a
 * rephrasing: name the term the variable stands for and specialise at it, which is how `Induct`
 * has always used an induction principle whose predicate is outside the fragment. `Unread`,
 * because nothing about the target was learned.
 *
 * What it does not say: that the target IS an instance. `Matching.why` reports the first condition
 * the walk met, and a pair refused there may also fail further along; `docs/adr/0030` measured
 * that every refusal of this kind the suite produced was such a pair.
 */
final case class BeyondMatching(pattern: Term, target: Term, refusal: Matching.Refusal)
  extends LogicError {
  def message: String =
    s"whether $target is an instance of $pattern is not decided here: " +
      s"${refusal.variable.name} is ${refusal.condition}, which is outside the fragment this " +
      s"matcher decides; supply ${refusal.variable.name} and specialise at it"

  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * A driver was asked to finish a goal and holds no procedure that could.
 *
 * Its own case, for the reason [[NotNormalised]] is its own case: "the closer looked and could not"
 * and "there was nothing to look with" read alike at a call site and imply opposite moves. The
 * first is a fact about the goal, and the second is a fact about how the driver was built, so it is
 * the caller's configuration that is wrong and not the mathematics.
 *
 * It exists because a driver over `num` alone has no algebraic closer and must not be given one it
 * cannot honour. `Ring` decides identities of the reals and refuses a goal of type `num` by type,
 * so a driver below the reals that carried `Ring.prove` would refuse every goal with a message
 * about the wrong thing.
 *
 * [[LogicError.Standing.Unread]] and not `Exhausted`: nothing searched and stopped, nothing was
 * asked at all.
 */
final case class NoCloser(goal: Term, driver: String) extends LogicError {
  def message: String =
    s"$driver was built with no closer, so nothing was asked about $goal: " +
      "what the rewriting left is undecided rather than unprovable"

  def standing: LogicError.Standing = LogicError.Standing.Unread
}

/**
 * A theorem was specialised at fewer arguments than it has leading quantifiers.
 *
 * Its own refusal rather than a [[NotOfForm]], and the two numbers are carried as numbers rather
 * than written into a sentence, because the two numbers are the whole content: what a caller has
 * to see is that it reached a theorem of a different arity from the one it meant to reach.
 *
 * It exists because the outcome it replaces was not an error at all. Four arguments into a
 * five-variable theorem produced a **partial instance**, one quantifier still in front and every
 * substitution shifted by one, and that theorem went on to fail somewhere else entirely: a session
 * on 2026-09-12 reached `NUM_DIVISION_UNIQUE` meaning `NUM_DIV_MOD_UNIQUE` and read the symptom at
 * an `mp` several steps later, with a message about an implication. A defect whose symptom appears
 * far from its cause is the shape that costs the most to find, and a short list is the only way to
 * produce one here.
 *
 * A partial instance is still wanted, once: `Rules.specPrefix` is where it is asked for by name.
 * The measurement that decided this is at that method.
 *
 * **The second count is given before its verb rather than after it, and that is the repair
 * finishing rather than a rewording.** Both numbers went through `Plural` on 2026-09-20 and the
 * sentence still read `1 argument were given` at one, because a counter repairs the noun and says
 * nothing about what agrees with it; the spec of this file asserted that sentence, so nothing was
 * going to go red on it either. `was given 1 argument` has no number in front of a verb to
 * disagree with.
 */
final case class PartialInstance(quantifiers: Int, arguments: Int, theorem: Term)
  extends LogicError {
  def message: String =
    s"this theorem has ${Plural.count(quantifiers, "leading quantifier", "leading quantifiers")} " +
      s"and was given ${Plural.count(arguments, "argument", "arguments")}: " +
      s"supply $quantifiers, or ask specPrefix for a partial instance"

  // `Unread`, and it is the case that made this classification earn its keep on the day it landed.
  // Two branches added it and the other on the same afternoon, and this one did not compile until
  // it answered, because `standing` is abstract on the trait: the caller asked a malformed
  // question, so no search ran and nothing at all was learned about the goal. It is emphatically
  // not `Decided`, and before this refusal existed it was not even a refusal -- it was an answer,
  // which is how its symptom ended up twenty lines from its cause.
  def standing: LogicError.Standing = LogicError.Standing.Unread
}

object LogicError {

  /**
   * A kernel result as a result of this layer.
   *
   * Public because every layer built on the logic needs it: a theory that declares a constant
   * calls the kernel and has to report what the kernel said. It was private to this package once,
   * which meant the module above had to invent its own wrapper, and two names for one conversion
   * is one too many.
   */
  def lift[T](result: Either[KernelError, T]): Either[LogicError, T] =
    result.left.map(FromKernel.apply)

  /**
   * What a refusal is about: the claim, the search, or the asking.
   *
   * Three answers rather than one, for the reason `Refutation` keeps seven and `Cost.Outcome` keeps
   * five: a caller that merges any two of them turns "I could not ask" into "I asked and the answer
   * was no". This is that discipline at the layer where the procedures actually live, and it was
   * the last one where the distinction was written in prose instead of in the type.
   *
   * Nested here rather than declared at the top of the package because `Novelty.Standing` already
   * exists one module up and a bare `Standing` in scope beside it would be a name a reader has to
   * resolve. `LogicError.Standing.Decided` says which question it answers.
   */
  enum Standing {

    /**
     * The procedure searched to the end of its fragment and the goal is not in it.
     *
     * The only one of the three that is an answer, and the only one a negative check may read as
     * one. [[DoesNotFollow]] and [[NotEqualTo]] are the two refusals that carry it, over the linear
     * and the ring fragments, and each says in its own documentation what its fragment does not
     * cover. Decided is not refuted: see [[DoesNotFollow]].
     *
     * **What a numeric screen taken BEFORE the attempt adds to that caveat**, which is not obvious
     * and is why it is written here rather than left to a reader. A refusal has three possible
     * explanations: the statement is false, the statement is true but outside the fragment, or the
     * statement is true and inside it and the proof was built wrongly. This enumeration separates
     * the third from the other two and **cannot ever separate the first from the second**, because
     * a procedure that searched its own fragment to the end has said nothing about the mathematics
     * outside it. A screen run first removes the first explanation from outside the system, so what
     * arrives is a measurement of where the procedures stop. A screen run afterwards removes
     * nothing, because by then the refusal has already been interpreted.
     *
     * Found by the consumer on 2026-09-12, which had done it in the right order without deciding
     * to and then saw why it worked. It is the repository's own "propose numerically, certify
     * symbolically" applied to a single statement rather than to a search.
     */
    case Decided

    /**
     * A bound or an unfinished rewriting stopped the work before it had looked at everything.
     *
     * Evidence in neither direction, which is what [[BoundReached]] and [[NotNormalised]] each say
     * in their own message. The next move is to raise the line and wait, which is the opposite of
     * the move [[Decided]] calls for, and confusing the two is the defect this enumeration exists
     * against: a real consumer read an exhausted search as a refutation and published it.
     */
    case Exhausted

    /**
     * Nothing about the goal was learned.
     *
     * The shape was one the procedure does not take, the text did not read, the theory lacked a
     * constant, an assembly below refused, or a search ran over a reading of the goal so coarse
     * that what it settled was not the goal. [[SkeletonFailsAt]] is that last one, and it is why
     * this case is defined by what was **learned** rather than by whether anything ran: the
     * sentence here said "the question was never put ... they agree that the search never ran"
     * until 2026-09-16, which is false of that refusal and was the whole of the argument for a
     * fourth standing. That refusal's own documentation carries the count that closed it.
     *
     * **The objection, which is that this case now names situations a caller repairs differently.**
     * It does, and it did before: counted against `Remedy`, the refusals filed here already lead to
     * `RepairTheText`, `RestateTheProblem`, `ExtendTheTheory` and `ChooseATerm`, four repairs and
     * not two. That is not a defect being widened, it is what this classification is not for. What
     * to do next is `Remedy`'s question and it answers it under a total match on the refusal, which
     * is a compiler check this enum has not got; what was learned is this one's, and the answer
     * here is the same for all five causes.
     */
    case Unread

    /**
     * Whether a refusal carrying this standing said something about the goal.
     *
     * The question [[decided]] is written in terms of, and the reason this is a match rather than a
     * comparison: a case added below does not compile until it answers here, exactly as a refusal
     * added above does not compile until it says which standing it carries. Until 2026-09-16 the
     * abstract `standing` protected one of those directions and nothing protected the other, so a
     * fourth case would have compiled in silence and every `== Standing.Decided` in the repository
     * would have answered `false` about it without anybody being asked.
     *
     * A wildcard case here would give that silence back, which is worth saying because the compiler
     * cannot: `-Xfatal-warnings` makes an omitted case an error and has nothing to say about a
     * `case _`.
     */
    def answersTheGoal: Boolean = this match {
      case Decided   => true
      case Exhausted => false
      case Unread    => false
    }

    /**
     * Whether the work stopped before it had finished, rather than finishing or never starting.
     *
     * The second question, and it is a second **match** rather than a negation of the first because
     * the two are independent: today no standing answers yes to both, and
     * [[LogicError.Standing.Unread]] answers no to both, which is what a single boolean could not
     * have carried. A case added below has to say where it falls on each, and if neither question
     * fits it, the honest move is a third one.
     *
     * The two readers are `Linarith`'s, where an escalation that stopped is reported in place of the
     * refusal from before it: "I stopped" is not a fact about the goal, and reporting it as one
     * sends a caller in the opposite direction.
     */
    def stoppedShort: Boolean = this match {
      case Decided   => false
      case Exhausted => true
      case Unread    => false
    }
  }

  /**
   * Whether a result decided the claim against its caller.
   *
   * The predicate a negative check is supposed to be written with, here rather than at each caller
   * so that there is one spelling of it. A `Right` is false, because a proof is not a decision that
   * something does not follow; every refusal but [[Standing.Decided]] is false, because a search
   * that stopped and a search that learned nothing about the goal are not answers.
   *
   * **What `true` does and does not claim, because the difference is what this predicate is for.**
   * It says a procedure went to the end of its fragment without finding the goal there. It does not
   * say the goal is false: over the chain's own library it is `true` of 62 theorems, read twice on
   * 2026-09-16, at `7.0` = `fb3f45a` and again at `78b7b35` where the library had grown by fourteen
   * and this count had not moved. [[SkeletonFailsAt]] holds both readings and what they settled.
   */
  def decided[T](result: Either[LogicError, T]): Boolean =
    result.left.exists(_.standing.answersTheGoal)
}
