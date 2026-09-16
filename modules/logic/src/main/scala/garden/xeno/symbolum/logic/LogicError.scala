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
 * **What a fourth case would have cost is that nothing would enforce it.** There is no exhaustive
 * match on [[LogicError.Standing]] anywhere under `src/main`: the readers are two
 * `== Standing.Exhausted` comparisons in `Linarith` and the two `decided` predicates, and those two
 * have no production caller at all, every call site in the repository being a spec. A fourth case
 * would compile silently and every existing comparison would answer `false` about it, which is this
 * enumeration's own defect one turn further out. The abstract `standing` above is what makes a new
 * **refusal** choose one; nothing makes a reader of a new **standing** notice it.
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
 */
final case class PartialInstance(quantifiers: Int, arguments: Int, theorem: Term)
  extends LogicError {
  def message: String =
    s"this theorem has $quantifiers leading quantifiers and $arguments arguments were given: " +
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
    result.left.exists(_.standing == Standing.Decided)
}
