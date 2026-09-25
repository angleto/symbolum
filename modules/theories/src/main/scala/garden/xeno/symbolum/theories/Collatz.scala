package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The rewriting system $$S_2$$, its counted sub-relation, its potential and its marked words.
 *
 * Source: `collatz@8b991e5`, `code/referee/checks_rewriting.py` lines 9 to 15, which is where the
 * eleven rules are written down and is the repository that owns them. Nothing here was transcribed
 * by eye: the rule table below was **generated** from those lines, and the letters, the splits and
 * the potential all follow the same source.
 *
 * == Why this is a development of its own and not part of `Forward` ==
 *
 * `Forward` is generic in the system: `WORD_RFC R` is about any `R`. This file is the one `R` that
 * one investigation is about. Keeping them apart is what lets the closure be reused and what keeps
 * a reader of `WORD_RFC` from thinking the eleven rules are part of what a closure is.
 *
 * == The alphabet, and why the digits are not named ==
 *
 * Seven letters, encoded as numbers, and the three digits are **0, 1 and 2 themselves**. That is
 * the decision worth knowing before reading anything below: `c` is a digit exactly when `c < 3`,
 * which is one comparison rather than a three-way disjunction, and it is what makes
 * [[Collatz.Potential]] one `NUM_SUM` over the positions. The other four letters are the numerals
 * above the digits, and they are named because a reader meeting `3` in a rule has no way to know it
 * is `f`.
 *
 * The cost of the encoding is that a letter is a number and nothing stops a term naming the letter
 * `9`. Nothing below cares: every rule names its letters, and a word over letters this system has
 * no rule for is a word no rule applies to, which is a normal form and not an error.
 *
 * == The three groups, which is the structure part C uses ==
 *
 * `D` is the two rules that consume the marker, `A` the six that commute a digit past a letter, and
 * `B` the three that act at the head. [[Collatz.Counted]] is `A` alone, and it is what the counted
 * sub-relation of `REACH` is built from: every `A`-step moves one digit one place nearer the head,
 * so it drops [[Collatz.Potential]] by exactly one, and no other rule lowers it. The relation
 * `REACH` is actually instantiated at is [[Collatz.RunCounted]], which is that one with the class
 * the measure behaves on carried along; the section below on where the argument becomes true says
 * why the class cannot be a side condition instead.
 *
 * == The marked words, which is where the argument stops being false ==
 *
 * [[Collatz.Marked]] is the class with exactly one tail marker, at the end, and
 * [[Collatz.MarkedClosed]] says a step never leaves it. That is not housekeeping: outside the class
 * the potential argument is false, and the source names the witness. `/ff.012` rewrites to `/0.012`
 * by `R1` and [[Collatz.Potential]] falls by three, which no counted step pays for. Restricting to
 * the marked words is what makes the inequality readable, and the restriction is only usable once
 * it is known to be preserved.
 *
 * **It is not where the argument becomes true, and this file said it was.** `REACH_POTENTIAL` asks
 * that a counted step drop the measure by exactly one and that no other step lower it, and both
 * fail on words this class accepts: `f0.` is marked, `A2` takes it to `0f.` and
 * [[Collatz.Potential]] is zero on both, because `NUM_SUB i 1` is truncated and nothing here says a
 * digit cannot sit at position 0; `0/0.` is marked, `B1` takes it to `0/t.` and the potential
 * falls, because the three `B` rules fire at any occurrence of the head marker and nothing here
 * says there is one.
 *
 * **Those two sentences are theorems and were six figures.** [[Collatz.ClassWitnesses]] is the
 * pair, derived and checked against the text each is written down as saying: `f0.` is marked, is
 * not anchored, is stepped by the commutation `A2`, and the measure does not fall across it; `0/0.`
 * is marked, is not anchored, is stepped by `B1`, no commutation steps it at all, and the measure
 * does fall. Until 2026-09-21 what stood here instead was a reading over every word of at most
 * seven letters — 9330 of 44790 counted steps out of the class failing the first hypothesis, 14454
 * of 33281 uncounted steps failing the second, against 0 of 3516 and 0 of 3280 once a head marker
 * is in front — which no test read and which is a property of the enumeration's bound as much as of
 * the system. The figures were evidence for the two sentences; the witnesses are the sentences.
 *
 * == Where it becomes true, which is that class with a head marker in front ==
 *
 * [[Collatz.Anchored]] is that predicate and [[Collatz.AnchoredClosed]] is its closure lemma, so
 * the measurement above is a theorem in both halves rather than a reading over seven letters:
 * [[Collatz.PotentialCountedStep]] says a counted step drops the measure by exactly one and
 * [[Collatz.PotentialPlainStep]] says no other step lowers it, each over a word that is anchored
 * and marked.
 *
 * [[Collatz.RunPotential]] is `REACH_POTENTIAL` carrying those two. What the instantiation had to
 * decide is where the class goes, because the lemma asks its hypotheses of **every** pair and has
 * no room for a side condition: it goes into the relation, as [[Collatz.Run]], and that loses
 * nothing because the class is closed under a step. [[Collatz.RunInhabited]] is the guard, since a
 * bound on every run of a relation that steps nothing is a theorem about nothing.
 *
 * What it does **not** yet reach is a run of positive length: detaching one needs a refusal of the
 * counted step at a concrete pair, which is a negative about `WORD_STEP` and nothing here proves
 * one.
 *
 * **What the bound buys the investigation, and the reading it must not be given.** It bounds the
 * commutations a run spends from **below**, by [[Collatz.Potential]] where the run began less
 * [[Collatz.Potential]] where it got to, so it is a statement about how long a derivation is and
 * none at all about whether derivations end. Termination of this system is what the investigation
 * wants and this is not a step towards it: a lower bound on the steps of a run cannot make any run
 * finite, whatever the measure. That termination is Yolcu, Aaronson and Heule's Conjecture 4.12,
 * open and rewarded, and it is **not** the Collatz conjecture either: by their Proposition 4.5(2)
 * it says every nonconvergent trajectory meets `5 mod 8`, which settles two of the four residue
 * classes their Theorem 4.10 leaves open. The place a lower bound on derivation length is actually
 * spent over there is a corollary of Koprowski and Waldmann's, which rules out a one-step arctic
 * termination proof once the derivational complexity is superlinear, and this theorem is not that
 * bound either: that one is a function of the initial word's length over a chosen family, this one
 * is one run against one measure. `collatz@8b991e5`,
 * `documents/05-open-problems-and-research-log.md`, sections 3.1.13 A and 3.1.14 E, is where both
 * of those live and is where a figure about either of them is read from.
 *
 * [[Collatz.TailFree]] is the other half and exists for the decomposition rather than for its own
 * sake: a marked word is a tail-free block with one marker on the end, so a step at `x l y` divides
 * into the case where the marker is inside `l` and the case where it is behind, and the two are
 * [[Collatz.MarkedStep]] and [[Collatz.TailFreeStep]].
 *
 * **The direction of that second condition is the one this repository has already got backwards
 * once.** `REACH_POTENTIAL` asks that no uncounted step LOWERS the measure, not that none raises
 * it. Two of the eleven do raise it, so the version with the inequality the other way round is
 * true, unusable, and was what a card carried until it was measured against the source.
 *
 * == The digit family, which is what the closure was built for ==
 *
 * [[Collatz.FamilyWithTail]] is `05` section 3.1.30 B: `/f0^j.` is in `WORD_RFC S2` for every `j`
 * from one up. [[Collatz.FamilyWithF]] is the induction it rests on, and the pair is one induction
 * and one extension rather than two inductions, which [[Collatz.digitFamily]] argues where it is
 * built. [[Collatz.Zeros]] is the run of digits both statements are written with, and it is the one
 * constant here that is not about the system.
 *
 * [[Collatz.ClosureRefused]] is what makes those two say something. `WORD_RFC S2` is constrained
 * from below by three clauses and from above by nothing at all, so a membership is worth exactly
 * what the non-memberships are worth, and there were none: both family facts would be theorems, and
 * so would every membership anybody proved after them, over a closure that held of every word.
 * `~(WORD_RFC S2 WORD_EMPTY)` costs one induction and the fact that a rule of this system has
 * letters on both sides, and it is the weakest statement that does the job.
 */
final class Collatz private (
  val forward: Forward,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  published: Map[String, Kernel.Thm],
  private[theories] val tools: Collatz.Concrete
) extends Signature {

  /** The facts this development proved, each cited under its name: what a consumer reads. */
  val facts: Map[String, Kernel.Thm] = Published.cite(published)

  /**
   * The eleven rules derived pairwise distinct, for the guard that the system is eleven rules.
   *
   * Not among [[facts]], and the reason is in [[Collatz.separations]]: nothing downstream needs
   * the rules to be distinct, so this is a fact about the encoding and belongs where this
   * repository keeps those, which is the spec that asks for it.
   */
  private[theories] def separations: Either[LogicError, Vector[(String, String, Kernel.Thm)]] =
    Collatz.separations(tools)

  /**
   * The two witnesses that say the anchored class is load-bearing, derived rather than enumerated.
   *
   * Not among [[facts]] for [[Collatz.separations]]'s reason: nothing downstream consumes them, and
   * what they are about is which hypothesis a published statement may not drop, which is a question
   * the spec asks. They are built here rather than in the spec because every step of them is this
   * file's machinery for a written-out word, none of which is reachable from outside it.
   *
   * Built on demand and not at construction: each is two words unrolled through `NUM_SUM` and one
   * of them walks the six counted clauses, so a development that never asks pays nothing.
   */
  private[theories] def classWitnesses: Either[LogicError, Collatz.ClassWitnesses] =
    Collatz.classWitnesses(tools, forward, definitions, facts)

  /**
   * `|- ~(WORD_STEP S2_COUNTED <word> <other>)` for a written-out pair the caller names.
   *
   * [[classWitnesses]] spends this at the one pair it is about, and that pair holds no marker, so
   * the reading at the other end of the block was derivable and never derived. Exposing the
   * builder is what lets a caller put a word **with** a marker to it, which is the half the
   * docstring of `Collatz.noCountedStepFrom` used to say was out of reach.
   *
   * It refuses a word that holds a marker and a digit both, by name, which is what it does not
   * cover rather than what it does not do today.
   */
  private[theories] def noCountedStep(
    word: String,
    other: String
  ): Either[LogicError, Kernel.Thm] =
    Collatz.noCountedStepFrom(
      tools,
      forward,
      forward.concatenation,
      definitions,
      Collatz.spell(word),
      Collatz.spell(other)
    )

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = forward.inductive.classical.logic
    .over(theory)
    .fold(
      error => throw new IllegalStateException(s"the logic does not extend: ${error.message}"),
      identity
    )

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Collatz {

  /* ------------------------------------------------------------------ the alphabet */

  /** The letter `f`, which is `3`: the digits are 0, 1 and 2 and the rest sit above them. */
  val F: String = "S2_F"

  /** The letter `t`, which is `4`. */
  val T: String = "S2_T"

  /** The head marker `/`, which is `5`. Every word of the system starts with it. */
  val Head: String = "S2_HEAD"

  /** The tail marker `.`, which is `6`. A marked word ends with it and holds no other. */
  val Tail: String = "S2_TAIL"

  /* ------------------------------------------------------------------ the system */

  /** `S2 l r` — `l -> r` is one of the eleven rules. */
  val Name: String = "S2"

  /** `S2_COUNTED l r` — `l -> r` is one of the six commutation rules, which is `A`. */
  val Counted: String = "S2_COUNTED"

  /** `S2_PHI w` — the sum, over the digit occurrences of `w`, of the distance from the head. */
  val Potential: String = "S2_PHI"

  /** `S2_MARKED w` — exactly one tail marker, and it is the last letter. */
  val Marked: String = "S2_MARKED"

  /**
   * `S2_TAILFREE u` — no letter of `u` is the tail marker.
   *
   * The ninth constant, and the one the closure of the marked class is written with rather than a
   * convenience. A marked word is a tail-free word with one marker on the end, so every statement
   * about how a step moves through a marked word splits into a statement about the piece holding
   * the marker and a statement about the pieces that do not. Without a name for the second the two
   * halves are the same quantified formula written out twice, which is how a lemma about the first
   * half ends up being proved again inside a proof about the second.
   */
  val TailFree: String = "S2_TAILFREE"

  /**
   * `S2_HEADFREE u` — no letter of `u` is the head marker.
   *
   * [[TailFree]] at the other marker, and the same construction serves both: what a proof about
   * either one does is read a letter and compare it, so the marker is an argument to those proofs
   * rather than a second copy of them. What it is **for** is the class the potential argument
   * holds on: outside a word with one head marker at the front, a `B` rule can fire at a digit
   * that is not the first one, and the measure falls across a step nothing counted.
   */
  val HeadFree: String = "S2_HEADFREE"

  /** `S2_ANCHORED w` — the first letter is the head marker, and no later letter is. */
  val Anchored: String = "S2_ANCHORED"

  /* ------------------------------------------------------------------ the facts */

  /** `|- !l r. S2_COUNTED l r ==> S2 l r` — the counted rules are rules. */
  val CountedIsRule: String = "S2_COUNTED_IS_RULE"

  /** `|- ?l r. S2 l r` — the system is inhabited, so nothing below is vacuously true. */
  val Inhabited: String = "S2_INHABITED"

  /**
   * `|- ~(S2 (WORD_SINGLETON S2_HEAD) (WORD_SINGLETON S2_HEAD))`.
   *
   * The refusal, and the reason it is the fact worth having rather than a courtesy. A relation that
   * held of everything would make `WORD_RFC S2` the set of all words and every statement downstream
   * true and empty. This is what says the eleven are eleven rules rather than a relation nobody
   * constrained, and it is derived by unfolding and refuting each of the eleven disjuncts on the
   * length of the words involved.
   */
  val Refused: String = "S2_REFUSED"

  /**
   * `|- !u v. S2_TAILFREE (WORD_CONCAT u v) = (S2_TAILFREE u /\ S2_TAILFREE v)`.
   *
   * Tail-freeness is a property of every letter, so it splits over a concatenation with nothing
   * left over. Both directions are needed and neither is the interesting one: a step takes
   * `x l y` to `x r y`, so the left-hand reading takes the context apart and the right-hand one
   * puts it back with the other rule side in the middle.
   */
  val TailFreeConcat: String = "S2_TAILFREE_CONCAT"

  /**
   * `|- !u v. 0 < WORD_LENGTH v ==> (S2_MARKED (WORD_CONCAT u v) = (S2_TAILFREE u /\ S2_MARKED v))`.
   *
   * The same split for the marked class, and the hypothesis is what makes it true. With `v` empty
   * the left-hand side is `S2_MARKED u`, which says nothing about `v` at all, and the right-hand
   * side asks `S2_MARKED WORD_EMPTY`, which is false: the equation would read `S2_MARKED u = F`
   * for every `u`. So the condition is not a technicality about where the marker sits, it is the
   * whole difference between a decomposition and a false statement.
   */
  val MarkedConcat: String = "S2_MARKED_CONCAT"

  /**
   * `|- !l r. S2 l r ==> 0 < WORD_LENGTH l /\ 0 < WORD_LENGTH r`.
   *
   * Every rule of the system has two or three letters on each side, and this is the consequence of
   * that which the closure needs: at the end of a word, `x l y` with `y` empty is `x l`, and
   * reading the marker off `l` rather than off `x` requires `l` to have a last letter.
   */
  val RuleNotEmpty: String = "S2_RULE_NOT_EMPTY"

  /**
   * `|- !l r. S2 l r /\ S2_MARKED l ==> S2_MARKED r`.
   *
   * Only the two `D` rules have a marked left-hand side, and both have a marked right-hand side:
   * `ff.` goes to `0.` and `t.` goes to `2.`. The other nine are discharged by refuting the
   * hypothesis, which is where the cost of this fact is, since a nine-fold vacuous case is nine
   * derivations that a concrete two-letter word does not end in the marker.
   */
  val MarkedStep: String = "S2_MARKED_STEP"

  /**
   * `|- !l r. S2 l r /\ S2_TAILFREE l ==> S2_TAILFREE r`.
   *
   * The mirror, and the split falls the other way: the nine rules that do not touch the marker
   * have tail-free sides, and the two `D` rules are discharged by refuting `S2_TAILFREE l`, their
   * left-hand sides being the only two that hold a marker.
   */
  val TailFreeStep: String = "S2_TAILFREE_STEP"

  /**
   * `|- !u v. S2_HEADFREE (WORD_CONCAT u v) = (S2_HEADFREE u /\ S2_HEADFREE v)`.
   *
   * [[TailFreeConcat]] at the head marker, proved by the same derivation with the marker passed in.
   */
  val HeadFreeConcat: String = "S2_HEADFREE_CONCAT"

  /**
   * `|- !u v. 0 < WORD_LENGTH u ==> (S2_ANCHORED (WORD_CONCAT u v) = (S2_ANCHORED u /\ S2_HEADFREE v))`.
   *
   * [[MarkedConcat]] read from the other end, and the guard moves with it: the marker is the FIRST
   * letter here, so it is the first block that has to be non-empty. With `u` empty the left-hand
   * side is `S2_ANCHORED v`, which says nothing about `u`, and the right-hand side asks
   * `S2_ANCHORED WORD_EMPTY`, which is false for want of a first letter.
   */
  val AnchoredConcat: String = "S2_ANCHORED_CONCAT"

  /**
   * `|- !l r. S2 l r /\ S2_HEADFREE l ==> S2_HEADFREE r`.
   *
   * The eight rules that do not name the head marker keep a word free of it; the three `B` rules
   * are discharged by refuting `S2_HEADFREE l`, their left-hand sides being the only ones that
   * hold a head marker.
   */
  val HeadFreeStep: String = "S2_HEADFREE_STEP"

  /**
   * `|- !l r. S2 l r /\ S2_ANCHORED l ==> S2_ANCHORED r`.
   *
   * The mirror of [[MarkedStep]]: only the three `B` rules have an anchored left-hand side, and
   * each has an anchored right-hand side, `/0 -> /t`, `/1 -> /ff` and `/2 -> /ft`. The other eight
   * are vacuous, their left-hand sides not beginning with the marker.
   */
  val AnchoredStep: String = "S2_ANCHORED_STEP"

  /**
   * `|- !u v. S2_ANCHORED u /\ WORD_STEP S2 u v ==> S2_ANCHORED v`.
   *
   * [[MarkedClosed]] at the other end of the word, and the division is the mirror image: either the
   * rule fires at the very front, and the marker is inside its own left-hand side, or it does not,
   * and the marker is in the prefix while the rule sees head-free letters only. `NUM_CASES` on the
   * prefix's length is what separates them.
   *
   * It is the second half of what the potential argument needs. `S2_MARKED` alone leaves the head
   * marker free to sit anywhere, and then a `B` rule fires at a digit that is not the first one and
   * lowers the measure across a step nothing counted: `0/0.` steps to `0/t.` and `S2_PHI` falls.
   */
  val AnchoredClosed: String = "S2_ANCHORED_CLOSED"

  /** `|- S2_ANCHORED </0.>`, the guard that says [[AnchoredClosed]] is about something. */
  val AnchoredInhabited: String = "S2_ANCHORED_INHABITED"

  /**
   * `|- !u v. S2_PHI (WORD_CONCAT u v) = NUM_ADD (S2_PHI u) <the second block, weighed where it sits>`.
   *
   * The measure over a word split in two, and the shape of the right-hand side is the whole content
   * of it. A tally that only saw letters would split with `S2_PHI v` on the right; this one weighs a
   * letter by its distance from the head, so the letters of `v` count from `WORD_LENGTH u` further
   * along than they do in `v` alone, and what appears is the shifted sum rather than the measure of
   * the block. `WORD_CONCAT_TALLY` is stated at a weight that takes the index for exactly this
   * reason and `Concatenation` says so where it is proved.
   *
   * It is what every statement about a step runs through: a step rewrites a factor, so both words
   * are three blocks, and this lemma twice is what turns each of them into a sum of three terms two
   * of which the rule does not touch.
   */
  val PotentialConcat: String = "S2_PHI_CONCAT"

  /**
   * `|- S2_PHI </00.> = SUC ZERO`, the measure at a word a reader can count by eye.
   *
   * What it guards is the reading of every figure below it. `S2_PHI` sums, over the positions of a
   * word, the distance from the head, counted only where the letter is a digit, and the two
   * decisions inside that sentence are invisible in the definition: the distance is `i - 1` over a
   * TRUNCATED subtraction, so a digit at position zero and one at position one both weigh nothing,
   * and a letter that is not a digit weighs nothing wherever it sits.
   *
   * `/00.` is the smallest word that shows both. Its two digits sit at positions one and two, so
   * they weigh nought and one, and the two markers weigh nothing at all: the measure is one. A
   * reader who took `S2_PHI` for "how many digits" or for "the sum of the positions" would get two
   * or three here, and nothing else in this development would correct them.
   */
  val PotentialAtAWord: String = "S2_PHI_AT_A_WORD"

  /**
   * `|- !x m y. S2_PHI ((x m) y) = (S2_PHI x + <m where it sits>) + <y where it sits>`.
   *
   * [[PotentialConcat]] twice, at the shape a step produces: `WORD_STEP` gives a word as a context,
   * a rewritten block and a tail, left-nested exactly like this, so every statement comparing the
   * measures of two words related by a step is this lemma at both of them.
   *
   * What it buys is that two of the three terms do not depend on the block. The first is the
   * context's own measure and the third is the tail weighed from `WORD_LENGTH (x m)` onwards, so
   * where a rule keeps the length of what it rewrites, both sides of a step have the **same** third
   * term and the comparison is between the two middle ones. Where a rule does not keep it -- `R1`
   * shortens and `B2` and `B3` lengthen -- the third terms differ, and that difference is the whole
   * reason the class the argument runs on is what it is.
   */
  val PotentialBlocks: String = "S2_PHI_BLOCKS"

  /**
   * `|- !u v. S2_ANCHORED u /\ WORD_STEP S2_COUNTED u v ==> S2_PHI u = SUC (S2_PHI v)`.
   *
   * The first of the two things `REACH_POTENTIAL` asks for, and the reason the anchored class is
   * needed rather than the marked one. Each of the six commutation rules moves one digit one place
   * towards the head and leaves everything else where it was, so the measure falls by exactly the
   * distance that digit lost, which is one -- **provided the rule did not fire at position zero**.
   *
   * At position zero it does not fall at all, because the distance is `i - 1` over a truncated
   * subtraction and a digit at position zero and one at position one both weigh nothing. `f0.`
   * steps to `0f.` by `A2` and the measure is nought on both. What rules that out is
   * [[Anchored]]: an anchored word has the head marker at position zero, and no commutation rule
   * has a head marker in it, so the rule's left-hand side cannot begin there.
   *
   * The tails do not move: every commutation rule has two letters on each side, so the block that
   * follows sits at the same distance from the head in both words, and the third term of
   * [[PotentialBlocks]] is the same term on both sides of the step.
   */
  val PotentialCountedStep: String = "S2_PHI_COUNTED_STEP"

  /**
   * `|- !u v. <the class> /\ WORD_STEP S2 u v /\ ~(WORD_STEP S2_COUNTED u v) ==> S2_PHI u <= S2_PHI v`.
   *
   * The second of the two things `REACH_POTENTIAL` asks for, and the one whose five rules fail in
   * three different ways. Six of the eleven clauses are not about arithmetic at all: a step by a
   * commutation rule **is** a counted step, built back out of the same four witnesses, so the
   * hypothesis refuses it and the clause closes on a contradiction.
   *
   * Of the five that remain:
   *
   *   - `R1` and `R2` consume the tail marker, so the marker is inside the rewritten block and the
   *     word is marked, which leaves nothing after it: the tail is empty, both tail sums are
   *     nought, and what is compared is `P + 0` against `P + (k - 1)`.
   *   - `B1` fires at the head, so the context is empty and the two blocks weigh the same: the two
   *     measures are the same term.
   *   - `B2` and `B3` also fire at the head and make the word one letter longer, so every letter
   *     after them moves one place along and weighs at least what it weighed. That is the one place
   *     `NUM_SUM_MONOTONE_BELOW` is spent, and the pointwise step is a case split on whether the
   *     letter there is a digit.
   */
  val PotentialPlainStep: String = "S2_PHI_PLAIN_STEP"

  /**
   * `S2_RUN u v` — a step of this system taken FROM a word of the class the measure works on.
   *
   * The relation `REACH` is instantiated at, and it exists because `REACH_POTENTIAL` asks its two
   * hypotheses of **every** pair while [[PotentialCountedStep]] and [[PotentialPlainStep]] hold
   * only where the word stepped from is anchored and marked. Restricting the relation rather than
   * weakening the lemma is what makes the two meet, and it costs nothing: the class is closed under
   * a step ([[AnchoredClosed]], [[MarkedClosed]]), so a run that begins inside it stays inside it
   * and every pair such a run can use is a pair of this relation.
   */
  val Run: String = "S2_RUN"

  /**
   * `S2_RUN_COUNTED u v` — such a step that is also a commutation, which is what gets counted.
   *
   * Written as [[Run]] **and** a counted step rather than as the class and a counted step, so that
   * the class is spelled in one place and `S2_RUN_COUNTED` is a sub-relation of `S2_RUN` by
   * construction. `REACH`'s counter advances on this one and stands still on the rest.
   */
  val RunCounted: String = "S2_RUN_COUNTED"

  /**
   * `|- !x q. REACH S2_RUN S2_RUN_COUNTED x q ==> S2_PHI x <= SND q + S2_PHI (FST q)`.
   *
   * `REACH_POTENTIAL` at this system, which is what `Reaching` was built for and what nothing
   * instantiated until it. Read from the other end it is the statement the investigation wants: a
   * run from `x` spends at least `S2_PHI x - S2_PHI (FST q)` counted steps getting to where it got,
   * so the measure bounds the length of a derivation from below.
   *
   * It is a bound and not a count: nothing here says a run of that length exists, and the empty run
   * satisfies it at every `x`. [[RunInhabited]] is what says the relation it quantifies over is not
   * empty, which is the guard a statement of this shape needs.
   */
  val RunPotential: String = "S2_RUN_POTENTIAL"

  /** `|- S2_RUN (/0.) (/t.)`: the relation the bound above is about relates something. */
  val RunInhabited: String = "S2_RUN_INHABITED"

  /** `|- !j. WORD_LENGTH (S2_ZEROS j) = j`, which is the recursion's own index read as a length. */
  val ZerosLength: String = "S2_ZEROS_LENGTH"

  /**
   * `|- !j. WORD_LENGTH (WORD_CONCAT (/f) (S2_ZEROS j)) = SUC (SUC j)`.
   *
   * The family without its tail marker, measured. It is here rather than inside the one proof that
   * spends it because that proof spends it under a binder: what the measure of a block placed after
   * this one depends on is how far along the word that block starts, and this says how far.
   */
  val StemLength: String = "S2_STEM_LENGTH"

  /**
   * `|- !j. S2_PHI (WORD_CONCAT (/f) (S2_ZEROS j)) = NUM_TRI j`.
   *
   * The measure of the family in closed form, and the closed form is a **triangular number** rather
   * than a quotient: `Numbering` defines `NUM_TRI` by recursion for exactly this reason, that
   * `j (j + 1) / 2` cannot be written on `num` without a division nothing here computes. The two
   * recurrences line up without arithmetic: the `j`th zero sits at position `j + 1` and contributes
   * its distance from the head, which is `SUC j`, and `NUM_TRI (SUC j)` is `NUM_TRI j + SUC j`.
   */
  val PotentialOfStem: String = "S2_PHI_STEM"

  /** `|- !j. S2_PHI (/f0^j.) = NUM_TRI j`: the tail marker is not a digit, so it weighs nothing. */
  val PotentialOfFamily: String = "S2_PHI_FAMILY"

  /**
   * `|- !j q. REACH S2_RUN S2_RUN_COUNTED (/f0^j.) q ==> NUM_TRI j <= SND q + S2_PHI (FST q)`.
   *
   * [[RunPotential]] at the one family this investigation has a name for, which is what makes the
   * bound a statement about a **size** rather than about an arbitrary word. Read at a run that ends
   * where the measure is nothing, it says a derivation from the `j`th member spends at least
   * `NUM_TRI j` commutations, and `NUM_TRI` grows as the square: that is the quadratic, in the one
   * direction this machinery supports, which is from below.
   *
   * What it is **not**: a statement that such a run exists, or that any run terminates. Both would
   * need a derivation of positive length, and [[RunPotential]] records what is missing for one.
   */
  val FamilyBounded: String = "S2_FAMILY_BOUNDED"

  /**
   * `|- S2_PHI (/f0.) = SUC ZERO`, derived through [[PotentialOfFamily]] and written by hand.
   *
   * The guard on the closed form, and it is the one an off-by-one would fail. The statement is a
   * concrete word and a concrete number, checked by eye: the one digit of `/f0.` sits at position
   * two and weighs its distance from the head, which is one. The **derivation** goes the other way
   * round, specialising the family at `SUC ZERO` and reducing both sides, so a `NUM_TRI` that
   * counted the letter rather than its distance would come back `SUC (SUC ZERO)` here and nowhere
   * else: every other fact about the family is stated in `NUM_TRI` and would agree with itself.
   */
  val FamilyAtOne: String = "S2_PHI_FAMILY_AT_ONE"

  /**
   * `|- !u v. S2_MARKED u /\ WORD_STEP S2 u v ==> S2_MARKED v`.
   *
   * What this development was asked for, and the sentence that lets a potential-function argument
   * be read on the marked words rather than on every word. Outside that class the argument is
   * false and the source says so with a witness: `/ff.012` rewrites to `/0.012` by `R1` and the
   * potential falls by three, which no counted step can pay for.
   *
   * The proof divides on whether the rule fires at the very end of the word. If it does, the
   * marker is inside the rule's own left-hand side and [[MarkedStep]] carries it; if it does not,
   * the marker is in the tail, the rule sees only tail-free letters, and [[TailFreeStep]] carries
   * those. `NUM_CASES` on the tail's length is what separates them and `WORD_LENGTH_ZERO` is what
   * turns the zero case back into the empty word.
   */
  val MarkedClosed: String = "S2_MARKED_CLOSED"

  /**
   * `|- S2_MARKED </0.>` and `|- WORD_STEP S2 </0.> </t.>`.
   *
   * The two guards that say [[MarkedClosed]] is about something. A closure statement over an empty
   * class is true and empty, and so is one over a relation that steps nothing, and neither shows
   * up as a failure anywhere: both halves would still be theorems. `/0.` is marked, `B1` fires on
   * it at the head, and `/t.` is what comes out, so `CollatzSpec` can detach the closure and get a
   * marked word back rather than assert that an implication exists.
   *
   * This is the discipline `RestsOnSpec` and `ProposeSpec` carry from the other side, at the one
   * statement in this file whose emptiness would be invisible.
   */
  val MarkedInhabited: String = "S2_MARKED_INHABITED"

  /** `|- WORD_STEP S2 </0.> </t.>`, the other half of what [[MarkedInhabited]] guards. */
  val StepInhabited: String = "S2_STEP_INHABITED"

  /* ------------------------------------------------------------------ the digit family */

  /**
   * `S2_ZEROS i` — the word `0^i`, which is the run of digits the family below is built out of.
   *
   * Defined by recursion on the index rather than as a `WORD_MAKE` with a conditional inside it,
   * and the choice is what the two proofs below cost rather than a preference. The family is
   * reached one letter at a time, so what every step of those proofs needs is
   * `0^(SUC i) = WORD_CONCAT 0^i 0`; the recursion hands that over as the defining equation, where
   * the shape built out of `WORD_MAKE` gives it only through `WORD_EXTENSIONALITY`, which is a
   * length and an argument about every index, per step, for a word every letter of which is the
   * same.
   *
   * The tenth constant of this development and the first that is not about the system itself. It is
   * here rather than in `Concatenation` because what it repeats is **this alphabet's** zero: the
   * general operation, a letter repeated, would be a constant of the chain, and `Concatenation` is
   * a link in it whose own spec asserts which six constants it adds.
   */
  val Zeros: String = "S2_ZEROS"

  /**
   * `|- S2_ZEROS ZERO = WORD_EMPTY` and `|- !n. S2_ZEROS (SUC n) = WORD_CONCAT (S2_ZEROS n) <0>`.
   *
   * The recursion's own two equations, published rather than kept inside the construction. A
   * defined constant whose equations nobody can reach is a name and not a function: every fact
   * below states something about `S2_ZEROS i` at an index nobody has written down, and without
   * these there is no way for a reader, or for a test, to get from such a fact to a word with
   * letters in it. `CollatzSpec` is what spends them, on the member of the family at `j = 1`.
   */
  val ZerosAtZero: String = "S2_ZEROS_ZERO"

  /** The other half of [[ZerosAtZero]], which its documentation covers. */
  val ZerosAtSuccessor: String = "S2_ZEROS_SUC"

  /**
   * `|- !i. WORD_RFC S2 (WORD_CONCAT (WORD_CONCAT </f> 0^i) <f>)` — `/f0^i f` is in the closure.
   *
   * The induction the family is reached by, and it is published rather than kept private because
   * it is the fact [[FamilyWithTail]] is one extension away from: a reader who wants to know why
   * `/f0^j.` is in the closure is reading this statement and then one clause instance.
   *
   * Source: `collatz@8b991e5`, `code/referee/checks_rewriting.py:713`, which measures the same two
   * facts twice, by generating the closure forwards and by a goal-directed backward search, and
   * which names the three clause instances the proof spends: the right-hand side of `B2`, which is
   * `/ff`, and the two right extensions `f|0 -> 0f` and `f|f. -> 0.`.
   */
  val FamilyWithF: String = "S2_FAMILY_F"

  /**
   * `|- !i. WORD_RFC S2 (WORD_CONCAT (WORD_CONCAT </f> 0^(SUC i)) <.>)` — the family itself.
   *
   * Stated at `SUC i` and not under a hypothesis `0 < j`, which is the same arrangement
   * `Provability` gives its reason for: the index of a member of this family is one more than the
   * number of extensions that reached it, and a guard bought to allow an index nobody can reach
   * would appear in every statement about the family afterwards. `/f.` is **not** a member and
   * the source's own backward search says so, so `j = 0` is not a case this omits, it is a case
   * that is false.
   */
  val FamilyWithTail: String = "S2_FAMILY_TAIL"

  /**
   * `|- ~(WORD_RFC S2 WORD_EMPTY)` — the closure of this system is not every word there is.
   *
   * The guard on the two statements above, and it is the one this file would be worthless without.
   * `WORD_RFC S2` is a predicate nothing else here constrains from above: a closure that held of
   * every word would make [[FamilyWithF]] and [[FamilyWithTail]] theorems about nothing, and both
   * of them, and every membership anybody proves after them, would still be derivable. That is the
   * shape of defect `RestsOnSpec` is about, at the one place in this development where it could
   * hide, and `ForwardSpec` does not cover it: what is asserted there is that the closure's
   * induction principle asks nothing of the system, not that any closure is proper.
   *
   * What it says is small on purpose. The source's own instrument refuses `/f.`, `/ff.` and `/tt.`
   * as well, and each of those wants an invariant about the letters rather than about the length;
   * the empty word is refused by the invariant that is already in the file, which is that every
   * rule of this system has letters on both sides. So this costs [[RuleNotEmpty]], the length of a
   * concatenation, and one induction over the closure, and it buys the only thing a vacuity guard
   * has to buy, which is that the predicate is not constant.
   */
  val ClosureRefused: String = "S2_RFC_REFUSED"

  /* ------------------------------------------------------------------ the types */

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Words: Type = TyApp(Word.TypeName, List(Numbers))

  private val LeftSide: FVar = Term.variable("l", Words)
  private val RightSide: FVar = Term.variable("r", Words)

  private val LengthType: Type = Type.fun(Words, Numbers)
  private val NthType: Type = Type.fun(Words, Type.fun(Numbers, Numbers))
  private val ConcatType: Type = Type.fun(Words, Type.fun(Words, Words))
  private val SystemType: Type = Type.fun(Words, Type.fun(Words, Type.Bool))
  private val OrderType: Type = Type.fun(Numbers, Type.fun(Numbers, Type.Bool))
  private val BinaryNumbers: Type = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  /* ------------------------------------------------------------------ the rule table */

  /** Which of the source's three groups a rule belongs to. */
  enum Group {

    /** `D`: the two rules that consume a digit next to the tail marker. */
    case Consumes

    /** `A`: the six that commute a digit one place towards the head. This is the counted one. */
    case Commutes

    /** `B`: the three that act at the head marker. */
    case AtTheHead
  }

  /**
   * One rule, with its letters named rather than spelled into a string.
   *
   * The table is the source of both things this development does with a rule, and it became a
   * table on 2026-09-16 for the second of them. The text of the definition is generated from it,
   * which is what it was for when the rules landed; a **proof** about one rule needs that rule's
   * two words as terms, and before the table existed the only place a rule was written down was
   * inside a string that had already been concatenated to ten others.
   *
   * A letter is spelled the way this theory spells it: a digit is its own numeral and the other
   * four are the constants that name them, which is [[Letters]] read from the other side.
   */
  final case class Rule(label: String, group: Group, left: Vector[String], right: Vector[String])

  /**
   * The eleven rules, in the source's own order: `RULES = D + A + B`.
   *
   * Source: `collatz@8b991e5`, `code/referee/checks_rewriting.py` lines 9 to 15. The spellings
   * below are that file's, letter for letter, and the order is that file's `D + A + B`.
   *
   * **What says this is faithful is a measurement and not care.** The text this table generates
   * was compared, character for character, against the hand-written literal it replaced, which was
   * itself generated from those lines when the rules landed; the two agree exactly, up to the
   * trailing space the literal ended with. A table that had moved a letter would have produced a
   * different string and the comparison would have said so. That check reads a second repository,
   * so it is a dated measurement rather than a gate, and what guards the table from here on is
   * `CollatzSpec`: eleven disjuncts counted off the definition, and the eleven left-hand sides
   * derived pairwise distinct.
   */
  val Rules: Vector[Rule] = Vector(
    rule("R1", Group.Consumes, "ff.", "0."),
    rule("R2", Group.Consumes, "t.", "2."),
    rule("A1", Group.Commutes, "t0", "1t"),
    rule("A2", Group.Commutes, "f0", "0f"),
    rule("A3", Group.Commutes, "t1", "2f"),
    rule("A4", Group.Commutes, "f1", "0t"),
    rule("A5", Group.Commutes, "f2", "1f"),
    rule("A6", Group.Commutes, "t2", "2t"),
    rule("B1", Group.AtTheHead, "/0", "/t"),
    rule("B2", Group.AtTheHead, "/1", "/ff"),
    rule("B3", Group.AtTheHead, "/2", "/ft")
  )

  /** `A`, the six that [[Counted]] is defined by, taken from the table rather than written twice. */
  val CountedRules: Vector[Rule] = Rules.filter(_.group == Group.Commutes)

  private def rule(label: String, group: Group, left: String, right: String): Rule =
    Rule(label, group, spell(left), spell(right))

  /** A word of the source's alphabet, as the letters this theory names them by. */
  private def spell(word: String): Vector[String] =
    word.map {
      case 'f' => F
      case 't' => T
      case '/' => Head
      case '.' => Tail
      case digit => digit.toString
    }.toVector

  /* ------------------------------------------------------------------ the text */

  private def singletonText(letter: String): String = s"WORD_SINGLETON ($letter:num)"

  /**
   * A word as a left-nested concatenation of one-letter words.
   *
   * Left-nested rather than right-nested because that is the shape the hand-written literal had,
   * and the shape decides which of `WORD_CONCAT_NTH_LEFT` and `WORD_CONCAT_NTH_RIGHT` reads which
   * letter. Every rule of this system has at least two letters, so the fold never meets an empty
   * word; a word with none would be `WORD_EMPTY` and is not something the table can hold.
   */
  private def wordText(letters: Vector[String]): String =
    letters.map(singletonText).reduceLeft((built, next) => s"WORD_CONCAT ($built) ($next)")

  /**
   * `/f0^index last`, as text: the digit family, with whatever letter ends it.
   *
   * Left-nested for [[wordText]]'s reason, and the nesting is what the proofs read: the extension
   * clause asks for a member of the shape `WORD_CONCAT p a`, so the last letter has to be the
   * outermost concatenation or the clause does not apply without an associativity first.
   */
  private def familyText(index: String, last: String): String =
    s"WORD_CONCAT (WORD_CONCAT (${wordText(spell("/f"))}) ($Zeros $index)) (${singletonText(last)})"

  /** A rule set as the disjunction of its clauses, which is how both relations are defined. */
  private def disjunctionText(rules: Vector[Rule]): String =
    "\\l:word(num). \\r:word(num). " +
      rules
        .map(entry => s"(l = ${wordText(entry.left)} /\\ r = ${wordText(entry.right)})")
        .mkString(" \\/ ")

  private val SystemBody: String = disjunctionText(Rules)

  private val CountedBody: String = disjunctionText(CountedRules)

  /**
   * `S2_PHI w` — the distance from the head, summed over the digit occurrences.
   *
   * The digits are `0`, `1` and `2` themselves, so "is a digit" is one comparison rather than a
   * three-way disjunction, which is what keeps this a single `NUM_SUM` over the positions.
   */
  private val PotentialBody: String =
    "\\w:word(num). NUM_SUM (\\i:num. COND (WORD_NTH w i < 3) (NUM_SUB i 1) 0) (WORD_LENGTH w)"

  /**
   * The two marker-free predicates are folds, since 2026-09-25: "no letter is the marker" is a
   * conjunction along the list, which `Folding.FoldOfEvery` says is the same as the reading by
   * position below. The positional reading is what every proof in this file written before then
   * runs on, and it is not rewritten: it is **derived** from the fold by [[byPosition]] and handed
   * to those proofs in the definition's place, so what changed is how the predicate is written and
   * how its split over a concatenation is proved, and nothing downstream of either.
   */
  private val TailFreeBody: String =
    "LIST_FOLD (\\x:num. \\r:bool. ~(x = S2_TAIL) /\\ r) T"

  private val HeadFreeBody: String =
    "LIST_FOLD (\\x:num. \\r:bool. ~(x = S2_HEAD) /\\ r) T"

  private val TailFreeByPosition: String =
    "\\w:word(num). !i:num. i < WORD_LENGTH w ==> ~(WORD_NTH w i = S2_TAIL)"

  private val HeadFreeByPosition: String =
    "\\w:word(num). !i:num. i < WORD_LENGTH w ==> ~(WORD_NTH w i = S2_HEAD)"

  /**
   * `S2_ANCHORED w` — positive length, the first letter is the head marker, and no later letter is.
   *
   * The inner claim is guarded by `0 < i /\ i < WORD_LENGTH w` rather than by the bound alone,
   * because position zero is the one place the marker is required rather than forbidden. That is
   * one conjunct more than [[MarkedBody]] carries, and it is what the index arithmetic buys: over a
   * truncated subtraction the last position has to be written `|w| - 1` and asks for the length to
   * be a successor before it is anything, where the first position is `ZERO` and asks for nothing.
   */
  private val AnchoredBody: String =
    "\\w:word(num). 0 < WORD_LENGTH w /\\ " +
      "WORD_NTH w ZERO = S2_HEAD /\\ " +
      "(!i:num. 0 < i /\\ i < WORD_LENGTH w ==> ~(WORD_NTH w i = S2_HEAD))"

  /** `S2_MARKED w` — positive length, the last letter is the marker, and no earlier letter is. */
  private val MarkedBody: String =
    "\\w:word(num). 0 < WORD_LENGTH w /\\ " +
      "WORD_NTH w (NUM_SUB (WORD_LENGTH w) 1) = S2_TAIL /\\ " +
      "(!i:num. i < NUM_SUB (WORD_LENGTH w) 1 ==> ~(WORD_NTH w i = S2_TAIL))"

  /**
   * `S2_RUN u v` — a step of `S2` from a word that is both anchored and marked.
   *
   * The class is written here and nowhere else: [[RunCountedBody]] names this relation rather than
   * repeating the two conjuncts, so the two cannot drift apart.
   */
  private val RunBody: String =
    "\\u:word(num). \\v:word(num). " +
      "WORD_STEP S2 u v /\\ S2_ANCHORED u /\\ S2_MARKED u"

  /** `S2_RUN_COUNTED u v` — one of those that is a commutation, which is the counted kind. */
  private val RunCountedBody: String =
    "\\u:word(num). \\v:word(num). S2_RUN u v /\\ WORD_STEP S2_COUNTED u v"

  /** The four letters that are not digits, in the order they are declared. */
  val Letters: Vector[(String, String)] =
    Vector(F -> "3", T -> "4", Head -> "5", Tail -> "6")

  /** Every definition this development introduces, as text, in dependency order. */
  val Bodies: Vector[(String, String)] =
    Letters.map { case (name, value) => name -> s"($value:num)" } ++
      Vector(
        Name -> SystemBody,
        Counted -> CountedBody,
        Potential -> PotentialBody,
        Marked -> MarkedBody,
        TailFree -> TailFreeBody,
        HeadFree -> HeadFreeBody,
        Anchored -> AnchoredBody,
        Run -> RunBody,
        RunCounted -> RunCountedBody
      )

  /** Every statement this development publishes, as text. */
  val Statements: Vector[(String, String)] = Vector(
    CountedIsRule -> "!l:word(num). !r:word(num). S2_COUNTED l r ==> S2 l r",
    Inhabited -> "?l:word(num). ?r:word(num). S2 l r",
    Refused ->
      ("~(S2 (WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (S2_HEAD:num)))"),
    TailFreeConcat ->
      ("!u:word(num). !v:word(num). S2_TAILFREE (WORD_CONCAT u v) = " +
        "(S2_TAILFREE u /\\ S2_TAILFREE v)"),
    MarkedConcat ->
      ("!u:word(num). !v:word(num). 0 < WORD_LENGTH v ==> " +
        "(S2_MARKED (WORD_CONCAT u v) = (S2_TAILFREE u /\\ S2_MARKED v))"),
    RuleNotEmpty ->
      ("!l:word(num). !r:word(num). S2 l r ==> " +
        "0 < WORD_LENGTH l /\\ 0 < WORD_LENGTH r"),
    MarkedStep -> "!l:word(num). !r:word(num). S2 l r /\\ S2_MARKED l ==> S2_MARKED r",
    TailFreeStep -> "!l:word(num). !r:word(num). S2 l r /\\ S2_TAILFREE l ==> S2_TAILFREE r",
    HeadFreeConcat ->
      ("!u:word(num). !v:word(num). S2_HEADFREE (WORD_CONCAT u v) = " +
        "(S2_HEADFREE u /\\ S2_HEADFREE v)"),
    AnchoredConcat ->
      ("!u:word(num). !v:word(num). 0 < WORD_LENGTH u ==> " +
        "(S2_ANCHORED (WORD_CONCAT u v) = (S2_ANCHORED u /\\ S2_HEADFREE v))"),
    HeadFreeStep -> "!l:word(num). !r:word(num). S2 l r /\\ S2_HEADFREE l ==> S2_HEADFREE r",
    AnchoredStep -> "!l:word(num). !r:word(num). S2 l r /\\ S2_ANCHORED l ==> S2_ANCHORED r",
    AnchoredClosed ->
      "!u:word(num). !v:word(num). S2_ANCHORED u /\\ WORD_STEP S2 u v ==> S2_ANCHORED v",
    MarkedClosed ->
      "!u:word(num). !v:word(num). S2_MARKED u /\\ WORD_STEP S2 u v ==> S2_MARKED v",
    MarkedInhabited -> s"S2_MARKED (${wordText(spell("/0."))})",
    AnchoredInhabited -> s"S2_ANCHORED (${wordText(spell("/0."))})",
    PotentialAtAWord -> s"S2_PHI (${wordText(spell("/00."))}) = SUC ZERO",
    PotentialBlocks ->
      ("!x:word(num). !m:word(num). !y:word(num). " +
        "S2_PHI (WORD_CONCAT (WORD_CONCAT x m) y) = " +
        "NUM_ADD (NUM_ADD (S2_PHI x) " +
        "(NUM_SUM (\\i:num. COND (WORD_NTH m i < 3) " +
        "(NUM_SUB (NUM_ADD (WORD_LENGTH x) i) 1) 0) (WORD_LENGTH m))) " +
        "(NUM_SUM (\\i:num. COND (WORD_NTH y i < 3) " +
        "(NUM_SUB (NUM_ADD (WORD_LENGTH (WORD_CONCAT x m)) i) 1) 0) (WORD_LENGTH y))"),
    PotentialCountedStep ->
      ("!u:word(num). !v:word(num). S2_ANCHORED u /\\ WORD_STEP S2_COUNTED u v ==> " +
        "S2_PHI u = SUC (S2_PHI v)"),
    PotentialPlainStep ->
      ("!u:word(num). !v:word(num). " +
        "S2_ANCHORED u /\\ S2_MARKED u /\\ WORD_STEP S2 u v /\\ " +
        "~(WORD_STEP S2_COUNTED u v) ==> NUM_LE (S2_PHI u) (S2_PHI v)"),
    PotentialConcat ->
      ("!u:word(num). !v:word(num). S2_PHI (WORD_CONCAT u v) = " +
        "NUM_ADD (S2_PHI u) " +
        "(NUM_SUM (\\i:num. COND (WORD_NTH v i < 3) " +
        "(NUM_SUB (NUM_ADD (WORD_LENGTH u) i) 1) 0) (WORD_LENGTH v))"),
    StepInhabited ->
      s"WORD_STEP S2 (${wordText(spell("/0."))}) (${wordText(spell("/t."))})",
    ZerosAtZero -> s"$Zeros ZERO = (WORD_EMPTY:word(num))",
    ZerosAtSuccessor ->
      s"!n:num. $Zeros (SUC n) = WORD_CONCAT ($Zeros n) (${singletonText("0")})",
    ClosureRefused -> "~(WORD_RFC S2 (WORD_EMPTY:word(num)))",
    FamilyWithF -> s"!i:num. WORD_RFC S2 (${familyText("i", F)})",
    FamilyWithTail -> s"!i:num. WORD_RFC S2 (${familyText("(SUC i)", Tail)})",
    RunPotential ->
      ("!x:word(num). !q:prod(word(num), num). " +
        "REACH S2_RUN S2_RUN_COUNTED x q ==> " +
        "NUM_LE (S2_PHI x) (NUM_ADD (SND q) (S2_PHI (FST q)))"),
    // Spelled from `spell` rather than from `BeforeTheStep`, which is declared below this vector:
    // a `val` of an object reading a `val` declared after it reads `null`, and the neighbours above
    // are written this way for the same reason.
    RunInhabited ->
      s"S2_RUN (${wordText(spell("/0."))}) (${wordText(spell("/t."))})",
    ZerosLength -> s"!j:num. WORD_LENGTH ($Zeros j) = j",
    StemLength ->
      s"!j:num. WORD_LENGTH (WORD_CONCAT (${wordText(spell("/f"))}) ($Zeros j)) = SUC (SUC j)",
    PotentialOfStem ->
      s"!j:num. S2_PHI (WORD_CONCAT (${wordText(spell("/f"))}) ($Zeros j)) = NUM_TRI j",
    PotentialOfFamily -> s"!j:num. S2_PHI (${familyText("j", Tail)}) = NUM_TRI j",
    FamilyBounded ->
      ("!j:num. !q:prod(word(num), num). " +
        s"REACH S2_RUN S2_RUN_COUNTED (${familyText("j", Tail)}) q ==> " +
        "NUM_LE (NUM_TRI j) (NUM_ADD (SND q) (S2_PHI (FST q)))"),
    FamilyAtOne -> s"S2_PHI (${wordText(spell("/f0."))}) = SUC ZERO"
  )

  /* ------------------------------------------------------------------ construction */

  /**
   * The development, built over [[Forward]] so that a claim about `WORD_RFC S2` is typable.
   *
   * Every constant here is a definition and none of them is an axiom. There is no count in this
   * sentence on purpose: it said nine for as long as there were nine and was wrong the day the
   * anchored class landed, and `CollatzSpec` asserts the whole set name for name, which is the
   * check a number here would only look like. The four letters are defined before the rules that
   * name them,
   * which is why [[Bodies]] is a vector rather than a map: a constant is reachable only from the
   * theory it was declared into, so the order is the construction and not a presentation choice.
   */
  def construct(
    forward: Forward,
    folding: Folding,
    reaching: Reaching,
    numbering: Numbering,
    naturals: Natural,
    peano: Peano,
    successor: Successor,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Collatz] = {
    val introduced = Bodies.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](
      Right((base, Map.empty))
    ) { (accumulated, entry) =>
      val (name, text) = entry
      for {
        state <- accumulated
        (theory, defined) = state
        body <- Parser.term(theory, notation, text)
        introduced <- LogicError.lift(Kernel.defineConstant(theory, name, body))
        (extended, definition) = introduced
      } yield (extended, defined + (name -> definition))
    }

    for {
      state <- introduced
      (declared, letters) = state

      // `S2_ZEROS` is introduced here and not in `Bodies` because it is a recursion and the nine
      // above are plain definitions: what `Recursion.define` hands back is the constant together
      // with its two equations, and those two equations are what both proofs of the family run on.
      recursion <- naturals.recursion
      zeros <- Recursion.define(
        forward.logic,
        naturals,
        declared,
        notation,
        recursion,
        Zeros,
        Words,
        "(WORD_EMPTY:word(num))",
        s"\\v:word(num). \\i:num. WORD_CONCAT v (${singletonText("0")})",
        None
      )
      (theory, zerosDefinition, zerosAtZero, zerosAtSuccessor) = zeros
      definitions = letters + (Zeros -> zerosDefinition)

      logic <- forward.inductive.classical.logic.over(theory)

      tailFreeByPosition <- byPosition(
        logic, forward.inductive.classical, folding, theory, notation,
        definitions, TailFree, Tail, TailFreeByPosition)
      headFreeByPosition <- byPosition(
        logic, forward.inductive.classical, folding, theory, notation,
        definitions, HeadFree, Head, HeadFreeByPosition)
      // What the proofs below read the two predicates by. The published definitions stay the
      // kernel's own, which are the folds.
      positional = definitions ++ Map(TailFree -> tailFreeByPosition, HeadFree -> headFreeByPosition)

      countedIsRule <- countedAreRules(logic, theory, notation, positional)
      inhabited <- inhabitedProof(logic, theory, notation, positional)
      refused <- refusal(
        logic, naturals, forward.concatenation, peano, theory, notation, positional)

      numbers <- Arithmetic.of(peano, naturals)
      tailFreeDefinition <- positional.get(TailFree).toRight(MissingDefinition(TailFree))
      markedDefinition <- positional.get(Marked).toRight(MissingDefinition(Marked))
      headFreeDefinition <- positional.get(HeadFree).toRight(MissingDefinition(HeadFree))
      anchoredDefinition <- positional.get(Anchored).toRight(MissingDefinition(Anchored))
      tailFreeConcat <- listSplits(
        logic, folding, theory, notation, definitions, TailFree, Tail, TailFreeConcat)
      headFreeConcat <- listSplits(
        logic, folding, theory, notation, definitions, HeadFree, Head, HeadFreeConcat)
      potentialDefinition <- positional.get(Potential).toRight(MissingDefinition(Potential))
      potentialConcat <- potentialSplits(
        logic, theory, notation, forward.concatenation, potentialDefinition)
      potentialBlocks <- potentialOfBlocks(logic, theory, potentialConcat)
      anchoredConcat <- anchoredSplits(
        logic,
        theory,
        forward.inductive.classical,
        forward.concatenation,
        numbers,
        headFreeDefinition,
        anchoredDefinition
      )
      markedConcat <- markedSplits(
        logic,
        theory,
        forward.inductive.classical,
        forward.concatenation,
        numbers,
        tailFreeDefinition,
        markedDefinition
      )

      tools <- concreteTools(
        logic, theory, notation, forward.concatenation, peano, naturals, successor, numbers, positional)
      // `COND` is polymorphic in the branches, so both rules arrive with a type variable where this
      // development has `num`, and a specialisation at a numeral would be refused for it.
      conditional <- forward.inductive.classical.fact(Classical.CondTrue).map(atNumbers)
      conditionalFalse <- forward.inductive.classical.fact(Classical.CondFalse).map(atNumbers)
      potentialAtAWord <- potentialOfWord(
        tools, spell("/00."), positional, conditional, conditionalFalse)
      ruleNotEmpty <- rulesAreNotEmpty(tools, positional)
      markedStep <- markedRules(tools, positional)
      tailFreeStep <- freeRules(tools, positional, Tail, TailFree, TailFreeStep)
      headFreeStep <- freeRules(tools, positional, Head, HeadFree, HeadFreeStep)
      anchoredStep <- anchoredRules(tools, positional)

      partial = Map(
        CountedIsRule -> countedIsRule,
        Inhabited -> inhabited,
        Refused -> refused,
        TailFreeConcat -> tailFreeConcat,
        MarkedConcat -> markedConcat,
        RuleNotEmpty -> ruleNotEmpty,
        MarkedStep -> markedStep,
        TailFreeStep -> tailFreeStep,
        HeadFreeConcat -> headFreeConcat,
        AnchoredConcat -> anchoredConcat,
        HeadFreeStep -> headFreeStep,
        AnchoredStep -> anchoredStep,
        PotentialBlocks -> potentialBlocks,
        PotentialConcat -> potentialConcat,
        PotentialAtAWord -> potentialAtAWord
      )
      potentialCountedStep <- potentialAcrossCounted(
        tools, forward, forward.concatenation, positional, partial, conditional, conditionalFalse)
      potentialPlainStep <- potentialAcrossPlain(
        tools,
        forward,
        forward.concatenation,
        forward.inductive.classical,
        positional,
        partial,
        conditional,
        conditionalFalse
      )
      markedClosed <- closedUnderSteps(tools, forward, forward.concatenation, positional, partial)
      anchoredClosed <- anchoredUnderSteps(tools, forward, forward.concatenation, positional, partial)
      markedInhabited <- markedWord(tools, BeforeTheStep)
      anchoredInhabited <- anchoredWord(tools, BeforeTheStep)
      stepInhabited <- stepHolds(tools, forward.concatenation, forward, positional)
      family <- digitFamily(
        tools, forward, naturals, positional, zerosAtZero, zerosAtSuccessor)
      (familyWithF, familyWithTail) = family
      closureRefused <- closureIsProper(tools, forward, ruleNotEmpty)
      familySizes <- familyLengths(
        tools, naturals, forward.concatenation, zerosAtZero, zerosAtSuccessor)
      (zerosLength, stemLength) = familySizes
      inClass = partial ++ Map(
        PotentialCountedStep -> potentialCountedStep,
        PotentialPlainStep -> potentialPlainStep,
        MarkedInhabited -> markedInhabited,
        AnchoredInhabited -> anchoredInhabited,
        StepInhabited -> stepInhabited
      )
      runPotentialFact <- runPotential(tools, reaching, positional, inClass)
      runInhabited <- runHolds(tools, positional, inClass)
      stemPotential <- potentialOfStem(
        tools,
        naturals,
        numbering,
        forward.concatenation,
        positional,
        inClass,
        zerosAtZero,
        zerosAtSuccessor,
        stemLength,
        conditional,
        conditionalFalse
      )
      quadratic <- familyBounded(
        tools,
        numbering,
        forward.concatenation,
        inClass ++ Map(RunPotential -> runPotentialFact),
        stemPotential,
        zerosAtZero,
        zerosAtSuccessor,
        conditional,
        conditionalFalse
      )
      (familyPotential, familyAtOne, familyBound) = quadratic
      facts = partial ++ Map(
        PotentialCountedStep -> potentialCountedStep,
        PotentialPlainStep -> potentialPlainStep,
        MarkedClosed -> markedClosed,
        AnchoredClosed -> anchoredClosed,
        MarkedInhabited -> markedInhabited,
        AnchoredInhabited -> anchoredInhabited,
        StepInhabited -> stepInhabited,
        ZerosAtZero -> zerosAtZero,
        ZerosAtSuccessor -> zerosAtSuccessor,
        FamilyWithF -> familyWithF,
        FamilyWithTail -> familyWithTail,
        ClosureRefused -> closureRefused,
        RunPotential -> runPotentialFact,
        RunInhabited -> runInhabited,
        ZerosLength -> zerosLength,
        StemLength -> stemLength,
        PotentialOfStem -> stemPotential,
        PotentialOfFamily -> familyPotential,
        FamilyAtOne -> familyAtOne,
        FamilyBounded -> familyBound
      )

      // Every statement checked against the text a reader reads it by, here rather than in the
      // spec, which is what `Concatenation.construct` does and for the same reason: a development
      // that built something other than what it says it built must not be handed out.
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { (accumulated, entry) =>
        val (name, text) = entry
        for {
          _ <- accumulated
          expected <- Parser.proposition(theory, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Collatz(forward, theory, notation, definitions, facts, tools)
  }

  /* ------------------------------------------------------------------ the arithmetic */

  /**
   * The facts about `num` the proofs below reach for, fetched once instead of threaded one by one.
   *
   * A record rather than a dozen parameters, which is what `Concatenation` does for the same reason
   * and for a set that overlaps this one: a proof about positions in a concatenation is an argument
   * about sums, differences and an order, and the word part of it is three lemmas.
   */
  private[theories] final case class Arithmetic(
    atMostSum: Kernel.Thm,
    belowThenAtMost: Kernel.Thm,
    addStrictlyMonotone: Kernel.Thm,
    addCancelsStrictOrder: Kernel.Thm,
    atMostFromNotBelow: Kernel.Thm,
    minusThenPlus: Kernel.Thm,
    addCommutative: Kernel.Thm,
    addAtSuccessor: Kernel.Thm,
    subAtZero: Kernel.Thm,
    zeroMinus: Kernel.Thm,
    subSuccessors: Kernel.Thm,
    oneIsSuccessorOfZero: Kernel.Thm,
    successorPositive: Kernel.Thm,
    belowSuccessor: Kernel.Thm,
    notBelowZero: Kernel.Thm,
    belowSuccessorCases: Kernel.Thm,
    strictTransitive: Kernel.Thm,
    zeroOrSuccessor: Kernel.Thm,
    sumAtZero: Kernel.Thm,
    sumAtSuccessor: Kernel.Thm,
    atMostFromBelow: Kernel.Thm,
    belowExcludesAtMost: Kernel.Thm,
    strictIrreflexive: Kernel.Thm,
    addAtZero: Kernel.Thm,
    zeroPlus: Kernel.Thm,
    successorPlus: Kernel.Thm,
    reflexive: Kernel.Thm,
    atMostSuccessor: Kernel.Thm,
    addMonotone: Kernel.Thm,
    sumMonotoneBelow: Kernel.Thm,
    strictDefinition: Kernel.Thm
  )

  private[theories] object Arithmetic {

    def of(peano: Peano, naturals: Natural): Either[LogicError, Arithmetic] =
      for {
        atMostSum <- peano.fact(Peano.AtMostSum)
        belowThenAtMost <- peano.fact(Peano.BelowThenAtMost)
        addStrictlyMonotone <- peano.fact(Peano.AddStrictlyMonotone)
        addCancelsStrictOrder <- peano.fact(Peano.AddCancelsStrictOrder)
        atMostFromNotBelow <- peano.fact(Peano.AtMostFromNotBelow)
        minusThenPlus <- peano.fact(Peano.MinusThenPlus)
        addCommutative <- peano.fact(Peano.AddCommutative)
        addAtSuccessor <- peano.fact(Peano.AddAtSuccessor)
        subAtZero <- peano.fact(Peano.SubAtZero)
        zeroMinus <- peano.fact(Peano.ZeroMinus)
        subSuccessors <- peano.fact(Peano.SubSuccessors)
        oneIsSuccessorOfZero <- peano.fact(Peano.NumeralOneIsSuccessorOfZero)
        successorPositive <- peano.fact(Peano.SuccessorPositive)
        belowSuccessor <- peano.fact(Peano.BelowSuccessor)
        notBelowZero <- peano.fact(Peano.NotBelowZero)
        belowSuccessorCases <- peano.fact(Peano.BelowSuccessorCases)
        strictTransitive <- peano.fact(Peano.StrictTransitive)
        zeroOrSuccessor <- naturals.fact(Natural.ZeroOrSuccessor)
        sumAtZero <- peano.fact(Peano.PartialSumAtZero)
        sumAtSuccessor <- peano.fact(Peano.PartialSumAtSuccessor)
        atMostFromBelow <- peano.fact(Peano.AtMostFromBelow)
        belowExcludesAtMost <- peano.fact(Peano.BelowExcludesAtMost)
        strictIrreflexive <- peano.fact(Peano.StrictIrreflexive)
        addAtZero <- peano.fact(Peano.AddAtZero)
        zeroPlus <- peano.fact(Peano.ZeroPlus)
        successorPlus <- peano.fact(Peano.SuccessorPlus)
        reflexive <- peano.fact(Peano.Reflexive)
        atMostSuccessor <- peano.fact(Peano.AtMostSuccessor)
        addMonotone <- peano.fact(Peano.AddMonotone)
        sumMonotoneBelow <- peano.fact(Peano.PartialSumMonotoneBelow)
        strictDefinition <- peano.definition(Peano.StrictOrder)
      } yield Arithmetic(
        atMostSum,
        belowThenAtMost,
        addStrictlyMonotone,
        addCancelsStrictOrder,
        atMostFromNotBelow,
        minusThenPlus,
        addCommutative,
        addAtSuccessor,
        subAtZero,
        zeroMinus,
        subSuccessors,
        oneIsSuccessorOfZero,
        successorPositive,
        belowSuccessor,
        notBelowZero,
        belowSuccessorCases,
        strictTransitive,
        zeroOrSuccessor,
        sumAtZero,
        sumAtSuccessor,
        atMostFromBelow,
        belowExcludesAtMost,
        strictIrreflexive,
        addAtZero,
        zeroPlus,
        successorPlus,
        reflexive,
        atMostSuccessor,
        addMonotone,
        sumMonotoneBelow,
        strictDefinition
      )
  }

  /* ------------------------------------------------------------------ the plumbing */

  /**
   * A polymorphic lemma of the word, read at the one type this development has words of.
   *
   * `Concatenation` is about `word('a)` and everything here is about `word(num)`, so every lemma
   * borrowed from it is instantiated on the way in. Done once, at the point the fact is fetched,
   * rather than at each `specAll`: an uninstantiated lemma specialised at a word of numbers is a
   * refusal naming the two types, and the refusal names the argument rather than the lemma.
   */
  private def atNumbers(theorem: Kernel.Thm): Kernel.Thm =
    Kernel.instType(Map(Classical.TypeVariable -> Numbers), theorem)

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))

  /** `|- R b c` from `|- b = a` and `|- R a c`: the relation's FIRST argument replaced. */
  private def carryLeft(
    relation: Term,
    equation: Kernel.Thm,
    other: Term,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      reversed <- Conv.sym(equation)
      moved <- Conv.apTerm(relation, reversed).flatMap(Conv.apThm(_, other))
      result <- LogicError.lift(Kernel.eqMp(moved, fact))
    } yield result

  /** `|- R i b` from `|- a = b` and `|- R i a`: the relation's SECOND argument replaced. */
  private def carryRight(
    relation: Term,
    left: Term,
    equation: Kernel.Thm,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- LogicError.lift(Term.app(relation, left))
      moved <- Conv.apTerm(partial, equation)
      result <- LogicError.lift(Kernel.eqMp(moved, fact))
    } yield result

  /** The `=` of a type, recovered from an equation built at it rather than named. */
  private def equalityAt(sample: Term, other: Term): Either[LogicError, Term] =
    LogicError.lift(Term.eq(sample, other)).flatMap {
      case App(App(equality, _), _) => Right(equality)
      case built => Left(NotOfForm("an equation", built))
    }

  /** `|- ~(b = c)` from `|- a = b` and `|- ~(a = c)`. */
  private def carryLeftNegated(
    logic: Logic,
    equation: Kernel.Thm,
    other: Term,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      sides <- Term.destEq(equation.conclusion).toRight(NotOfForm("an equation", equation.conclusion))
      equality <- equalityAt(sides._1, other)
      moved <- Conv.apTerm(equality, equation).flatMap(Conv.apThm(_, other))
      negated <- Conv.apTerm(logic.negation, moved)
      result <- LogicError.lift(Kernel.eqMp(negated, fact))
    } yield result

  /**
   * `|- !i. i < b ==> c`, from a proof of `c` under the assumption `i < b`.
   *
   * The binder, the guard and the consequent are read out of the statement the caller asks for
   * rather than rebuilt, and what the step returns is checked against the consequent before it is
   * discharged. A step that proved something else would otherwise be generalised into a theorem
   * that is true and is not the claim, which is the failure `Bounded.prove` ends with the same
   * check against.
   */
  private def underTheBound(
    logic: Logic,
    statement: Term
  )(
    step: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      predicate <- logic
        .destForallPredicate(statement)
        .toRight(NotOfForm("a claim about every index", statement))
      domain <- Type
        .destFun(Term.typeOf(predicate))
        .map(_._1)
        .toRight(NotOfForm("a predicate", predicate))
      index = Conv.freshVariable("i", domain, Term.freeVariables(statement))
      applied <- LogicError.lift(Term.app(predicate, index))
      body <- Conv.betaRoot(applied).flatMap(rightOf)
      parts <- logic.destImp(body).toRight(NotOfForm("an implication under the quantifier", body))
      (guard, consequent) = parts
      assumed <- LogicError.lift(Kernel.assume(guard))
      proved <- step(index, assumed)
      _ <-
        if (proved.conclusion == consequent) Right(())
        else Left(NotOfForm("the claim at this index as it is written", proved.conclusion))
      result <- rules.disch(guard, proved).flatMap(rules.gen(index, _))
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm("the bounded claim as it is written", result.conclusion))
    } yield result
  }

  /* ------------------------------------------------------------------ the marked class */

  /**
   * [[TailFreeConcat]] and [[HeadFreeConcat]]: freedom from a marker splits over a concatenation.
   *
   * By the lists since 2026-09-25, and that is the whole of the proof: the predicate is a fold of
   * conjunctions, `Folding.FoldOfEveryConcat` is the split of such a fold, and the definition read
   * backwards puts the predicate's name on each of the three folds. The version it replaces read
   * every index of `u v` through `WORD_CONCAT_NTH_LEFT` and `WORD_CONCAT_NTH_RIGHT` with an
   * excluded middle on `i < |u|` and the difference placed by `NUM_SUB_ADD`, and it was 150 lines.
   */
  private def listSplits(
    logic: Logic,
    folding: Folding,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm],
    name: String,
    markerName: String,
    statement: String
  ): Either[LogicError, Kernel.Thm] =
    for {
      definition <- definitions.get(name).toRight(MissingDefinition(name))
      split <- folding.fact(Folding.FoldOfEveryConcat).map(atNumbers)
      predicate <- Parser.term(theory, notation, s"\\x:num. ~(x = $markerName)")
      specialised <- logic.rules.spec(predicate, split)
      reduced <- Conv.betaNormalise(specialised.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, specialised)))
      named <- Conv.sym(definition).flatMap(back => Rewrite.Rule.all(logic, Vector(back)))
      result <- Rewrite.inTheorem(named, reduced)
      expected <- Parser.proposition(theory, notation, Statements.toMap.apply(statement))
      _ <- if (result.conclusion == expected) Right(())
           else Left(NotOfForm(s"$statement as it is written", result.conclusion))
    } yield result

  /**
   * `|- S2_TAILFREE = \w. !i. i < WORD_LENGTH w ==> ~(WORD_NTH w i = S2_TAIL)`, and the same at the
   * head marker: the definition these predicates had until 2026-09-25, derived now from the fold.
   *
   * `Folding.FoldOfEvery` at the predicate "is not the marker" gives the equation at every word, and
   * eta turns an equation at every word into one between the two functions. What comes out is
   * handed to the proofs of this file under the definition's name, so that none of them changed
   * when the predicate did; the kernel's definition, the fold, is what the development publishes.
   */
  private def byPosition(
    logic: Logic,
    classical: Classical,
    folding: Folding,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm],
    name: String,
    markerName: String,
    positionalText: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      definition <- definitions.get(name).toRight(MissingDefinition(name))
      every <- folding.fact(Folding.FoldOfEvery).map(atNumbers)
      predicate <- Parser.term(theory, notation, s"\\x:num. ~(x = $markerName)")
      specialised <- rules.spec(predicate, every)
      reduced <- Conv.betaNormalise(specialised.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, specialised)))
      word <- Parser.term(theory, notation, "w:word(num)").flatMap {
        case variable: FVar => Right(variable)
        case other => Left(NotOfForm("a variable", other))
      }
      atWord <- rules.spec(word, reduced)
      opened <- Conv.apThm(definition, word)
      positional <- Parser.term(theory, notation, positionalText)
      applied <- LogicError.lift(Term.app(positional, word))
      contracted <- Conv.betaRoot(applied).flatMap(Conv.sym)
      pointwise <- Conv.trans(opened, atWord).flatMap(Conv.trans(_, contracted))
      general <- rules.gen(word, pointwise)
      result <- classical.ext(logic, general)
      constant <- leftOf(definition)
      expected <- LogicError.lift(Term.eq(constant, positional))
      _ <- if (result.conclusion == expected) Right(())
           else Left(NotOfForm(s"$name read by position", result.conclusion))
    } yield result
  }
  /**
   * `|- WORD_NTH w (NUM_SUB k 1) = WORD_NTH w j` where `|- k = SUC j`: the last position, placed.
   *
   * Truncated subtraction is why this is a lemma of its own rather than a step: `k - 1` is not `j`
   * for a `k` nothing says is positive, and every statement about a marked word reads its last
   * letter at `|w| - 1`. Written `SUC j` the arithmetic is three rewrites and no side condition,
   * which is the whole reason the caller obtains a successor from `NUM_CASES` first.
   */
  private def lastPosition(
    logic: Logic,
    theory: Theory,
    numbers: Arithmetic,
    size: Kernel.Thm,
    predecessor: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      minus <- LogicError.lift(theory.constant(Peano.Subtraction, BinaryNumbers))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(Numbers, Numbers))
      )
      one <- leftOf(numbers.oneIsSuccessorOfZero)
      spelled <- LogicError.lift(Term.app(successor, predecessor))

      atSuccessor <- Conv.apTerm(minus, size).flatMap(Conv.apThm(_, one))
      partial <- LogicError.lift(Term.app(minus, spelled))
      unfolded <- Conv.apTerm(partial, numbers.oneIsSuccessorOfZero)
      peeled <- rules.specAll(numbers.subSuccessors, List(predecessor, zero))
      collapsed <- rules.spec(predecessor, numbers.subAtZero)
      result <- Conv
        .trans(atSuccessor, unfolded)
        .flatMap(Conv.trans(_, peeled))
        .flatMap(Conv.trans(_, collapsed))
    } yield result
  }

  /**
   * [[MarkedConcat]]: a marked word is a tail-free block and a marked block, and the tail is where
   * the marker is.
   *
   * Everything here runs at `|v| = SUC k`, obtained from `NUM_CASES` against the hypothesis, and
   * that is the decision worth knowing before reading it: the two positions the statement is about
   * are `|v| - 1` and `|u v| - 1`, and over a truncated subtraction neither is anything until the
   * length is known to be a successor. Written `SUC k` they are `k` and `|u| + k`, and the two
   * entry lemmas of `Concatenation` meet at exactly that pair, `WORD_CONCAT_NTH_RIGHT` being
   * already stated at a shifted index.
   *
   * The zero case is not an awkward corner, it is the statement being false there: `WORD_CONCAT u
   * WORD_EMPTY` is `u`, so the left-hand side would be `S2_MARKED u` and the right-hand side would
   * ask `S2_MARKED WORD_EMPTY`, which has no last letter. The hypothesis is what the proof spends
   * to close that branch, and it spends it against `NUM_NOT_LT_ZERO` rather than by a case split.
   */
  private def markedSplits(
    logic: Logic,
    theory: Theory,
    classical: Classical,
    concatenation: Concatenation,
    numbers: Arithmetic,
    tailFreeDefinition: Kernel.Thm,
    markedDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val v = Term.variable("v", Words)

    for {
      length <- concatenation.fact(Concatenation.Length).map(atNumbers)
      nthLeft <- concatenation.fact(Concatenation.NthLeft).map(atNumbers)
      nthRight <- concatenation.fact(Concatenation.NthRight).map(atNumbers)

      concatConstant <- LogicError.lift(theory.constant(Concatenation.Name, ConcatType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, LengthType))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, NthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, OrderType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, BinaryNumbers))
      minus <- LogicError.lift(theory.constant(Peano.Subtraction, BinaryNumbers))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      marker <- LogicError.lift(theory.constant(Tail, Numbers))

      joined <- LogicError.lift(Term.appAll(concatConstant, List(u, v)))
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))
      nthOfV <- LogicError.lift(Term.app(nthConstant, v))
      sizeU <- LogicError.lift(Term.app(lengthConstant, u))
      sizeV <- LogicError.lift(Term.app(lengthConstant, v))
      total <- LogicError.lift(Term.appAll(plus, List(sizeU, sizeV)))
      lengths <- rules.specAll(length, List(u, v))

      positiveTerm <- LogicError.lift(Term.appAll(strictOrder, List(zero, sizeV)))
      positive <- LogicError.lift(Kernel.assume(positiveTerm))

      openedJoined <- Conv.unfold(markedDefinition, List(joined))
      openedV <- Conv.unfold(markedDefinition, List(v))
      openedU <- Conv.unfold(tailFreeDefinition, List(u))
      claimJoined <- leftOf(openedJoined)
      claimV <- leftOf(openedV)
      claimU <- leftOf(openedU)
      both <- logic.mkConj(claimU, claimV)
      equation <- LogicError.lift(Term.eq(claimJoined, both))

      /* the length is a successor, or the hypothesis is false */
      cases <- rules.spec(sizeV, numbers.zeroOrSuccessor)
      emptyBranch <- {
        for {
          disjuncts <- logic
            .destDisj(cases.conclusion)
            .toRight(NotOfForm("a disjunction", cases.conclusion))
          (isZero, _) = disjuncts
          assumed <- LogicError.lift(Kernel.assume(isZero))
          carried <- carryRight(strictOrder, zero, assumed, positive)
          nothing <- rules.spec(zero, numbers.notBelowZero)
          absurd <- rules.notElim(nothing, carried)
          result <- rules.falsityElim(equation, absurd)
        } yield result
      }

      successorBranch <- {
        val predecessor = Conv.freshVariable(
          "k",
          Numbers,
          Term.freeVariables(equation) ++ Term.freeVariables(sizeV)
        )

        for {
          disjuncts <- logic
            .destDisj(cases.conclusion)
            .toRight(NotOfForm("a disjunction", cases.conclusion))
          (_, isSuccessor) = disjuncts
          existential <- LogicError.lift(Kernel.assume(isSuccessor))
          predicate <- logic
            .destExistsPredicate(isSuccessor)
            .toRight(NotOfForm("an existential", isSuccessor))
          applied <- LogicError.lift(Term.app(predicate, predecessor))
          instance <- Conv.betaRoot(applied).flatMap(rightOf)
          size <- LogicError.lift(Kernel.assume(instance))

          proved <- markedSplitsAtSuccessor(
            logic,
            theory,
            classical,
            numbers,
            Split(u, v, nthOfJoined, nthOfV, sizeU, sizeV, total, predecessor),
            (strictOrder, plus, minus, marker),
            (lengths, nthLeft, nthRight),
            (openedJoined, openedV, openedU),
            (positive, size)
          )
          result <- rules.existsElim(existential, predecessor, proved)
        } yield result
      }

      settled <- rules.disjElim(cases, emptyBranch, successorBranch)
      discharged <- rules.disch(positiveTerm, settled)
      result <- rules.genAll(discharged, List(u, v))
    } yield result
  }

  /**
   * `|- <letter> < 3` or `|- ~(<letter> < 3)`, which is what decides a position's weight.
   *
   * The alphabet is seven numerals and the digits are the three below three, so this is a
   * comparison of numerals and nothing about words. It runs in successor form: the letters and the
   * bound are written in the bit encoding, where `<` has no decision procedure here, and
   * `Successor.spell` is what puts both sides where [[numeralBelow]] can compare them.
   *
   * The refusal is derived rather than assumed for the same reason [[notTheMarker]] is: at a letter
   * that IS a digit, a caller asking for the negative answer would otherwise get a theorem about
   * nothing, and here it gets a refusal naming the letter.
   */
  private def belowThree(
    tools: Concrete,
    letter: String,
    wanted: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules
    val digits = Set("0", "1", "2")

    // Two refusals with a literal each, rather than one whose prose is built from the flag.
    // `NotationBoundarySpec` has two tables about a description: one for every expression a refusal
    // interpolates, and one for a description that is neither a literal nor an interpolation. A
    // boolean belongs to neither reading, and the message also read badly, ending "is false" where
    // what the caller needs to be told is which of the two answers it asked for. A literal is in
    // no table at all, which is what makes this the repair and a row the workaround.
    if (digits.contains(letter) != wanted)
      if (wanted)
        Left(
          NotOfForm(
            "a digit, which a comparison below three asks for",
            Term.variable(letter, Numbers)
          ))
      else
        Left(
          NotOfForm(
            "a letter that is not a digit, which a comparison above three asks for",
            Term.variable(letter, Numbers)
          ))
    else
      for {
        letterTerm <- tools.letter(letter)
        boundTerm <- Parser.term(tools.theory, tools.notation, "(3:num)", Numbers)
        letterValue <- Rewrite.rewrite(tools.letters, letterTerm)
        letterNumeral <- rightOf(letterValue)
        letterSpelt <- tools.successor.spell(letterNumeral).flatMap(Conv.trans(letterValue, _))
        boundSpelt <- tools.successor.spell(boundTerm)
        letterSuccessors <- rightOf(letterSpelt)
        boundSuccessors <- rightOf(boundSpelt)
        letterCount <- countOfSuccessors(tools, letterSuccessors)
        boundCount <- countOfSuccessors(tools, boundSuccessors)
        order <- tools.strictOrder

        answer <-
          if (wanted)
            for {
              small <- numeralBelow(tools, letterCount, boundCount)
              placed <- carryLeft(order, letterSpelt, boundSuccessors, small)
              result <- carryRight(order, letterTerm, Conv.sym(boundSpelt).getOrElse(boundSpelt), placed)
            } yield result
          else
            for {
              refused <- notNumeralBelow(tools, letterCount, boundCount)
              placed <- carryLeftNegatedOrder(tools, order, letterSpelt, boundSuccessors, refused)
              reversed <- Conv.sym(boundSpelt)
              result <- carryRightNegatedOrder(tools, order, letterTerm, reversed, placed)
            } yield result
      } yield answer
  }

  /** How many successors a numeral in successor form carries, read off the term. */
  private def countOfSuccessors(tools: Concrete, numeral: Term): Either[LogicError, Int] =
    for {
      zero <- tools.zero
      successor <- tools.successorOf
      count <- Bounded
        .lengthOf(zero, successor, numeral)
        .toRight(NotOfForm(s"a numeral of ${Natural.TypeName}", numeral))
    } yield count

  /** `|- ~(SUC^a ZERO < SUC^b ZERO)` for `a >= b`, which is the refusal [[numeralBelow]] has no form of. */
  private def notNumeralBelow(
    tools: Concrete,
    left: Int,
    right: Int
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      leftTerm <- tools.numeral(left)
      rightTerm <- tools.numeral(right)
      order <- tools.strictOrder
      claim <- LogicError.lift(Term.appAll(order, List(leftTerm, rightTerm)))
      assumed <- LogicError.lift(Kernel.assume(claim))
      absurd <-
        if (left == right)
          for {
            irreflexive <- rules.spec(leftTerm, tools.numbers.strictIrreflexive)
            contradiction <- rules.notElim(irreflexive, assumed)
          } yield contradiction
        else
          for {
            other <- numeralBelow(tools, right, left)
            excluded <- rules
              .specAll(tools.numbers.belowExcludesAtMost, List(rightTerm, leftTerm))
              .flatMap(rules.mp(_, other))
            weaker <- rules
              .specAll(tools.numbers.atMostFromBelow, List(leftTerm, rightTerm))
              .flatMap(rules.mp(_, assumed))
            contradiction <- rules.notElim(excluded, weaker)
          } yield contradiction
      result <- rules.notIntro(claim, absurd)
    } yield result
  }

  /** `|- ~(R a' b)` from `|- a = a'` and `|- ~(R a b)`: the order's FIRST argument replaced. */
  private def carryLeftNegatedOrder(
    tools: Concrete,
    order: Term,
    equation: Kernel.Thm,
    other: Term,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      reversed <- Conv.sym(equation)
      moved <- Conv.apTerm(order, reversed).flatMap(Conv.apThm(_, other))
      negated <- Conv.apTerm(tools.logic.negation, moved)
      result <- LogicError.lift(Kernel.eqMp(negated, fact))
    } yield result

  /** `|- ~(R a b')` from `|- b = b'` and `|- ~(R a b)`: the order's SECOND argument replaced. */
  private def carryRightNegatedOrder(
    tools: Concrete,
    order: Term,
    left: Term,
    equation: Kernel.Thm,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- LogicError.lift(Term.app(order, left))
      moved <- Conv.apTerm(partial, equation)
      negated <- Conv.apTerm(tools.logic.negation, moved)
      result <- LogicError.lift(Kernel.eqMp(negated, fact))
    } yield result

  /**
   * `|- f <numeral j> = <what the letter at j weighs>`, the summand of the measure at one position.
   *
   * Three steps and the middle one is the decision. The redex contracts to a conditional on whether
   * the letter at that position is a digit; the letter is read off the word and compared with three;
   * and `COND_TRUE` or `COND_FALSE` turns the answer into the branch. Nothing here simplifies the
   * branch it produces: at a digit what comes out is the distance as written, `(k + j) - 1` over a
   * truncated subtraction, and folding that into a numeral is the caller's arithmetic rather than
   * this function's.
   */
  private def summandAt(
    tools: Concrete,
    summand: Term,
    letters: Vector[String],
    position: Int,
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      index <- tools.numeral(position)
      applied <- LogicError.lift(Term.app(summand, index))
      contracted <- Conv.betaRoot(applied)
      body <- rightOf(contracted)
      parts <- body match {
        case App(App(App(_, condition), whenTrue), whenFalse) =>
          Right((condition, whenTrue, whenFalse))
        case other => Left(NotOfForm("a conditional", other))
      }
      (condition, whenTrue, whenFalse) = parts

      isDigit = Set("0", "1", "2").contains(letters(position))
      entry <- letterAt(tools, letters, position)
      order <- tools.strictOrder
      three <- Parser.term(tools.theory, tools.notation, "(3:num)", Numbers)

      decided <-
        if (isDigit)
          for {
            atLetter <- belowThree(tools, letters(position), wanted = true)
            held <- carryLeft(order, entry, three, atLetter)
            chosen <- rules
              .specAll(conditional, List(condition, whenTrue, whenFalse))
              .flatMap(rules.mp(_, held))
          } yield chosen
        else
          for {
            atLetter <- belowThree(tools, letters(position), wanted = false)
            held <- carryLeftNegatedOrder(tools, order, entry, three, atLetter)
            chosen <- rules
              .specAll(conditionalFalse, List(condition, whenTrue, whenFalse))
              .flatMap(rules.mp(_, held))
          } yield chosen
      result <- Conv.trans(contracted, decided)
    } yield result
  }

  /**
   * `|- NUM_SUM f (WORD_LENGTH <word>) = <value>`, the sum unfolded one position at a time.
   *
   * The summand is the caller's rather than one built here, because the term a caller has is the one
   * `S2_PHI_CONCAT` or the definition handed it and a summand written again would be the same
   * function twice. The bound is a concrete word's length, so it is a numeral in successor form and
   * `NUM_SUM_SUC` applies to it exactly that many times.
   *
   * What comes out is left-nested with `ZERO` at its foot, which is the recursion's own shape; the
   * two identities of addition fold the zeros away at the end, and every position whose letter is
   * not a digit contributed one.
   */
  private def sumOverPositions(
    tools: Concrete,
    summand: Term,
    letters: Vector[String],
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    def walk(position: Int): Either[LogicError, Kernel.Thm] =
      if (position == 0) rules.spec(summand, tools.numbers.sumAtZero)
      else
        for {
          below <- walk(position - 1)
          index <- tools.numeral(position - 1)
          step <- rules
            .spec(summand, tools.numbers.sumAtSuccessor)
            .flatMap(rules.spec(index, _))
          entry <- summandAt(tools, summand, letters, position - 1, conditional, conditionalFalse)
          plus <- LogicError.lift(
            tools.theory.constant(Peano.Addition, BinaryNumbers)
          )
          value <- rightOf(below)
          onTheLeft <- Conv
            .apTerm(plus, below)
            .flatMap(Conv.apThm(_, entry.conclusion match {
              case App(App(_, left), _) => left
              case other => other
            }))
          partial <- LogicError.lift(Term.app(plus, value))
          onTheRight <- Conv.apTerm(partial, entry)
          joined <- Conv.trans(onTheLeft, onTheRight)
          result <- Conv.trans(step, joined)
        } yield result

    for {
      length <- lengthIsNumeral(tools, letters)
      sumConstant <- LogicError.lift(
        tools.theory.constant(
          Peano.PartialSum,
          Type.fun(Type.fun(Numbers, Numbers), Type.fun(Numbers, Numbers))
        )
      )
      partial <- LogicError.lift(Term.app(sumConstant, summand))
      atNumeral <- Conv.apTerm(partial, length)
      walked <- walk(letters.size)
      joined <- Conv.trans(atNumeral, walked)
      value <- rightOf(joined)
      folded <- Rewrite.rewrite(tools.folds, value)
      result <- Conv.trans(joined, folded)
    } yield result
  }

  /**
   * [[PotentialCountedStep]]: a commutation step drops the measure by exactly one.
   *
   * The shape of the proof is [[anchoredUnderSteps]]'s -- open the step, walk the clauses -- with
   * arithmetic where that one has the class lemmas. Per clause:
   *
   *   - both words are read as a context, a written-out block and a tail, and [[PotentialBlocks]]
   *     turns each measure into three terms;
   *   - the two block sums are evaluated by [[sumOverPositions]] at the offset `WORD_LENGTH x`,
   *     which is where the rule fired, and the two tail sums are rewritten by the lengths of the
   *     written-out blocks: both rules have two letters a side, so what comes out is the same term
   *     and it cancels without being looked at;
   *   - what is left is `(P + k) + T = SUC ((P + (k - 1)) + T)`, which is the successor recurrences
   *     of addition on both sides of `k = SUC (k - 1)`.
   *
   * That last equation is the one that needs `0 < k`, and [[prefixIsNotEmpty]] is where the
   * anchored class is spent to get it.
   */
  private def potentialAcrossCounted(
    tools: Concrete,
    forward: Forward,
    concatenation: Concatenation,
    definitions: Map[String, Kernel.Thm],
    facts: Map[String, Kernel.Thm],
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules
    val subject = Term.variable("u", Words)
    val result = Term.variable("v", Words)

    for {
      target <- statement(tools.theory, tools.notation, PotentialCountedStep)
      body <- openAt(logic, target, List(subject, result))
      parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (premiseTerm, conclusionTerm) = parts
      premise <- LogicError.lift(Kernel.assume(premiseTerm))
      anchoredSubject <- rules.conjElim1(premise)
      stepped <- rules.conjElim2(premise)

      counted <- tools.constant(Counted, Type.fun(Words, Type.fun(Words, Type.Bool)))
      potential <- tools.constant(Potential, Type.fun(Words, Numbers))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      plus <- LogicError.lift(tools.theory.constant(Peano.Addition, BinaryNumbers))
      successorOf <- tools.successorOf
      potentialBlocks <- facts.get(PotentialBlocks).toRight(MissingDefinition(PotentialBlocks))
      countedDefinition <- definitions.get(Counted).toRight(MissingDefinition(Counted))

      stepDefinition <- forward.definition(Forward.Step).map(atNumbers)
      opened <- Conv.unfold(stepDefinition, List(counted, subject, result))
      existential <- LogicError.lift(Kernel.eqMp(opened, stepped))

      settled <- openWitnesses(
        logic,
        existential,
        4,
        Term.freeVariables(conclusionTerm) ++ Term.freeVariables(premiseTerm)
      ) { (witnesses, held) =>
        witnesses match {
          case List(front, left, right, tail) =>
            for {
              ruleHolds <- rules.conjElim1(held)
              rest <- rules.conjElim2(held)
              subjectEquation <- rules.conjElim1(rest)
              resultEquation <- rules.conjElim2(rest)

              asDisjunction <- Conv
                .unfold(countedDefinition, List(left, right))
                .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, ruleHolds)))

              answer <- overClauses(logic, asDisjunction, CountedRules.size) {
                (position, leftEquation, rightEquation) =>
                  for {
                    entry <- CountedRules
                      .lift(position)
                      .toRight(NotOfForm(s"a counted rule at $position", conclusionTerm))
                    proved <- countedClause(
                      tools,
                      concatenation,
                      facts,
                      Step(front, left, right, tail, subject, result),
                      Readers(potential, concat, plus, successorOf, potentialBlocks),
                      entry,
                      leftEquation,
                      rightEquation,
                      anchoredSubject,
                      subjectEquation,
                      resultEquation,
                      conditional,
                      conditionalFalse
                    )
                    _ <-
                      if (proved.conclusion == conclusionTerm) Right(())
                      else Left(NotOfForm(s"the measure at ${entry.label}", proved.conclusion))
                  } yield proved
              }
            } yield answer

          case other => Left(NotOfForm("four witnesses", Term.variable(other.size.toString, Words)))
        }
      }

      discharged <- rules.disch(premiseTerm, settled)
      generalised <- rules.genAll(discharged, List(subject, result))
      _ <-
        if (generalised.conclusion == target) Right(())
        else Left(NotOfForm(s"$PotentialCountedStep as it is written", generalised.conclusion))
    } yield generalised
  }

  /**
   * One clause of [[PotentialCountedStep]]: the measure of both words, normalised, and compared.
   *
   * The comparison is between two terms that differ in one place, and everything before it is
   * getting them into that shape: both words read as three blocks, the two written-out blocks
   * evaluated, and the tail sums rewritten by the lengths so that the two become the same term.
   */
  private def countedClause(
    tools: Concrete,
    concatenation: Concatenation,
    facts: Map[String, Kernel.Thm],
    step: Step,
    readers: Readers,
    entry: Rule,
    leftEquation: Kernel.Thm,
    rightEquation: Kernel.Thm,
    anchoredSubject: Kernel.Thm,
    subjectEquation: Kernel.Thm,
    resultEquation: Kernel.Thm,
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      wordLeft <- tools.word(entry.left)
      wordRight <- tools.word(entry.right)

      placedLeft <- placeBlock(readers.concat, step.front, leftEquation, step.tail)
      subjectAt <- Conv.trans(subjectEquation, placedLeft)
      placedRight <- placeBlock(readers.concat, step.front, rightEquation, step.tail)
      resultAt <- Conv.trans(resultEquation, placedRight)

      blocksLeft <- rules.specAll(readers.blocks, List(step.front, wordLeft, step.tail))
      measureLeft <- Conv.apTerm(readers.potential, subjectAt).flatMap(Conv.trans(_, blocksLeft))
      blocksRight <- rules.specAll(readers.blocks, List(step.front, wordRight, step.tail))
      measureRight <- Conv.apTerm(readers.potential, resultAt).flatMap(Conv.trans(_, blocksRight))

      normalLeft <- normalisedMeasure(tools, measureLeft, entry.left, conditional, conditionalFalse)
      normalRight <- normalisedMeasure(tools, measureRight, entry.right, conditional, conditionalFalse)

      positive <- prefixIsNotEmpty(
        tools, concatenation, facts, step, entry, subjectAt, anchoredSubject)
      spelled <- successorOfPredecessor(tools, step.front, positive)
      result <- measureFallsByOne(tools, readers, normalLeft, normalRight, spelled)
    } yield result
  }

  /** `|- (x l) y = (x <word>) y` from `|- l = <word>`: the block placed inside its context. */
  private def placeBlock(
    concat: Term,
    front: Term,
    equation: Kernel.Thm,
    tail: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      inner <- LogicError.lift(Term.app(concat, front)).flatMap(partial => Conv.apTerm(partial, equation))
      outer <- Conv.apTerm(concat, inner).flatMap(Conv.apThm(_, tail))
    } yield outer

  /**
   * `|- S2_PHI w = <the three terms, the middle one evaluated and the outer one folded>`.
   *
   * The middle sum is over a word with no variables in it, so [[sumOverPositions]] settles it; the
   * tail sum's offset is `WORD_LENGTH (x m)`, which the lengths fold to `SUC^n (WORD_LENGTH x)` and
   * which is therefore the same term for two blocks of the same length.
   */
  private def normalisedMeasure(
    tools: Concrete,
    measure: Kernel.Thm,
    letters: Vector[String],
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      sum <- rightOf(measure)
      middle <- sum match {
        case App(App(_, App(App(_, _), block)), _) => Right(block)
        case other => Left(NotOfForm("a measure of three blocks", other))
      }
      summand <- middle match {
        case App(App(_, function), _) => Right(function)
        case other => Left(NotOfForm("a sum over a bound", other))
      }
      evaluated <- sumOverPositions(tools, summand, letters, conditional, conditionalFalse)

      // The evaluated sum is stated at `WORD_LENGTH <word>` and the rewriting below turns that
      // bound into a numeral before anything else fires, so the equation as it comes back never
      // matches. It is restated at the numeral first, which is the same theorem read where the
      // rewriter will be looking.
      // The same rule set the outer rewrite below uses, and not a smaller one. A block placed in
      // an EMPTY context carries `WORD_LENGTH WORD_EMPTY` inside its own summand, which the
      // identities fold and the lengths alone do not: restated against half the rules, this
      // equation is about a summand the outer pass has already rewritten past.
      atNumeral <- leftOf(evaluated).flatMap(
        Rewrite.rewrite(tools.lengths ++ tools.identities, _))
      restated <- Conv.sym(atNumeral).flatMap(Conv.trans(_, evaluated))

      folding <- unfoldingRules(tools.logic, Vector(restated))
      normalised <- Rewrite.rewrite(tools.lengths ++ tools.identities ++ folding, sum)
      result <- Conv.trans(measure, normalised)
    } yield result

  /**
   * `|- (P + a) + t = SUC ((P + b) + t)` carried onto the two measures, from `|- a = SUC b`.
   *
   * Two successor recurrences and nothing else: addition takes the successor out of its right
   * argument and then out of its left one, which is exactly the shape the three blocks leave.
   */
  private def measureFallsByOne(
    tools: Concrete,
    readers: Readers,
    measureLeft: Kernel.Thm,
    measureRight: Kernel.Thm,
    spelled: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      sum <- rightOf(measureLeft)
      shape <- sum match {
        case App(App(_, App(App(_, context), _)), tail) => Right((context, tail))
        case other => Left(NotOfForm("a measure of three blocks", other))
      }
      (context, tail) = shape
      successorSides <- Term
        .destEq(spelled.conclusion)
        .toRight(NotOfForm("an equation", spelled.conclusion))
      predecessor <- successorSides._2 match {
        case App(_, inner) => Right(inner)
        case other => Left(NotOfForm("a successor", other))
      }

      partial <- LogicError.lift(Term.app(readers.plus, context))
      atTheBlock <- Conv.apTerm(partial, spelled)
      takenOut <- rules.specAll(tools.numbers.addAtSuccessor, List(context, predecessor))
      block <- Conv.trans(atTheBlock, takenOut)

      withTail <- Conv.apTerm(readers.plus, block).flatMap(Conv.apThm(_, tail))
      smaller <- LogicError.lift(Term.appAll(readers.plus, List(context, predecessor)))
      liftedOut <- rules.specAll(tools.numbers.successorPlus, List(smaller, tail))
      whole <- Conv.trans(withTail, liftedOut)

      onTheRight <- Conv.sym(measureRight).flatMap(Conv.apTerm(readers.successorOf, _))
      joined <- Conv.trans(whole, onTheRight)
      result <- Conv.trans(measureLeft, joined)
    } yield result
  }

  /**
   * `|- WORD_LENGTH x = SUC (WORD_LENGTH x - 1)`, which is what a positive length spells.
   *
   * `NUM_LT ZERO k` is `NUM_LE (SUC ZERO) k` by the strict order's own definition, so
   * [[Peano.MinusThenPlus]] applies at one and gives `(k - 1) + 1 = k`; the identities fold the
   * left side into `SUC (k - 1)` and the equation is turned round.
   */
  private def successorOfPredecessor(
    tools: Concrete,
    word: Term,
    positive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      lengthOf <- tools.lengthOf
      size <- LogicError.lift(Term.app(lengthOf, word))
      zero <- tools.zero
      one <- tools.numeral(1)

      // The positivity is the caller's theorem rather than an assumption made here. Assuming it
      // leaves a hypothesis on everything downstream, and what reports that is the generalisation
      // at the very end refusing a variable that occurs free in it.
      asAtMost <- Conv
        .unfold(tools.numbers.strictDefinition, List(zero, size))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, positive)))
      // `NUM_MINUS_THEN_PLUS` takes the larger number first: `!m n. n <= m ==> (m - n) + n = m`.
      restored <- rules
        .specAll(tools.numbers.minusThenPlus, List(size, one))
        .flatMap(rules.mp(_, asAtMost))
      folded <- rightOf(restored).flatMap(_ => leftOf(restored)).flatMap(
        left => Rewrite.rewrite(tools.identities, left))
      placed <- Conv.sym(folded).flatMap(Conv.trans(_, restored))
      result <- Conv.sym(placed)
    } yield result
  }

  /**
   * `|- 0 < WORD_LENGTH x`, from the word being anchored and the rule not firing at its first letter.
   *
   * The one place this proof spends [[Anchored]], and what it spends it on is the position the rule
   * fired at. With the context empty the word IS the rule's left-hand side followed by the tail, so
   * an anchored word would have that side anchored too, and [[notAnchoredWord]] refuses exactly
   * that: no commutation rule begins with the head marker.
   */
  private def prefixIsNotEmpty(
    tools: Concrete,
    concatenation: Concatenation,
    facts: Map[String, Kernel.Thm],
    step: Step,
    entry: Rule,
    subjectAt: Kernel.Thm,
    anchoredSubject: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      anchored <- tools.constant(Anchored, Type.fun(Words, Type.Bool))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      lengthOf <- tools.lengthOf
      order <- tools.strictOrder
      zero <- tools.zero
      wordLeft <- tools.word(entry.left)

      emptyLeft <- concatenation.fact(Concatenation.EmptyLeft).map(atNumbers)
      lengthZero <- concatenation.fact(Concatenation.LengthZero).map(atNumbers)
      anchoredConcat <- facts.get(AnchoredConcat).toRight(MissingDefinition(AnchoredConcat))

      frontLength <- LogicError.lift(Term.app(lengthOf, step.front))
      positiveTerm <- LogicError.lift(Term.appAll(order, List(zero, frontLength)))

      cases <- rules.spec(frontLength, tools.numbers.zeroOrSuccessor)
      disjuncts <- logic
        .destDisj(cases.conclusion)
        .toRight(NotOfForm("a disjunction", cases.conclusion))
      (isZero, isSuccessor) = disjuncts

      atTheFront <- {
        for {
          assumedZero <- LogicError.lift(Kernel.assume(isZero))
          frontEmpty <- rules.spec(step.front, lengthZero).flatMap(rules.mp(_, assumedZero))
          collapsed <- collapsedFront(
            logic, concat, step.front, wordLeft, step.tail, frontEmpty, emptyLeft)
          atBlock <- Conv
            .trans(subjectAt, collapsed)
            .flatMap(Conv.apTerm(anchored, _))
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, anchoredSubject)))
          leftPositive <- positiveLength(tools, entry.left)
          split <- rules
            .specAll(anchoredConcat, List(wordLeft, step.tail))
            .flatMap(rules.mp(_, leftPositive))
          both <- LogicError.lift(Kernel.eqMp(split, atBlock))
          anchoredBlock <- rules.conjElim1(both)
          refused <- notAnchoredWord(tools, entry.left)
          absurd <- rules.notElim(refused, anchoredBlock)
          anything <- rules.falsityElim(positiveTerm, absurd)
        } yield anything
      }

      inside <- {
        val predecessor = Conv.freshVariable(
          "k",
          Numbers,
          Term.freeVariables(positiveTerm) ++ Term.freeVariables(isSuccessor)
        )

        for {
          assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
          predicate <- logic
            .destExistsPredicate(isSuccessor)
            .toRight(NotOfForm("an existential", isSuccessor))
          applied <- LogicError.lift(Term.app(predicate, predecessor))
          instance <- Conv.betaRoot(applied).flatMap(rightOf)
          size <- LogicError.lift(Kernel.assume(instance))
          positive <- rules
            .spec(predecessor, tools.numbers.successorPositive)
            .flatMap(fact => Conv.sym(size).flatMap(carryRight(order, zero, _, fact)))
          closed <- rules.existsElim(assumedSuccessor, predecessor, positive)
        } yield closed
      }

      result <- rules.disjElim(cases, atTheFront, inside)
    } yield result
  }

  /**
   * [[PotentialPlainStep]]: an uncounted step never lowers the measure.
   *
   * Eleven clauses and the six commutation ones are closed without arithmetic: a step by such a
   * rule is a counted step over the same four witnesses, which the hypothesis refuses.
   */
  private def potentialAcrossPlain(
    tools: Concrete,
    forward: Forward,
    concatenation: Concatenation,
    classical: Classical,
    definitions: Map[String, Kernel.Thm],
    facts: Map[String, Kernel.Thm],
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules
    val subject = Term.variable("u", Words)
    val result = Term.variable("v", Words)

    for {
      target <- statement(tools.theory, tools.notation, PotentialPlainStep)
      body <- openAt(logic, target, List(subject, result))
      parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (premiseTerm, conclusionTerm) = parts
      premise <- LogicError.lift(Kernel.assume(premiseTerm))
      anchoredSubject <- rules.conjElim1(premise)
      afterAnchored <- rules.conjElim2(premise)
      markedSubject <- rules.conjElim1(afterAnchored)
      afterMarked <- rules.conjElim2(afterAnchored)
      stepped <- rules.conjElim1(afterMarked)
      notCounted <- rules.conjElim2(afterMarked)

      system <- tools.constant(Name, Type.fun(Words, Type.fun(Words, Type.Bool)))
      counted <- tools.constant(Counted, Type.fun(Words, Type.fun(Words, Type.Bool)))
      potential <- tools.constant(Potential, Type.fun(Words, Numbers))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      plus <- LogicError.lift(tools.theory.constant(Peano.Addition, BinaryNumbers))
      successorOf <- tools.successorOf
      potentialBlocks <- facts.get(PotentialBlocks).toRight(MissingDefinition(PotentialBlocks))
      systemDefinition <- definitions.get(Name).toRight(MissingDefinition(Name))
      countedDefinition <- definitions.get(Counted).toRight(MissingDefinition(Counted))

      stepDefinition <- forward.definition(Forward.Step).map(atNumbers)
      opened <- Conv.unfold(stepDefinition, List(system, subject, result))
      countedOpened <- Conv.unfold(stepDefinition, List(counted, subject, result))
      existential <- LogicError.lift(Kernel.eqMp(opened, stepped))

      settled <- openWitnesses(
        logic,
        existential,
        4,
        Term.freeVariables(conclusionTerm) ++ Term.freeVariables(premiseTerm)
      ) { (witnesses, held) =>
        witnesses match {
          case List(front, left, right, tail) =>
            for {
              ruleHolds <- rules.conjElim1(held)
              rest <- rules.conjElim2(held)
              subjectEquation <- rules.conjElim1(rest)
              resultEquation <- rules.conjElim2(rest)

              asDisjunction <- Conv
                .unfold(systemDefinition, List(left, right))
                .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, ruleHolds)))

              answer <- overClauses(logic, asDisjunction, Rules.size) {
                (position, leftEquation, rightEquation) =>
                  for {
                    entry <- Rules
                      .lift(position)
                      .toRight(NotOfForm(s"a rule at $position", conclusionTerm))
                    step = Step(front, left, right, tail, subject, result)
                    readers = Readers(potential, concat, plus, successorOf, potentialBlocks)
                    proved <-
                      if (entry.group == Group.Commutes)
                        refusedAsCounted(
                          tools,
                          step,
                          entry,
                          leftEquation,
                          rightEquation,
                          subjectEquation,
                          resultEquation,
                          countedDefinition,
                          countedOpened,
                          notCounted,
                          conclusionTerm
                        )
                      else
                        plainClause(
                          tools,
                          concatenation,
                          classical,
                          facts,
                          step,
                          readers,
                          entry,
                          leftEquation,
                          rightEquation,
                          Class(anchoredSubject, markedSubject),
                          subjectEquation,
                          resultEquation,
                          conditional,
                          conditionalFalse
                        )
                    _ <-
                      if (proved.conclusion == conclusionTerm) Right(())
                      else Left(NotOfForm(s"the measure at ${entry.label}", proved.conclusion))
                  } yield proved
              }
            } yield answer

          case other => Left(NotOfForm("four witnesses", Term.variable(other.size.toString, Words)))
        }
      }

      discharged <- rules.disch(premiseTerm, settled)
      generalised <- rules.genAll(discharged, List(subject, result))
      _ <-
        if (generalised.conclusion == target) Right(())
        else Left(NotOfForm(s"$PotentialPlainStep as it is written", generalised.conclusion))
    } yield generalised
  }

  /**
   * One of the five uncounted clauses of [[PotentialPlainStep]], in the shape its rule has.
   *
   * The two consuming rules eat the tail marker, so the marked word has nothing after the block and
   * both tail sums vanish; the three head rules fire at the front, so the context is empty. What is
   * compared after that is `P` against `P + w` for the first pair, two identical terms for `B1`,
   * and two tails one place apart for `B2` and `B3`.
   */
  private def plainClause(
    tools: Concrete,
    concatenation: Concatenation,
    classical: Classical,
    facts: Map[String, Kernel.Thm],
    step: Step,
    readers: Readers,
    entry: Rule,
    leftEquation: Kernel.Thm,
    rightEquation: Kernel.Thm,
    held: Class,
    subjectEquation: Kernel.Thm,
    resultEquation: Kernel.Thm,
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      wordLeft <- tools.word(entry.left)
      wordRight <- tools.word(entry.right)
      empty <- tools.constant(Concatenation.Empty, Words)
      atMost <- LogicError.lift(tools.theory.constant(Peano.NonStrictOrder, OrderType))

      placedLeft <- placeBlock(readers.concat, step.front, leftEquation, step.tail)
      subjectAt <- Conv.trans(subjectEquation, placedLeft)
      placedRight <- placeBlock(readers.concat, step.front, rightEquation, step.tail)
      resultAt <- Conv.trans(resultEquation, placedRight)

      // Which block the class says is empty, and the equation that says so.
      shape <-
        if (entry.group == Group.Consumes)
          tailIsEmpty(tools, concatenation, facts, step, entry, subjectAt, held.marked)
            .map(equation => (equation, false))
        else
          prefixIsEmpty(tools, concatenation, facts, step, entry, subjectAt, held.anchored)
            .map(equation => (equation, true))
      (emptyEquation, atTheFront) = shape

      collapsedLeft <-
        if (atTheFront) replaceFront(readers.concat, emptyEquation, wordLeft, step.tail)
        else replaceTail(readers.concat, step.front, wordLeft, emptyEquation)
      collapsedRight <-
        if (atTheFront) replaceFront(readers.concat, emptyEquation, wordRight, step.tail)
        else replaceTail(readers.concat, step.front, wordRight, emptyEquation)

      subjectFinal <- Conv.trans(subjectAt, collapsedLeft)
      resultFinal <- Conv.trans(resultAt, collapsedRight)

      context = if (atTheFront) empty else step.front
      rest = if (atTheFront) step.tail else empty

      blocksLeft <- rules.specAll(readers.blocks, List(context, wordLeft, rest))
      measureLeft <- Conv.apTerm(readers.potential, subjectFinal).flatMap(Conv.trans(_, blocksLeft))
      blocksRight <- rules.specAll(readers.blocks, List(context, wordRight, rest))
      measureRight <- Conv.apTerm(readers.potential, resultFinal).flatMap(Conv.trans(_, blocksRight))

      normalLeft <- normalisedMeasure(tools, measureLeft, entry.left, conditional, conditionalFalse)
      normalRight <- normalisedMeasure(tools, measureRight, entry.right, conditional, conditionalFalse)

      valueLeft <- rightOf(normalLeft)
      valueRight <- rightOf(normalRight)

      // Three shapes and the group decides which. A consuming rule leaves `P` against `P + w`, a
      // head rule that keeps the length leaves two identical terms, and one that lengthens leaves
      // two tails a place apart.
      comparison <-
        if (entry.group == Group.Consumes) summandIsAtMost(tools, valueLeft, valueRight)
        else if (valueLeft == valueRight) rules.spec(valueLeft, tools.numbers.reflexive)
        else tailGrows(tools, classical, valueLeft, valueRight, conditional, conditionalFalse)

      subjectMeasure <- leftOf(normalLeft)
      carried <- carryLeft(atMost, normalLeft, valueRight, comparison)
      reversed <- Conv.sym(normalRight)
      result <- carryRight(atMost, subjectMeasure, reversed, carried)
    } yield result
  }

  /** `|- (x m) y = (x m) WORD_EMPTY` from `|- y = WORD_EMPTY`. */
  private def replaceTail(
    concat: Term,
    front: Term,
    block: Term,
    tailEmpty: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      blockTerm <- LogicError.lift(Term.appAll(concat, List(front, block)))
      partial <- LogicError.lift(Term.app(concat, blockTerm))
      result <- Conv.apTerm(partial, tailEmpty)
    } yield result

  /** `|- (x m) y = (WORD_EMPTY m) y` from `|- x = WORD_EMPTY`. */
  private def replaceFront(
    concat: Term,
    frontEmpty: Kernel.Thm,
    block: Term,
    tail: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      inner <- Conv.apTerm(concat, frontEmpty).flatMap(Conv.apThm(_, block))
      result <- Conv.apTerm(concat, inner).flatMap(Conv.apThm(_, tail))
    } yield result

  /**
   * `|- y = WORD_EMPTY`, where `y` is whatever follows a consuming rule in a marked word.
   *
   * The one place a consuming clause spends [[Marked]], and it is what makes the two tail sums
   * vanish instead of having to be compared. Both rules of that group carry the tail marker inside
   * their own left-hand side, so a non-empty `y` would put a second marker after it, or the same
   * one somewhere that is not the last letter; a marked word has exactly one and it is the last.
   *
   * `MarkedConcat` asks for a tail nobody has shown non-empty, which is why the length is split
   * first: the zero case **is** the conclusion, by `WORD_LENGTH_ZERO`, and the successor case is
   * the contradiction.
   */
  private def tailIsEmpty(
    tools: Concrete,
    concatenation: Concatenation,
    facts: Map[String, Kernel.Thm],
    step: Step,
    entry: Rule,
    subjectAt: Kernel.Thm,
    markedSubject: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      marked <- tools.constant(Marked, Type.fun(Words, Type.Bool))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      empty <- tools.constant(Concatenation.Empty, Words)
      lengthOf <- tools.lengthOf
      order <- tools.strictOrder
      zero <- tools.zero
      wordLeft <- tools.word(entry.left)
      position <- entry.left.indexOf(Tail) match {
        case -1 => Left(NotOfForm(s"a rule with a tail marker in it, at ${entry.label}", wordLeft))
        case found => Right(found)
      }

      lengthZero <- concatenation.fact(Concatenation.LengthZero).map(atNumbers)
      markedConcat <- facts.get(MarkedConcat).toRight(MissingDefinition(MarkedConcat))
      tailFreeConcat <- facts.get(TailFreeConcat).toRight(MissingDefinition(TailFreeConcat))

      goal <- LogicError.lift(Term.eq(step.tail, empty))
      block <- LogicError.lift(Term.appAll(concat, List(step.front, wordLeft)))
      tailLength <- LogicError.lift(Term.app(lengthOf, step.tail))
      atWord <- Conv
        .apTerm(marked, subjectAt)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, markedSubject)))

      cases <- rules.spec(tailLength, tools.numbers.zeroOrSuccessor)
      disjuncts <- logic
        .destDisj(cases.conclusion)
        .toRight(NotOfForm("a disjunction", cases.conclusion))
      (isZero, isSuccessor) = disjuncts

      atZero <- {
        for {
          assumedZero <- LogicError.lift(Kernel.assume(isZero))
          result <- rules.spec(step.tail, lengthZero).flatMap(rules.mp(_, assumedZero))
        } yield result
      }

      inside <- {
        val predecessor = Conv.freshVariable(
          "k",
          Numbers,
          Term.freeVariables(goal) ++ Term.freeVariables(isSuccessor)
        )

        for {
          assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
          predicate <- logic
            .destExistsPredicate(isSuccessor)
            .toRight(NotOfForm("an existential", isSuccessor))
          applied <- LogicError.lift(Term.app(predicate, predecessor))
          instance <- Conv.betaRoot(applied).flatMap(rightOf)
          size <- LogicError.lift(Kernel.assume(instance))
          positive <- rules
            .spec(predecessor, tools.numbers.successorPositive)
            .flatMap(fact => Conv.sym(size).flatMap(carryRight(order, zero, _, fact)))
          split <- rules
            .specAll(markedConcat, List(block, step.tail))
            .flatMap(rules.mp(_, positive))
          both <- LogicError.lift(Kernel.eqMp(split, atWord))
          blockFree <- rules.conjElim1(both)
          pieces <- rules.specAll(tailFreeConcat, List(step.front, wordLeft))
          parts <- LogicError.lift(Kernel.eqMp(pieces, blockFree))
          ruleFree <- rules.conjElim2(parts)
          refused <- notFreeWord(tools, entry.left, position, Tail)
          absurd <- rules.notElim(refused, ruleFree)
          anything <- rules.falsityElim(goal, absurd)
          closed <- rules.existsElim(assumedSuccessor, predecessor, anything)
        } yield closed
      }

      result <- rules.disjElim(cases, atZero, inside)
    } yield result
  }

  /**
   * `|- x = WORD_EMPTY`, where `x` is whatever precedes a head rule in an anchored word.
   *
   * The twin of [[tailIsEmpty]] at the other end and at the other class. The three head rules carry
   * the head marker as their first letter, and an anchored word has that marker at position zero
   * and nowhere else, so nothing can stand in front of one.
   *
   * `AnchoredConcat` splits `x` from what follows it, and what follows it here is `m y` rather than
   * the `(x m) y` the step hands over: the association is moved by `WORD_CONCAT_ASSOC` first, which
   * is the one place this proof differs from its twin.
   */
  private def prefixIsEmpty(
    tools: Concrete,
    concatenation: Concatenation,
    facts: Map[String, Kernel.Thm],
    step: Step,
    entry: Rule,
    subjectAt: Kernel.Thm,
    anchoredSubject: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      anchored <- tools.constant(Anchored, Type.fun(Words, Type.Bool))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      empty <- tools.constant(Concatenation.Empty, Words)
      lengthOf <- tools.lengthOf
      order <- tools.strictOrder
      zero <- tools.zero
      wordLeft <- tools.word(entry.left)
      position <- entry.left.indexOf(Head) match {
        case -1 => Left(NotOfForm(s"a rule with a head marker in it, at ${entry.label}", wordLeft))
        case found => Right(found)
      }

      lengthZero <- concatenation.fact(Concatenation.LengthZero).map(atNumbers)
      associative <- concatenation.fact(Concatenation.Associative).map(atNumbers)
      anchoredConcat <- facts.get(AnchoredConcat).toRight(MissingDefinition(AnchoredConcat))
      headFreeConcat <- facts.get(HeadFreeConcat).toRight(MissingDefinition(HeadFreeConcat))

      goal <- LogicError.lift(Term.eq(step.front, empty))
      rest <- LogicError.lift(Term.appAll(concat, List(wordLeft, step.tail)))
      frontLength <- LogicError.lift(Term.app(lengthOf, step.front))

      moved <- rules.specAll(associative, List(step.front, wordLeft, step.tail))
      reassociated <- Conv.trans(subjectAt, moved)
      atWord <- Conv
        .apTerm(anchored, reassociated)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, anchoredSubject)))

      cases <- rules.spec(frontLength, tools.numbers.zeroOrSuccessor)
      disjuncts <- logic
        .destDisj(cases.conclusion)
        .toRight(NotOfForm("a disjunction", cases.conclusion))
      (isZero, isSuccessor) = disjuncts

      atZero <- {
        for {
          assumedZero <- LogicError.lift(Kernel.assume(isZero))
          result <- rules.spec(step.front, lengthZero).flatMap(rules.mp(_, assumedZero))
        } yield result
      }

      inside <- {
        val predecessor = Conv.freshVariable(
          "k",
          Numbers,
          Term.freeVariables(goal) ++ Term.freeVariables(isSuccessor)
        )

        for {
          assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
          predicate <- logic
            .destExistsPredicate(isSuccessor)
            .toRight(NotOfForm("an existential", isSuccessor))
          applied <- LogicError.lift(Term.app(predicate, predecessor))
          instance <- Conv.betaRoot(applied).flatMap(rightOf)
          size <- LogicError.lift(Kernel.assume(instance))
          positive <- rules
            .spec(predecessor, tools.numbers.successorPositive)
            .flatMap(fact => Conv.sym(size).flatMap(carryRight(order, zero, _, fact)))
          split <- rules
            .specAll(anchoredConcat, List(step.front, rest))
            .flatMap(rules.mp(_, positive))
          both <- LogicError.lift(Kernel.eqMp(split, atWord))
          afterFree <- rules.conjElim2(both)
          pieces <- rules.specAll(headFreeConcat, List(wordLeft, step.tail))
          parts <- LogicError.lift(Kernel.eqMp(pieces, afterFree))
          ruleFree <- rules.conjElim1(parts)
          refused <- notFreeWord(tools, entry.left, position, Head)
          absurd <- rules.notElim(refused, ruleFree)
          anything <- rules.falsityElim(goal, absurd)
          closed <- rules.existsElim(assumedSuccessor, predecessor, anything)
        } yield closed
      }

      result <- rules.disjElim(cases, atZero, inside)
    } yield result
  }

  /**
   * `|- a <= a + w`, which is what a consuming rule leaves once the tail has gone.
   *
   * The rule ate a letter that contributed nothing and left a digit that contributes `|x| - 1`, so
   * the measure gains a summand and loses none. `NUM_LE_ADD` holds with no side condition because
   * there are no negative numbers here, and what makes it apply is that the term on the right is
   * the term on the left with something added and not merely a larger number.
   */
  private def summandIsAtMost(
    tools: Concrete,
    valueLeft: Term,
    valueRight: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      parts <- destAdd(tools, valueRight)
      _ <-
        if (parts._1 == valueLeft) Right(())
        else Left(NotOfForm("the measure before the step, with a summand added", valueRight))
      result <- tools.rules.specAll(tools.numbers.atMostSum, List(valueLeft, parts._2))
    } yield result

  /**
   * `|- P + T <= P + T'`, where `T` and `T'` are one tail read at two offsets a place apart.
   *
   * The two head rules that lengthen the word push everything after them one place further from
   * the head, and a digit's contribution is its distance from it. So the comparison is between two
   * sums over the same tail and the same bound whose summands differ in one number, which is
   * `NUM_SUM_MONOTONE_BELOW` over a pointwise argument, and the context in front of them is carried
   * by `NUM_ADD_MONOTONE` rather than looked at.
   */
  private def tailGrows(
    tools: Concrete,
    classical: Classical,
    valueLeft: Term,
    valueRight: Term,
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      leftParts <- destAdd(tools, valueLeft)
      rightParts <- destAdd(tools, valueRight)
      _ <-
        if (leftParts._1 == rightParts._1) Right(())
        else Left(NotOfForm("two measures over one context", valueRight))
      (context, tailLeft) = leftParts
      tailRight = rightParts._2

      before <- destSum(tools, tailLeft)
      after <- destSum(tools, tailRight)
      _ <-
        if (before._2 == after._2) Right(())
        else Left(NotOfForm("two sums over one bound", tailRight))

      monotone <- rules.specAll(
        tools.numbers.sumMonotoneBelow, List(before._1, after._1, before._2))
      shape <- logic
        .destImp(monotone.conclusion)
        .toRight(NotOfForm("an implication", monotone.conclusion))
      pointwise <- underTheBound(logic, shape._1) { (index, _) =>
        laterIsLarger(tools, classical, before._1, after._1, index, conditional, conditionalFalse)
      }
      sums <- rules.mp(monotone, pointwise)
      result <- rules
        .specAll(tools.numbers.addMonotone, List(context, tailLeft, tailRight))
        .flatMap(rules.mp(_, sums))
    } yield result
  }

  /**
   * `|- f i <= g i`, for the two summands of [[tailGrows]] at one index.
   *
   * Both are a conditional on the same question, whether the letter there is a digit, and the
   * branches nobody takes are the same term, so the split is on that question and not on anything
   * about the two offsets. Where the letter is not a digit both sides are the same number and the
   * order is reflexive; where it is, [[oneMorePlace]] compares the two contributions.
   *
   * What comes back is stated at the **redex**, `f i` rather than the conditional it reduces to,
   * because that is what `NUM_SUM_MONOTONE_BELOW`'s antecedent is written with.
   */
  private def laterIsLarger(
    tools: Concrete,
    classical: Classical,
    before: Term,
    after: Term,
    index: FVar,
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      atMost <- tools.constant(Peano.NonStrictOrder, OrderType)
      openedBefore <- LogicError.lift(Term.app(before, index)).flatMap(Conv.betaRoot)
      openedAfter <- LogicError.lift(Term.app(after, index)).flatMap(Conv.betaRoot)
      bodyBefore <- rightOf(openedBefore)
      bodyAfter <- rightOf(openedAfter)
      partsBefore <- destCond(bodyBefore)
      partsAfter <- destCond(bodyAfter)
      _ <-
        if (partsBefore._1 == partsAfter._1 && partsBefore._3 == partsAfter._3) Right(())
        else Left(NotOfForm("two summands differing only in the offset", bodyAfter))
      (condition, sooner, otherwise) = partsBefore
      later = partsAfter._2

      cases <- classical.excludedMiddleAt(condition)
      disjuncts <- logic
        .destDisj(cases.conclusion)
        .toRight(NotOfForm("a disjunction", cases.conclusion))
      (holds, fails) = disjuncts

      atADigit <- {
        for {
          assumed <- LogicError.lift(Kernel.assume(holds))
          chosenBefore <- rules
            .specAll(conditional, List(condition, sooner, otherwise))
            .flatMap(rules.mp(_, assumed))
          chosenAfter <- rules
            .specAll(conditional, List(condition, later, otherwise))
            .flatMap(rules.mp(_, assumed))
          compared <- oneMorePlace(tools, sooner, later)
          onTheLeft <- carryLeft(atMost, chosenBefore, later, compared)
          reversed <- Conv.sym(chosenAfter)
          result <- carryRight(atMost, bodyBefore, reversed, onTheLeft)
        } yield result
      }

      elsewhere <- {
        for {
          assumed <- LogicError.lift(Kernel.assume(fails))
          chosenBefore <- rules
            .specAll(conditionalFalse, List(condition, sooner, otherwise))
            .flatMap(rules.mp(_, assumed))
          chosenAfter <- rules
            .specAll(conditionalFalse, List(condition, later, otherwise))
            .flatMap(rules.mp(_, assumed))
          same <- rules.spec(otherwise, tools.numbers.reflexive)
          onTheLeft <- carryLeft(atMost, chosenBefore, otherwise, same)
          reversed <- Conv.sym(chosenAfter)
          result <- carryRight(atMost, bodyBefore, reversed, onTheLeft)
        } yield result
      }

      settled <- rules.disjElim(cases, atADigit, elsewhere)
      onTheRedex <- carryLeft(atMost, openedBefore, bodyAfter, settled)
      applied <- leftOf(openedBefore)
      reversed <- Conv.sym(openedAfter)
      result <- carryRight(atMost, applied, reversed, onTheRedex)
    } yield result
  }

  /**
   * `|- (c + i) - 1 <= (SUC c + i) - 1`, the same digit one place further from the head.
   *
   * Written as a comparison of two **normalised** terms rather than as a lemma about subtraction,
   * because there is no monotonicity of truncated subtraction in this development and the two
   * offsets here are concrete. `NUM_SUC_ADD` lifts the successor out of the sum and the folds take
   * the `- 1` off both, so what is left is a number against its own successor.
   */
  private def oneMorePlace(
    tools: Concrete,
    sooner: Term,
    later: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      shifting <- unfoldingRules(tools.logic, Vector(tools.numbers.successorPlus))
      folding = shifting ++ tools.folds
      normalSooner <- Rewrite.rewrite(folding, sooner)
      normalLater <- Rewrite.rewrite(folding, later)
      small <- rightOf(normalSooner)
      large <- rightOf(normalLater)
      successorOf <- tools.successorOf
      expected <- LogicError.lift(Term.app(successorOf, small))
      _ <-
        if (large == expected) Right(())
        else Left(NotOfForm("a contribution exactly one place later", large))
      atMost <- tools.constant(Peano.NonStrictOrder, OrderType)
      step <- tools.rules.spec(small, tools.numbers.atMostSuccessor)
      onTheLeft <- carryLeft(atMost, normalSooner, large, step)
      reversed <- Conv.sym(normalLater)
      result <- carryRight(atMost, sooner, reversed, onTheLeft)
    } yield result

  /** `x + y` taken apart, with the constant checked rather than the shape alone. */
  private def destAdd(tools: Concrete, term: Term): Either[LogicError, (Term, Term)] =
    for {
      plus <- tools.constant(Peano.Addition, BinaryNumbers)
      parts <- term match {
        case App(App(head, left), right) if head == plus => Right((left, right))
        case other => Left(NotOfForm("a sum of two numbers", other))
      }
    } yield parts

  /** `NUM_SUM f k` taken apart, the same way and for the same reason. */
  private def destSum(tools: Concrete, term: Term): Either[LogicError, (Term, Term)] =
    for {
      sum <- tools.constant(
        Peano.PartialSum,
        Type.fun(Type.fun(Numbers, Numbers), Type.fun(Numbers, Numbers))
      )
      parts <- term match {
        case App(App(head, summand), bound) if head == sum => Right((summand, bound))
        case other => Left(NotOfForm("a partial sum", other))
      }
    } yield parts

  /** `COND p a b` taken apart at the one type this development conditions on. */
  private def destCond(term: Term): Either[LogicError, (Term, Term, Term)] =
    term match {
      case App(App(App(_, condition), whenTrue), whenFalse) =>
        Right((condition, whenTrue, whenFalse))
      case other => Left(NotOfForm("a conditional", other))
    }

  /**
   * [[RunPotential]]: `REACH_POTENTIAL` instantiated at this system.
   *
   * The whole of the work is in the two hypotheses, and what makes them provable is that the
   * relation carries the class rather than the lemma asking for it. `REACH_POTENTIAL` wants its
   * measure to fall by exactly one across **every** counted pair and to hold up across every other
   * one, with no side condition available; [[PotentialCountedStep]] and [[PotentialPlainStep]] are
   * both conditional on the word stepped from being anchored and marked. Putting those two
   * conditions inside `S2_RUN` is what closes the gap, and it loses nothing, because the class is
   * closed under a step: a run that starts inside it never leaves.
   *
   * The second hypothesis is where the two definitions pay for being nested. `~(S2_RUN_COUNTED u v)`
   * with `S2_RUN u v` in hand gives `~(WORD_STEP S2_COUNTED u v)` in three lines, because
   * `S2_RUN_COUNTED` **is** `S2_RUN` and a counted step; had it been the class and a counted step,
   * the same inference would have had to take the class apart a second time.
   */
  private def runPotential(
    tools: Concrete,
    reaching: Reaching,
    definitions: Map[String, Kernel.Thm],
    facts: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules
    val subject = Term.variable("x", Words)
    val left = Term.variable("u", Words)
    val right = Term.variable("v", Words)

    for {
      target <- statement(tools.theory, tools.notation, RunPotential)
      run <- tools.constant(Run, SystemType)
      runCounted <- tools.constant(RunCounted, SystemType)
      potential <- tools.constant(Potential, Type.fun(Words, Numbers))
      runDefinition <- definitions.get(Run).toRight(MissingDefinition(Run))
      runCountedDefinition <- definitions.get(RunCounted).toRight(MissingDefinition(RunCounted))
      countedStep <- facts
        .get(PotentialCountedStep)
        .toRight(MissingDefinition(PotentialCountedStep))
      plainStep <- facts.get(PotentialPlainStep).toRight(MissingDefinition(PotentialPlainStep))

      lemma <- reaching.fact(Reaching.Potential).map(atWords)
      specialised <- rules.specAll(lemma, List(run, runCounted, potential, subject))
      parts <- logic
        .destImp(specialised.conclusion)
        .toRight(NotOfForm("an implication", specialised.conclusion))
      halves <- logic
        .destConj(parts._1)
        .toRight(NotOfForm("the two hypotheses of REACH_POTENTIAL", parts._1))
      (countedTerm, plainTerm) = halves

      falls <- overAStep(logic, countedTerm, left, right) { premise =>
        for {
          opened <- Conv
            .unfold(runCountedDefinition, List(left, right))
            .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, premise)))
          inRun <- rules.conjElim1(opened)
          isCounted <- rules.conjElim2(opened)
          held <- openRun(rules, runDefinition, left, right, inRun)
          joined <- rules.conjIntro(held._2, isCounted)
          result <- rules.specAll(countedStep, List(left, right)).flatMap(rules.mp(_, joined))
        } yield result
      }

      holdsUp <- overAStep(logic, plainTerm, left, right) { premise =>
        for {
          inRun <- rules.conjElim1(premise)
          notInCounted <- rules.conjElim2(premise)
          held <- openRun(rules, runDefinition, left, right, inRun)
          (stepped, anchored, marked) = held

          folding <- Conv.unfold(runCountedDefinition, List(left, right))
          countedStepTerm <- rightOf(folding).flatMap(
            body => logic.destConj(body).map(_._2).toRight(NotOfForm("a counted step", body)))
          refused <- {
            for {
              assumed <- LogicError.lift(Kernel.assume(countedStepTerm))
              rebuilt <- rules.conjIntro(inRun, assumed)
              inCounted <- Conv
                .sym(folding)
                .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, rebuilt)))
              absurd <- rules.notElim(notInCounted, inCounted)
              result <- rules.notIntro(countedStepTerm, absurd)
            } yield result
          }

          joined <- rules
            .conjIntro(stepped, refused)
            .flatMap(rules.conjIntro(marked, _))
            .flatMap(rules.conjIntro(anchored, _))
          result <- rules.specAll(plainStep, List(left, right)).flatMap(rules.mp(_, joined))
        } yield result
      }

      both <- rules.conjIntro(falls, holdsUp)
      settled <- rules.mp(specialised, both)
      result <- rules.genAll(settled, List(subject))
      _ <-
        if (result.conclusion == target) Right(())
        else Left(NotOfForm(s"$RunPotential as it is written", result.conclusion))
    } yield result
  }

  /**
   * [[RunInhabited]]: the relation [[RunPotential]] quantifies over relates something.
   *
   * A bound on every run of a relation that steps nothing is true and empty, and no other test here
   * would notice: `REACH_START` inhabits the closure at every `x` whatever the relation does, so
   * even a detachment of the bound would come back with `S2_PHI x <= 0 + S2_PHI x`. The three
   * conjuncts are the step of `S2_STEP_INHABITED` and the class at the word it starts from.
   */
  private def runHolds(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm],
    facts: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      target <- statement(tools.theory, tools.notation, RunInhabited)
      before <- tools.word(BeforeTheStep)
      after <- tools.word(AfterTheStep)
      runDefinition <- definitions.get(Run).toRight(MissingDefinition(Run))
      stepped <- facts.get(StepInhabited).toRight(MissingDefinition(StepInhabited))
      anchored <- facts.get(AnchoredInhabited).toRight(MissingDefinition(AnchoredInhabited))
      marked <- facts.get(MarkedInhabited).toRight(MissingDefinition(MarkedInhabited))

      joined <- rules.conjIntro(anchored, marked).flatMap(rules.conjIntro(stepped, _))
      result <- Conv
        .unfold(runDefinition, List(before, after))
        .flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, joined)))
      _ <-
        if (result.conclusion == target) Right(())
        else Left(NotOfForm(s"$RunInhabited as it is written", result.conclusion))
    } yield result
  }

  /** The three conjuncts of `S2_RUN u v`, which both hypotheses of the instantiation take apart. */
  private def openRun(
    rules: Rules,
    runDefinition: Kernel.Thm,
    left: Term,
    right: Term,
    inRun: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm, Kernel.Thm)] =
    for {
      opened <- Conv
        .unfold(runDefinition, List(left, right))
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, inRun)))
      stepped <- rules.conjElim1(opened)
      rest <- rules.conjElim2(opened)
      anchored <- rules.conjElim1(rest)
      marked <- rules.conjElim2(rest)
    } yield (stepped, anchored, marked)

  /**
   * `|- !u v. P ==> Q`, from a proof of `Q` under `P`, against the statement the caller wants.
   *
   * [[underTheBound]] one binder wider and without the arithmetic: what it is for is a hypothesis
   * of `REACH_POTENTIAL`, which is read off the specialised lemma rather than written again here,
   * so the check at the end is what says the two are the same claim.
   */
  private def overAStep(
    logic: Logic,
    statement: Term,
    left: FVar,
    right: FVar
  )(
    step: Kernel.Thm => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      body <- openAt(logic, statement, List(left, right))
      parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (premiseTerm, conclusionTerm) = parts
      premise <- LogicError.lift(Kernel.assume(premiseTerm))
      proved <- step(premise)
      _ <-
        if (proved.conclusion == conclusionTerm) Right(())
        else Left(NotOfForm("the claim at this step as it is written", proved.conclusion))
      discharged <- rules.disch(premiseTerm, proved)
      result <- rules.genAll(discharged, List(left, right))
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm("the hypothesis as REACH_POTENTIAL writes it", result.conclusion))
    } yield result
  }

  /** A polymorphic lemma of the reachability, read at the type this development has states of. */
  private def atWords(theorem: Kernel.Thm): Kernel.Thm =
    Kernel.instType(Map(Classical.TypeVariable -> Words), theorem)

  /**
   * [[ZerosLength]] and [[StemLength]]: how long the family is, which is what its measure needs.
   *
   * The first is the recursion read as a length and is one induction; the second needs none,
   * because a concatenation's length is the sum of two and the left one is a written-out word the
   * length rules settle. Both are here rather than inside [[potentialOfStem]] because that proof
   * spends the second **under a binder**: the weight of a letter is its distance from the head, so
   * a block placed after the stem needs to know how far along the word it starts.
   */
  private def familyLengths(
    tools: Concrete,
    naturals: Natural,
    concatenation: Concatenation,
    zerosAtZero: Kernel.Thm,
    zerosAtSuccessor: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      lengthOf <- tools.lengthOf
      concat <- tools.constant(Concatenation.Name, ConcatType)
      zerosOf <- tools.constant(Zeros, Type.fun(Numbers, Words))
      stem <- tools.word(spell("/f"))
      digitZero <- tools.word(spell("0"))

      emptyLength <- concatenation.fact(Concatenation.EmptyLength).map(atNumbers)
      concatLength <- concatenation.fact(Concatenation.Length).map(atNumbers)
      singletonLength = tools.singletonLength

      induction <- naturals.fact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)

      lengths <- statement(tools.theory, tools.notation, ZerosLength)
      zerosLength <- driver.proveBy(
        lengths,
        goal =>
          for {
            opened <- Conv.apTerm(lengthOf, zerosAtZero)
            result <- Conv.trans(opened, emptyLength)
            _ <-
              if (result.conclusion == goal) Right(())
              else Left(NotOfForm("the empty run's length as the driver opened it", result.conclusion))
          } yield result,
        opened =>
          for {
            grown <- rules.spec(opened.variable, zerosAtSuccessor)
            atIndex <- LogicError.lift(Term.app(zerosOf, opened.variable))
            measured <- Conv.apTerm(lengthOf, grown)
            split <- rules.specAll(concatLength, List(atIndex, digitZero))
            joined <- Conv.trans(measured, split)
            // `|0^j| + |0|` is `j + SUC ZERO`, and the successor comes out of the right summand by
            // the recurrence and the zero goes by the identity. Two rewrites and no induction of
            // their own, which is why the length of a run is not its own development.
            folding <- unfoldingRules(
              logic,
              Vector(opened.hypothesis, singletonLength, tools.numbers.addAtSuccessor,
                tools.numbers.addAtZero)
            )
            value <- rightOf(joined)
            folded <- Rewrite.rewrite(folding ++ tools.lengths, value)
            result <- Conv.trans(joined, folded)
            _ <-
              if (result.conclusion == opened.goal) Right(())
              else Left(NotOfForm("the run's length as the driver opened it", result.conclusion))
          } yield result
      )

      stemStatement <- statement(tools.theory, tools.notation, StemLength)
      index = Conv.freshVariable("j", Numbers, Term.freeVariables(stemStatement))
      atIndex <- LogicError.lift(Term.app(zerosOf, index))
      split <- rules.specAll(concatLength, List(stem, atIndex))
      folding <- unfoldingRules(
        logic,
        Vector(zerosLength, tools.numbers.successorPlus, tools.numbers.zeroPlus)
      )
      value <- rightOf(split)
      folded <- Rewrite.rewrite(folding ++ tools.lengths, value)
      shaped <- Conv.trans(split, folded)
      stemLength <- rules.gen(index, shaped)
      _ <-
        if (stemLength.conclusion == stemStatement) Right(())
        else Left(NotOfForm(s"$StemLength as it is written", stemLength.conclusion))
    } yield (zerosLength, stemLength)
  }

  /**
   * [[PotentialOfStem]]: the measure of the family, in closed form, by induction on the run.
   *
   * The step is [[PotentialConcat]] at the stem and one digit. What comes back is the measure of
   * the shorter stem plus a sum over a one-letter word, [[sumOverPositions]] evaluates that sum,
   * and what it evaluates to is `WORD_LENGTH <stem> - 1`, which [[StemLength]] turns into `SUC j`.
   * Then `NUM_TRI j + SUC j` is `NUM_TRI (SUC j)` by the triangular numbers' own recurrence, and
   * the two recursions meeting is the whole content: neither is rearranged to fit the other.
   */
  private def potentialOfStem(
    tools: Concrete,
    naturals: Natural,
    numbering: Numbering,
    concatenation: Concatenation,
    definitions: Map[String, Kernel.Thm],
    facts: Map[String, Kernel.Thm],
    zerosAtZero: Kernel.Thm,
    zerosAtSuccessor: Kernel.Thm,
    stemLength: Kernel.Thm,
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      potential <- tools.constant(Potential, Type.fun(Words, Numbers))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      zerosOf <- tools.constant(Zeros, Type.fun(Numbers, Words))
      stem <- tools.word(spell("/f"))
      digitZero <- tools.word(spell("0"))

      associative <- concatenation.fact(Concatenation.Associative).map(atNumbers)
      emptyRight <- concatenation.fact(Concatenation.EmptyRight).map(atNumbers)
      potentialConcat <- facts.get(PotentialConcat).toRight(MissingDefinition(PotentialConcat))
      triangleAtZero <- numbering.fact(Numbering.TriangleAtZero)
      triangleAtSuccessor <- numbering.fact(Numbering.TriangleAtSuccessor)

      induction <- naturals.fact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)

      target <- statement(tools.theory, tools.notation, PotentialOfStem)
      result <- driver.proveBy(
        target,
        goal =>
          for {
            // `(/f) 0^0` is `(/f) WORD_EMPTY` is `/f`, written as the family rather than as the
            // word it happens to equal, which is [[digitFamily]]'s base case read for a measure.
            inFront <- LogicError.lift(Term.app(concat, stem))
            opened <- Conv.apTerm(inFront, zerosAtZero)
            collapsed <- rules.spec(stem, emptyRight).flatMap(Conv.trans(opened, _))
            measured <- Conv.apTerm(potential, collapsed)
            evaluated <- potentialOfWord(tools, spell("/f"), definitions, conditional, conditionalFalse)
            joined <- Conv.trans(measured, evaluated)
            atZero <- Conv.sym(triangleAtZero)
            settled <- Conv.trans(joined, atZero)
            _ <-
              if (settled.conclusion == goal) Right(())
              else Left(NotOfForm("the measure at the empty run as the driver opened it", settled.conclusion))
          } yield settled,
        opened =>
          for {
            atIndex <- LogicError.lift(Term.app(zerosOf, opened.variable))
            prefix <- LogicError.lift(Term.appAll(concat, List(stem, atIndex)))
            grown <- runOneLonger(
              tools, concat, stem, atIndex, digitZero, opened.variable,
              associative, zerosAtSuccessor)
            shaped <- Conv.sym(grown)
            measured <- Conv.apTerm(potential, shaped)
            split <- rules.specAll(potentialConcat, List(prefix, digitZero))
            joined <- Conv.trans(measured, split)

            value <- rightOf(joined)
            tail <- value match {
              case App(App(_, _), sum) => Right(sum)
              case other => Left(NotOfForm("the measure of two blocks", other))
            }
            summand <- tail match {
              case App(App(_, function), _) => Right(function)
              case other => Left(NotOfForm("a sum over a bound", other))
            }
            evaluated <- sumOverPositions(tools, summand, spell("0"), conditional, conditionalFalse)

            folded <- foldedSum(
              tools,
              Vector(stemLength, opened.hypothesis, tools.numbers.oneIsSuccessorOfZero,
                tools.numbers.subSuccessors, tools.numbers.subAtZero),
              evaluated,
              value
            )
            carried <- Conv.trans(joined, folded)

            // The goal's own right-hand side is taken to where the left one ended rather than the
            // other way round. `NUM_TRI (SUC j)` is `NUM_TRI j + SUC j` by the recurrence, and the
            // identities then lift that successor out of the sum exactly as they lifted the one on
            // the left, so the two meet at a term neither of the two recursions is written in.
            sides <- Term
              .destEq(opened.goal)
              .toRight(NotOfForm("an equation", opened.goal))
            recurrence <- unfoldingRules(logic, Vector(triangleAtSuccessor))
            expansion <- Rewrite.rewrite(recurrence ++ tools.identities, sides._2)
            settled <- Conv.sym(expansion).flatMap(Conv.trans(carried, _))
            _ <-
              if (settled.conclusion == opened.goal) Right(())
              else Left(NotOfForm("the measure at the longer run as the driver opened it", settled.conclusion))
          } yield settled
      )
    } yield result
  }

  /**
   * [[PotentialOfFamily]] and [[FamilyBounded]]: the tail marker weighs nothing, and the bound.
   *
   * One [[PotentialConcat]] over a word whose second block is a single letter that is not a digit,
   * so the sum it contributes is `ZERO` and the measure of the family is the measure of its stem.
   * The bound after it is [[RunPotential]] with that equation carried into its left side, and
   * nothing else: what makes it a statement about a size rather than about a word is `NUM_TRI`.
   */
  private def familyBounded(
    tools: Concrete,
    numbering: Numbering,
    concatenation: Concatenation,
    facts: Map[String, Kernel.Thm],
    stemPotential: Kernel.Thm,
    zerosAtZero: Kernel.Thm,
    zerosAtSuccessor: Kernel.Thm,
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm, Kernel.Thm)] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      potential <- tools.constant(Potential, Type.fun(Words, Numbers))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      zerosOf <- tools.constant(Zeros, Type.fun(Numbers, Words))
      marker <- tools.word(spell("."))
      stem <- tools.word(spell("/f"))
      potentialConcat <- facts.get(PotentialConcat).toRight(MissingDefinition(PotentialConcat))
      runPotential <- facts.get(RunPotential).toRight(MissingDefinition(RunPotential))
      emptyLeft <- concatenation.fact(Concatenation.EmptyLeft).map(atNumbers)
      triangleAtZero <- numbering.fact(Numbering.TriangleAtZero)
      triangleAtSuccessor <- numbering.fact(Numbering.TriangleAtSuccessor)

      target <- statement(tools.theory, tools.notation, PotentialOfFamily)
      index = Conv.freshVariable("j", Numbers, Term.freeVariables(target))
      atIndex <- LogicError.lift(Term.app(zerosOf, index))
      prefix <- LogicError.lift(Term.appAll(concat, List(stem, atIndex)))

      split <- rules.specAll(potentialConcat, List(prefix, marker))
      value <- rightOf(split)
      tail <- value match {
        case App(App(_, _), sum) => Right(sum)
        case other => Left(NotOfForm("the measure of two blocks", other))
      }
      summand <- tail match {
        case App(App(_, function), _) => Right(function)
        case other => Left(NotOfForm("a sum over a bound", other))
      }
      evaluated <- sumOverPositions(tools, summand, spell("."), conditional, conditionalFalse)
      atThisIndex <- rules.spec(index, stemPotential)
      folded <- foldedSum(tools, Vector(atThisIndex), evaluated, value)
      shaped <- Conv.trans(split, folded)
      familyPotential <- rules.gen(index, shaped)
      _ <-
        if (familyPotential.conclusion == target) Right(())
        else Left(NotOfForm(s"$PotentialOfFamily as it is written", familyPotential.conclusion))

      // The closed form read at one index, against a statement written by hand. Both sides are
      // reduced by rewriting rather than by a second derivation, so what this compares is the
      // family's own equation with a word and a number a reader checks by eye.
      atOne <- statement(tools.theory, tools.notation, FamilyAtOne)
      one <- tools.numeral(1)
      instanceAtOne <- rules.spec(one, familyPotential)
      shapes <- unfoldingRules(
        tools.logic,
        Vector(zerosAtSuccessor, zerosAtZero, emptyLeft, triangleAtSuccessor, triangleAtZero,
          tools.numbers.zeroPlus)
      )
      sidesAtOne <- Term
        .destEq(instanceAtOne.conclusion)
        .toRight(NotOfForm("an equation", instanceAtOne.conclusion))
      wordReduced <- Rewrite.rewrite(shapes, sidesAtOne._1)
      valueReduced <- Rewrite.rewrite(shapes, sidesAtOne._2)
      readAtOne <- Conv
        .sym(wordReduced)
        .flatMap(Conv.trans(_, instanceAtOne))
        .flatMap(Conv.trans(_, valueReduced))
      _ <-
        if (readAtOne.conclusion == atOne) Right(())
        else Left(NotOfForm(s"$FamilyAtOne as it is written", readAtOne.conclusion))

      bound <- statement(tools.theory, tools.notation, FamilyBounded)
      subject = Conv.freshVariable("j", Numbers, Term.freeVariables(bound))
      atSubject <- LogicError.lift(Term.app(zerosOf, subject))
      family <- LogicError
        .lift(Term.appAll(concat, List(stem, atSubject)))
        .flatMap(front => LogicError.lift(Term.appAll(concat, List(front, marker))))
      atMost <- LogicError.lift(tools.theory.constant(Peano.NonStrictOrder, OrderType))
      instance <- rules.spec(family, runPotential)
      closedForm <- rules.spec(subject, familyPotential)
      closed <- underEveryReach(logic, atMost, instance, closedForm)
      result <- rules.genAll(closed, List(subject))
      _ <-
        if (result.conclusion == bound) Right(())
        else Left(NotOfForm(s"$FamilyBounded as it is written", result.conclusion))
    } yield (familyPotential, readAtOne, result)
  }

  /**
   * A measure of two blocks with the second one's sum evaluated and everything folded.
   *
   * [[normalisedMeasure]]'s manoeuvre, at a caller whose offset is a term rather than a written-out
   * word's length: the evaluated sum is stated at `NUM_SUM f (WORD_LENGTH <word>)`, the rewriting
   * below normalises that bound and the summand with it before anything else fires, so the equation
   * as it comes back never matches. It is restated against **the same rules the pass below uses**,
   * which is the half that was wrong first: restated against a smaller set, the equation is about a
   * summand the outer pass has already rewritten past, and here the extra rule is the one that says
   * how long the first block is.
   */
  private def foldedSum(
    tools: Concrete,
    extra: Vector[Kernel.Thm],
    evaluated: Kernel.Thm,
    value: Term
  ): Either[LogicError, Kernel.Thm] =
    for {
      preparation <- unfoldingRules(tools.logic, extra)
      ambient = preparation ++ tools.lengths ++ tools.identities
      atNumeral <- leftOf(evaluated).flatMap(Rewrite.rewrite(ambient, _))
      restated <- Conv.sym(atNumeral).flatMap(Conv.trans(_, evaluated))
      sum <- unfoldingRules(tools.logic, Vector(restated))
      folded <- Rewrite.rewrite(sum ++ ambient, value)
    } yield folded

  /** `|- !q. REACH ... x q ==> c <= ...` from the same with `S2_PHI x` there and `|- S2_PHI x = c`. */
  private def underEveryReach(
    logic: Logic,
    atMost: Term,
    quantified: Kernel.Thm,
    closedForm: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      predicate <- logic
        .destForallPredicate(quantified.conclusion)
        .toRight(NotOfForm("a claim about every reach", quantified.conclusion))
      domain <- Type
        .destFun(Term.typeOf(predicate))
        .map(_._1)
        .toRight(NotOfForm("a predicate", predicate))
      witness = Conv.freshVariable(
        "q",
        domain,
        Term.freeVariables(quantified.conclusion) ++ Term.freeVariables(closedForm.conclusion)
      )
      opened <- rules.spec(witness, quantified)
      parts <- logic
        .destImp(opened.conclusion)
        .toRight(NotOfForm("an implication", opened.conclusion))
      (premiseTerm, conclusionTerm) = parts
      premise <- LogicError.lift(Kernel.assume(premiseTerm))
      held <- rules.mp(opened, premise)
      other <- conclusionTerm match {
        case App(App(_, _), right) => Right(right)
        case other => Left(NotOfForm("an order statement", other))
      }
      reversed <- Conv.sym(closedForm)
      carried <- carryLeft(atMost, reversed, other, held)
      discharged <- rules.disch(premiseTerm, carried)
      result <- rules.gen(witness, discharged)
    } yield result
  }

  /** What the word is known to be, which is two facts everywhere below. */
  private final case class Class(anchored: Kernel.Thm, marked: Kernel.Thm)

  /**
   * A commutation clause of [[PotentialPlainStep]], closed by building the counted step it denies.
   *
   * The four witnesses the plain step handed over are the same four a counted step wants, and the
   * rule at this clause is one of the six, so the existential goes back together and the hypothesis
   * refuses it. Nothing here is about the measure.
   */
  private def refusedAsCounted(
    tools: Concrete,
    step: Step,
    entry: Rule,
    leftEquation: Kernel.Thm,
    rightEquation: Kernel.Thm,
    subjectEquation: Kernel.Thm,
    resultEquation: Kernel.Thm,
    countedDefinition: Kernel.Thm,
    countedOpened: Kernel.Thm,
    notCounted: Kernel.Thm,
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      position <- CountedRules
        .indexWhere(_.label == entry.label) match {
        case -1 => Left(NotOfForm(s"a counted rule named ${entry.label}", conclusion))
        case found => Right(found)
      }
      clauses <- Conv.unfold(countedDefinition, List(step.left, step.right)).flatMap(rightOf)
      pair <- rules.conjIntro(leftEquation, rightEquation)
      asClause <- intoDisjunction(logic, clauses, position, CountedRules.size, pair)
      countedRule <- Conv
        .unfold(countedDefinition, List(step.left, step.right))
        .flatMap(Conv.sym)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, asClause)))

      pairedBody <- rules.conjIntro(subjectEquation, resultEquation).flatMap(rules.conjIntro(countedRule, _))
      quantified <- rightOf(countedOpened)
      existential <- existsAll(
        logic,
        quantified,
        List(step.front, step.left, step.right, step.tail),
        pairedBody
      )
      countedStep <- Conv
        .sym(countedOpened)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, existential)))
      absurd <- rules.notElim(notCounted, countedStep)
      result <- rules.falsityElim(conclusion, absurd)
    } yield result
  }

  /** A proof of one disjunct, placed at its position in a disjunction of `size` clauses. */
  // `$size clauses` never says one, for the reason `${Rules.size} clauses` further down never
  // does: this method is private and its one caller passes `CountedRules.size`, which is the six
  // commuting rules read off the table. The table is what `collatz@8b991e5` generates, and a
  // rewriting system of one rule is not the system this file is about.
  private def intoDisjunction(
    logic: Logic,
    disjunction: Term,
    position: Int,
    size: Int,
    proof: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    def walk(current: Term, index: Int): Either[LogicError, Kernel.Thm] =
      logic.destDisj(current) match {
        case None =>
          if (index == size - 1) Right(proof)
          else Left(NotOfForm(s"$size clauses", current))

        case Some((here, others)) =>
          if (index == position) rules.disjIntro1(others, proof)
          else walk(others, index + 1).flatMap(rules.disjIntro2(here, _))
      }

    walk(disjunction, 0)
  }

  /** `?x1 ... xn. body` from a proof of the body at the given witnesses, innermost first. */
  private def existsAll(
    logic: Logic,
    statement: Term,
    witnesses: List[Term],
    proof: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    witnesses match {
      case Nil =>
        if (proof.conclusion == statement) Right(proof)
        else Left(NotOfForm("the body as the existential states it", proof.conclusion))

      case witness :: rest =>
        for {
          predicate <- logic
            .destExistsPredicate(statement)
            .toRight(NotOfForm("an existential", statement))
          applied <- LogicError.lift(Term.app(predicate, witness))
          inner <- Conv.betaRoot(applied).flatMap(rightOf)
          below <- existsAll(logic, inner, rest, proof)
          result <- logic.rules.existsIntro(predicate, witness, below)
        } yield result
    }

  /** What a step handed over: the four witnesses and the two words they decompose. */
  private final case class Step(
    front: Term,
    left: Term,
    right: Term,
    tail: Term,
    subject: Term,
    result: Term
  )

  /** The constants and the lemma a measure comparison reads its terms through. */
  private final case class Readers(
    potential: Term,
    concat: Term,
    plus: Term,
    successorOf: Term,
    blocks: Kernel.Thm
  )

  /**
   * A claim proved at every clause of a disjunction, which is [[overEveryRule]]'s walk without the
   * statement around it.
   *
   * `$expected clauses` is not a count that reaches one: this method is private and its three
   * callers pass `Rules.size` or `CountedRules.size`, eleven and six, both read off the table
   * rather than written. `intoDisjunction` above carries the same argument for its own `size`.
   */
  private def overClauses(
    logic: Logic,
    disjunction: Kernel.Thm,
    expected: Int
  )(
    at: (Int, Kernel.Thm, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    def clause(position: Int, term: Term): Either[LogicError, Kernel.Thm] =
      for {
        assumed <- LogicError.lift(Kernel.assume(term))
        leftEquation <- rules.conjElim1(assumed)
        rightEquation <- rules.conjElim2(assumed)
        proved <- at(position, leftEquation, rightEquation)
      } yield proved

    def walk(position: Int, term: Term): Either[LogicError, Kernel.Thm] =
      logic.destDisj(term) match {
        case None =>
          if (position == expected - 1) clause(position, term)
          else Left(NotOfForm(s"$expected clauses", term))

        case Some((here, others)) =>
          for {
            first <- clause(position, here)
            rest <- walk(position + 1, others)
            assumed <- LogicError.lift(Kernel.assume(term))
            split <- rules.disjElim(assumed, first, rest)
          } yield split
      }

    walk(0, disjunction.conclusion).flatMap(proved => rules.proveHyp(disjunction, proved))
  }

  /**
   * [[PotentialBlocks]]: the measure of a context, a block and a tail, by [[PotentialConcat]] twice.
   *
   * The outer application splits the word where the tail begins and the inner one splits what is
   * left where the block begins, which is the order the left-nesting forces: `(x m) y` is a
   * concatenation whose first half is itself one, so the outer split is the only one that applies
   * to the term as it stands.
   */
  private def potentialOfBlocks(
    logic: Logic,
    theory: Theory,
    potentialConcat: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val context = Term.variable("x", Words)
    val block = Term.variable("m", Words)
    val tail = Term.variable("y", Words)

    for {
      concat <- LogicError.lift(theory.constant(Concatenation.Name, ConcatType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, BinaryNumbers))
      joined <- LogicError.lift(Term.appAll(concat, List(context, block)))

      outer <- rules.specAll(potentialConcat, List(joined, tail))
      inner <- rules.specAll(potentialConcat, List(context, block))

      sides <- Term.destEq(outer.conclusion).toRight(NotOfForm("an equation", outer.conclusion))
      (_, sum) = sides
      shifted <- sum match {
        case App(App(_, _), second) => Right(second)
        case other => Left(NotOfForm("a sum of two blocks", other))
      }
      readBack <- Conv.apTerm(plus, inner).flatMap(Conv.apThm(_, shifted))

      whole <- Conv.trans(outer, readBack)
      result <- rules.genAll(whole, List(context, block, tail))
    } yield result
  }

  /** [[PotentialAtAWord]]: the measure of a written-out word, read off its own definition. */
  private def potentialOfWord(
    tools: Concrete,
    letters: Vector[String],
    definitions: Map[String, Kernel.Thm],
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      subject <- tools.word(letters)
      potentialDefinition <- definitions.get(Potential).toRight(MissingDefinition(Potential))
      opened <- Conv.unfold(potentialDefinition, List(subject))
      body <- rightOf(opened)
      summand <- body match {
        case App(App(_, function), _) => Right(function)
        case other => Left(NotOfForm("a sum over a bound", other))
      }
      evaluated <- sumOverPositions(tools, summand, letters, conditional, conditionalFalse)
      result <- Conv.trans(opened, evaluated)
    } yield result

  /**
   * [[PotentialConcat]]: the measure over a word split in two, by the tally at its own weight.
   *
   * Four steps and the middle two are the point. `WORD_CONCAT_TALLY` is stated for a weight
   * `f : num -> 'a -> num` and a summand `\i. f i (WORD_NTH w i)`, so what this specialises it at
   * is the measure's own weight written out, `\i. \a. COND (a < 3) (i - 1) 0`; what comes back
   * carries a redex at every one of the three summands, and `Conv.normaliseSides` is what contracts
   * them. Then the two ends are read back as `S2_PHI`, which is its definition used in the
   * direction nothing else here needs it.
   *
   * The third summand is left as it comes out of the tally rather than being turned into anything:
   * it is not `S2_PHI v` and cannot be, which is what the published statement is for.
   */
  private def potentialSplits(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    concatenation: Concatenation,
    potentialDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val v = Term.variable("v", Words)

    for {
      tally <- concatenation.fact(Concatenation.Tally).map(atNumbers)
      weight <- Parser.term(
        theory,
        notation,
        "\\i:num. \\a:num. COND (a < 3) (NUM_SUB i 1) 0",
        Type.fun(Numbers, Type.fun(Numbers, Numbers))
      )
      concatConstant <- LogicError.lift(theory.constant(Concatenation.Name, ConcatType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, BinaryNumbers))
      joined <- LogicError.lift(Term.appAll(concatConstant, List(u, v)))

      instance <- rules.specAll(tally, List(weight, u, v)).flatMap(Conv.normaliseSides)

      phiJoined <- Conv.unfold(potentialDefinition, List(joined))
      phiU <- Conv.unfold(potentialDefinition, List(u))

      sides <- Term.destEq(instance.conclusion).toRight(NotOfForm("an equation", instance.conclusion))
      (_, sum) = sides
      shifted <- sum match {
        case App(App(_, _), second) => Right(second)
        case other => Left(NotOfForm("a sum of two blocks", other))
      }
      readBack <- Conv
        .sym(phiU)
        .flatMap(equation => Conv.apTerm(plus, equation))
        .flatMap(Conv.apThm(_, shifted))

      body <- Conv.trans(instance, readBack)
      whole <- Conv.trans(phiJoined, body)
      result <- rules.genAll(whole, List(u, v))
    } yield result
  }

  /**
   * [[AnchoredConcat]]: an anchored word is an anchored block and a head-free block.
   *
   * [[MarkedConcat]] read from the other end, and the two differ in one respect that decides which
   * is the harder proof. The marker this one is about sits at position **zero**, which is a numeral
   * and not `|w| - 1`, so nothing here has to know that a length is a successor before it can name
   * a position: there is no case split on the length at all, and the hypothesis `0 < |u|` is spent
   * twice rather than being what makes the statement sayable.
   *
   * Where it is spent is worth naming, because it is the whole content of the guard. Left to right,
   * it is what carries `0 < |u v|`: an anchored word has a first letter, and `u` is where that
   * letter is. Right to left, it is what says the letters of `v` sit at positions above zero in
   * `u v`, which is what lets the inner claim of `S2_ANCHORED`, stated about those positions only,
   * say anything about `v` at all.
   */
  private def anchoredSplits(
    logic: Logic,
    theory: Theory,
    classical: Classical,
    concatenation: Concatenation,
    numbers: Arithmetic,
    headFreeDefinition: Kernel.Thm,
    anchoredDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val v = Term.variable("v", Words)

    for {
      length <- concatenation.fact(Concatenation.Length).map(atNumbers)
      nthLeft <- concatenation.fact(Concatenation.NthLeft).map(atNumbers)
      nthRight <- concatenation.fact(Concatenation.NthRight).map(atNumbers)

      concatConstant <- LogicError.lift(theory.constant(Concatenation.Name, ConcatType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, LengthType))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, NthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, OrderType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, BinaryNumbers))
      minus <- LogicError.lift(theory.constant(Peano.Subtraction, BinaryNumbers))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      marker <- LogicError.lift(theory.constant(Head, Numbers))

      joined <- LogicError.lift(Term.appAll(concatConstant, List(u, v)))
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))
      sizeU <- LogicError.lift(Term.app(lengthConstant, u))
      sizeV <- LogicError.lift(Term.app(lengthConstant, v))
      total <- LogicError.lift(Term.appAll(plus, List(sizeU, sizeV)))
      lengths <- rules.specAll(length, List(u, v))
      widened <- Conv.sym(lengths)

      positiveTerm <- LogicError.lift(Term.appAll(strictOrder, List(zero, sizeU)))
      positive <- LogicError.lift(Kernel.assume(positiveTerm))

      // `0 < |u| <= |u| + |v|`, which is the guard reaching the whole word's own first letter.
      atMostTotal <- rules.specAll(numbers.atMostSum, List(sizeU, sizeV))
      positiveSum <- rules
        .conjIntro(positive, atMostTotal)
        .flatMap(pair =>
          rules.specAll(numbers.belowThenAtMost, List(zero, sizeU, total)).flatMap(rules.mp(_, pair))
        )
      positiveJoined <- carryRight(strictOrder, zero, widened, positiveSum)

      openedJoined <- Conv.unfold(anchoredDefinition, List(joined))
      openedU <- Conv.unfold(anchoredDefinition, List(u))
      openedV <- Conv.unfold(headFreeDefinition, List(v))
      claimJoined <- leftOf(openedJoined)
      claimU <- leftOf(openedU)
      claimV <- leftOf(openedV)
      both <- logic.mkConj(claimU, claimV)

      partsJoined <- rightOf(openedJoined).flatMap(threeParts(logic, _))
      (_, atZeroJoinedTerm, everyJoinedTerm) = partsJoined
      partsU <- rightOf(openedU).flatMap(threeParts(logic, _))
      (_, _, everyUTerm) = partsU
      everyVTerm <- rightOf(openedV)

      atZero <- rules.specAll(nthLeft, List(u, v, zero)).flatMap(rules.mp(_, positive))

      /* left to right: the whole word is anchored, so the first block is and the second is free */
      assumedJoined <- LogicError.lift(Kernel.assume(claimJoined))
      heldJoined <- LogicError.lift(Kernel.eqMp(openedJoined, assumedJoined))
      restJoined <- rules.conjElim2(heldJoined)
      atZeroJoined <- rules.conjElim1(restJoined)
      everyJoined <- rules.conjElim2(restJoined)

      atZeroU <- Conv.sym(atZero).flatMap(Conv.trans(_, atZeroJoined))

      onU <- atEveryIndexOfBlock(logic, everyUTerm) { (i, above, below) =>
        for {
          atMostU <- rules.specAll(numbers.atMostSum, List(sizeU, sizeV))
          pair <- rules.conjIntro(below, atMostU)
          belowSum <- rules
            .specAll(numbers.belowThenAtMost, List(i, sizeU, total))
            .flatMap(rules.mp(_, pair))
          inJoined <- carryRight(strictOrder, i, widened, belowSum)
          guard <- rules.conjIntro(above, inJoined)
          notMarker <- rules.spec(i, everyJoined).flatMap(rules.mp(_, guard))
          entry <- rules.specAll(nthLeft, List(u, v, i)).flatMap(rules.mp(_, below))
          result <- carryLeftNegated(logic, entry, marker, notMarker)
        } yield result
      }

      onV <- underTheBound(logic, everyVTerm) { (j, below) =>
        for {
          shifted <- LogicError.lift(Term.appAll(plus, List(sizeU, j)))
          atMostShifted <- rules.specAll(numbers.atMostSum, List(sizeU, j))
          shiftedPositive <- rules
            .conjIntro(positive, atMostShifted)
            .flatMap(pair =>
              rules
                .specAll(numbers.belowThenAtMost, List(zero, sizeU, shifted))
                .flatMap(rules.mp(_, pair))
            )
          belowSum <- rules
            .specAll(numbers.addStrictlyMonotone, List(sizeU, j, sizeV))
            .flatMap(rules.mp(_, below))
          inJoined <- carryRight(strictOrder, shifted, widened, belowSum)
          guard <- rules.conjIntro(shiftedPositive, inJoined)
          notMarker <- rules.spec(shifted, everyJoined).flatMap(rules.mp(_, guard))
          entry <- rules.specAll(nthRight, List(u, v, j)).flatMap(rules.mp(_, below))
          result <- carryLeftNegated(logic, entry, marker, notMarker)
        } yield result
      }

      anchoredU <- rules
        .conjIntro(atZeroU, onU)
        .flatMap(rules.conjIntro(positive, _))
        .flatMap(held => Conv.sym(openedU).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, held))))
      headFreeV <- Conv.sym(openedV).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, onV)))
      forward <- rules.conjIntro(anchoredU, headFreeV)

      /* right to left: an anchored block in front of a head-free one is an anchored word */
      assumedBoth <- LogicError.lift(Kernel.assume(both))
      fromU <- rules
        .conjElim1(assumedBoth)
        .flatMap(held => LogicError.lift(Kernel.eqMp(openedU, held)))
      fromV <- rules
        .conjElim2(assumedBoth)
        .flatMap(held => LogicError.lift(Kernel.eqMp(openedV, held)))
      restU <- rules.conjElim2(fromU)
      atZeroFromU <- rules.conjElim1(restU)
      everyFromU <- rules.conjElim2(restU)

      atZeroWhole <- Conv.trans(atZero, atZeroFromU)
      _ <-
        if (atZeroWhole.conclusion == atZeroJoinedTerm) Right(())
        else Left(NotOfForm("the marker at the first letter as it is written", atZeroWhole.conclusion))

      onJoined <- atEveryIndexOfBlock(logic, everyJoinedTerm) { (i, above, below) =>
        for {
          inSum <- carryRight(strictOrder, i, lengths, below)
          belowU <- LogicError.lift(Term.appAll(strictOrder, List(i, sizeU)))

          insideU <- LogicError.lift(Kernel.assume(belowU))
          entryLeft <- rules.specAll(nthLeft, List(u, v, i)).flatMap(rules.mp(_, insideU))
          guard <- rules.conjIntro(above, insideU)
          notU <- rules.spec(i, everyFromU).flatMap(rules.mp(_, guard))
          firstCase <- Conv
            .sym(entryLeft)
            .flatMap(equation => carryLeftNegated(logic, equation, marker, notU))

          notInsideU <- logic.mkNot(belowU)
          assumedOutside <- LogicError.lift(Kernel.assume(notInsideU))
          atLeast <- rules
            .specAll(numbers.atMostFromNotBelow, List(i, sizeU))
            .flatMap(rules.mp(_, assumedOutside))
          difference <- LogicError.lift(Term.appAll(minus, List(i, sizeU)))
          restored <- rules
            .specAll(numbers.minusThenPlus, List(i, sizeU))
            .flatMap(rules.mp(_, atLeast))
          commuted <- rules.specAll(numbers.addCommutative, List(difference, sizeU))
          placed <- Conv.sym(commuted).flatMap(Conv.trans(_, restored))
          sumBelow <- carryLeft(strictOrder, placed, total, inSum)
          inV <- rules
            .specAll(numbers.addCancelsStrictOrder, List(sizeU, difference, sizeV))
            .flatMap(rules.mp(_, sumBelow))
          entryRight <- rules
            .specAll(nthRight, List(u, v, difference))
            .flatMap(rules.mp(_, inV))
          atIndex <- Conv
            .apTerm(nthOfJoined, placed)
            .flatMap(Conv.sym)
            .flatMap(Conv.trans(_, entryRight))
          notV <- rules.spec(difference, fromV).flatMap(rules.mp(_, inV))
          secondCase <- Conv
            .sym(atIndex)
            .flatMap(equation => carryLeftNegated(logic, equation, marker, notV))

          cases <- classical.excludedMiddleAt(belowU)
          settled <- rules.disjElim(cases, firstCase, secondCase)
        } yield settled
      }

      backward <- rules
        .conjIntro(atZeroWhole, onJoined)
        .flatMap(rules.conjIntro(positiveJoined, _))
        .flatMap(held =>
          Conv.sym(openedJoined).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, held)))
        )

      equated = Kernel.deductAntisym(backward, forward)
      discharged <- rules.disch(positiveTerm, equated)
      result <- rules.genAll(discharged, List(u, v))
    } yield result
  }

  /**
   * `|- !i. 0 < i /\ i < b ==> c`, proved by assuming both halves and handing them over.
   *
   * [[underTheBound]] where the guard is the conjunction `S2_ANCHORED`'s inner claim carries. The
   * two halves go to the caller separately because they answer different questions: the bound is
   * what places the index inside a block, and `0 < i` is what says the position is not the one the
   * marker is required at.
   */
  private def atEveryIndexOfBlock(
    logic: Logic,
    statement: Term
  )(
    step: (FVar, Kernel.Thm, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    underTheBound(logic, statement) { (index, guard) =>
      for {
        above <- rules.conjElim1(guard)
        below <- rules.conjElim2(guard)
        result <- step(index, above, below)
      } yield result
    }
  }

  /** The words, the readers and the sizes one proof about a split needs, gathered. */
  private final case class Split(
    u: Term,
    v: Term,
    nthOfJoined: Term,
    nthOfV: Term,
    sizeU: Term,
    sizeV: Term,
    total: Term,
    predecessor: Term
  )

  /** [[MarkedConcat]] with the tail's length known to be `SUC k`, which is where it is provable. */
  private def markedSplitsAtSuccessor(
    logic: Logic,
    theory: Theory,
    classical: Classical,
    numbers: Arithmetic,
    words: Split,
    constants: (Term, Term, Term, Term),
    joins: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    opened: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    premises: (Kernel.Thm, Kernel.Thm)
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    import words.{u, v, nthOfJoined, nthOfV, sizeU, sizeV, total, predecessor}
    val (strictOrder, plus, minus, marker) = constants
    val (lengths, nthLeft, nthRight) = joins
    val (openedJoined, openedV, openedU) = opened
    val (positive, size) = premises

    for {
      claimJoined <- leftOf(openedJoined)
      claimV <- leftOf(openedV)
      claimU <- leftOf(openedU)
      both <- logic.mkConj(claimU, claimV)

      /* the two positions the statement reads, placed against the successor */
      markerV <- lastPosition(logic, theory, numbers, size, predecessor)
      shifted <- LogicError.lift(Term.appAll(plus, List(sizeU, predecessor)))
      partialU <- LogicError.lift(Term.app(plus, sizeU))
      sumIsSuccessor <- Conv
        .apTerm(partialU, size)
        .flatMap(step =>
          rules.specAll(numbers.addAtSuccessor, List(sizeU, predecessor)).flatMap(Conv.trans(step, _))
        )
      joinedIsSuccessor <- Conv.trans(lengths, sumIsSuccessor)
      markerJoined <- lastPosition(logic, theory, numbers, joinedIsSuccessor, shifted)

      /* `k < |v|`, which every reading of the tail needs */
      belowSpelled <- rules.spec(predecessor, numbers.belowSuccessor)
      inTail <- Conv
        .sym(size)
        .flatMap(equation => carryRight(strictOrder, predecessor, equation, belowSpelled))

      entryAtMarker <- rules
        .specAll(nthRight, List(u, v, predecessor))
        .flatMap(rules.mp(_, inTail))

      everyUTerm <- rightOf(openedU)
      markedJoinedTerm <- rightOf(openedJoined)
      markedVTerm <- rightOf(openedV)
      joinedParts <- threeParts(logic, markedJoinedTerm)
      (_, _, everyJoinedTerm) = joinedParts
      tailParts <- threeParts(logic, markedVTerm)
      (_, _, everyTailTerm) = tailParts

      /* left to right: the whole word is marked, so the tail is and the front is tail-free */
      assumedJoined <- LogicError.lift(Kernel.assume(claimJoined))
      markedJoined <- LogicError.lift(Kernel.eqMp(openedJoined, assumedJoined))
      restJoined <- rules.conjElim2(markedJoined)
      atMarkerJoined <- rules.conjElim1(restJoined)
      everyJoined <- rules.conjElim2(restJoined)

      atShifted <- Conv
        .apTerm(nthOfJoined, markerJoined)
        .flatMap(Conv.sym)
        .flatMap(Conv.trans(_, atMarkerJoined))
      atTail <- Conv.sym(entryAtMarker).flatMap(Conv.trans(_, atShifted))
      atMarkerTail <- Conv.apTerm(nthOfV, markerV).flatMap(Conv.trans(_, atTail))

      everyTail <- underTheBound(logic, everyTailTerm) { (i, below) =>
        for {
          belowPredecessor <- carryRight(strictOrder, i, markerV, below)
          pair <- rules.conjIntro(belowPredecessor, inTail)
          belowTail <- rules
            .specAll(numbers.strictTransitive, List(i, predecessor, sizeV))
            .flatMap(rules.mp(_, pair))
          entry <- rules.specAll(nthRight, List(u, v, i)).flatMap(rules.mp(_, belowTail))
          moved <- rules
            .specAll(numbers.addStrictlyMonotone, List(sizeU, i, predecessor))
            .flatMap(rules.mp(_, belowPredecessor))
          atIndex <- LogicError.lift(Term.appAll(plus, List(sizeU, i)))
          inRange <- Conv
            .sym(markerJoined)
            .flatMap(equation => carryRight(strictOrder, atIndex, equation, moved))
          notMarker <- rules.spec(atIndex, everyJoined).flatMap(rules.mp(_, inRange))
          result <- carryLeftNegated(logic, entry, marker, notMarker)
        } yield result
      }

      markedTail <- rules
        .conjIntro(atMarkerTail, everyTail)
        .flatMap(rules.conjIntro(positive, _))
        .flatMap(held => Conv.sym(openedV).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, held))))

      everyFront <- underTheBound(logic, everyUTerm) { (i, below) =>
        for {
          atMost <- rules.specAll(numbers.atMostSum, List(sizeU, predecessor))
          pair <- rules.conjIntro(below, atMost)
          belowShifted <- rules
            .specAll(numbers.belowThenAtMost, List(i, sizeU, shifted))
            .flatMap(rules.mp(_, pair))
          inRange <- Conv
            .sym(markerJoined)
            .flatMap(equation => carryRight(strictOrder, i, equation, belowShifted))
          notMarker <- rules.spec(i, everyJoined).flatMap(rules.mp(_, inRange))
          entry <- rules.specAll(nthLeft, List(u, v, i)).flatMap(rules.mp(_, below))
          result <- carryLeftNegated(logic, entry, marker, notMarker)
        } yield result
      }

      tailFreeFront <- Conv
        .sym(openedU)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, everyFront)))
      backward <- rules.conjIntro(tailFreeFront, markedTail)

      /* right to left: a tail-free front and a marked tail make a marked word */
      assumedBoth <- LogicError.lift(Kernel.assume(both))
      fromFront <- rules
        .conjElim1(assumedBoth)
        .flatMap(held => LogicError.lift(Kernel.eqMp(openedU, held)))
      fromTail <- rules
        .conjElim2(assumedBoth)
        .flatMap(held => LogicError.lift(Kernel.eqMp(openedV, held)))
      restTail <- rules.conjElim2(fromTail)
      atMarkerOfTail <- rules.conjElim1(restTail)
      everyOfTail <- rules.conjElim2(restTail)

      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      atMost <- LogicError.lift(theory.constant(Peano.NonStrictOrder, OrderType))
      commuted <- rules.specAll(numbers.addCommutative, List(sizeV, sizeU))
      atMostTotal <- rules
        .specAll(numbers.atMostSum, List(sizeV, sizeU))
        .flatMap(fact => carryRight(atMost, sizeV, commuted, fact))
      positiveSum <- rules
        .conjIntro(positive, atMostTotal)
        .flatMap(pair =>
          rules
            .specAll(numbers.belowThenAtMost, List(zero, sizeV, total))
            .flatMap(rules.mp(_, pair))
        )
      positiveJoined <- Conv
        .sym(lengths)
        .flatMap(equation => carryRight(strictOrder, zero, equation, positiveSum))

      atTailMarker <- Conv.apTerm(nthOfV, markerV).flatMap(Conv.sym).flatMap(Conv.trans(_, atMarkerOfTail))
      atJoinedMarker <- Conv
        .trans(entryAtMarker, atTailMarker)
        .flatMap(step => Conv.apTerm(nthOfJoined, markerJoined).flatMap(Conv.trans(_, step)))

      everyOfJoined <- underTheBound(logic, everyJoinedTerm) { (i, below) =>
        for {
          belowShifted <- carryRight(strictOrder, i, markerJoined, below)
          belowU <- LogicError.lift(Term.appAll(strictOrder, List(i, sizeU)))

          insideU <- LogicError.lift(Kernel.assume(belowU))
          entryLeft <- rules.specAll(nthLeft, List(u, v, i)).flatMap(rules.mp(_, insideU))
          notFront <- rules.spec(i, fromFront).flatMap(rules.mp(_, insideU))
          firstCase <- Conv
            .sym(entryLeft)
            .flatMap(equation => carryLeftNegated(logic, equation, marker, notFront))

          notInsideU <- logic.mkNot(belowU)
          assumedOutside <- LogicError.lift(Kernel.assume(notInsideU))
          atLeast <- rules
            .specAll(numbers.atMostFromNotBelow, List(i, sizeU))
            .flatMap(rules.mp(_, assumedOutside))
          difference <- LogicError.lift(Term.appAll(minus, List(i, sizeU)))
          restored <- rules
            .specAll(numbers.minusThenPlus, List(i, sizeU))
            .flatMap(rules.mp(_, atLeast))
          swapped <- rules.specAll(numbers.addCommutative, List(difference, sizeU))
          placed <- Conv.sym(swapped).flatMap(Conv.trans(_, restored))
          sumBelow <- carryLeft(strictOrder, placed, shifted, belowShifted)
          belowPredecessor <- rules
            .specAll(numbers.addCancelsStrictOrder, List(sizeU, difference, predecessor))
            .flatMap(rules.mp(_, sumBelow))
          pair <- rules.conjIntro(belowPredecessor, inTail)
          belowTail <- rules
            .specAll(numbers.strictTransitive, List(difference, predecessor, sizeV))
            .flatMap(rules.mp(_, pair))
          entryRight <- rules
            .specAll(nthRight, List(u, v, difference))
            .flatMap(rules.mp(_, belowTail))
          atIndex <- Conv
            .apTerm(nthOfJoined, placed)
            .flatMap(Conv.sym)
            .flatMap(Conv.trans(_, entryRight))
          belowMarker <- Conv
            .sym(markerV)
            .flatMap(equation => carryRight(strictOrder, difference, equation, belowPredecessor))
          notTail <- rules.spec(difference, everyOfTail).flatMap(rules.mp(_, belowMarker))
          secondCase <- Conv
            .sym(atIndex)
            .flatMap(equation => carryLeftNegated(logic, equation, marker, notTail))

          split <- classical.excludedMiddleAt(belowU)
          settled <- rules.disjElim(split, firstCase, secondCase)
        } yield settled
      }

      forward <- rules
        .conjIntro(atJoinedMarker, everyOfJoined)
        .flatMap(rules.conjIntro(positiveJoined, _))
        .flatMap(held => Conv.sym(openedJoined).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, held))))

      result = Kernel.deductAntisym(forward, backward)
    } yield result
  }

  /** `p /\ (q /\ r)` taken apart, which is the shape [[MarkedBody]] has. */
  private def threeParts(logic: Logic, term: Term): Either[LogicError, (Term, Term, Term)] =
    for {
      outer <- logic.destConj(term).toRight(NotOfForm("a conjunction", term))
      (first, rest) = outer
      inner <- logic.destConj(rest).toRight(NotOfForm("a conjunction", rest))
      (second, third) = inner
    } yield (first, second, third)

  /* ------------------------------------------------------------------ concrete words */

  /** `|- S2_ANCHORED <word>`, for a word whose first letter is the head marker and whose others are not. */
  private def anchoredWord(
    tools: Concrete,
    letters: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      subject <- tools.word(letters)
      definition <- tools.anchoredDefinition
      opened <- Conv.unfold(definition, List(subject))
      statement <- rightOf(opened)
      parts <- threeParts(tools.logic, statement)
      (positiveTerm, atMarkerTerm, everyTerm) = parts

      size <- lengthIsNumeral(tools, letters)
      order <- tools.strictOrder
      zero <- tools.zero
      predecessor <- tools.numeral(letters.size - 1)

      positive <- rules
        .spec(predecessor, tools.numbers.successorPositive)
        .flatMap(fact => Conv.sym(size).flatMap(carryRight(order, zero, _, fact)))
      _ <-
        if (positive.conclusion == positiveTerm) Right(())
        else Left(NotOfForm("the positive length as it is written", positive.conclusion))

      atMarker <- letterAt(tools, letters, 0)
      _ <-
        if (atMarker.conclusion == atMarkerTerm) Right(())
        else Left(NotOfForm("the marker at the first letter as it is written", atMarker.conclusion))

      // The enumeration runs over every position of the word, position zero included, and that one
      // is closed by the guard rather than by a letter: `0 < 0` is false, so what the marker is
      // there never comes up. The other positions are the ordinary refusal.
      every <- atEveryIndexGuarded(tools, everyTerm, size, letters.size) { (above, index, equal) =>
        for {
          position <- positionOf(tools, equal, letters.size)
          held <- above.toRight(NotOfForm("a guard above position zero", everyTerm))
          result <-
            if (position == 0)
              for {
                consequent <- consequentOf(tools.logic, everyTerm, index)
                atZero <- carryRight(order, zero, equal, held)
                none <- rules.spec(zero, tools.numbers.notBelowZero)
                absurd <- rules.notElim(none, atZero)
                anything <- rules.falsityElim(consequent, absurd)
              } yield anything
            else noMarkerAt(tools, letters, position, index, equal, Head)
        } yield result
      }

      held <- rules.conjIntro(atMarker, every).flatMap(rules.conjIntro(positive, _))
      result <- Conv
        .sym(opened)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, held)))
    } yield result
  }

  /** `|- ~(S2_ANCHORED <word>)`, for a word whose first letter is not the head marker. */
  private def notAnchoredWord(
    tools: Concrete,
    letters: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      subject <- tools.word(letters)
      definition <- tools.anchoredDefinition
      opened <- Conv.unfold(definition, List(subject))
      claim <- leftOf(opened)
      assumed <- LogicError.lift(Kernel.assume(claim))
      held <- LogicError.lift(Kernel.eqMp(opened, assumed))
      rest <- rules.conjElim2(held)
      atMarker <- rules.conjElim1(rest)

      entry <- letterAt(tools, letters, 0)
      value <- Conv.sym(entry).flatMap(Conv.trans(_, atMarker))
      apart <- notTheMarker(tools, letters.head, Head)
      absurd <- rules.notElim(apart, value)
      result <- rules.notIntro(claim, absurd)
    } yield result
  }

  /** The consequent of `!i. guard ==> c` at a given index, which is what a vacuous case proves. */
  private def consequentOf(
    logic: Logic,
    statement: Term,
    index: FVar
  ): Either[LogicError, Term] =
    for {
      predicate <- logic
        .destForallPredicate(statement)
        .toRight(NotOfForm("a claim about every index", statement))
      applied <- LogicError.lift(Term.app(predicate, index))
      body <- Conv.betaRoot(applied).flatMap(rightOf)
      parts <- logic.destImp(body).toRight(NotOfForm("an implication under the quantifier", body))
    } yield parts._2

  /**
   * Everything a proof about ONE written-out word reaches for, gathered once for eleven rules.
   *
   * The two rule sets are the reason this is a record and not a parameter list. [[lengths]] turns
   * `WORD_LENGTH` of a concatenation of one-letter words into a numeral in successor form, and
   * [[positions]] is that plus the three facts that take `SUC^n ZERO - 1` down to `SUC^(n-1) ZERO`.
   * The second is **never** applied to a whole proposition: `NUM_ONE_SUC` rewrites every `1`, and
   * three of these eleven rules have the letter `1` in them, so a proposition rewritten with it
   * comes back about a different word. It is applied to the index alone and carried in by
   * congruence, which is the one thing to know before editing anything below.
   */
  private[theories] final case class Concrete(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    numbers: Arithmetic,
    naturals: Natural,
    successor: Successor,
    lengths: Vector[Rewrite.Rule],
    positions: Vector[Rewrite.Rule],
    letters: Vector[Rewrite.Rule],
    identities: Vector[Rewrite.Rule],
    folds: Vector[Rewrite.Rule],
    entryLeft: Kernel.Thm,
    entryRight: Kernel.Thm,
    singletonLength: Kernel.Thm,
    singletonNth: Kernel.Thm,
    tailFreeDefinition: Kernel.Thm,
    headFreeDefinition: Kernel.Thm,
    markedDefinition: Kernel.Thm,
    anchoredDefinitionOf: Kernel.Thm
  ) {

    val rules: Rules = logic.rules

    /**
     * "No letter of this word is that marker", by the marker's own name.
     *
     * The two classes are one construction read at two letters, so what a proof about either needs
     * is the marker and its definition together. A proof that took only the marker would open the
     * wrong definition and fail at the first conversion, which is a refusal a reader has to trace
     * back; this is the pair, and the refusal names the marker instead.
     */
    def freeDefinition(marker: String): Either[LogicError, Kernel.Thm] =
      marker match {
        case Tail => Right(tailFreeDefinition)
        case Head => Right(headFreeDefinition)
        case other => Left(MissingDefinition(other))
      }

    def constant(name: String, ty: Type): Either[LogicError, Term] =
      LogicError.lift(theory.constant(name, ty))

    lazy val zero: Either[LogicError, Term] = constant(Natural.NumberZero, Numbers)

    lazy val successorOf: Either[LogicError, Term] =
      constant(Natural.NumberSuccessor, Type.fun(Numbers, Numbers))

    lazy val strictOrder: Either[LogicError, Term] = constant(Peano.StrictOrder, OrderType)

    lazy val nth: Either[LogicError, Term] = constant(Word.Nth, NthType)

    lazy val lengthOf: Either[LogicError, Term] = constant(Word.Length, LengthType)

    lazy val marker: Either[LogicError, Term] = constant(Tail, Numbers)

    /** The anchored class's own definition, as the two concrete-word proofs reach for it. */
    lazy val anchoredDefinition: Either[LogicError, Kernel.Thm] = Right(anchoredDefinitionOf)

    /** `SUC` applied `count` times to `ZERO`, spelled the way every bound below is. */
    def numeral(count: Int): Either[LogicError, Term] =
      for {
        z <- zero
        suc <- successorOf
        built <- Bounded.numeral(z, suc, count)
      } yield built

    /** The word a rule's letters spell, parsed from the same text the definition is built from. */
    def word(letters: Vector[String]): Either[LogicError, Term] =
      Parser.term(theory, notation, wordText(letters), Words)

    /**
     * One letter, as a term.
     *
     * Parsed rather than fetched from the theory, and that is not a convenience: three of the seven
     * letters are the digits `0`, `1` and `2`, which are **numerals** and not constants of any name.
     * Asking the theory for a constant called `0` is a refusal naming a constant nobody declared,
     * which is what the first version of this file got back.
     */
    def letter(name: String): Either[LogicError, Term] =
      Parser.term(theory, notation, s"($name:num)", Numbers)
  }

  /** `|- ~(a = c)` from `|- c = b` and `|- ~(a = b)`: the equation's RIGHT side replaced. */
  private def carryRightNegated(
    logic: Logic,
    equation: Kernel.Thm,
    left: Term,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      sides <- Term.destEq(equation.conclusion).toRight(NotOfForm("an equation", equation.conclusion))
      equality <- equalityAt(left, sides._1)
      partial <- LogicError.lift(Term.app(equality, left))
      moved <- Conv.apTerm(partial, equation).flatMap(Conv.sym)
      negated <- Conv.apTerm(logic.negation, moved)
      result <- LogicError.lift(Kernel.eqMp(negated, fact))
    } yield result

  /** `|- SUC^j ZERO < SUC^k ZERO` for `j < k`, by walking up one successor at a time. */
  private def numeralBelow(
    tools: Concrete,
    lower: Int,
    upper: Int
  ): Either[LogicError, Kernel.Thm] =
    if (upper <= lower)
      Left(NotOfForm(s"a pair with $lower below it", Term.variable("bound", Numbers)))
    else if (upper == lower + 1)
      tools.numeral(lower).flatMap(tools.rules.spec(_, tools.numbers.belowSuccessor))
    else
      for {
        below <- numeralBelow(tools, lower, upper - 1)
        step <- tools.numeral(upper - 1).flatMap(tools.rules.spec(_, tools.numbers.belowSuccessor))
        pair <- tools.rules.conjIntro(below, step)
        here <- tools.numeral(lower)
        middle <- tools.numeral(upper - 1)
        top <- tools.numeral(upper)
        result <- tools.rules
          .specAll(tools.numbers.strictTransitive, List(here, middle, top))
          .flatMap(tools.rules.mp(_, pair))
      } yield result

  /** `|- WORD_LENGTH <word> = SUC^n ZERO`, the letters having gone out with the lengths. */
  private def lengthIsNumeral(
    tools: Concrete,
    letters: Vector[String]
  ): Either[LogicError, Kernel.Thm] =
    for {
      subject <- tools.word(letters)
      lengthOf <- tools.lengthOf
      applied <- LogicError.lift(Term.app(lengthOf, subject))
      computed <- Rewrite.rewrite(tools.lengths, applied)
      expected <- tools.numeral(letters.size)
      answer <- rightOf(computed)
      _ <-
        if (answer == expected) Right(())
        else Left(NotOfForm(s"a length of ${letters.size}", answer))
    } yield computed

  /** `|- NUM_SUB (WORD_LENGTH <word>) 1 = SUC^(n-1) ZERO`: where a marked word's marker sits. */
  private def lastIsNumeral(
    tools: Concrete,
    letters: Vector[String]
  ): Either[LogicError, Kernel.Thm] =
    for {
      subject <- tools.word(letters)
      lengthOf <- tools.lengthOf
      minus <- tools.constant(Peano.Subtraction, BinaryNumbers)
      one <- leftOf(tools.numbers.oneIsSuccessorOfZero)
      applied <- LogicError.lift(Term.app(lengthOf, subject))
      index <- LogicError.lift(Term.appAll(minus, List(applied, one)))
      computed <- Rewrite.rewrite(tools.positions, index)
      expected <- tools.numeral(letters.size - 1)
      answer <- rightOf(computed)
      _ <-
        if (answer == expected) Right(())
        else Left(NotOfForm(s"a last position of ${letters.size - 1}", answer))
    } yield computed

  /**
   * `|- WORD_NTH <word> (SUC^j ZERO) = <the j-th letter>`.
   *
   * The word is left-nested, so the last letter is read by `WORD_CONCAT_NTH_RIGHT` at the shifted
   * index `|front| + ZERO` and every earlier one by `WORD_CONCAT_NTH_LEFT` into the front, which
   * is where the recursion goes. The shifted index is normalised by the length rules rather than
   * by hand: `|front| + ZERO` and `SUC^(n-1) ZERO` are the same number and not the same term.
   */
  private def letterAt(
    tools: Concrete,
    letters: Vector[String],
    position: Int
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    if (letters.size == 1)
      for {
        letter <- tools.letter(letters.head)
        result <- rules.spec(letter, tools.singletonNth)
      } yield result
    else {
      val front = letters.init
      for {
        frontWord <- tools.word(front)
        lastLetter <- tools.letter(letters.last)
        singleton <- tools.constant(Concatenation.Singleton, Type.fun(Numbers, Words))
        lastWord <- LogicError.lift(Term.app(singleton, lastLetter))
        index <- tools.numeral(position)

        result <-
          if (position == letters.size - 1)
            for {
              zero <- tools.zero
              positive <- rules.spec(lastLetter, tools.singletonLength).flatMap { size =>
                Conv.sym(size).flatMap { reversed =>
                  tools.strictOrder.flatMap { order =>
                    rules
                      .spec(zero, tools.numbers.successorPositive)
                      .flatMap(carryRight(order, zero, reversed, _))
                  }
                }
              }
              entry <- rules
                .specAll(tools.entryRight, List(frontWord, lastWord, zero))
                .flatMap(rules.mp(_, positive))
              shiftedIndex <- leftOf(entry).flatMap {
                case App(_, argument) => Right(argument)
                case other => Left(NotOfForm("an entry at an index", other))
              }
              placed <- Rewrite.rewrite(tools.lengths, shiftedIndex)
              answer <- rightOf(placed)
              _ <-
                if (answer == index) Right(())
                else Left(NotOfForm(s"the position ${letters.size - 1}", answer))
              nth <- tools.nth
              subject <- tools.word(letters)
              nthOfSubject <- LogicError.lift(Term.app(nth, subject))
              moved <- Conv.apTerm(nthOfSubject, placed).flatMap(Conv.sym)
              inner <- rules.spec(lastLetter, tools.singletonNth)
              result <- Conv.trans(moved, entry).flatMap(Conv.trans(_, inner))
            } yield result
          else
            for {
              size <- lengthIsNumeral(tools, front)
              order <- tools.strictOrder
              small <- numeralBelow(tools, position, front.size)
              below <- Conv
                .sym(size)
                .flatMap(reversed => carryRight(order, index, reversed, small))
              outer <- rules
                .specAll(tools.entryLeft, List(frontWord, lastWord, index))
                .flatMap(rules.mp(_, below))
              inner <- letterAt(tools, front, position)
              result <- Conv.trans(outer, inner)
            } yield result
      } yield result
    }
  }

  /**
   * `|- ~(<one letter> = <another>)`, through the numerals the two letters are defined as.
   *
   * Four of the seven letters are defined constants and three are numerals, so neither side can be
   * handed to `Successor.distinct` as it stands: the definitions are unfolded first and the answer
   * is carried back across them. What decides it is the bit encoding, which is the only thing here
   * that can say two numbers of `num` differ.
   */
  private def lettersDiffer(
    tools: Concrete,
    first: String,
    second: String
  ): Either[LogicError, Kernel.Thm] =
    if (first == second)
      Left(NotOfForm("two different letters", Term.variable(first, Numbers)))
    else
      for {
        firstTerm <- tools.letter(first)
        secondTerm <- tools.letter(second)
        firstValue <- Rewrite.rewrite(tools.letters, firstTerm)
        secondValue <- Rewrite.rewrite(tools.letters, secondTerm)
        left <- rightOf(firstValue)
        right <- rightOf(secondValue)
        apart <- tools.successor.distinct(left, right)
        atFirst <- Conv
          .sym(firstValue)
          .flatMap(equation => carryLeftNegated(tools.logic, equation, right, apart))
        result <- carryRightNegated(tools.logic, secondValue, firstTerm, atFirst)
      } yield result

  /** `|- ~(<letter> = <marker>)`, which is [[lettersDiffer]] at whichever letter is the marker. */
  private def notTheMarker(
    tools: Concrete,
    letter: String,
    marker: String
  ): Either[LogicError, Kernel.Thm] =
    lettersDiffer(tools, letter, marker)

  /**
   * `|- !i. i < b ==> c`, where `b` is a numeral, by splitting the bound one successor at a time.
   *
   * `Bounded.prove` is the general form of this and cannot be used: it reads the bound off the
   * statement, and the statements here have `WORD_LENGTH w` or `NUM_SUB (WORD_LENGTH w) 1` there.
   * Rewriting those into numerals first is what the record's docstring forbids, since three of the
   * eleven rules have the letter `1` in them and `NUM_ONE_SUC` does not know the difference. So
   * the bound stays as written, the equation to the numeral is carried in on the ASSUMPTION
   * instead, and what is enumerated is that.
   */
  private def atEveryIndex(
    tools: Concrete,
    statement: Term,
    boundIsNumeral: Kernel.Thm,
    size: Int
  )(
    at: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    atEveryIndexGuarded(tools, statement, boundIsNumeral, size)((_, index, equal) => at(index, equal))

  /**
   * The same, where the guard under the quantifier is a conjunction and not the bound alone.
   *
   * `S2_ANCHORED` is why this exists: its inner claim is about the positions **above** the first,
   * so what stands under the quantifier is `0 < i /\ i < WORD_LENGTH w`, and the enumeration needs
   * the second half while the case at position zero needs the first. Deciding from the shape of the
   * guard rather than from a flag keeps one walk for both: a caller whose guard is the bound alone
   * is handed `None` and cannot tell this function from the one above it.
   */
  private def atEveryIndexGuarded(
    tools: Concrete,
    statement: Term,
    boundIsNumeral: Kernel.Thm,
    size: Int
  )(
    at: (Option[Kernel.Thm], FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    underTheBound(tools.logic, statement) { (index, guard) =>
      val conjuncts = tools.logic.destConj(guard.conclusion)

      for {
        extra <- conjuncts match {
          case Some(_) => rules.conjElim1(guard).map(Some(_))
          case None => Right(None)
        }
        below <- conjuncts match {
          case Some(_) => rules.conjElim2(guard)
          case None => Right(guard)
        }
        order <- tools.strictOrder
        carried <- carryRight(order, index, boundIsNumeral, below)
        consequent <- {
          val stripped = for {
            predicate <- tools.logic.destForallPredicate(statement)
          } yield predicate
          stripped match {
            case None => Left(NotOfForm("a claim about every index", statement))
            case Some(predicate) =>
              for {
                applied <- LogicError.lift(Term.app(predicate, index))
                body <- Conv.betaRoot(applied).flatMap(rightOf)
                parts <- tools.logic
                  .destImp(body)
                  .toRight(NotOfForm("an implication under the quantifier", body))
              } yield parts._2
          }
        }

        result <- {
          def walk(remaining: Int, fact: Kernel.Thm): Either[LogicError, Kernel.Thm] =
            if (remaining == 0)
              for {
                none <- rules.spec(index, tools.numbers.notBelowZero)
                absurd <- rules.notElim(none, fact)
                anything <- rules.falsityElim(consequent, absurd)
              } yield anything
            else
              for {
                smaller <- tools.numeral(remaining - 1)
                split <- rules
                  .specAll(tools.numbers.belowSuccessorCases, List(smaller, index))
                  .flatMap(rules.mp(_, fact))
                disjuncts <- tools.logic
                  .destDisj(split.conclusion)
                  .toRight(NotOfForm("a disjunction", split.conclusion))
                (lower, here) = disjuncts
                assumedLower <- LogicError.lift(Kernel.assume(lower))
                leftCase <- walk(remaining - 1, assumedLower)
                assumedHere <- LogicError.lift(Kernel.assume(here))
                rightCase <- at(extra, index, assumedHere)
                settled <- rules.disjElim(split, leftCase, rightCase)
              } yield settled

          walk(size, carried)
        }
      } yield result
    }
  }

  /**
   * `|- ~(WORD_NTH <word> i = <letter>)` from `|- i = SUC^j ZERO` and the letter at `j`.
   *
   * The letter is fetched with [[Concrete.letter]] rather than with [[Concrete.constant]], and
   * that is what lets a **digit** be refused here as well as a marker: three of the seven letters
   * are numerals and not constants of any name, so asking the theory for a constant called `0` is
   * a refusal naming a constant nobody declared. [[lettersDiffer]] under it was already parsing,
   * so this was the one line that decided which letters this walk could reach.
   */
  private def noMarkerAt(
    tools: Concrete,
    letters: Vector[String],
    position: Int,
    index: FVar,
    equal: Kernel.Thm,
    markerName: String
  ): Either[LogicError, Kernel.Thm] =
    for {
      entry <- letterAt(tools, letters, position)
      apart <- notTheMarker(tools, letters(position), markerName)
      marker <- tools.letter(markerName)
      atNumeral <- Conv
        .sym(entry)
        .flatMap(equation => carryLeftNegated(tools.logic, equation, marker, apart))
      nth <- tools.nth
      subject <- tools.word(letters)
      nthOfSubject <- LogicError.lift(Term.app(nth, subject))
      moved <- Conv.apTerm(nthOfSubject, equal).flatMap(Conv.sym)
      result <- carryLeftNegated(tools.logic, moved, marker, atNumeral)
    } yield result

  /** `|- S2_TAILFREE <word>` or `|- S2_HEADFREE <word>`, for a word no letter of which is that marker. */
  private def freeWord(
    tools: Concrete,
    letters: Vector[String],
    markerName: String
  ): Either[LogicError, Kernel.Thm] =
    for {
      subject <- tools.word(letters)
      definition <- tools.freeDefinition(markerName)
      opened <- Conv.unfold(definition, List(subject))
      statement <- rightOf(opened)
      size <- lengthIsNumeral(tools, letters)
      every <- atEveryIndex(tools, statement, size, letters.size) { (index, equal) =>
        for {
          position <- positionOf(tools, equal, letters.size)
          result <- noMarkerAt(tools, letters, position, index, equal, markerName)
        } yield result
      }
      result <- Conv
        .sym(opened)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, every)))
    } yield result

  /** Which index the enumeration is at, read off the numeral it handed back. */
  private def positionOf(
    tools: Concrete,
    equal: Kernel.Thm,
    size: Int
  ): Either[LogicError, Int] =
    for {
      sides <- Term.destEq(equal.conclusion).toRight(NotOfForm("an equation", equal.conclusion))
      zero <- tools.zero
      successor <- tools.successorOf
      count <- Bounded
        .lengthOf(zero, successor, sides._2)
        .toRight(NotOfForm("a numeral of num", sides._2))
      _ <-
        if (count < size) Right(())
        else Left(NotOfForm(s"a position below $size", sides._2))
    } yield count

  /** `|- ~(S2_TAILFREE <word>)` or its head-marker twin, for a word whose letter at `position` is it. */
  private def notFreeWord(
    tools: Concrete,
    letters: Vector[String],
    position: Int,
    markerName: String
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      subject <- tools.word(letters)
      definition <- tools.freeDefinition(markerName)
      opened <- Conv.unfold(definition, List(subject))
      claim <- leftOf(opened)
      assumed <- LogicError.lift(Kernel.assume(claim))
      every <- LogicError.lift(Kernel.eqMp(opened, assumed))

      size <- lengthIsNumeral(tools, letters)
      order <- tools.strictOrder
      index <- tools.numeral(position)
      small <- numeralBelow(tools, position, letters.size)
      below <- Conv.sym(size).flatMap(reversed => carryRight(order, index, reversed, small))
      notMarker <- rules.spec(index, every).flatMap(rules.mp(_, below))
      entry <- letterAt(tools, letters, position)
      absurd <- rules.notElim(notMarker, entry)
      result <- rules.notIntro(claim, absurd)
    } yield result
  }

  /** `|- S2_MARKED <word>`, for a word whose last letter is the marker and whose others are not. */
  private def markedWord(
    tools: Concrete,
    letters: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      subject <- tools.word(letters)
      opened <- Conv.unfold(tools.markedDefinition, List(subject))
      statement <- rightOf(opened)
      parts <- threeParts(tools.logic, statement)
      (positiveTerm, atMarkerTerm, everyTerm) = parts

      size <- lengthIsNumeral(tools, letters)
      last <- lastIsNumeral(tools, letters)
      order <- tools.strictOrder
      zero <- tools.zero
      predecessor <- tools.numeral(letters.size - 1)

      positive <- rules
        .spec(predecessor, tools.numbers.successorPositive)
        .flatMap(fact => Conv.sym(size).flatMap(carryRight(order, zero, _, fact)))
      _ <-
        if (positive.conclusion == positiveTerm) Right(())
        else Left(NotOfForm("the positive length as it is written", positive.conclusion))

      nth <- tools.nth
      nthOfSubject <- LogicError.lift(Term.app(nth, subject))
      entry <- letterAt(tools, letters, letters.size - 1)
      atMarker <- Conv.apTerm(nthOfSubject, last).flatMap(Conv.trans(_, entry))
      _ <-
        if (atMarker.conclusion == atMarkerTerm) Right(())
        else Left(NotOfForm("the marker at the last letter as it is written", atMarker.conclusion))

      every <- atEveryIndex(tools, everyTerm, last, letters.size - 1) { (index, equal) =>
        for {
          position <- positionOf(tools, equal, letters.size - 1)
          result <- noMarkerAt(tools, letters, position, index, equal, Tail)
        } yield result
      }

      held <- rules.conjIntro(atMarker, every).flatMap(rules.conjIntro(positive, _))
      result <- Conv
        .sym(opened)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, held)))
    } yield result
  }

  /** `|- ~(S2_MARKED <word>)`, for a word whose last letter is not the marker. */
  private def notMarkedWord(
    tools: Concrete,
    letters: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      subject <- tools.word(letters)
      opened <- Conv.unfold(tools.markedDefinition, List(subject))
      claim <- leftOf(opened)
      assumed <- LogicError.lift(Kernel.assume(claim))
      held <- LogicError.lift(Kernel.eqMp(opened, assumed))
      rest <- rules.conjElim2(held)
      atMarker <- rules.conjElim1(rest)

      last <- lastIsNumeral(tools, letters)
      nth <- tools.nth
      nthOfSubject <- LogicError.lift(Term.app(nth, subject))
      atNumeral <- Conv
        .apTerm(nthOfSubject, last)
        .flatMap(Conv.sym)
        .flatMap(Conv.trans(_, atMarker))
      entry <- letterAt(tools, letters, letters.size - 1)
      value <- Conv.sym(entry).flatMap(Conv.trans(_, atNumeral))
      apart <- notTheMarker(tools, letters.last, Tail)
      absurd <- rules.notElim(apart, value)
      result <- rules.notIntro(claim, absurd)
    } yield result
  }

  /**
   * The rule sets and lemmas a proof about a written-out word runs on, assembled once.
   *
   * The three rule sets are what makes this worth building rather than fetching per proof: eleven
   * rules, two sides each, and every one of them reads a length and a letter.
   */
  private def concreteTools(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    concatenation: Concatenation,
    peano: Peano,
    naturals: Natural,
    successor: Successor,
    numbers: Arithmetic,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Concrete] =
    for {
      concatLength <- concatenation.fact(Concatenation.Length).map(atNumbers)
      singletonLength <- concatenation.fact(Concatenation.SingletonLength).map(atNumbers)
      singletonNth <- concatenation.fact(Concatenation.SingletonNth).map(atNumbers)
      entryLeft <- concatenation.fact(Concatenation.NthLeft).map(atNumbers)
      entryRight <- concatenation.fact(Concatenation.NthRight).map(atNumbers)
      addSuc <- peano.fact(Peano.AddAtSuccessor)
      addZero <- peano.fact(Peano.AddAtZero)

      lengths <- unfoldingRules(logic, Vector(concatLength, singletonLength, addSuc, addZero))
      positions <- unfoldingRules(
        logic,
        Vector(
          concatLength,
          singletonLength,
          addSuc,
          addZero,
          numbers.oneIsSuccessorOfZero,
          numbers.subSuccessors,
          numbers.subAtZero
        )
      )
      letterDefinitions <- Letters
        .map(_._1)
        .foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) {
          (accumulated, name) =>
            for {
              held <- accumulated
              definition <- definitions.get(name).toRight(MissingDefinition(name))
            } yield held :+ definition
        }
      letters <- unfoldingRules(logic, letterDefinitions)
      // Two sets and the line between them is the summand. [[identities]] is what tidies a term
      // AROUND a sum: the identities of addition and its successor recurrence, which is all the
      // offsets need. [[folds]] adds the numeral one spelled as a successor and the two recurrences
      // of truncated subtraction, and it is used INSIDE a sum's evaluation.
      //
      // Keeping the first set clear of the second is not tidiness. `oneIsSuccessorOfZero` rewrites
      // the `1` of `i - 1` and the one inside the bit encoding of `3`, both of which live in the
      // summand; a summand rewritten there is no longer the term the evaluated equation is about,
      // and the equation then fails to fire with no sign that anything went wrong.
      emptyLength <- concatenation.fact(Concatenation.EmptyLength).map(atNumbers)
      identities <- unfoldingRules(
        logic,
        Vector(
          numbers.addAtZero,
          numbers.zeroPlus,
          numbers.addAtSuccessor,
          numbers.sumAtZero,
          emptyLength
        )
      )
      // `NUM_SUB_ZERO` is here for the position a digit can only sit at in a word with no head
      // marker in front of it: at position zero the weight is `0 - 1`, and the two recurrences
      // above reduce a difference of two successors and a subtraction of zero, neither of which
      // that is. Without it the measure of `0f.` evaluates to `NUM_SUB ZERO (SUC ZERO)` and stops,
      // which is the right number in a shape `Successor.distinct` cannot read.
      folds <- unfoldingRules(
        logic,
        Vector(
          numbers.addAtZero,
          numbers.zeroPlus,
          numbers.addAtSuccessor,
          numbers.oneIsSuccessorOfZero,
          numbers.subSuccessors,
          numbers.subAtZero,
          numbers.zeroMinus
        )
      )

      tailFreeDefinition <- definitions.get(TailFree).toRight(MissingDefinition(TailFree))
      headFreeDefinition <- definitions.get(HeadFree).toRight(MissingDefinition(HeadFree))
      markedDefinition <- definitions.get(Marked).toRight(MissingDefinition(Marked))
      anchoredDefinition <- definitions.get(Anchored).toRight(MissingDefinition(Anchored))
    } yield Concrete(
      logic,
      theory,
      notation,
      numbers,
      naturals,
      successor,
      lengths,
      positions,
      letters,
      identities,
      folds,
      entryLeft,
      entryRight,
      singletonLength,
      singletonNth,
      tailFreeDefinition,
      headFreeDefinition,
      markedDefinition,
      anchoredDefinition
    )

  /* ------------------------------------------------------------------ the eleven rules */

  /** `|- 0 < WORD_LENGTH <word>`, the length being a successor. */
  private def positiveLength(
    tools: Concrete,
    letters: Vector[String]
  ): Either[LogicError, Kernel.Thm] =
    for {
      size <- lengthIsNumeral(tools, letters)
      order <- tools.strictOrder
      zero <- tools.zero
      predecessor <- tools.numeral(letters.size - 1)
      result <- tools.rules
        .spec(predecessor, tools.numbers.successorPositive)
        .flatMap(fact => Conv.sym(size).flatMap(carryRight(order, zero, _, fact)))
    } yield result

  /**
   * A claim about every rule, proved by opening the definition and answering the eleven clauses.
   *
   * The clause a case is given is `l = <written word> /\ r = <written word>`, so the case does not
   * reason about the rule at all: it carries the conclusion across the two equations from a proof
   * about words with no variables in them. Which of the eleven it is comes from the position in the
   * spine, and the position is checked against [[Rules]] rather than assumed, because a definition
   * whose clauses had been reordered would otherwise be answered with the wrong word's proof.
   */
  private def overEveryRule(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm],
    name: String
  )(
    at: (Rule, Kernel.Thm, Kernel.Thm, Option[Kernel.Thm], Term) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      target <- statement(theory, notation, name)
      body <- strippedBody(logic, target)
      parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (premiseTerm, conclusionTerm) = parts
      premise <- LogicError.lift(Kernel.assume(premiseTerm))
      holds <-
        if (logic.destConj(premiseTerm).isDefined) rules.conjElim1(premise)
        else Right(premise)

      // The side premise comes OUT of the one assumption rather than being assumed again. A second
      // `Kernel.assume` of the same proposition is a second hypothesis that nothing discharges, and
      // what reports it is the generalisation at the end refusing a variable that occurs free in it.
      side <-
        if (logic.destConj(premiseTerm).isDefined) rules.conjElim2(premise).map(Some(_))
        else Right(None)

      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      opened <- Conv.unfold(system, List(LeftSide, RightSide))
      asDisjunction <- LogicError.lift(Kernel.eqMp(opened, holds))

      settled <- {
        def walk(position: Int, disjunction: Term): Either[LogicError, Kernel.Thm] = {
          def clause(term: Term): Either[LogicError, Kernel.Thm] =
            for {
              entry <- Rules.lift(position).toRight(NotOfForm(s"a rule at position $position", term))
              assumed <- LogicError.lift(Kernel.assume(term))
              leftEquation <- rules.conjElim1(assumed)
              rightEquation <- rules.conjElim2(assumed)
              proved <- at(entry, leftEquation, rightEquation, side, conclusionTerm)
              _ <-
                if (proved.conclusion == conclusionTerm) Right(())
                else Left(NotOfForm(s"the conclusion at ${entry.label}", proved.conclusion))
            } yield proved

          logic.destDisj(disjunction) match {
            case None =>
              if (position == Rules.size - 1) clause(disjunction)
              else Left(NotOfForm(s"${Rules.size} clauses", disjunction))

            case Some((here, rest)) =>
              for {
                first <- clause(here)
                others <- walk(position + 1, rest)
                assumed <- LogicError.lift(Kernel.assume(disjunction))
                split <- rules.disjElim(assumed, first, others)
              } yield split
          }
        }

        rightOf(opened).flatMap(walk(0, _))
      }

      discharged <- rules.proveHyp(asDisjunction, settled)
      result <- rules
        .disch(premiseTerm, discharged)
        .flatMap(rules.genAll(_, List(LeftSide, RightSide)))
      _ <-
        if (result.conclusion == target) Right(())
        else Left(NotOfForm(s"$name as it is written", result.conclusion))
    } yield result
  }

  /** `|- P <side>` carried to `|- P <variable>` across `|- variable = <side>`. */
  private def acrossTheClause(
    predicate: Term,
    equation: Kernel.Thm,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      moved <- Conv.sym(equation).flatMap(Conv.apTerm(predicate, _))
      result <- LogicError.lift(Kernel.eqMp(moved, fact))
    } yield result

  /** `|- ~(P <side>)` spent against `|- P variable`, which the clause says is the same thing. */
  private def refuteAtTheClause(
    logic: Logic,
    predicate: Term,
    equation: Kernel.Thm,
    held: Kernel.Thm,
    refusal: Kernel.Thm,
    conclusion: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      moved <- Conv.apTerm(predicate, equation)
      atClause <- LogicError.lift(Kernel.eqMp(moved, held))
      absurd <- rules.notElim(refusal, atClause)
      result <- rules.falsityElim(conclusion, absurd)
    } yield result
  }

  /** [[RuleNotEmpty]]: every rule has letters on both sides, which is read off the lengths. */
  private def rulesAreNotEmpty(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic

    overEveryRule(logic, tools.theory, tools.notation, definitions, RuleNotEmpty) {
      (entry, leftEquation, rightEquation, _, _) =>
        for {
          lengthOf <- tools.lengthOf
          order <- tools.strictOrder
          zero <- tools.zero
          leftPositive <- positiveLength(tools, entry.left)
          rightPositive <- positiveLength(tools, entry.right)
          leftLengths <- Conv.apTerm(lengthOf, leftEquation).flatMap(Conv.sym)
          rightLengths <- Conv.apTerm(lengthOf, rightEquation).flatMap(Conv.sym)
          onLeft <- carryRight(order, zero, leftLengths, leftPositive)
          onRight <- carryRight(order, zero, rightLengths, rightPositive)
          result <- tools.rules.conjIntro(onLeft, onRight)
        } yield result
    }
  }

  /**
   * [[MarkedStep]]: the two rules that consume the marker take a marked word to a marked word.
   *
   * The nine others are vacuous, and the nine derivations that say so are the cost of this fact:
   * each one refutes `S2_MARKED` of a written-out two-letter word, which is the last letter read
   * off and compared with the marker. Nothing here is a case analysis on the letters as letters.
   */
  private def markedRules(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic

    overEveryRule(logic, tools.theory, tools.notation, definitions, MarkedStep) {
      (entry, leftEquation, rightEquation, side, conclusion) =>
        for {
          marked <- tools.constant(Marked, Type.fun(Words, Type.Bool))
          held <- side.toRight(NotOfForm("a premise about the left-hand side", conclusion))
          result <-
            if (entry.group == Group.Consumes)
              markedWord(tools, entry.right)
                .flatMap(acrossTheClause(marked, rightEquation, _))
            else
              notMarkedWord(tools, entry.left).flatMap(
                refuteAtTheClause(logic, marked, leftEquation, held, _, conclusion)
              )
        } yield result
    }
  }

  /**
   * [[AnchoredStep]]: the three rules that fire at the head take an anchored word to an anchored one.
   *
   * [[markedRules]] at the other end of the word. The eight others are vacuous and the eight
   * derivations that say so are the cost: each refutes `S2_ANCHORED` of a written-out word by
   * reading its first letter, which is not the head marker.
   */
  private def anchoredRules(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic

    overEveryRule(logic, tools.theory, tools.notation, definitions, AnchoredStep) {
      (entry, leftEquation, rightEquation, side, conclusion) =>
        for {
          anchored <- tools.constant(Anchored, Type.fun(Words, Type.Bool))
          held <- side.toRight(NotOfForm("a premise about the left-hand side", conclusion))
          result <-
            if (entry.left.headOption.contains(Head))
              anchoredWord(tools, entry.right)
                .flatMap(acrossTheClause(anchored, rightEquation, _))
            else
              notAnchoredWord(tools, entry.left).flatMap(
                refuteAtTheClause(logic, anchored, leftEquation, held, _, conclusion)
              )
        } yield result
    }
  }

  /**
   * [[TailFreeStep]] and [[HeadFreeStep]]: the rules that do not name a marker keep a word free of it.
   *
   * One derivation for both, and which rules are vacuous is read off the table rather than off the
   * group: a rule is the interesting case exactly when its left-hand side spells the marker, which
   * is `R1` and `R2` for the tail and the three `B` rules for the head. Reading it from the letters
   * is what makes this one function: the groups answer a different question, which is what the
   * source calls the rules, and a group that gained a member would silently change which clause
   * this proof takes.
   */
  private def freeRules(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm],
    markerName: String,
    className: String,
    statementName: String
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic

    overEveryRule(logic, tools.theory, tools.notation, definitions, statementName) {
      (entry, leftEquation, rightEquation, side, conclusion) =>
        for {
          free <- tools.constant(className, Type.fun(Words, Type.Bool))
          held <- side.toRight(NotOfForm("a premise about the left-hand side", conclusion))
          result <-
            if (entry.left.contains(markerName))
              notFreeWord(tools, entry.left, entry.left.indexOf(markerName), markerName).flatMap(
                refuteAtTheClause(logic, free, leftEquation, held, _, conclusion)
              )
            else
              freeWord(tools, entry.right, markerName)
                .flatMap(acrossTheClause(free, rightEquation, _))
        } yield result
    }
  }

  /* ------------------------------------------------------------------ the eleven are eleven */

  /**
   * `|- ~(<one rule's left-hand side> = <another's>)`, for every pair of the eleven.
   *
   * The guard that says the system has eleven rules rather than some smaller number wearing eleven
   * names. It is derived rather than counted: `CollatzSpec` already counts the disjuncts off the
   * definition, and a count answers "how many clauses were written" where this answers "how many
   * pairs the relation holds of", which is the question a collapsed table would make the two
   * disagree on.
   *
   * The left-hand sides are enough, because the eleven of them are already pairwise distinct: a
   * pair of rules agreeing on both sides would first have to agree on the left. Nothing here is
   * published, and that is deliberate — no consumer needs the rules to be distinct, it is a fact
   * about the encoding, and facts about the encoding are what this repository keeps in its specs.
   */
  private[theories] def separations(tools: Concrete): Either[LogicError, Vector[(String, String, Kernel.Thm)]] = {
    val pairs =
      for {
        first <- Rules.indices
        second <- (first + 1) until Rules.size
      } yield (first, second)

    pairs.foldLeft[Either[LogicError, Vector[(String, String, Kernel.Thm)]]](Right(Vector.empty)) {
      case (accumulated, (first, second)) =>
        for {
          held <- accumulated
          apart <- wordsDiffer(tools, Rules(first).left, Rules(second).left)
        } yield held :+ ((Rules(first).label, Rules(second).label, apart))
    }
  }

  /**
   * `|- ~(<one written word> = <another>)`, refuted on the lengths or on a letter they disagree at.
   *
   * Two words of different lengths are separated by `WORD_LENGTH`, which lands on two runs of
   * successors and is what [[refuteSuccessors]] was written for. Two of the same length are
   * separated by `WORD_NTH` at the first position they disagree at, which is what [[letterAt]]
   * reads. A caller that hands it two equal words is refused by name rather than answered.
   */
  private def wordsDiffer(
    tools: Concrete,
    first: Vector[String],
    second: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      left <- tools.word(first)
      right <- tools.word(second)
      claim <- LogicError.lift(Term.eq(left, right))
      assumed <- LogicError.lift(Kernel.assume(claim))

      absurd <-
        if (first.size != second.size)
          for {
            lengthOf <- tools.lengthOf
            applied <- Conv.apTerm(lengthOf, assumed)
            leftSize <- lengthIsNumeral(tools, first)
            rightSize <- lengthIsNumeral(tools, second)
            equal <- Conv
              .sym(leftSize)
              .flatMap(Conv.trans(_, applied))
              .flatMap(Conv.trans(_, rightSize))
            falsity <- refuteSuccessors(tools.logic, tools.naturals, equal)
          } yield falsity
        else
          for {
            position <- first.indices
              .find(index => first(index) != second(index))
              .toRight(NotOfForm("two different words", left))
            nth <- tools.nth
            index <- tools.numeral(position)
            applied <- Conv.apTerm(nth, assumed).flatMap(Conv.apThm(_, index))
            leftLetter <- letterAt(tools, first, position)
            rightLetter <- letterAt(tools, second, position)
            equal <- Conv
              .sym(leftLetter)
              .flatMap(Conv.trans(_, applied))
              .flatMap(Conv.trans(_, rightLetter))
            apart <- lettersDiffer(tools, first(position), second(position))
            falsity <- rules.notElim(apart, equal)
          } yield falsity

      result <- rules.notIntro(claim, absurd)
    } yield result
  }

  /* ------------------------------------------------------------------ what it is about */

  /** The word `/0.`, which is marked, and `/t.`, which is what `B1` turns it into. */
  private val BeforeTheStep: Vector[String] = spell("/0.")

  private val AfterTheStep: Vector[String] = spell("/t.")

  /** `|- S2 <a rule's left-hand side> <its right-hand side>`, by picking that rule's disjunct. */
  /**
   * [[FamilyWithF]] and [[FamilyWithTail]]: the digit family lies in the closure of this system.
   *
   * Source: `collatz@8b991e5`, `code/referee/checks_rewriting.py:713`, which is `05` section
   * 3.1.30 B and which measures the same two facts twice: once by the induction written out below
   * and once by a goal-directed backward search that knows nothing of it. Three clause instances
   * are what the proof spends, and that file names all three, so a rule table that moved underneath
   * this proof breaks it there as well as here.
   *
   * == The three instances, and why each one is the clause it is ==
   *
   * The base is `/ff`, which is the **right-hand side** of `B2`, so it is in the closure by
   * [[Forward.RightSide]] and nothing else is needed for it. Each step is a **right extension**:
   * the member ends in a letter `a`, a rule reads `a b -> r`, and what comes out is the member with
   * its final `a` replaced by `r`. With `a` the letter `f` and `b` the digit `0`, rule `A2` reads
   * `f0 -> 0f` and `/f0^i f` becomes `/f0^(SUC i) f`, which is the induction. With `a` the letter
   * `f` and `b` the word `f.`, rule `R1` reads `ff. -> 0.` and the same member becomes
   * `/f0^(SUC i) .`, which is the family.
   *
   * So there is one induction and not two: [[FamilyWithTail]] is [[FamilyWithF]] with one extension
   * on the end, and the second statement costs an associativity rather than a second pass over the
   * numbers.
   *
   * == The associativity, which is where the work actually is ==
   *
   * Every word here is spelled left-nested, by [[wordText]], and the extension clause asks for a
   * member of the shape `WORD_CONCAT p a` and hands back `WORD_CONCAT p r`. Those two are exactly
   * the spellings a caller wants **only** where `a` and `r` are one letter. `R1` has three letters
   * on the left and the split this proof needs cuts after the first, so the rule's own left-hand
   * side `(f f) .` has to be read as `f (f .)` before the clause applies: that is
   * [[Concatenation.Associative]] spent on the rule rather than on the word, and [[carryLeft]] is
   * what moves the rule across it. The same lemma is spent twice more per step, on the member: once
   * to turn `p (0 f)` back into `(p 0) f`, and once to turn `((/f) 0^i) 0` into `(/f) (0^i 0)`,
   * which is where the recursion's own equation for `S2_ZEROS` meets it.
   */
  private def digitFamily(
    tools: Concrete,
    forward: Forward,
    naturals: Natural,
    definitions: Map[String, Kernel.Thm],
    zerosAtZero: Kernel.Thm,
    zerosAtSuccessor: Kernel.Thm
  ): Either[LogicError, (Kernel.Thm, Kernel.Thm)] = {
    val logic = tools.logic
    val rules = logic.rules
    val concatenation = forward.concatenation

    def ruleAt(label: String): Either[LogicError, Kernel.Thm] =
      Rules
        .indexWhere(_.label == label) match {
        case -1 => Left(NotOfForm(s"a rule labelled $label", LeftSide))
        case position => ruleHolds(tools, definitions, position)
      }

    def sideOf(label: String, left: Boolean): Either[LogicError, Term] =
      Rules
        .find(_.label == label)
        .toRight(NotOfForm(s"a rule labelled $label", LeftSide))
        .flatMap(entry => tools.word(if (left) entry.left else entry.right))

    for {
      system <- tools.constant(Name, SystemType)
      closure <- tools.constant(Forward.Name, Type.fun(SystemType, Type.fun(Words, Type.Bool)))
      membership <- LogicError.lift(Term.app(closure, system))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      zerosOf <- tools.constant(Zeros, Type.fun(Numbers, Words))

      stem <- tools.word(spell("/f"))
      letterF <- tools.word(spell("f"))
      digitZero <- tools.word(spell("0"))
      marker <- tools.word(spell("."))
      afterF <- tools.word(spell("f."))

      associative <- concatenation.fact(Concatenation.Associative).map(atNumbers)
      emptyRight <- concatenation.fact(Concatenation.EmptyRight).map(atNumbers)
      rightSide <- forward.fact(Forward.RightSide).map(atNumbers)
      extend <- forward.fact(Forward.Extend).map(atNumbers)

      fNotEmpty <- notEmptyWord(tools, concatenation, spell("f"))
      zeroNotEmpty <- notEmptyWord(tools, concatenation, spell("0"))
      afterFNotEmpty <- notEmptyWord(tools, concatenation, spell("f."))

      induction <- naturals.fact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)

      withFStatement <- statement(tools.theory, tools.notation, FamilyWithF)
      withF <- driver.proveBy(
        withFStatement,
        goal =>
          for {
            rule <- ruleAt("B2")
            left <- sideOf("B2", left = true)
            right <- sideOf("B2", left = false)
            instance <- rules.specAll(rightSide, List(system, left, right))
            member <- rules.mp(instance, rule)
            // `(/f) 0^0` is `(/f) WORD_EMPTY` is `/f`, so the base word is `/ff` written as the
            // family rather than as a different term that happens to print the same.
            inFront <- LogicError.lift(Term.app(concat, stem))
            opened <- Conv.apTerm(inFront, zerosAtZero)
            collapsed <- rules.spec(stem, emptyRight).flatMap(Conv.trans(opened, _))
            equation <- Conv.apTerm(concat, collapsed).flatMap(Conv.apThm(_, letterF))
            result <- acrossTheClause(membership, equation, member)
            _ <-
              if (result.conclusion == goal) Right(())
              else Left(NotOfForm("the base case as the driver opened it", result.conclusion))
          } yield result,
        opened =>
          for {
            atIndex <- LogicError.lift(Term.app(zerosOf, opened.variable))
            prefix <- LogicError.lift(Term.app(concat, stem)).flatMap(
              partial => LogicError.lift(Term.app(partial, atIndex)))
            rule <- ruleAt("A2")
            right <- sideOf("A2", left = false)
            instance <- rules.specAll(extend, List(system, prefix, letterF, digitZero, right))
            premises <- conjoin(logic, List(opened.hypothesis, rule, fNotEmpty, zeroNotEmpty))
            member <- rules.mp(instance, premises)
            reassociated <- rules.specAll(associative, List(prefix, digitZero, letterF))
            moved <- acrossTheClause(membership, reassociated, member)
            grown <- runOneLonger(
              tools, concat, stem, atIndex, digitZero, opened.variable,
              associative, zerosAtSuccessor)
            equation <- Conv.apTerm(concat, grown).flatMap(Conv.apThm(_, letterF)).flatMap(Conv.sym)
            result <- acrossTheClause(membership, equation, moved)
            _ <-
              if (result.conclusion == opened.goal) Right(())
              else Left(NotOfForm("the step as the driver opened it", result.conclusion))
          } yield result
      )

      index = Term.variable("i", Numbers)
      atIndex <- LogicError.lift(Term.app(zerosOf, index))
      prefix <- LogicError
        .lift(Term.app(concat, stem))
        .flatMap(partial => LogicError.lift(Term.app(partial, atIndex)))
      held <- rules.spec(index, withF)
      ruleR1 <- ruleAt("R1")
      right <- sideOf("R1", left = false)
      split <- rules.specAll(associative, List(letterF, letterF, marker)).flatMap(Conv.sym)
      shaped <- carryLeft(system, split, right, ruleR1)
      instance <- rules.specAll(extend, List(system, prefix, letterF, afterF, right))
      premises <- conjoin(logic, List(held, shaped, fNotEmpty, afterFNotEmpty))
      member <- rules.mp(instance, premises)
      reassociated <- rules.specAll(associative, List(prefix, digitZero, marker))
      moved <- acrossTheClause(membership, reassociated, member)
      grown <- runOneLonger(
        tools, concat, stem, atIndex, digitZero, index, associative, zerosAtSuccessor)
      equation <- Conv.apTerm(concat, grown).flatMap(Conv.apThm(_, marker)).flatMap(Conv.sym)
      carried <- acrossTheClause(membership, equation, moved)
      withTail <- rules.gen(index, carried)

      expected <- statement(tools.theory, tools.notation, FamilyWithTail)
      _ <-
        if (withTail.conclusion == expected) Right(())
        else Left(NotOfForm(s"$FamilyWithTail as it is written", withTail.conclusion))
    } yield (withF, withTail)
  }

  /**
   * `|- WORD_CONCAT (WORD_CONCAT stem 0^i) 0 = WORD_CONCAT stem 0^(SUC i)`.
   *
   * The one equation both halves of [[digitFamily]] end on, and it is the recursion's own step
   * equation with an associativity in front of it: what the closure hands back is the run with a
   * digit concatenated on the outside, and what the statement names is the run at the next index.
   */
  private def runOneLonger(
    tools: Concrete,
    concat: Term,
    stem: Term,
    atIndex: Term,
    digit: Term,
    index: Term,
    associative: Kernel.Thm,
    zerosAtSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      regrouped <- tools.rules.specAll(associative, List(stem, atIndex, digit))
      longer <- tools.rules.spec(index, zerosAtSuccessor).flatMap(Conv.sym)
      inFront <- LogicError.lift(Term.app(concat, stem))
      carried <- Conv.apTerm(inFront, longer)
      result <- Conv.trans(regrouped, carried)
    } yield result

  /**
   * [[ClosureRefused]]: the empty word is not in the closure, so the closure is not every word.
   *
   * One induction over `WORD_RFC S2`, at the invariant `\w. ~(w = WORD_EMPTY)`, and the three
   * clauses are the same argument three times: whatever a clause produces has a rule's right-hand
   * side inside it, [[RuleNotEmpty]] says that side has letters, and a concatenation with a
   * non-empty part is non-empty. Nothing in it reads a letter, which is why it is cheap and also
   * why it says so little: `/f.` is refused by the source's instrument too and is not refused here,
   * because what rules that word out is an argument about which letters can stand next to which.
   *
   * [[Forward.Induction]] asks **nothing** of the system, which is what makes this affordable at
   * all: the half of `INDUCTIVE` that settles a non-membership is the free half, and the
   * monotonicity that the introduction rules pay for is not needed here.
   */
  private def closureIsProper(
    tools: Concrete,
    forward: Forward,
    ruleNotEmpty: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules
    val concatenation = forward.concatenation

    /** `!w. <premise> ==> ~(w = WORD_EMPTY)`, from a proof of the conclusion under the premise. */
    def forEachWord(
      clause: Term
    )(
      at: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
    ): Either[LogicError, Kernel.Thm] =
      for {
        predicate <- logic
          .destForallPredicate(clause)
          .toRight(NotOfForm("a claim about every word", clause))
        witness = Conv.freshVariable("w", Words, Term.freeVariables(clause))
        applied <- LogicError.lift(Term.app(predicate, witness))
        body <- Conv.betaRoot(applied).flatMap(rightOf)
        parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
        (premise, _) = parts
        assumed <- LogicError.lift(Kernel.assume(premise))
        proved <- at(witness, assumed)
        discharged <- rules.disch(premise, proved)
        result <- rules.gen(witness, discharged)
      } yield result

    for {
      system <- tools.constant(Name, SystemType)
      closure <- tools.constant(Forward.Name, Type.fun(SystemType, Type.fun(Words, Type.Bool)))
      membership <- LogicError.lift(Term.app(closure, system))
      empty <- tools.constant(Concatenation.Empty, Words)
      concat <- tools.constant(Concatenation.Name, ConcatType)
      lengthOf <- tools.lengthOf
      order <- tools.strictOrder
      zero <- tools.zero

      emptyLength <- concatenation.fact(Concatenation.EmptyLength).map(atNumbers)
      concatLength <- concatenation.fact(Concatenation.Length).map(atNumbers)
      induction <- forward.fact(Forward.Induction).map(atNumbers)
      stepDefinition <- forward.definition(Forward.Step).map(atNumbers)

      /* The invariant, as a predicate to instantiate the induction principle with. */
      subject = Term.variable("w", Words)
      equated <- LogicError.lift(Term.eq(subject, empty))
      denied <- LogicError.lift(Term.app(logic.negation, equated))
      invariant <- LogicError.lift(Term.abs(subject, denied))

      instance <- rules.specAll(induction, List(system, invariant))
      opened <- Conv
        .betaNormalise(instance.conclusion)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, instance)))
      premises <- logic
        .destImp(opened.conclusion)
        .map(_._1)
        .toRight(NotOfForm("an implication", opened.conclusion))
      firstTwo <- logic.destConj(premises).toRight(NotOfForm("a conjunction", premises))
      (contains, rest) = firstTwo
      lastTwo <- logic.destConj(rest).toRight(NotOfForm("a conjunction", rest))
      (inside, extending) = lastTwo

      /* A right-hand side has letters, so the word the clause produces has letters. */
      byContaining <- forEachWord(contains) { (word, held) =>
        openWitnesses(logic, held, 1, Set(word)) { (witnesses, rule) =>
          for {
            left <- witnesses.headOption.toRight(NotOfForm("a left-hand side", word))
            sides <- rules.specAll(ruleNotEmpty, List(left, word)).flatMap(rules.mp(_, rule))
            positive <- rules.conjElim2(sides)
            result <- notEmptyFrom(tools, emptyLength, word, positive)
          } yield result
        }
      }

      /* A step rewrites inside a context, and what it puts there is a right-hand side. */
      byReducing <- forEachWord(inside) { (word, held) =>
        openWitnesses(logic, held, 1, Set(word)) { (witnesses, pair) =>
          for {
            before <- witnesses.headOption.toRight(NotOfForm("the word stepped from", word))
            step <- rules.conjElim2(pair)
            unfolded <- Conv.unfold(stepDefinition, List(system, before, word))
            existential <- LogicError.lift(Kernel.eqMp(unfolded, step))
            result <- openWitnesses(logic, existential, 4, Set(word, before)) { (inner, body) =>
              inner match {
                case List(front, left, right, back) =>
                  for {
                    rule <- rules.conjElim1(body)
                    equation <- rules.conjElim2(body).flatMap(rules.conjElim2)
                    sides <- rules.specAll(ruleNotEmpty, List(left, right)).flatMap(rules.mp(_, rule))
                    positive <- rules.conjElim2(sides)
                    block <- joined(concat, front, right)
                    inBlock <- positiveJoined(
                      tools, concatLength, concat, front, right, positive, onTheLeft = false)
                    whole <- positiveJoined(
                      tools, concatLength, concat, block, back, inBlock, onTheLeft = true)
                    here <- positiveAt(tools, lengthOf, order, zero, equation, whole)
                    result <- notEmptyFrom(tools, emptyLength, word, here)
                  } yield result

                case other => Left(NotOfForm(s"four witnesses, not ${other.size}", word))
              }
            }
          } yield result
        }
      }

      /* An extension replaces the member's last block by a right-hand side, and keeps its front. */
      byExtending <- forEachWord(extending) { (word, held) =>
        openWitnesses(logic, held, 4, Set(word)) { (witnesses, body) =>
          witnesses match {
            case List(front, first, second, right) =>
              for {
                rule <- rules.conjElim2(body).flatMap(rules.conjElim1)
                equation <- rules
                  .conjElim2(body)
                  .flatMap(rules.conjElim2)
                  .flatMap(rules.conjElim2)
                  .flatMap(rules.conjElim2)
                left <- joined(concat, first, second)
                sides <- rules.specAll(ruleNotEmpty, List(left, right)).flatMap(rules.mp(_, rule))
                positive <- rules.conjElim2(sides)
                whole <- positiveJoined(
                  tools, concatLength, concat, front, right, positive, onTheLeft = false)
                here <- positiveAt(tools, lengthOf, order, zero, equation, whole)
                result <- notEmptyFrom(tools, emptyLength, word, here)
              } yield result

            case other => Left(NotOfForm(s"four witnesses, not ${other.size}", word))
          }
        }
      }

      everywhere <- conjoin(logic, List(byContaining, byReducing, byExtending))
        .flatMap(rules.mp(opened, _))
      atEmpty <- rules.spec(empty, everywhere)
      claim <- LogicError.lift(Term.app(membership, empty))
      assumed <- LogicError.lift(Kernel.assume(claim))
      refused <- rules.mp(atEmpty, assumed)
      falsity <- rules.notElim(refused, Conv.refl(empty))
      result <- rules.notIntro(claim, falsity)
    } yield result
  }

  /** `WORD_CONCAT u v`, as a term. */
  private def joined(concat: Term, left: Term, right: Term): Either[LogicError, Term] =
    LogicError.lift(Term.app(concat, left)).flatMap(partial => LogicError.lift(Term.app(partial, right)))

  /**
   * `|- 0 < WORD_LENGTH (WORD_CONCAT u v)` from the same of whichever half has the letters.
   *
   * Two directions and one proof, because `NUM_LE_LT_TRANS` reads the same either way once the sum
   * is written with the non-empty half in front: `NUM_LE m (NUM_ADD m n)` is the bound, and the
   * half that is not in front gets there by commuting the sum rather than by a second lemma.
   */
  private def positiveJoined(
    tools: Concrete,
    concatLength: Kernel.Thm,
    concat: Term,
    left: Term,
    right: Term,
    positive: Kernel.Thm,
    onTheLeft: Boolean
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      lengthOf <- tools.lengthOf
      order <- tools.strictOrder
      zero <- tools.zero
      atMost <- tools.constant(Peano.NonStrictOrder, OrderType)
      sizeLeft <- LogicError.lift(Term.app(lengthOf, left))
      sizeRight <- LogicError.lift(Term.app(lengthOf, right))
      lengths <- rules.specAll(concatLength, List(left, right))
      bound <-
        if (onTheLeft) rules.specAll(tools.numbers.atMostSum, List(sizeLeft, sizeRight))
        else
          for {
            flipped <- rules.specAll(tools.numbers.atMostSum, List(sizeRight, sizeLeft))
            commuted <- rules.specAll(tools.numbers.addCommutative, List(sizeRight, sizeLeft))
            moved <- carryRight(atMost, sizeRight, commuted, flipped)
          } yield moved
      sum <- Term
        .destEq(lengths.conclusion)
        .map(_._2)
        .toRight(NotOfForm("an equation", lengths.conclusion))
      size = if (onTheLeft) sizeLeft else sizeRight
      premises <- rules.conjIntro(positive, bound)
      below <- rules
        .specAll(tools.numbers.belowThenAtMost, List(zero, size, sum))
        .flatMap(rules.mp(_, premises))
      result <- Conv.sym(lengths).flatMap(carryRight(order, zero, _, below))
    } yield result
  }

  /** `|- 0 < WORD_LENGTH w` from `|- w = <a word>` and `|- 0 < WORD_LENGTH <that word>`. */
  private def positiveAt(
    tools: Concrete,
    lengthOf: Term,
    order: Term,
    zero: Term,
    equation: Kernel.Thm,
    positive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Conv
      .apTerm(lengthOf, equation)
      .flatMap(Conv.sym)
      .flatMap(carryRight(order, zero, _, positive))

  /**
   * `|- ~(w = WORD_EMPTY)` from `|- 0 < WORD_LENGTH w`.
   *
   * The empty word is the only one with no letters, which is `WORD_EMPTY_LENGTH` read as a
   * refusal: a word that is the empty word has length zero, and nothing is below zero.
   */
  private def notEmptyFrom(
    tools: Concrete,
    emptyLength: Kernel.Thm,
    subject: Term,
    positive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic

    for {
      empty <- tools.constant(Concatenation.Empty, Words)
      lengthOf <- tools.lengthOf
      order <- tools.strictOrder
      zero <- tools.zero
      equation <- LogicError.lift(Term.eq(subject, empty))
      assumed <- LogicError.lift(Kernel.assume(equation))
      lengths <- Conv.apTerm(lengthOf, assumed)
      collapsed <- Conv.trans(lengths, emptyLength)
      absurd <- carryRight(order, zero, collapsed, positive)
      refused <- logic.rules.spec(zero, tools.numbers.notBelowZero)
      falsity <- logic.rules.notElim(refused, absurd)
      result <- logic.rules.notIntro(equation, falsity)
    } yield result
  }

  /**
   * `|- ~(<word> = WORD_EMPTY)`, for a word written out letter by letter.
   *
   * The two side conditions the extension clause carries, discharged the only way a word spelled as
   * a concatenation of singletons can discharge them: by its length. `Concatenation` publishes no
   * fact of this shape and this is not the place to add one, because the general statement is about
   * `word('a)` and would be a lemma of a link in the chain; what is needed here is the instance at
   * three concrete words.
   */
  private def notEmptyWord(
    tools: Concrete,
    concatenation: Concatenation,
    letters: Vector[String]
  ): Either[LogicError, Kernel.Thm] =
    for {
      subject <- tools.word(letters)
      positive <- positiveLength(tools, letters)
      emptyLength <- concatenation.fact(Concatenation.EmptyLength).map(atNumbers)
      result <- notEmptyFrom(tools, emptyLength, subject, positive)
    } yield result

  /** A right-nested conjunction of what is held, which is the shape a clause's premises take. */
  private def conjoin(
    logic: Logic,
    facts: List[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    facts match {
      case Nil => Left(NotOfForm("at least one premise", LeftSide))
      case single :: Nil => Right(single)
      case head :: rest => conjoin(logic, rest).flatMap(logic.rules.conjIntro(head, _))
    }

  private def ruleHolds(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm],
    position: Int
  ): Either[LogicError, Kernel.Thm] =
    relationHolds(tools, definitions, Rules, Name, position)

  /**
   * The same at either table, which is what a step by a **commutation** needs.
   *
   * `S2` and `S2_COUNTED` are the same text over two vectors of rules ([[disjunctionText]]), so a
   * proof that one clause of one of them holds is the same walk at both, and the position is the
   * position in whichever table the caller named. Splitting this out is what keeps the eleven and
   * the six from each having a copy: a second copy agrees with this one on the day it is written
   * and is a defect from then on, whether or not it has yet stopped agreeing.
   */
  private def relationHolds(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm],
    table: Vector[Rule],
    name: String,
    position: Int
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic

    for {
      entry <- table.lift(position).toRight(NotOfForm(s"a rule at position $position", LeftSide))
      system <- definitions.get(name).toRight(MissingDefinition(name))
      left <- tools.word(entry.left)
      right <- tools.word(entry.right)
      opened <- Conv.unfold(system, List(left, right))
      disjunction <- rightOf(opened)
      chosen <- introduceAt(logic, disjunction, position)
      result <- Conv
        .sym(opened)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, chosen)))
    } yield result
  }

  /** The `position`-th disjunct of a right-nested disjunction, proved by reflexivity on its pair. */
  private def introduceAt(
    logic: Logic,
    disjunction: Term,
    position: Int
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    logic.destDisj(disjunction) match {
      case None =>
        if (position == 0) byReflexivity(logic, disjunction)
        else Left(NotOfForm(s"a disjunction with a clause at $position", disjunction))

      case Some((here, rest)) =>
        if (position == 0) byReflexivity(logic, here).flatMap(rules.disjIntro1(rest, _))
        else introduceAt(logic, rest, position - 1).flatMap(rules.disjIntro2(here, _))
    }
  }

  /** `l = l /\ r = r`, which is what a clause of this system says once both sides are written out. */
  private def byReflexivity(logic: Logic, clause: Term): Either[LogicError, Kernel.Thm] =
    for {
      parts <- logic.destConj(clause).toRight(NotOfForm("a conjunction", clause))
      (leftEquation, rightEquation) = parts
      left <- Term.destEq(leftEquation).map(_._1).toRight(NotOfForm("an equation", leftEquation))
      right <- Term.destEq(rightEquation).map(_._1).toRight(NotOfForm("an equation", rightEquation))
      result <- logic.rules.conjIntro(Conv.refl(left), Conv.refl(right))
    } yield result

  /**
   * [[StepInhabited]]: `B1` fires at the head of `/0.` and what comes out is `/t.`.
   *
   * The witnesses are the empty word in front, the rule's two sides, and the marker behind, and the
   * only work is that `WORD_STEP` writes a word as `x l y` while [[wordText]] writes it left-nested
   * with nothing in front. `WORD_CONCAT_EMPTY_LEFT` is what reconciles the two, once per side.
   */
  private def stepHolds(
    tools: Concrete,
    concatenation: Concatenation,
    forward: Forward,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic

    for {
      target <- statement(tools.theory, tools.notation, StepInhabited)
      before <- tools.word(BeforeTheStep)
      after <- tools.word(AfterTheStep)
      leftSide <- tools.word(BeforeTheStep.init)
      rightSide <- tools.word(AfterTheStep.init)
      marker <- tools.marker
      singleton <- tools.constant(Concatenation.Singleton, Type.fun(Numbers, Words))
      tail <- LogicError.lift(Term.app(singleton, marker))
      empty <- tools.constant(Concatenation.Empty, Words)
      concat <- tools.constant(Concatenation.Name, ConcatType)
      system <- tools.constant(Name, Type.fun(Words, Type.fun(Words, Type.Bool)))
      emptyLeft <- concatenation.fact(Concatenation.EmptyLeft).map(atNumbers)

      rule <- ruleHolds(tools, definitions, Rules.indexWhere(_.label == "B1"))
      beforeEquation <- inFront(logic, concat, empty, leftSide, tail, emptyLeft)
      afterEquation <- inFront(logic, concat, empty, rightSide, tail, emptyLeft)

      stepDefinition <- forward.definition(Forward.Step).map(atNumbers)
      opened <- Conv.unfold(stepDefinition, List(system, before, after))
      existential <- rightOf(opened)
      witnessed <- withWitnesses(logic, existential, List(empty, leftSide, rightSide, tail)) { body =>
        for {
          pair <- logic.rules.conjIntro(beforeEquation, afterEquation)
          held <- logic.rules.conjIntro(rule, pair)
          _ <-
            if (held.conclusion == body) Right(())
            else Left(NotOfForm("the step's own clause", held.conclusion))
        } yield held
      }
      result <- Conv
        .sym(opened)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, witnessed)))
      _ <-
        if (result.conclusion == target) Right(())
        else Left(NotOfForm(s"$StepInhabited as it is written", result.conclusion))
    } yield result
  }

  /** `|- WORD_CONCAT block tail = WORD_CONCAT (WORD_CONCAT WORD_EMPTY block) tail`. */
  private def inFront(
    logic: Logic,
    concat: Term,
    empty: Term,
    block: Term,
    tail: Term,
    emptyLeft: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      collapsed <- logic.rules.spec(block, emptyLeft)
      moved <- Conv.apTerm(concat, collapsed).flatMap(Conv.apThm(_, tail))
      result <- Conv.sym(moved)
    } yield result

  /** A nest of existentials introduced at the given witnesses, innermost first. */
  private def withWitnesses(
    logic: Logic,
    existential: Term,
    witnesses: List[Term]
  )(
    at: Term => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    witnesses match {
      case Nil => at(existential)
      case witness :: rest =>
        for {
          predicate <- logic
            .destExistsPredicate(existential)
            .toRight(NotOfForm("an existential", existential))
          applied <- LogicError.lift(Term.app(predicate, witness))
          inner <- Conv.betaRoot(applied).flatMap(rightOf)
          proved <- withWitnesses(logic, inner, rest)(at)
          result <- logic.rules.existsIntro(predicate, witness, proved)
        } yield result
    }

  /* ------------------------------------------------------------------ the closure */

  /**
   * [[MarkedClosed]]: a step of the system takes a marked word to a marked word.
   *
   * A step is `u = x l y`, `v = x r y`, and the whole argument is which side of the marker the
   * rule fired on. The marker is the last letter of `u`, so either `y` is empty and the rule saw
   * the marker inside its own left-hand side, or `y` is not and the rule saw tail-free letters
   * only. `NUM_CASES` on `WORD_LENGTH y` is the split, [[Concatenation.LengthZero]] turns the
   * first branch's length back into `WORD_EMPTY`, and the two step lemmas carry the two branches.
   *
   * The four existentials of `WORD_STEP` are opened in the order the definition binds them, `x`,
   * `l`, `r`, `y`, and each witness is fresh against everything already in play: a witness that
   * collided with the statement's own `u` or `v` would escape into the conclusion and the
   * elimination would refuse it, which is the check `Rules.existsElim` makes.
   */
  private def closedUnderSteps(
    tools: Concrete,
    forward: Forward,
    concatenation: Concatenation,
    definitions: Map[String, Kernel.Thm],
    facts: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules
    val subject = Term.variable("u", Words)
    val result = Term.variable("v", Words)

    for {
      target <- statement(tools.theory, tools.notation, MarkedClosed)
      stripped <- Logic.stripForall(target)
      (variables, _) = stripped
      _ <-
        if (variables.size == 2) Right(())
        else Left(NotOfForm("a claim about two words", target))
      body <- openAt(logic, target, List(subject, result))
      parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (premiseTerm, conclusionTerm) = parts
      premise <- LogicError.lift(Kernel.assume(premiseTerm))
      markedSubject <- rules.conjElim1(premise)
      stepped <- rules.conjElim2(premise)

      marked <- tools.constant(Marked, Type.fun(Words, Type.Bool))
      tailFree <- tools.constant(TailFree, Type.fun(Words, Type.Bool))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      lengthOf <- tools.lengthOf
      order <- tools.strictOrder
      zero <- tools.zero
      system <- tools.constant(Name, Type.fun(Words, Type.fun(Words, Type.Bool)))

      emptyRight <- concatenation.fact(Concatenation.EmptyRight).map(atNumbers)
      lengthZero <- concatenation.fact(Concatenation.LengthZero).map(atNumbers)
      markedConcat <- facts.get(MarkedConcat).toRight(MissingDefinition(MarkedConcat))
      tailFreeConcat <- facts.get(TailFreeConcat).toRight(MissingDefinition(TailFreeConcat))
      ruleNotEmpty <- facts.get(RuleNotEmpty).toRight(MissingDefinition(RuleNotEmpty))
      markedStep <- facts.get(MarkedStep).toRight(MissingDefinition(MarkedStep))
      tailFreeStep <- facts.get(TailFreeStep).toRight(MissingDefinition(TailFreeStep))

      stepDefinition <- forward.definition(Forward.Step).map(atNumbers)
      opened <- Conv.unfold(stepDefinition, List(system, subject, result))
      existential <- LogicError.lift(Kernel.eqMp(opened, stepped))

      settled <- openWitnesses(
        logic,
        existential,
        4,
        Term.freeVariables(conclusionTerm) ++ Term.freeVariables(premiseTerm)
      ) { (witnesses, held) =>
        witnesses match {
          case List(front, left, right, tail) =>
            for {
              ruleHolds <- rules.conjElim1(held)
              rest <- rules.conjElim2(held)
              subjectEquation <- rules.conjElim1(rest)
              resultEquation <- rules.conjElim2(rest)

              sizes <- rules.specAll(ruleNotEmpty, List(left, right)).flatMap(rules.mp(_, ruleHolds))
              leftPositive <- rules.conjElim1(sizes)
              rightPositive <- rules.conjElim2(sizes)

              blockLeft <- LogicError.lift(Term.appAll(concat, List(front, left)))
              blockRight <- LogicError.lift(Term.appAll(concat, List(front, right)))
              tailLength <- LogicError.lift(Term.app(lengthOf, tail))

              cases <- rules.spec(tailLength, tools.numbers.zeroOrSuccessor)
              disjuncts <- logic
                .destDisj(cases.conclusion)
                .toRight(NotOfForm("a disjunction", cases.conclusion))
              (isZero, isSuccessor) = disjuncts

              atEnd <- {
                for {
                  assumedZero <- LogicError.lift(Kernel.assume(isZero))
                  tailEmpty <- rules.spec(tail, lengthZero).flatMap(rules.mp(_, assumedZero))
                  onLeft <- collapsedTail(logic, concat, blockLeft, tailEmpty, emptyRight)
                  onRight <- collapsedTail(logic, concat, blockRight, tailEmpty, emptyRight)

                  atBlock <- Conv
                    .trans(subjectEquation, onLeft)
                    .flatMap(Conv.apTerm(marked, _))
                    .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, markedSubject)))
                  split <- rules
                    .specAll(markedConcat, List(front, left))
                    .flatMap(rules.mp(_, leftPositive))
                  both <- LogicError.lift(Kernel.eqMp(split, atBlock))
                  tailFreeFront <- rules.conjElim1(both)
                  markedLeft <- rules.conjElim2(both)
                  markedRight <- rules
                    .conjIntro(ruleHolds, markedLeft)
                    .flatMap(pair =>
                      rules.specAll(markedStep, List(left, right)).flatMap(rules.mp(_, pair))
                    )
                  splitRight <- rules
                    .specAll(markedConcat, List(front, right))
                    .flatMap(rules.mp(_, rightPositive))
                  markedBlock <- rules
                    .conjIntro(tailFreeFront, markedRight)
                    .flatMap(pair =>
                      Conv.sym(splitRight).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, pair)))
                    )
                  answer <- Conv
                    .trans(resultEquation, onRight)
                    .flatMap(Conv.sym)
                    .flatMap(Conv.apTerm(marked, _))
                    .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, markedBlock)))
                } yield answer
              }

              inside <- {
                val predecessor = Conv.freshVariable(
                  "k",
                  Numbers,
                  Term.freeVariables(conclusionTerm) ++ Term.freeVariables(isSuccessor)
                )

                for {
                  assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
                  predicate <- logic
                    .destExistsPredicate(isSuccessor)
                    .toRight(NotOfForm("an existential", isSuccessor))
                  applied <- LogicError.lift(Term.app(predicate, predecessor))
                  instance <- Conv.betaRoot(applied).flatMap(rightOf)
                  size <- LogicError.lift(Kernel.assume(instance))

                  tailPositive <- rules
                    .spec(predecessor, tools.numbers.successorPositive)
                    .flatMap(fact => Conv.sym(size).flatMap(carryRight(order, zero, _, fact)))

                  atBlock <- Conv
                    .apTerm(marked, subjectEquation)
                    .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, markedSubject)))
                  split <- rules
                    .specAll(markedConcat, List(blockLeft, tail))
                    .flatMap(rules.mp(_, tailPositive))
                  both <- LogicError.lift(Kernel.eqMp(split, atBlock))
                  tailFreeBlock <- rules.conjElim1(both)
                  markedTail <- rules.conjElim2(both)

                  splitBlock <- rules.specAll(tailFreeConcat, List(front, left))
                  pieces <- LogicError.lift(Kernel.eqMp(splitBlock, tailFreeBlock))
                  tailFreeFront <- rules.conjElim1(pieces)
                  tailFreeLeft <- rules.conjElim2(pieces)
                  tailFreeRight <- rules
                    .conjIntro(ruleHolds, tailFreeLeft)
                    .flatMap(pair =>
                      rules.specAll(tailFreeStep, List(left, right)).flatMap(rules.mp(_, pair))
                    )
                  splitRight <- rules.specAll(tailFreeConcat, List(front, right))
                  tailFreeBlockRight <- rules
                    .conjIntro(tailFreeFront, tailFreeRight)
                    .flatMap(pair =>
                      Conv.sym(splitRight).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, pair)))
                    )
                  splitTail <- rules
                    .specAll(markedConcat, List(blockRight, tail))
                    .flatMap(rules.mp(_, tailPositive))
                  markedWhole <- rules
                    .conjIntro(tailFreeBlockRight, markedTail)
                    .flatMap(pair =>
                      Conv.sym(splitTail).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, pair)))
                    )
                  answer <- Conv
                    .sym(resultEquation)
                    .flatMap(Conv.apTerm(marked, _))
                    .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, markedWhole)))
                  closed <- rules.existsElim(assumedSuccessor, predecessor, answer)
                } yield closed
              }

              answer <- rules.disjElim(cases, atEnd, inside)
            } yield answer

          case other => Left(NotOfForm("four witnesses", Term.variable(other.size.toString, Words)))
        }
      }

      discharged <- rules.disch(premiseTerm, settled)
      generalised <- rules.genAll(discharged, List(subject, result))
      _ <-
        if (generalised.conclusion == target) Right(())
        else Left(NotOfForm(s"$MarkedClosed as it is written", generalised.conclusion))
    } yield generalised
  }

  /**
   * [[AnchoredClosed]]: a step out of an anchored word lands in one.
   *
   * [[closedUnderSteps]] in a mirror, and the mirror is not quite an image: the marker is at the
   * front, so the division is on the **prefix** the rule fired after, and the block that has to be
   * non-empty for the split to hold is the one on the left of it.
   *
   * Either the prefix is empty, and then the marker is inside the rule's own left-hand side and
   * [[AnchoredStep]] carries it; or it is not, and then the marker is in the prefix, the rule saw
   * head-free letters only, and [[HeadFreeStep]] carries those. `NUM_CASES` on the prefix's length
   * is the split and `Concatenation.LengthZero` turns the zero case back into the empty word.
   *
   * One thing here has no counterpart in the marked proof. `S2_ANCHORED_CONCAT` asks that its first
   * block be non-empty, and in the second branch that block is `WORD_CONCAT x l` rather than a
   * witness the step handed over, so its length is a sum and the positivity has to be derived:
   * `0 < |x| <= |x| + |l|` against `Concatenation.Length`, which is [[positiveBlock]].
   */
  private def anchoredUnderSteps(
    tools: Concrete,
    forward: Forward,
    concatenation: Concatenation,
    definitions: Map[String, Kernel.Thm],
    facts: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules
    val subject = Term.variable("u", Words)
    val result = Term.variable("v", Words)

    for {
      target <- statement(tools.theory, tools.notation, AnchoredClosed)
      stripped <- Logic.stripForall(target)
      (variables, _) = stripped
      _ <-
        if (variables.size == 2) Right(())
        else Left(NotOfForm("a claim about two words", target))
      body <- openAt(logic, target, List(subject, result))
      parts <- logic.destImp(body).toRight(NotOfForm("an implication", body))
      (premiseTerm, conclusionTerm) = parts
      premise <- LogicError.lift(Kernel.assume(premiseTerm))
      anchoredSubject <- rules.conjElim1(premise)
      stepped <- rules.conjElim2(premise)

      anchored <- tools.constant(Anchored, Type.fun(Words, Type.Bool))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      lengthOf <- tools.lengthOf
      order <- tools.strictOrder
      zero <- tools.zero
      system <- tools.constant(Name, Type.fun(Words, Type.fun(Words, Type.Bool)))

      emptyLeft <- concatenation.fact(Concatenation.EmptyLeft).map(atNumbers)
      concatLength <- concatenation.fact(Concatenation.Length).map(atNumbers)
      lengthZero <- concatenation.fact(Concatenation.LengthZero).map(atNumbers)
      anchoredConcat <- facts.get(AnchoredConcat).toRight(MissingDefinition(AnchoredConcat))
      headFreeConcat <- facts.get(HeadFreeConcat).toRight(MissingDefinition(HeadFreeConcat))
      ruleNotEmpty <- facts.get(RuleNotEmpty).toRight(MissingDefinition(RuleNotEmpty))
      anchoredStep <- facts.get(AnchoredStep).toRight(MissingDefinition(AnchoredStep))
      headFreeStep <- facts.get(HeadFreeStep).toRight(MissingDefinition(HeadFreeStep))

      stepDefinition <- forward.definition(Forward.Step).map(atNumbers)
      opened <- Conv.unfold(stepDefinition, List(system, subject, result))
      existential <- LogicError.lift(Kernel.eqMp(opened, stepped))

      settled <- openWitnesses(
        logic,
        existential,
        4,
        Term.freeVariables(conclusionTerm) ++ Term.freeVariables(premiseTerm)
      ) { (witnesses, held) =>
        witnesses match {
          case List(front, left, right, tail) =>
            for {
              ruleHolds <- rules.conjElim1(held)
              rest <- rules.conjElim2(held)
              subjectEquation <- rules.conjElim1(rest)
              resultEquation <- rules.conjElim2(rest)

              sizes <- rules.specAll(ruleNotEmpty, List(left, right)).flatMap(rules.mp(_, ruleHolds))
              leftPositive <- rules.conjElim1(sizes)
              rightPositive <- rules.conjElim2(sizes)

              blockLeft <- LogicError.lift(Term.appAll(concat, List(front, left)))
              blockRight <- LogicError.lift(Term.appAll(concat, List(front, right)))
              frontLength <- LogicError.lift(Term.app(lengthOf, front))

              cases <- rules.spec(frontLength, tools.numbers.zeroOrSuccessor)
              disjuncts <- logic
                .destDisj(cases.conclusion)
                .toRight(NotOfForm("a disjunction", cases.conclusion))
              (isZero, isSuccessor) = disjuncts

              atTheFront <- {
                for {
                  assumedZero <- LogicError.lift(Kernel.assume(isZero))
                  frontEmpty <- rules.spec(front, lengthZero).flatMap(rules.mp(_, assumedZero))
                  onLeft <- collapsedFront(logic, concat, front, left, tail, frontEmpty, emptyLeft)
                  onRight <- collapsedFront(logic, concat, front, right, tail, frontEmpty, emptyLeft)

                  atBlock <- Conv
                    .trans(subjectEquation, onLeft)
                    .flatMap(Conv.apTerm(anchored, _))
                    .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, anchoredSubject)))
                  split <- rules
                    .specAll(anchoredConcat, List(left, tail))
                    .flatMap(rules.mp(_, leftPositive))
                  both <- LogicError.lift(Kernel.eqMp(split, atBlock))
                  anchoredLeft <- rules.conjElim1(both)
                  headFreeTail <- rules.conjElim2(both)
                  anchoredRight <- rules
                    .conjIntro(ruleHolds, anchoredLeft)
                    .flatMap(pair =>
                      rules.specAll(anchoredStep, List(left, right)).flatMap(rules.mp(_, pair))
                    )
                  splitRight <- rules
                    .specAll(anchoredConcat, List(right, tail))
                    .flatMap(rules.mp(_, rightPositive))
                  anchoredBlock <- rules
                    .conjIntro(anchoredRight, headFreeTail)
                    .flatMap(pair =>
                      Conv.sym(splitRight).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, pair)))
                    )
                  answer <- Conv
                    .trans(resultEquation, onRight)
                    .flatMap(Conv.sym)
                    .flatMap(Conv.apTerm(anchored, _))
                    .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, anchoredBlock)))
                } yield answer
              }

              inside <- {
                val predecessor = Conv.freshVariable(
                  "k",
                  Numbers,
                  Term.freeVariables(conclusionTerm) ++ Term.freeVariables(isSuccessor)
                )

                for {
                  assumedSuccessor <- LogicError.lift(Kernel.assume(isSuccessor))
                  predicate <- logic
                    .destExistsPredicate(isSuccessor)
                    .toRight(NotOfForm("an existential", isSuccessor))
                  applied <- LogicError.lift(Term.app(predicate, predecessor))
                  instance <- Conv.betaRoot(applied).flatMap(rightOf)
                  size <- LogicError.lift(Kernel.assume(instance))

                  frontPositive <- rules
                    .spec(predecessor, tools.numbers.successorPositive)
                    .flatMap(fact => Conv.sym(size).flatMap(carryRight(order, zero, _, fact)))
                  blockLeftPositive <- positiveBlock(
                    tools, concatLength, order, zero, front, left, frontPositive)
                  blockRightPositive <- positiveBlock(
                    tools, concatLength, order, zero, front, right, frontPositive)

                  atBlock <- Conv
                    .apTerm(anchored, subjectEquation)
                    .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, anchoredSubject)))
                  split <- rules
                    .specAll(anchoredConcat, List(blockLeft, tail))
                    .flatMap(rules.mp(_, blockLeftPositive))
                  both <- LogicError.lift(Kernel.eqMp(split, atBlock))
                  anchoredBlock <- rules.conjElim1(both)
                  headFreeTail <- rules.conjElim2(both)

                  splitBlock <- rules
                    .specAll(anchoredConcat, List(front, left))
                    .flatMap(rules.mp(_, frontPositive))
                  pieces <- LogicError.lift(Kernel.eqMp(splitBlock, anchoredBlock))
                  anchoredFront <- rules.conjElim1(pieces)
                  headFreeLeft <- rules.conjElim2(pieces)
                  headFreeRight <- rules
                    .conjIntro(ruleHolds, headFreeLeft)
                    .flatMap(pair =>
                      rules.specAll(headFreeStep, List(left, right)).flatMap(rules.mp(_, pair))
                    )
                  splitRight <- rules
                    .specAll(anchoredConcat, List(front, right))
                    .flatMap(rules.mp(_, frontPositive))
                  anchoredBlockRight <- rules
                    .conjIntro(anchoredFront, headFreeRight)
                    .flatMap(pair =>
                      Conv.sym(splitRight).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, pair)))
                    )
                  splitWhole <- rules
                    .specAll(anchoredConcat, List(blockRight, tail))
                    .flatMap(rules.mp(_, blockRightPositive))
                  anchoredWhole <- rules
                    .conjIntro(anchoredBlockRight, headFreeTail)
                    .flatMap(pair =>
                      Conv.sym(splitWhole).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, pair)))
                    )
                  answer <- Conv
                    .sym(resultEquation)
                    .flatMap(Conv.apTerm(anchored, _))
                    .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, anchoredWhole)))
                  closed <- rules.existsElim(assumedSuccessor, predecessor, answer)
                } yield closed
              }

              answer <- rules.disjElim(cases, atTheFront, inside)
            } yield answer

          case other => Left(NotOfForm("four witnesses", Term.variable(other.size.toString, Words)))
        }
      }

      discharged <- rules.disch(premiseTerm, settled)
      generalised <- rules.genAll(discharged, List(subject, result))
      _ <-
        if (generalised.conclusion == target) Right(())
        else Left(NotOfForm(s"$AnchoredClosed as it is written", generalised.conclusion))
    } yield generalised
  }

  /**
   * `|- WORD_CONCAT (WORD_CONCAT front block) tail = WORD_CONCAT block tail`, the front being empty.
   *
   * [[collapsedTail]] at the other end, and it takes one step more: the empty word disappears on
   * the left of a concatenation that is itself the left argument of another, so the equation has to
   * be carried under the outer application as well as proved under the inner one.
   */
  private def collapsedFront(
    logic: Logic,
    concat: Term,
    front: Term,
    block: Term,
    tail: Term,
    frontEmpty: Kernel.Thm,
    emptyLeft: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      moved <- Conv.apTerm(concat, frontEmpty).flatMap(Conv.apThm(_, block))
      collapsed <- logic.rules.spec(block, emptyLeft)
      inner <- Conv.trans(moved, collapsed)
      result <- Conv.apTerm(concat, inner).flatMap(Conv.apThm(_, tail))
    } yield result

  /** `|- 0 < WORD_LENGTH (WORD_CONCAT front block)` from `|- 0 < WORD_LENGTH front`. */
  private def positiveBlock(
    tools: Concrete,
    concatLength: Kernel.Thm,
    order: Term,
    zero: Term,
    front: Term,
    block: Term,
    frontPositive: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      lengths <- rules.specAll(concatLength, List(front, block))
      sides <- Term.destEq(lengths.conclusion).toRight(NotOfForm("an equation", lengths.conclusion))
      (_, sum) = sides
      lengthConstant <- tools.lengthOf
      sizeFront <- LogicError.lift(Term.app(lengthConstant, front))
      sizeBlock <- LogicError.lift(Term.app(lengthConstant, block))
      atMost <- rules.specAll(tools.numbers.atMostSum, List(sizeFront, sizeBlock))
      pair <- rules.conjIntro(frontPositive, atMost)
      positiveSum <- rules
        .specAll(tools.numbers.belowThenAtMost, List(zero, sizeFront, sum))
        .flatMap(rules.mp(_, pair))
      result <- Conv.sym(lengths).flatMap(carryRight(order, zero, _, positiveSum))
    } yield result
  }

  /** `|- WORD_CONCAT block tail = block`, the tail having been shown to be the empty word. */
  private def collapsedTail(
    logic: Logic,
    concat: Term,
    block: Term,
    tailEmpty: Kernel.Thm,
    emptyRight: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- LogicError.lift(Term.app(concat, block))
      moved <- Conv.apTerm(partial, tailEmpty)
      collapsed <- logic.rules.spec(block, emptyRight)
      result <- Conv.trans(moved, collapsed)
    } yield result

  /** `!x y. body` opened at the given arguments, beta-contracted, one quantifier at a time. */
  private def openAt(
    logic: Logic,
    statement: Term,
    arguments: List[Term]
  ): Either[LogicError, Term] =
    arguments.foldLeft[Either[LogicError, Term]](Right(statement)) { (accumulated, argument) =>
      for {
        current <- accumulated
        predicate <- logic
          .destForallPredicate(current)
          .toRight(NotOfForm("a quantified claim", current))
        applied <- LogicError.lift(Term.app(predicate, argument))
        opened <- Conv.betaRoot(applied).flatMap(rightOf)
      } yield opened
    }

  /** A nest of existentials opened at fresh witnesses, and closed again over what they proved. */
  private def openWitnesses(
    logic: Logic,
    existential: Kernel.Thm,
    depth: Int,
    taken: Set[FVar]
  )(
    at: (List[FVar], Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    def walk(
      current: Kernel.Thm,
      remaining: Int,
      avoid: Set[FVar],
      witnesses: List[FVar]
    ): Either[LogicError, Kernel.Thm] =
      if (remaining == 0) at(witnesses.reverse, current)
      else
        for {
          predicate <- logic
            .destExistsPredicate(current.conclusion)
            .toRight(NotOfForm("an existential", current.conclusion))
          domain <- Type
            .destFun(Term.typeOf(predicate))
            .map(_._1)
            .toRight(NotOfForm("a predicate", predicate))
          witness = Conv.freshVariable("w", domain, avoid ++ Term.freeVariables(predicate))
          applied <- LogicError.lift(Term.app(predicate, witness))
          instance <- Conv.betaRoot(applied).flatMap(rightOf)
          assumed <- LogicError.lift(Kernel.assume(instance))
          proved <- walk(assumed, remaining - 1, avoid + witness, witness :: witnesses)
          closed <- logic.rules.existsElim(current, witness, proved)
        } yield closed

    walk(existential, depth, taken, Nil)
  }

  /* ------------------------------------------------------------------ the proofs */

  private def statement(
    theory: Theory,
    notation: Notation,
    name: String
  ): Either[LogicError, Term] =
    Statements
      .collectFirst { case (label, text) if label == name => text }
      .toRight(MissingDefinition(name))
      .flatMap(text => Parser.proposition(theory, notation, text))

  /**
   * [[CountedIsRule]]: every clause of `S2_COUNTED` is a clause of `S2`.
   *
   * The two definitions are disjunctions over the same shape and the six of `A` are literally six
   * of the eleven, so the proof is: unfold both, assume the six-way disjunction, and in each case
   * introduce the matching disjunct of the eleven. The rewriter does the unfolding and `Minimal`
   * does the propositional step, which is the one place in this file where a search is used at all
   * and it costs nothing: the fragment is a disjunction of conjunctions of equations with no
   * negation in it.
   */
  private def countedAreRules(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      target <- statement(theory, notation, CountedIsRule)
      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      counted <- definitions.get(Counted).toRight(MissingDefinition(Counted))
      rules <- unfoldingRules(logic, Vector(system, counted))

      // Minimal decides a propositional fragment, so the two quantifiers come off first and go
      // back on at the end. What is left between them is a disjunction of conjunctions of
      // equations with no negation in it, which is exactly the fragment, and it costs no axiom --
      // the reason this proof is not `Propositional`, which would decide the same goal and charge
      // `SELECT` for a classical step it does not need.
      body <- strippedBody(logic, target)
      opened <- Rewrite.rewrite(rules, body).flatMap(rightOf)
      proved <- Minimal(logic).prove(opened)
      inBody <- shapeBack(logic, rules, body, proved)
      result <- logic.rules.gen(RightSide, inBody).flatMap(logic.rules.gen(LeftSide, _))
    } yield result

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def unfoldingRules(
    logic: Logic,
    definitions: Vector[Kernel.Thm]
  ): Either[LogicError, Vector[Rewrite.Rule]] =
    definitions.foldLeft[Either[LogicError, Vector[Rewrite.Rule]]](Right(Vector.empty)) {
      (accumulated, definition) =>
        for {
          rules <- accumulated
          rule <- Rewrite.Rule.of(logic, definition)
        } yield rules :+ rule
    }

  private def shapeBack(
    logic: Logic,
    rules: Vector[Rewrite.Rule],
    target: Term,
    proved: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Rewrite.rewrite(rules, target).flatMap(Conv.sym).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, proved)))

  /**
   * [[Inhabited]]: the system relates something to something.
   *
   * The guard against the whole file being vacuous, and it is the cheapest of the three: `R1` is a
   * clause of the definition, so the proof is to unfold, supply that clause by reflexivity on both
   * sides, and close the two existentials at its own two words.
   */
  private def inhabitedProof(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      target <- statement(theory, notation, Inhabited)
      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      rules <- unfoldingRules(logic, Vector(system))
      opened <- Rewrite.rewrite(rules, target).flatMap(rightOf)

      // By hand and not by a search: this is an existential, and none of the three procedures in
      // this repository takes a quantifier. The witnesses are `R1`'s own two words, so each side
      // closes by reflexivity and the only work is putting the pair under the two binders.
      left <- Parser.term(theory, notation, RuleOneLeft, Words)
      right <- Parser.term(theory, notation, RuleOneRight, Words)
      witnessed <- firstDisjunctAt(logic, opened, left, right)
      result <- shapeBack(logic, rules, target, witnessed)
    } yield result

  /**
   * The innermost body of `?l r. c1 \/ rest` proved at two witnesses, by reflexivity on `R1`.
   *
   * The disjunction is right-nested and `R1` is the first clause, so the proof is one
   * `disjIntro1` over a conjunction of two reflexivities, closed under the two existentials.
   */
  private def firstDisjunctAt(
    logic: Logic,
    existential: Term,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      outer <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
      atLeft <- LogicError.lift(Term.app(outer, left))
      openedLeft <- Conv.betaRoot(atLeft).flatMap(rightOf)
      inner <- logic.destExistsPredicate(openedLeft).toRight(NotOfForm("an existential", openedLeft))
      atRight <- LogicError.lift(Term.app(inner, right))
      body <- Conv.betaRoot(atRight).flatMap(rightOf)

      sides <- logic.destDisj(body).toRight(NotOfForm("a disjunction", body))
      (clause, rest) = sides
      pair <- logic.destConj(clause).toRight(NotOfForm("a conjunction", clause))
      (leftEq, rightEq) = pair
      leftTerm <- Term.destEq(leftEq).map(_._1).toRight(NotOfForm("an equation", leftEq))
      rightTerm <- Term.destEq(rightEq).map(_._1).toRight(NotOfForm("an equation", rightEq))
      both <- rules.conjIntro(Conv.refl(leftTerm), Conv.refl(rightTerm))
      chosen <- rules.disjIntro1(rest, both)

      closedInner <- rules.existsIntro(inner, right, chosen)
      closedOuter <- rules.existsIntro(outer, left, closedInner)
    } yield closedOuter
  }

  /* ------------------------------------------- the class, and why it is the anchored one */

  /**
   * The two counterexamples that say [[Anchored]] cannot be weakened to [[Marked]].
   *
   * Each is the antecedents of one published statement, with `S2_ANCHORED` dropped, holding at a
   * concrete pair where that statement's conclusion is refuted. It is `ReachingSpec`'s idiom at the
   * lemma this development instantiates, and it is the only form a negative control can take here:
   * a theorem does not refuse, so nothing can be asserted about a statement nobody proved, and what
   * is exhibited instead is the instance that makes it false.
   *
   * **What this replaced.** Until 2026-09-21 the reason the class is the anchored one and not the
   * marked one rested on six figures, measured over every word of at most seven letters, living in
   * two copies of prose and read by no test. A figure of that kind is a property of the
   * enumeration's bound as much as of the system; these two are theorems the kernel checked, and
   * they are what those figures were evidence for.
   */
  private[theories] final case class ClassWitnesses(
    counted: CountedWitness,
    plain: PlainWitness
  ) {

    /** Every witness beside the name [[WitnessStatements]] writes it down under. */
    def named: Vector[(String, Kernel.Thm)] = Vector(
      CountedIsMarked -> counted.marked,
      CountedIsNotAnchored -> counted.notAnchored,
      CountedStepHolds -> counted.stepped,
      CountedMeasureStands -> counted.measureStands,
      PlainIsMarked -> plain.marked,
      PlainIsNotAnchored -> plain.notAnchored,
      PlainStepHolds -> plain.stepped,
      PlainStepIsNotCounted -> plain.notCounted,
      PlainMeasureFalls -> plain.measureFalls
    )
  }

  /* The nine names, so that a witness and the text it is read by cannot be paired by position. */

  val CountedIsMarked: String = "S2_COUNTED_WITNESS_MARKED"

  val CountedIsNotAnchored: String = "S2_COUNTED_WITNESS_NOT_ANCHORED"

  val CountedStepHolds: String = "S2_COUNTED_WITNESS_STEP"

  val CountedMeasureStands: String = "S2_COUNTED_WITNESS_MEASURE"

  val PlainIsMarked: String = "S2_PLAIN_WITNESS_MARKED"

  val PlainIsNotAnchored: String = "S2_PLAIN_WITNESS_NOT_ANCHORED"

  val PlainStepHolds: String = "S2_PLAIN_WITNESS_STEP"

  val PlainStepIsNotCounted: String = "S2_PLAIN_WITNESS_NOT_COUNTED"

  val PlainMeasureFalls: String = "S2_PLAIN_WITNESS_MEASURE"

  /**
   * What each witness says, as text, which is what says the nine are the nine claimed.
   *
   * The same discipline [[Statements]] carries, at facts this development does not publish: a
   * derivation that reached a theorem about some other word or some other relation is true and is
   * not the counterexample, and nothing in its shape would say so. `CollatzSpec` is what compares
   * them, which is where [[separations]] is checked too and for the same reason.
   */
  private[theories] val WitnessStatements: Vector[(String, String)] = Vector(
    CountedIsMarked -> s"S2_MARKED (${wordText(spell("f0."))})",
    CountedIsNotAnchored -> s"~(S2_ANCHORED (${wordText(spell("f0."))}))",
    CountedStepHolds ->
      s"WORD_STEP S2_COUNTED (${wordText(spell("f0."))}) (${wordText(spell("0f."))})",
    CountedMeasureStands ->
      (s"~(S2_PHI (${wordText(spell("f0."))}) = " +
        s"SUC (S2_PHI (${wordText(spell("0f."))})))"),
    PlainIsMarked -> s"S2_MARKED (${wordText(spell("0/0."))})",
    PlainIsNotAnchored -> s"~(S2_ANCHORED (${wordText(spell("0/0."))}))",
    PlainStepHolds -> s"WORD_STEP S2 (${wordText(spell("0/0."))}) (${wordText(spell("0/t."))})",
    PlainStepIsNotCounted ->
      s"~(WORD_STEP S2_COUNTED (${wordText(spell("0/0."))}) (${wordText(spell("0/t."))}))",
    PlainMeasureFalls ->
      (s"~(NUM_LE (S2_PHI (${wordText(spell("0/0."))})) " +
        s"(S2_PHI (${wordText(spell("0/t."))})))")
  )

  /**
   * `f0.` is marked, is not anchored, steps by `A2` to `0f.`, and the measure does not fall.
   *
   * [[PotentialCountedStep]] with `S2_ANCHORED u` dropped, refuted. `A2` fires at position zero,
   * and there the weight of a digit is `0 - 1` over a truncated subtraction, which is what a digit
   * at position one weighs too: both words measure nothing, so `S2_PHI u = SUC (S2_PHI v)` says
   * `ZERO = SUC ZERO`. Every field holds with nothing assumed.
   */
  private[theories] final case class CountedWitness(
    marked: Kernel.Thm,
    notAnchored: Kernel.Thm,
    stepped: Kernel.Thm,
    measureStands: Kernel.Thm
  )

  /**
   * `0/0.` is marked, is not anchored, steps by `B1` to `0/t.`, nothing counts it, and the measure
   * falls.
   *
   * [[PotentialPlainStep]] with `S2_ANCHORED u` dropped, refuted. The antecedent that costs
   * something is [[notCounted]]: it is a **negative** about a relation, so exhibiting which rule
   * fired does not give it, and [[noCountedStepFrom]] is what does. The second digit sits at
   * position two and weighs one, `B1` turns it into a `t`, and `t` is not a digit, so the measure
   * goes from one to nothing across a step nothing counts. Every field holds with nothing assumed.
   */
  private[theories] final case class PlainWitness(
    marked: Kernel.Thm,
    notAnchored: Kernel.Thm,
    stepped: Kernel.Thm,
    notCounted: Kernel.Thm,
    measureFalls: Kernel.Thm
  )

  /** `0/0.`, marked and not anchored, and `0/t.`, which `B1` turns it into. */
  private val BeforeTheUncountedStep: Vector[String] = spell("0/0.")

  private val AfterTheUncountedStep: Vector[String] = spell("0/t.")

  /** `f0.`, marked and not anchored, and `0f.`, which `A2` turns it into. */
  private val BeforeTheCountedStep: Vector[String] = spell("f0.")

  private val AfterTheCountedStep: Vector[String] = spell("0f.")

  private def classWitnesses(
    tools: Concrete,
    forward: Forward,
    definitions: Map[String, Kernel.Thm],
    facts: Map[String, Kernel.Thm]
  ): Either[LogicError, ClassWitnesses] = {
    val concatenation = forward.concatenation

    for {
      // `COND` is polymorphic in its branches and the measure's is `num`, which is the same
      // instantiation every other reader of these two rules in this file makes.
      conditional <- forward.inductive.classical.fact(Classical.CondTrue).map(atNumbers)
      conditionalFalse <- forward.inductive.classical.fact(Classical.CondFalse).map(atNumbers)

      marked <- markedWord(tools, BeforeTheCountedStep)
      notAnchored <- notAnchoredWord(tools, BeforeTheCountedStep)
      stepped <- stepAt(
        tools,
        concatenation,
        forward,
        definitions,
        CountedRules,
        Counted,
        "A2",
        Vector.empty,
        BeforeTheCountedStep.drop(2)
      )
      measureStands <- successorIsRefused(
        tools,
        definitions,
        conditional,
        conditionalFalse,
        BeforeTheCountedStep,
        AfterTheCountedStep
      )

      markedPlain <- markedWord(tools, BeforeTheUncountedStep)
      notAnchoredPlain <- notAnchoredWord(tools, BeforeTheUncountedStep)
      steppedPlain <- stepAt(
        tools,
        concatenation,
        forward,
        definitions,
        Rules,
        Name,
        "B1",
        BeforeTheUncountedStep.take(1),
        BeforeTheUncountedStep.drop(3)
      )
      notCounted <- noCountedStepFrom(
        tools,
        forward,
        concatenation,
        definitions,
        BeforeTheUncountedStep,
        AfterTheUncountedStep
      )
      measureFalls <- atMostIsRefused(
        tools,
        definitions,
        conditional,
        conditionalFalse,
        BeforeTheUncountedStep,
        AfterTheUncountedStep
      )
    } yield ClassWitnesses(
      CountedWitness(marked, notAnchored, stepped, measureStands),
      PlainWitness(markedPlain, notAnchoredPlain, steppedPlain, notCounted, measureFalls)
    )
  }

  /**
   * `|- ~(S2_PHI <before> = SUC (S2_PHI <after>))`: both measures evaluated, then told apart.
   *
   * `Successor.distinct` settles the two numerals, which is the instrument the letters are told
   * apart by one floor down. The refusal is then carried back onto the two `S2_PHI` terms, because
   * what has to be false is the lemma's conclusion as the lemma writes it and not a claim about
   * numerals that happens to have the same content.
   */
  private def successorIsRefused(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm],
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm,
    before: Vector[String],
    after: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic

    for {
      leftMeasure <- measureIsNumeral(tools, definitions, conditional, conditionalFalse, before)
      rightMeasure <- measureIsNumeral(tools, definitions, conditional, conditionalFalse, after)
      leftValue <- rightOf(leftMeasure)

      successorOf <- tools.successorOf
      raised <- Conv.apTerm(successorOf, rightMeasure)
      successorOfRight <- rightOf(raised)
      apart <- numeralsApart(tools, leftValue, successorOfRight)

      equality <- equalityAt(leftValue, successorOfRight)
      result <- notRelation(logic, equality, leftMeasure, raised, apart)
    } yield result
  }

  /**
   * `|- S2_PHI <word> = SUC^n ZERO`, refused rather than handed on where it is not a numeral.
   *
   * [[potentialOfWord]] evaluates the sum and what comes out is whatever the fold rules leave, and
   * both readers below compare that with another number. A comparison is available in successor
   * form and in no other, so the check belongs here once rather than arriving as a refusal from
   * inside whichever comparison met it. It is also what says this file's arithmetic reaches every
   * position of a word: the fold set was one rule short of position zero until 2026-09-21, and what
   * it left there was the right number in a shape nothing could read.
   */
  private def measureIsNumeral(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm],
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm,
    letters: Vector[String]
  ): Either[LogicError, Kernel.Thm] =
    for {
      measure <- potentialOfWord(tools, letters, definitions, conditional, conditionalFalse)
      value <- rightOf(measure)
      count <- countOfSuccessors(tools, value)
      spelled <- tools.numeral(count)
      _ <-
        if (spelled == value) Right(())
        else Left(NotOfForm("the measure as a run of successors", value))
    } yield measure

  /**
   * `|- ~(SUC^a ZERO = SUC^b ZERO)`, through the order rather than through the bit encoding.
   *
   * `Successor.distinct` is the instrument for two numerals **as written**, which here means the
   * bit encoding; every number in this file is already a run of successors, which that reader
   * refuses by name. Two runs of different lengths are ordered by [[numeralBelow]], and an equation
   * between them would put one of them strictly below itself, which `NUM_LT_IRREFL` denies.
   */
  private def numeralsApart(
    tools: Concrete,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    for {
      leftCount <- countOfSuccessors(tools, left)
      rightCount <- countOfSuccessors(tools, right)
      _ <-
        if (leftCount != rightCount) Right(())
        else Left(NotOfForm(s"two numerals with different values, and both are $leftCount", left))

      order <- tools.strictOrder
      below <- numeralBelow(tools, leftCount.min(rightCount), leftCount.max(rightCount))
      claim <- LogicError.lift(Term.eq(left, right))
      assumed <- LogicError.lift(Kernel.assume(claim))

      // Either way round the equation collapses the pair onto the larger of the two, and it is the
      // larger because that is the one the order names on the side the equation does not rewrite.
      reflexive <-
        if (leftCount < rightCount) Conv.sym(assumed).flatMap(carryLeft(order, _, right, below))
        else carryRight(order, right, assumed, below)
      never <- rules.spec(right, tools.numbers.strictIrreflexive)
      absurd <- rules.notElim(never, reflexive)
      result <- rules.notIntro(claim, absurd)
    } yield result
  }

  /**
   * `|- ~(NUM_LE (S2_PHI <before>) (S2_PHI <after>))`, which is the measure falling across a step.
   *
   * `NUM_LT_EXCLUDES_LE` at the two evaluated measures: the second is strictly below the first, and
   * on `num` that is what denies the order the other way round. No case split and no classical
   * step, which is the shape `ReachingSpec` refutes its own `1 <= 0` with.
   */
  private def atMostIsRefused(
    tools: Concrete,
    definitions: Map[String, Kernel.Thm],
    conditional: Kernel.Thm,
    conditionalFalse: Kernel.Thm,
    before: Vector[String],
    after: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      leftMeasure <- measureIsNumeral(tools, definitions, conditional, conditionalFalse, before)
      rightMeasure <- measureIsNumeral(tools, definitions, conditional, conditionalFalse, after)
      leftValue <- rightOf(leftMeasure)
      rightValue <- rightOf(rightMeasure)

      leftCount <- countOfSuccessors(tools, leftValue)
      rightCount <- countOfSuccessors(tools, rightValue)
      _ <-
        if (rightCount < leftCount) Right(())
        else Left(NotOfForm(s"a measure strictly below $leftCount", rightValue))

      below <- numeralBelow(tools, rightCount, leftCount)
      apart <- rules
        .specAll(tools.numbers.belowExcludesAtMost, List(rightValue, leftValue))
        .flatMap(rules.mp(_, below))

      order <- tools.constant(Peano.NonStrictOrder, OrderType)
      result <- notRelation(logic, order, leftMeasure, rightMeasure, apart)
    } yield result
  }

  /** `|- ~(R A B)` from `|- A = a`, `|- B = b` and `|- ~(R a b)`: both arguments replaced. */
  private def notRelation(
    logic: Logic,
    relation: Term,
    left: Kernel.Thm,
    right: Kernel.Thm,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      subject <- leftOf(right)
      replacement <- rightOf(left)
      atLeft <- Conv.apTerm(relation, left).flatMap(Conv.apThm(_, subject))
      partial <- LogicError.lift(Term.app(relation, replacement))
      atRight <- Conv.apTerm(partial, right)
      whole <- Conv.trans(atLeft, atRight)
      negated <- Conv.apTerm(logic.negation, whole)
      result <- Conv.sym(negated).flatMap(equation => LogicError.lift(Kernel.eqMp(equation, fact)))
    } yield result

  /**
   * `|- WORD_CONCAT <front> <back> = <front ++ back>`: the two spellings of one word reconciled.
   *
   * [[wordText]] writes a word left-nested and `WORD_STEP` writes it as a context, a block and a
   * tail, so a step at a written-out rule has the same word in two shapes and neither is the other
   * by reflexivity. The recursion runs on `back`'s **last** letter, which is where the left-nesting
   * puts the outermost concatenation: one `WORD_CONCAT_ASSOC` carries that letter out of the block
   * and what is left is the same question one letter shorter. An empty front is
   * `WORD_CONCAT_EMPTY_LEFT`, which is the single case [[stepHolds]] had before this existed.
   */
  private def concatIsWord(
    tools: Concrete,
    concatenation: Concatenation,
    front: Vector[String],
    back: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = tools.rules

    if (back.isEmpty) Left(NotOfForm("a block with letters in it", LeftSide))
    else if (front.isEmpty)
      for {
        block <- tools.word(back)
        emptyLeft <- concatenation.fact(Concatenation.EmptyLeft).map(atNumbers)
        result <- rules.spec(block, emptyLeft)
      } yield result
    else if (back.size == 1) tools.word(front ++ back).map(Conv.refl)
    else
      for {
        concat <- tools.constant(Concatenation.Name, ConcatType)
        frontWord <- tools.word(front)
        initWord <- tools.word(back.init)
        lastLetter <- tools.letter(back.last)
        singleton <- tools.constant(Concatenation.Singleton, Type.fun(Numbers, Words))
        lastWord <- LogicError.lift(Term.app(singleton, lastLetter))
        associative <- concatenation.fact(Concatenation.Associative).map(atNumbers)
        moved <- rules
          .specAll(associative, List(frontWord, initWord, lastWord))
          .flatMap(Conv.sym)
        inner <- concatIsWord(tools, concatenation, front, back.init)
        carried <- Conv.apTerm(concat, inner).flatMap(Conv.apThm(_, lastWord))
        result <- Conv.trans(moved, carried)
      } yield result
  }

  /**
   * `|- <front ++ block ++ tail> = WORD_CONCAT (WORD_CONCAT <front> <block>) <tail>`.
   *
   * The equation a clause of `WORD_STEP` asks for, at a word written out letter by letter.
   * [[concatIsWord]] twice: once inside the context, once around the tail.
   */
  private def blockEquation(
    tools: Concrete,
    concatenation: Concatenation,
    front: Vector[String],
    block: Vector[String],
    tail: Vector[String]
  ): Either[LogicError, Kernel.Thm] =
    for {
      concat <- tools.constant(Concatenation.Name, ConcatType)
      tailWord <- tools.word(tail)
      inner <- concatIsWord(tools, concatenation, front, block)
      carried <- Conv.apTerm(concat, inner).flatMap(Conv.apThm(_, tailWord))
      outer <- concatIsWord(tools, concatenation, front ++ block, tail)
      whole <- Conv.trans(carried, outer)
      result <- Conv.sym(whole)
    } yield result

  /**
   * `|- WORD_STEP <relation> <front block tail> <front other tail>`, one named rule fired in place.
   *
   * [[stepHolds]] with the context, the tail and the rule table as arguments rather than as three
   * constants of the file, which is what a witness other than `/0.` needs. The witnesses handed to
   * the four existentials are the context, the rule's two sides and the tail, and the only work is
   * [[blockEquation]], because the definition writes a word as `x l y` and this file writes it
   * left-nested.
   */
  private def stepAt(
    tools: Concrete,
    concatenation: Concatenation,
    forward: Forward,
    definitions: Map[String, Kernel.Thm],
    table: Vector[Rule],
    relation: String,
    label: String,
    front: Vector[String],
    tail: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic

    for {
      position <- table.indexWhere(_.label == label) match {
        case -1 => Left(NotOfForm(s"a rule named $label", LeftSide))
        case found => Right(found)
      }
      entry <- table.lift(position).toRight(NotOfForm(s"a rule at $position", LeftSide))

      before <- tools.word(front ++ entry.left ++ tail)
      after <- tools.word(front ++ entry.right ++ tail)
      context <-
        if (front.isEmpty) tools.constant(Concatenation.Empty, Words)
        else tools.word(front)
      leftSide <- tools.word(entry.left)
      rightSide <- tools.word(entry.right)
      tailWord <- tools.word(tail)
      relationTerm <- tools.constant(relation, Type.fun(Words, Type.fun(Words, Type.Bool)))

      rule <- relationHolds(tools, definitions, table, relation, position)
      beforeEquation <- blockEquation(tools, concatenation, front, entry.left, tail)
      afterEquation <- blockEquation(tools, concatenation, front, entry.right, tail)

      stepDefinition <- forward.definition(Forward.Step).map(atNumbers)
      opened <- Conv.unfold(stepDefinition, List(relationTerm, before, after))
      existential <- rightOf(opened)
      witnessed <- withWitnesses(logic, existential, List(context, leftSide, rightSide, tailWord)) {
        body =>
          for {
            pair <- logic.rules.conjIntro(beforeEquation, afterEquation)
            held <- logic.rules.conjIntro(rule, pair)
            _ <-
              if (held.conclusion == body) Right(())
              else Left(NotOfForm("the step's own clause", held.conclusion))
          } yield held
      }
      result <- Conv
        .sym(opened)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, witnessed)))
    } yield result
  }

  /**
   * `|- !i. i < WORD_LENGTH <word> ==> ~(WORD_NTH <word> i = <letter>)`, for a word without it.
   *
   * [[freeWord]] at a letter that is not one of the two markers, and therefore without a constant
   * of its own to be the definition of: the claim is built as a term instead of being unfolded out
   * of one, and the walk over the positions is the same. What wants it is [[noCountedStepFrom]],
   * where the position the letter is refused at is `WORD_LENGTH x + SUC^j ZERO` for a context
   * nobody has written down, so a claim about every position is the only shape that reaches it.
   */
  private def noLetterBelowLength(
    tools: Concrete,
    letters: Vector[String],
    letterName: String
  ): Either[LogicError, Kernel.Thm] = {
    val spelling = wordText(letters)

    for {
      _ <-
        if (letters.contains(letterName)) Left(NotOfForm(s"a word without $letterName", LeftSide))
        else Right(())
      statement <- Parser.proposition(
        tools.theory,
        tools.notation,
        s"!i:num. i < WORD_LENGTH ($spelling) ==> ~(WORD_NTH ($spelling) i = ($letterName:num))"
      )
      size <- lengthIsNumeral(tools, letters)
      result <- atEveryIndex(tools, statement, size, letters.size) { (index, equal) =>
        for {
          position <- positionOf(tools, equal, letters.size)
          answer <- noMarkerAt(tools, letters, position, index, equal, letterName)
        } yield answer
      }
    } yield result
  }

  /**
   * The letters a commutation's left-hand side carries at one offset, read off the table.
   *
   * Every one of the six is a **marker followed by a digit**, so `countedLettersAt(0)` is `f` and
   * `t` and `countedLettersAt(1)` is `0`, `1` and `2`. Taken from [[CountedRules]] rather than
   * written out, so a table that grew a rule opening on a third letter widens the refusal
   * [[noCountedStepFrom]] builds instead of leaving it short by one clause.
   */
  private def countedLettersAt(offset: Int): Vector[String] =
    CountedRules.flatMap(_.left.lift(offset)).distinct

  /**
   * `|- ~(WORD_STEP S2_COUNTED <word> <other>)`: no commutation takes this word anywhere.
   *
   * The antecedent [[PlainWitness]] cannot get by naming the rule that fired. `B1` is not a
   * commutation, which is a fact about the table; that a **different** factorisation of the same
   * pair is not a commutation step either is a fact about the word, and this is that fact.
   *
   * What it runs on is that a commutation's left-hand side is two letters and this word holds
   * none of the letters that stand at one of the two offsets. **There are therefore two readings
   * and not one**, which is [[countedLettersAt]]: a word with no `f` and no `t` cannot supply the
   * first letter, and a word with no `0`, `1` and `2` cannot supply the second. The second is
   * what reaches a word holding a marker, `/ff.` being one, and the enumeration of `WORD_LENGTH
   * x` that such a word looks like it needs is not needed at either offset.
   *
   * The shape is one walk with the offset in it. From `u = (x l) y` and `SUC^j ZERO < WORD_LENGTH
   * l` comes `WORD_LENGTH x + SUC^j ZERO < WORD_LENGTH u`, which is where a letter of `u` may be
   * read, and `WORD_NTH u (WORD_LENGTH x + SUC^j ZERO) = WORD_NTH l (SUC^j ZERO)`, which is what
   * is read there. Each of the six clauses then names its own letter at that offset and the
   * refusals close it.
   *
   * **The index is left as `WORD_LENGTH x + SUC^j ZERO` and never normalised**, which is what
   * makes one walk serve both. Reading it back as `WORD_LENGTH x` at offset zero is what the
   * first version of this did, and it cost the `NUM_ADD_ZERO` rewrite on both the order and the
   * entry, in the one case where the two happen to agree.
   *
   * The length of the block is derived **inside** the clause and not in front of it, since
   * `S2_RULE_NOT_EMPTY` gives `0 < WORD_LENGTH l` and the second offset wants `SUC ZERO <
   * WORD_LENGTH l`. Each clause equates `l` to a written-out word, so its length is a numeral
   * there and the order is [[numeralBelow]]: more than the uniform fact says, from the clause
   * that was going to be opened anyway.
   *
   * **What it does not cover**: a word holding a marker **and** a digit. Both readings refuse
   * such a word, and refusing the step for it wants the enumeration of `WORD_LENGTH x`, which is
   * the shape this avoids at both offsets. `/f0.` is the smallest one.
   */
  private def noCountedStepFrom(
    tools: Concrete,
    forward: Forward,
    concatenation: Concatenation,
    definitions: Map[String, Kernel.Thm],
    letters: Vector[String],
    after: Vector[String]
  ): Either[LogicError, Kernel.Thm] = {
    val logic = tools.logic
    val rules = logic.rules

    for {
      subject <- tools.word(letters)
      result <- tools.word(after)
      counted <- tools.constant(Counted, Type.fun(Words, Type.fun(Words, Type.Bool)))
      concat <- tools.constant(Concatenation.Name, ConcatType)
      lengthOf <- tools.lengthOf
      nth <- tools.nth
      order <- tools.strictOrder

      countedDefinition <- definitions.get(Counted).toRight(MissingDefinition(Counted))
      concatLength <- concatenation.fact(Concatenation.Length).map(atNumbers)
      nthLeft <- concatenation.fact(Concatenation.NthLeft).map(atNumbers)
      nthRight <- concatenation.fact(Concatenation.NthRight).map(atNumbers)

      // Which end of the block this word can be refused at. Both offsets are tried and the first
      // that works is taken, which makes the marker reading the one a word admitting both gets:
      // it is the cheaper walk and it is the one every caller before 2026-09-22 was written
      // against. A word admitting neither is refused here rather than further in, because the
      // refusal is about the word and not about any clause.
      offset <- (0 until CountedRules.map(_.left.size).minOption.getOrElse(0))
        .find(at => !letters.exists(countedLettersAt(at).contains))
        .toRight(NotOfForm("a word missing every letter at one end of a commutation", subject))

      // The letters at that offset, refused of this word once rather than once per clause. Read
      // off the table, so a rule carrying a letter nobody has refused adds a refusal instead of
      // silently not being covered by one; the bound above is the SHORTEST left-hand side, so an
      // offset no rule reaches cannot be chosen and a clause cannot fall out of the walk.
      refusals <- countedLettersAt(offset)
        .foldLeft[Either[LogicError, Map[String, Kernel.Thm]]](Right(Map.empty)) {
          (built, letterName) =>
            for {
              collected <- built
              refusal <- noLetterBelowLength(tools, letters, letterName)
            } yield collected.updated(letterName, refusal)
        }
      offsetNumeral <- tools.numeral(offset)

      stepDefinition <- forward.definition(Forward.Step).map(atNumbers)
      opened <- Conv.unfold(stepDefinition, List(counted, subject, result))
      claim <- leftOf(opened)
      assumed <- LogicError.lift(Kernel.assume(claim))
      existential <- LogicError.lift(Kernel.eqMp(opened, assumed))

      settled <- openWitnesses(logic, existential, 4, Term.freeVariables(claim)) {
        (witnesses, held) =>
          witnesses match {
            case List(front, left, right, tail) =>
              for {
                ruleHeld <- rules.conjElim1(held)
                rest <- rules.conjElim2(held)
                subjectEquation <- rules.conjElim1(rest)

                contextLength <- LogicError.lift(Term.app(lengthOf, front))
                blockLength <- LogicError.lift(Term.app(lengthOf, left))
                tailLength <- LogicError.lift(Term.app(lengthOf, tail))
                block <- LogicError.lift(Term.appAll(concat, List(front, left)))
                blockTerm <- LogicError.lift(Term.app(lengthOf, block))

                asDisjunction <- Conv
                  .unfold(countedDefinition, List(left, right))
                  .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, ruleHeld)))

                answer <- overClauses(logic, asDisjunction, CountedRules.size) {
                  (position, leftEquation, _) =>
                    for {
                      entry <- CountedRules
                        .lift(position)
                        .toRight(NotOfForm(s"a counted rule at $position", LeftSide))
                      letterName <- entry.left
                        .lift(offset)
                        .toRight(NotOfForm(s"a letter at $offset of ${entry.label}", LeftSide))
                      refusal <- refusals
                        .get(letterName)
                        .toRight(MissingDefinition(letterName))

                      // `SUC^j ZERO < |l|`, where the uniform fact gives only `0 < |l|`. This
                      // clause says `l` IS a written-out word, so its length is a numeral and the
                      // order between two numerals is a walk up the successors.
                      blockIsNumeral <- lengthIsNumeral(tools, entry.left)
                      blockEquation <- Conv
                        .apTerm(lengthOf, leftEquation)
                        .flatMap(Conv.trans(_, blockIsNumeral))
                      belowSize <- numeralBelow(tools, offset, entry.left.size)
                      offsetBelow <- Conv
                        .sym(blockEquation)
                        .flatMap(carryRight(order, offsetNumeral, _, belowSize))

                      // `|x| + SUC^j ZERO < |x| + |l|`: the offset is inside the block. The index
                      // is read off this rather than built, which is what keeps it the same term
                      // the entry lemma produces one step down.
                      shifted <- rules
                        .specAll(
                          tools.numbers.addStrictlyMonotone,
                          List(contextLength, offsetNumeral, blockLength))
                        .flatMap(rules.mp(_, offsetBelow))
                      index <- shifted.conclusion match {
                        case App(App(_, at), _) => Right(at)
                        case other => Left(NotOfForm("an order with an index on the left", other))
                      }

                      // and `< |x l|`, which is that read back through the concatenation's length.
                      blockSize <- rules.specAll(concatLength, List(front, left))
                      insideConcat <- Conv
                        .sym(blockSize)
                        .flatMap(carryRight(order, index, _, shifted))

                      // and `< |u|`, which is where a letter of the written-out word may be read.
                      wholeSize <- rules.specAll(concatLength, List(block, tail))
                      wholeSum <- rightOf(wholeSize)
                      atMost <- rules.specAll(tools.numbers.atMostSum, List(blockTerm, tailLength))
                      reaches <- rules
                        .specAll(tools.numbers.belowThenAtMost, List(index, blockTerm, wholeSum))
                        .flatMap(claimed =>
                          rules.conjIntro(insideConcat, atMost).flatMap(rules.mp(claimed, _)))
                      wordSum <- Conv
                        .apTerm(lengthOf, subjectEquation)
                        .flatMap(Conv.trans(_, wholeSize))
                      inWord <- Conv
                        .sym(wordSum)
                        .flatMap(carryRight(order, index, _, reaches))

                      // `WORD_NTH u index = WORD_NTH l (SUC^j ZERO)`: the letter the rule fired
                      // on, read twice. The two halves meet with no rewriting between them,
                      // because the entry lemma on the right is stated at exactly this index.
                      leftRead <- rules
                        .specAll(nthLeft, List(block, tail, index))
                        .flatMap(rules.mp(_, insideConcat))
                      rightRead <- rules
                        .specAll(nthRight, List(front, left, offsetNumeral))
                        .flatMap(rules.mp(_, offsetBelow))
                      atBlock <- Conv
                        .apTerm(nth, subjectEquation)
                        .flatMap(Conv.apThm(_, index))
                        .flatMap(Conv.trans(_, leftRead))
                        .flatMap(Conv.trans(_, rightRead))

                      opening <- letterAt(tools, entry.left, offset)
                      carried <- Conv
                        .apTerm(nth, leftEquation)
                        .flatMap(Conv.apThm(_, offsetNumeral))
                        .flatMap(Conv.trans(_, opening))
                      reading <- Conv.trans(atBlock, carried)
                      denied <- rules.spec(index, refusal).flatMap(rules.mp(_, inWord))
                      absurd <- rules.notElim(denied, reading)
                    } yield absurd
                }
              } yield answer

            case other =>
              Left(NotOfForm("four witnesses", Term.variable(other.size.toString, Words)))
          }
      }

      refused <- rules.notIntro(claim, settled)
    } yield refused
  }

  /** `R1`'s two words, which are the witnesses [[Inhabited]] uses, taken from the table. */
  private val RuleOneLeft: String = wordText(Rules.head.left)

  private val RuleOneRight: String = wordText(Rules.head.right)

  /**
   * [[Refused]]: the head letter on its own does not rewrite to itself.
   *
   * The half that says the eleven are a constraint. Every clause of the definition equates `l` to a
   * word of length two or three, and `WORD_SINGLETON` has length one, so each disjunct dies on the
   * lengths. `Minimal` cannot take this one: it refuses a goal with a negation in it, and this goal
   * is a negation of a disjunction of eleven conjunctions of equations between words.
   *
   * So it goes to `Propositional` instead, over the length facts as atoms. What that costs is
   * written where this repository writes such things rather than hidden: the classical decision
   * closes with double negation and charges `SELECT`, where the intuitionistic one charges nothing.
   * The trade is taken here because the alternative is eleven hand refutations that differ only in
   * which numeral they compare, and because a refusal that costs one foundational axiom is still a
   * refusal the kernel checked.
   */
  private def refusal(
    logic: Logic,
    naturals: Natural,
    concatenation: Concatenation,
    peano: Peano,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      target <- statement(theory, notation, Refused)
      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      rules <- unfoldingRules(logic, Vector(system))
      lengthRules <- lengthRuleSet(logic, concatenation, peano)
      opened <- Rewrite.rewrite(rules, target).flatMap(rightOf)

      // `Propositional` was tried here first and refuses, correctly and with the right message:
      // the atoms are uninterpreted, so the skeleton of eleven disjuncts is satisfiable and the
      // refusal says so rather than guessing. Nothing about words is propositional, which is the
      // whole content of this lemma, so the eleven are refuted one at a time on their lengths.
      disjunction <- logic.destNot(opened).toRight(NotOfForm("a negation", opened))
      contradiction <- refuteDisjunction(logic, naturals, lengthRules, disjunction)
      negated <- logic.rules.notIntro(disjunction, contradiction)
      result <- shapeBack(logic, rules, target, negated)
    } yield result

  /**
   * Every disjunct refuted, and the disjunction with it.
   *
   * Right-nested, so this walks the spine: refute the head clause, recurse on the tail, and put
   * the two cases together with `disjElim` at falsity. Eleven clauses and one shape, because every
   * clause of this system says the left side **is** a particular word.
   */
  private def refuteDisjunction(
    logic: Logic,
    naturals: Natural,
    lengthRules: Vector[Rewrite.Rule],
    disjunction: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    logic.destDisj(disjunction) match {
      case None => refuteClause(logic, naturals, lengthRules, disjunction)
      case Some((clause, rest)) =>
        for {
          here <- refuteClause(logic, naturals, lengthRules, clause)
          there <- refuteDisjunction(logic, naturals, lengthRules, rest)
          assumed <- LogicError.lift(Kernel.assume(disjunction))
          split <- rules.disjElim(assumed, here, there)
        } yield split
    }
  }

  /**
   * One clause refuted on the length of the word its left conjunct names.
   *
   * The clause is `l = w /\ r = w'` with `l` already the one-letter word this lemma is about. So
   * the left conjunct equates a word of length one with a word of length two or three, and what
   * refutes it is applying `WORD_LENGTH` to both sides and asking `Successor` whether the two
   * numerals differ. No case analysis on the letters is needed and none is done: the letters could
   * all be equal and the clause would still be false.
   */
  private def refuteClause(
    logic: Logic,
    naturals: Natural,
    lengthRules: Vector[Rewrite.Rule],
    clause: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      parts <- logic.destConj(clause).toRight(NotOfForm("a conjunction", clause))
      (equation, _) = parts
      assumed <- LogicError.lift(Kernel.assume(clause))
      leftHalf <- rules.conjElim1(assumed)

      sides <- Term.destEq(equation).toRight(NotOfForm("an equation", equation))
      _ = sides
      lengthOf <- lengthFunction(logic)

      applied <- Conv.apTerm(lengthOf, leftHalf)
      computed <- Rewrite.inTheorem(lengthRules, applied)
      numerals <- Term.destEq(computed.conclusion).toRight(NotOfForm("an equation", computed.conclusion))
      (shortLength, longLength) = numerals

      falsity <- refuteSuccessors(logic, naturals, computed)
    } yield falsity
  }

  /**
   * `SUC^m 0 = SUC^n 0` with `m < n` refuted, by peeling the common successors off.
   *
   * `Successor.distinct` is the obvious tool and it is the wrong one here: it reads a numeral in
   * the bit encoding, and what the length rules produce is successor form, so it refuses with
   * "expected a numeral of num, found (SUC ZERO)". Converting to the bit encoding to ask it would
   * be a conversion in order to reach a procedure that then converts back.
   *
   * What refutes it directly is the two Peano facts the naturals already derive: strip the
   * successors both sides share with `NUM_SUC_INJECTIVE` until one side is `0`, and close with
   * `NUM_SUC_NOT_ZERO`. It terminates because each step removes one successor from each side and
   * the sides differ in how many they have.
   */
  private def refuteSuccessors(
    logic: Logic,
    naturals: Natural,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    def peel(current: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val sides = Term.destEq(current.conclusion)
      sides match {
        case None => Left(NotOfForm("an equation", current.conclusion))
        case Some((left, right)) =>
          (successorOf(left), successorOf(right)) match {
            case (Some(innerLeft), Some(innerRight)) =>
              for {
                injective <- naturals.fact(Natural.SuccessorInjective)
                // The INNER terms, not the sides: the lemma is `SUC x = SUC y ==> x = y`, so what
                // it is specialised at is what sits under each successor. Passing the sides builds
                // a true instance about two taller numbers whose antecedent nothing here proves,
                // which is what the first version did and what the refusal named.
                stripped <- rules.specAll(injective, List(innerLeft, innerRight))
                smaller <- rules.mp(stripped, current)
                result <- peel(smaller)
              } yield result

            // One side has run out of successors, so the other is `SUC something = 0` up to
            // symmetry, which is the fact the naturals publish.
            case (Some(_), None) => closeAgainstZero(logic, naturals, current)
            case (None, Some(_)) => Conv.sym(current).flatMap(closeAgainstZero(logic, naturals, _))
            case (None, None) =>
              Left(NotOfForm("two numerals of different height", current.conclusion))
          }
      }
    }

    peel(equation)
  }

  private def successorOf(term: Term): Option[Term] = term match {
    case App(Const(Natural.NumberSuccessor, _), argument) => Some(argument)
    case _ => None
  }

  private def closeAgainstZero(
    logic: Logic,
    naturals: Natural,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      notZero <- naturals.fact(Natural.SuccessorNotZero)
      sides <- Term.destEq(equation.conclusion).toRight(NotOfForm("an equation", equation.conclusion))
      (left, _) = sides
      inner <- successorOf(left).toRight(NotOfForm("a successor", left))
      instance <- logic.rules.spec(inner, notZero)
      falsity <- logic.rules.notElim(instance, equation)
    } yield falsity

  /** `WORD_LENGTH` at this development's word type, ready to be applied to both sides. */
  private def lengthFunction(logic: Logic): Either[LogicError, Term] =
    LogicError.lift(logic.theory.constant(Word.Length, Type.fun(Words, Numbers)))

  /** `!l r. body` minus its two leading quantifiers, which is what a propositional search takes. */
  private def strippedBody(logic: Logic, target: Term): Either[LogicError, Term] =
    for {
      outer <- logic.destForallPredicate(target).toRight(NotOfForm("a quantified claim", target))
      atLeft <- LogicError.lift(Term.app(outer, LeftSide))
      openedLeft <- Conv.betaRoot(atLeft).flatMap(rightOf)
      inner <- logic.destForallPredicate(openedLeft).toRight(NotOfForm("a quantified claim", openedLeft))
      atRight <- LogicError.lift(Term.app(inner, RightSide))
      body <- Conv.betaRoot(atRight).flatMap(rightOf)
    } yield body

  /**
   * What turns a concatenation of singletons into a numeral: the two length facts and the two
   * equations that evaluate the addition.
   *
   * `WORD_CONCAT_LENGTH` turns the word into a sum, `WORD_SINGLETON_LENGTH` turns each summand into
   * `SUC 0`, and `NUM_ADD_SUC` with `NUM_ADD_ZERO` walk the sum down to a numeral in successor
   * form, which is the form `Successor.distinct` reads. Four rules and no search.
   */
  private def lengthRuleSet(
    logic: Logic,
    concatenation: Concatenation,
    peano: Peano
  ): Either[LogicError, Vector[Rewrite.Rule]] =
    for {
      concatLength <- concatenation.fact(Concatenation.Length)
      singletonLength <- concatenation.fact(Concatenation.SingletonLength)
      addSuc <- peano.fact(Peano.AddAtSuccessor)
      addZero <- peano.fact(Peano.AddAtZero)
      rules <- unfoldingRules(logic, Vector(concatLength, singletonLength, addSuc, addZero))
    } yield rules
}
