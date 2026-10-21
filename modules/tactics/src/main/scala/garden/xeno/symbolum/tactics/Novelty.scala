package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.{Logic, Rewrite}
import garden.xeno.symbolum.theories.{Field, Library, Ring, Signature}

/**
 * How much more than the minimum a claim cost, which is the only implementable reading of surprise.
 *
 * A generator of conjectures without a novelty filter produces rubbish by volume. It proposes
 * `x + 0 = x`, the kernel certifies it, and nothing has been discovered. The criterion is usually
 * vague, "is it interesting", and nobody knows how to implement that.
 *
 * There is an implementable one here, and it is available **because this system has cheap decision
 * procedures**: if `Ring` settles it at once, it is not news. What survives the screen, is
 * certified, and needed more than the cheapest procedure that could have been asked, is the
 * candidate worth a person's attention.
 *
 * == Why this system can measure it and the comparators cannot ==
 *
 *  - **Per-proof axiom reach.** `Derivation.axiomsOf` says which of the sixteen a proof touched.
 *    Lean's `#print axioms` answers `propext, Classical.choice, Quot.sound` for essentially every
 *    Mathlib declaration, because the reals are constructed there, so the answer carries no
 *    information about the mathematics. A line like "three axioms least, eight median, fifteen
 *    most, completeness never" is one only an axiomatised theory can write about itself.
 *  - **Per-proof inference count.** `Derivation.size`. In Lean a proof is a term and there is no
 *    count of primitive steps; heartbeats measure elaboration effort instead.
 *  - **The address before the spend.** `Prove.addressOf` says whose fragment a goal is in without
 *    attempting it, so "which is the cheapest procedure that could settle this" is answerable
 *    before anything is spent.
 *
 * == What this is not ==
 *
 * **An ordering, not a verdict.** Surprising is not a property a program decides, and this file
 * does not pretend otherwise: what comes back ranks what a person will look at first. That is the
 * same discipline `Refutation` keeps seven outcomes for and `Discovery` keeps four reasons for.
 * Collapsing the ordering into "this is a discovery" is the one way this machinery can mislead.
 *
 * **And the honest limit, which the calibration below measures rather than hides.** Everything the
 * automated surface proves is routine almost by construction, because that surface *is* the
 * decision procedures. [[Novelty.Standing.Earned]] is reachable today through a hand derivation or
 * through `Induct`, and through the escalations inside LINARITH, and not otherwise. A richer prover
 * would make the scale say more; today it mostly separates the trivial from the unreachable, which
 * is still the separation a generator needs most.
 *
 * == The third signal, measured and not built ==
 *
 * The card that asked for this scale named three components, and called the third the strongest:
 * whether a claim's proof **needed a lemma no previous theorem had touched**. It is not here, and
 * that is a measurement rather than an omission.
 *
 * Measured first on 2026-09-11 and **again on 2026-09-12**, and the population is named because the
 * first reading did not name its own: it is `Library.of(Chain.standard)`, which holds 183 distinct
 * names of which 162 are derived lemmas rather than axioms or definitions. Of those 162, 59 are
 * rested on by no other held theorem, 18 by exactly one and 85 by two or more; so far the signal
 * looks discriminating. What kills it is the other side: the lemmas a proof reaches are the common
 * infrastructure — `NUM_REP_0` is rested on by 106 of the 183, and the four lemmas under it by 103
 * or 104 each — and a certified proof rested on **eleven to twenty-six** of them when that was last
 * counted, on 2026-09-11, which this reading did not repeat.
 *
 * The 2026-09-11 reading said 104 lemmas, 30, 15 and 59, with `NUM_REP_0` at 57. That was the same
 * measurement over a smaller library: four developments joined it on 2026-09-12 and the count went
 * from 138 entries to 186, which `LibrarySpec` asserts. **The shape did not change and neither did
 * the conclusion**, which is what makes it worth re-reading rather than re-deciding.
 *
 * The library has since grown again, to 278 entries and 275 distinct names on 2026-09-13, and the
 * reading above has **not** been repeated over it. The figures in this paragraph are therefore the
 * population of 2026-09-12 and are left saying so rather than quietly re-read as current: what a
 * third growth would decide is whether the shape survives it, and nobody has asked.
 *
 * The other half is **hand-measured on 2026-09-11 and not re-measured since**: put to the 37
 * certified proposals `Propose` made from the library as it then stood, the signal fired **once**,
 * and that once was a proposal resting on the lemma it was made from.
 *
 * So it separates nothing here. It is not a bad idea: it is an idea that needs a library large
 * enough and loose enough that a proof can reach a corner of it, and this one is a library where
 * every proof goes through the naturals' representation. `NoveltySpec` pins the shape rather than
 * the counts, so that the day the shape changes somebody is told.
 */
final class Novelty private (
  val cost: Cost,
  val ring: Ring,
  val library: Option[(Library, Logic)]
) {

  import Novelty.*

  val reals: Signature = cost.reals

  /** The reading for a claim in the development's notation. */
  def of(text: String): Either[TacticError, Reading] =
    TacticError.lift(reals.proposition(text)).flatMap(of)

  /**
   * The reading for a claim already read.
   *
   * The order is the order of what an answer costs. The address is free, so it is asked first and
   * a claim no procedure can take never spends anything. The cheapest procedure is asked next,
   * because a claim it settles is over: nothing further is worth measuring about it.
   */
  def of(claim: Term): Either[TacticError, Reading] = {
    val address = cost.prove.addressOf(claim)

    cost.of(claim).map { report =>
      val settledCheaply = ring.prove(claim).isRight

      // The two cheap answers come before the report's, and in that order. Rewriting with the held
      // lemmas IS a proof, so a claim that falls out of them is a corollary WHATEVER the tactic
      // surface said about it: the first version asked this only of a claim the tactics had already
      // proved, and so never fired on the ones the tactics cannot reach, which are exactly the ones
      // a reader would otherwise be told are open.
      val standing =
        if (settledCheaply) Standing.Immediate
        else if (follows(claim)) Standing.Known
        else report.outcome match {
        case Cost.Outcome.Proved => Standing.Earned
        case Cost.Outcome.Conditional => Standing.Earned
        case Cost.Outcome.Holds => Standing.Decided
        case Cost.Outcome.Fails => Standing.False
        case Cost.Outcome.Unsettled =>
          address match {
            case Prove.Address.Nobody(_) => Standing.Unreadable
            case _ => Standing.Open
          }
        }

      Reading(claim, standing, address, report.inferences, report.axioms.size, report)
    }
  }

  /**
   * Whether the claim falls out of the lemmas already held, by rewriting alone.
   *
   * The second half of "how much more than the minimum", and the half that separates a new result
   * from a restatement of one. A candidate the ring normalisation cannot see but that collapses the
   * moment the existing lemmas are used as rewrite rules is a corollary, not news.
   *
   * **Only the equational lemmas take part**, because only an equation is a rewrite rule, and the
   * rest of the library is skipped rather than refused: `Rule.of` declines a lemma whose conclusion
   * is not an equation and that is the right answer for a conditional or an inequality. So this
   * under-reports rather than over-reports, which is the direction to err in: a claim called new
   * that was a corollary wastes a reader's time, and a corollary called new is the failure this
   * whole scale exists to prevent.
   *
   * A library the caller did not supply means no answer, and `Standing.Known` is then unreachable.
   * That is stated rather than defaulted, because "we did not look" and "we looked and it is new"
   * are the two things this repository is most careful never to merge.
   */
  private def follows(claim: Term): Boolean = library.exists { case (held, logic) =>

    val equations = held.entries
      .map(_.theorem)
      .flatMap(theorem => Rewrite.Rule.of(logic, theorem).toOption)
      .filterNot(rule => permutative(rule.lhs, rule.rhs))

    // Held outright, up to instantiating the lemma's own quantifiers. Asked before the rewriting
    // because it is a lookup and the rewriting is a search, and because it catches the shape the
    // rewriting cannot see at all: `!x. 0 <= x * x` is not an equation, so no rule set could ever
    // turn one side of it into the other, and it is `SQUARE_NONNEG` written out.
    val alreadyHeld = held.instantiating(claim).nonEmpty

    val rewritesAway =
      Logic
        .stripForall(claim)
        .toOption
        .map(_._2)
        .flatMap(body => Term.destEq(body))
        .exists { case (left, right) =>
          Rewrite.prove(equations, left, right).isRight
        }

    alreadyHeld || rewritesAway
  }


  /**
   * Whether a rule only rearranges, which is the shape that loops without an ordering to stop it.
   *
   * `ADD_SYM` is `x + y = y + x`, and used as an unordered rewrite rule it alternates for ever and
   * eats the step budget, so a rule set built out of every equation in the library settles nothing
   * and this whole question would answer "no" to everything. Measured rather than reasoned about:
   * a first version had no filter and the corollary test came back `Open`.
   *
   * The repository already knows this shape. `Rewrite.orderedRewriteConv` exists precisely for
   * permutative rules and terminates by taking a total order on terms of one size; the note on it
   * says a rule that grows the term needs a different argument. Rather than reach for that ordering
   * here, the permutative rules are dropped: they can only rearrange, so they can turn one side
   * into the other only when the two are rearrangements of each other, and a claim that is a
   * rearrangement of a held lemma is one `Ring` settles at once and has already been called
   * `Immediate` above.
   */
  private def permutative(left: Term, right: Term): Boolean = {
    def leaves(term: Term): Vector[String] = term match {
      case App(fn, argument) => leaves(fn) ++ leaves(argument)
      case Abs(_, body) => leaves(body)
      case other => Vector(other.toString)
    }

    leaves(left).sorted == leaves(right).sorted
  }

  /**
   * The candidates worth a person's attention, most first.
   *
   * `Open` before `Earned` deliberately: a claim that survived the screen and was **not** certified
   * is the one thing a decision procedure cannot settle and a person might, which is what
   * `Discovery`'s `NotProvableHere` bucket means and why that bucket is the loop's whole argument.
   * Within a standing, more inferences and wider axiom reach come first.
   */
  def rank(readings: Vector[Reading]): Vector[Reading] =
    readings.sortBy(reading => (-Standing.weight(reading.standing), -reading.inferences, -reading.axioms))
}

object Novelty {

  /**
   * How far past the cheapest answer a claim went, worst news first.
   *
   * The scale is about **cost against the minimum**, not about truth: `False` is near the bottom
   * not because a false claim is uninteresting but because deciding it false ends the question,
   * and this ordering exists to say what to look at next.
   */
  enum Standing {

    /** Screened true, certified by nothing here. The one a person might settle and a procedure cannot. */
    case Open

    /** Certified, and not by the cheapest procedure that could have been asked. */
    case Earned

    /**
     * Certified, and it falls out of the lemmas already held by rewriting alone.
     *
     * A corollary rather than a result. Ranked below [[Immediate]] on purpose, and the difference
     * is thin but real: both are "not news", and this one is worse because it adds nothing even to
     * the library. An immediate ring identity at least is not yet written down anywhere.
     */
    case Known

    /** Certified at once by the ring normalisation. Not news. */
    case Immediate

    /** Decided without a certificate, by quantifier elimination. */
    case Decided

    /** Decided false. The question is over. */
    case False

    /** No procedure here can take a claim of that shape. Nothing was spent. */
    case Unreadable
  }

  object Standing {

    /** The ordering, written out rather than left to the enum's declaration order. */
    def weight(standing: Standing): Int = standing match {
      case Standing.Open => 6
      case Standing.Earned => 5
      case Standing.Decided => 4
      case Standing.Immediate => 3
      case Standing.Known => 2
      case Standing.False => 1
      case Standing.Unreadable => 0
    }
  }

  /**
   * What a claim cost against the minimum, with the report it came from.
   *
   * `report` is kept whole rather than summarised: this file ranks, and a caller that wants to know
   * what a claim charges or where it fails reads the five answers `Cost` gathered instead of a
   * number this one invented.
   */
  final case class Reading(
    claim: Term,
    standing: Standing,
    address: Prove.Address,
    inferences: Int,
    axioms: Int,
    report: Cost.Report
  )

  /**
   * Over the standard development, with the lemmas of the standard chain as what is already known.
   *
   * The library is what makes [[Standing.Known]] reachable. Without one the scale still works and
   * says less, which is the honest arrangement rather than a degraded one.
   */
  lazy val standard: Novelty = {
    val chain = garden.xeno.symbolum.theories.Chain.standard

    // The prover a chain deserves, the one `Ask` asks: the widest signature and the whole chain's
    // library. The reader and the library have to agree, and a first version had them disagree,
    // which the test about a corollary caught. Until card `cab4b920` this was
    // `Prove.construct(chain.order, chain.series)`, whose library is what an `Order` reaches, so a
    // claim restating a lemma above `Order` came back unsettled here and proved through `Ask`.
    val prove = Prove
      .construct(chain)
      .fold(error => throw new IllegalStateException(s"the standard novelty does not build: ${error.message}"), identity)

    new Novelty(
      Cost(prove, Field.standard, Abduce.standard, Quantified.standard),
      Ring.standard,
      Some((Library.of(chain), chain.logic))
    )
  }

  /** Over a development of one's own, with or without a library of what is already known. */
  def apply(cost: Cost, ring: Ring, library: Option[(Library, Logic)] = None): Novelty =
    new Novelty(cost, ring, library)
}
