package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The fact that carries a domain claim into arithmetic, found instead of named.
 *
 * `docs/adr/0024` decided that a claim about a domain which reaches the foundation's constants is
 * settled when the **caller** hands over the theorem relating them: `Domain.Built.settle` takes a
 * vector of bridges, specialises each at the claim's own foundation-typed subterms, and reports
 * what the conclusion spent. That record names the search as the next piece of work and puts four
 * conditions on it — bounded, reports what it used, refuses rather than guesses, and does not make
 * the accounting worse. This is that step, and `docs/adr/0027` is what it landed as.
 *
 * == Why it is a file of its own and not a mode of `Domain.Built.settle` ==
 *
 * `Domain.scala` names no library and has no way to resolve a name, which is a decision that file
 * states: a caller's bridge may be a fact it derived by hand and never published, so the argument
 * there is a theorem rather than a name. Putting a search inside `settle` would put `Library`
 * underneath it and take that away.
 *
 * So the search sits **above** `settle` and calls it. What follows is worth more than the tidiness:
 * every theorem this file hands back was built by that method out of the derived rules and the
 * kernel, and every refusal that method gives is still what a caller gets by calling it. The
 * repository's standing rule about search — it may add a theorem and must never take a refusal
 * away — is structural here rather than something to be checked.
 *
 * == What makes it bounded ==
 *
 * The candidates are the library's lemmas **about the foundation constants the claim already
 * names**, by [[Library.about]], and not the library; [[candidates]] is that set, published so that
 * a caller can see the search space rather than infer it. Each is tried on its own, so the cost is
 * one call to `settle` per candidate and each of those is `2n + 1` decisions over its instances. A
 * claim whose constants hold more than [[Candidates]] such lemmas is refused rather than run.
 *
 * Three things cut that set down and they are not all the same kind of thing. A lemma binding a
 * type the claim names no term of is dropped **exactly**: it produces no instance and can change no
 * decision. A lemma that is **inert** here is dropped exactly too, for a reason [[inert]] gives: it
 * speaks, with one polarity, about a constant neither the claim nor the domain's axioms name, so
 * every instance of it is true under an assignment the rest of the decision cannot see. A lemma
 * about what a numeral is built from is dropped as a **judgement** about what a claim is about,
 * which the `Literal` set states and names what it loses.
 *
 * == Why the report names the bridges, and why it is entitled to ==
 *
 * `Domain.Spending` reports axioms, and a bridge is a theorem rather than an axiom, so a reader of
 * the price cannot see which fact carried the claim across: what shows is the naturals' two axioms,
 * which every arithmetic lemma there is would have charged. [[Found.bridges]] is the missing half,
 * and it is honest for a measured reason rather than by construction.
 *
 * **A bridge that settles a claim is not always a bridge the claim needed.** A foundation constant
 * can sit where the decision never reads it — `NUM_LT (Attempts j) 3 /\ Abandoned j ==> Abandoned j`
 * is settled by any lemma at all and by none — and a report naming whichever was tried first would
 * be inventing a reason. So that question is asked first, with `|- T` for a bridge: a claim that
 * settles carrying nothing but truth needed no arithmetic and comes back with [[Found.bridges]]
 * empty. Every bridge this file names is one the claim did not settle without.
 *
 * == Cheapest rather than first ==
 *
 * Every candidate that carries the claim on its own is tried rather than the first one that works,
 * and what is reported is the one whose conclusion spends the fewest foundational axioms, then the
 * one whose free route was not cut short, then the first by name. The others that would also have
 * worked are in [[Found.alternatives]] rather than dropped, because "the cheapest was chosen" is a
 * claim a reader should be able to check instead of taking.
 *
 * == What it does not do ==
 *
 * **It does not combine bridges.** A claim needing two lemmas at once is refused, and the refusal
 * says so rather than leaving a reader to conclude the claim is out of reach: naming both settles
 * it, which is the route `docs/adr/0024` built and this one does not remove. Why the combining
 * search is a piece of work of its own rather than a flag here is in that record's successor.
 *
 * It does not search over the domain's own axioms, look for a claim, or interpret anything. A claim
 * whose arithmetic is about a domain **type** has no bridge to find, exactly as it has none to be
 * named, and it is refused here by the sentence `settle` refuses it with.
 */
object Bridging {

  /**
   * How many library lemmas one claim may put to the decision.
   *
   * A bound on this search rather than on the library, and it counts decision runs: one call to
   * `Domain.Built.settle` per candidate, each of them `2n + 1` decisions over its own instances.
   * `BridgingSpec` measures the search space of the retry claim of `docs/adr/0024` against this
   * number rather than writing either down, which is what says the bound is above the shape the
   * method was built for and not merely above nothing.
   *
   * A caller past the bound is not stuck: naming the bridge is the route `docs/adr/0024` built and
   * this search does not replace it.
   */
  val Candidates: Int = 128

  /**
   * What the search settled, the bridges it spent, and how much it had to look at.
   *
   * [[bridges]] is empty in two situations that [[verdict]] tells apart: a claim that needed no
   * arithmetic settles with nothing spent, and a claim no candidate carried comes back refused.
   */
  final case class Found(
    verdict: Domain.Verdict,
    bridges: Vector[Library.Entry],
    considered: Int,
    alternatives: Vector[Library.Entry]
  ) {

    /** The line a report prints: what carried the claim, what it cost, and out of how many. */
    def summary: String = {
      val spent =
        if (bridges.isEmpty) "no bridge"
        else s"over ${bridges.map(entry => s"${entry.development}.${entry.name}").mkString(", ")}"

      val price = verdict match {
        case Domain.Verdict.Settled(_, spending) => spending.summary
        case Domain.Verdict.CutShort(_, spending, _) =>
          s"${spending.summary}, and the free route was cut short rather than decided"
        case Domain.Verdict.Countermodel(_) => "a countermodel of the claim's skeleton"
        case Domain.Verdict.Refused(why) => why
      }

      s"$spent, ${plural(considered, "candidate")} considered: $price"
    }
  }

  /**
   * The claim settled over a bridge this search found, or the refusal that says it found none.
   *
   * `library` is the caller's rather than the chain's, so a session holding facts of its own puts
   * them in with `Library.++` and has them searched. Ordering here is this file's own, so what that
   * buys is membership rather than precedence.
   */
  def settle(built: Domain.Built, classical: Classical, library: Library, goal: Term): Found =
    if (built.reaches(goal).isEmpty) Found(built.settle(classical, goal), Vector.empty, 0, Vector.empty)
    else
      withoutArithmetic(built, classical, goal) match {
        case Some(verdict) => Found(verdict, Vector.empty, 0, Vector.empty)
        case None => search(built, classical, library, goal)
      }

  /**
   * The same, for a claim written in the domain's own notation.
   *
   * Read against the domain's notation and not the classical extension's, for the reason
   * `Domain.Built.settle`'s text overload gives: the two differ by everything the foundation added
   * below the domain, and a claim about counted things is written with numerals.
   */
  def settle(built: Domain.Built, classical: Classical, library: Library, text: String): Found =
    Parser.proposition(built.theory, built.notation, text) match {
      case Left(error) => Found(Domain.Verdict.Refused(error.message), Vector.empty, 0, Vector.empty)
      case Right(goal) => settle(built, classical, library, goal)
    }

  /**
   * The lemmas this search would try for that claim, which is the whole of what it may spend.
   *
   * Published rather than private because a bound nobody can see the subject of is a number: a
   * caller that wants to know why a claim was refused for its size, or a test that wants to measure
   * the search space against [[Candidates]], asks here.
   *
   * Two things shape it and neither is a preference. Lemmas are deduplicated by name **and**
   * statement rather than by either alone: `Order` re-exports the facts of `Positivity`, so three
   * names are held by two developments each and trying both would be two decision runs of one
   * question, while two genuinely different statements under one name are two candidates and
   * reporting one of them for the other would name the wrong lemma.
   *
   * And a lemma is dropped where the claim names no term of some binder's type. That is exact
   * rather than a heuristic: a bridge is specialised at the maximal subterms of its binders' types
   * that the claim names, so such a lemma produces **no instance**, and a bridge with no instances
   * changes no decision `Domain.Built.settle` makes. The one thing it could still do is come back
   * settled anyway, which is the inert claim that [[settle]] rules out before it gets here.
   */
  def candidates(built: Domain.Built, library: Library, goal: Term): Vector[Library.Entry] =
    (built.reaches(goal) -- Literal).toVector.sorted
      .flatMap(library.about)
      .distinctBy(entry => (entry.name, entry.theorem.conclusion))
      .filter(entry => specialisable(built, goal, entry.theorem))
      .filterNot(entry => inert(built, goal, entry.theorem))
      .sortBy(entry => (entry.name, entry.development))

  /**
   * What a numeral is built from, which a claim names without being about it.
   *
   * `Domain.Structural` draws this line once already, for the connectives: what a claim is built
   * **with** rather than what it is **about**. A numeral is the same thing one level down.
   * `Attempts j < 3` reaches `NUM_ONE` and `NUM_BIT1` because `docs/adr/0012` encodes `3` in them,
   * and a reader who wrote that claim did not name them: what the claim is about is the order.
   *
   * The measurement that made this a decision rather than a tidy-up. On 2026-09-18 the retry claim
   * of `docs/adr/0024` had **128** candidates after every other filter, of which most came from
   * those two, and a peer's lemmas landing in `Peano` the same afternoon pushed the search one past
   * [[Candidates]] and turned an answer into a refusal for size. A bound whose subject grows with
   * the library every time anybody proves something about the number one is a bound on the wrong
   * thing.
   *
   * **It is a heuristic and not the exact filter above, so the loss is named.** A bridge that is
   * genuinely about the encoding — `Peano.NUM_ONE_SUC` is the one to picture — is not found by this
   * search, and a caller that wants it names it, which is the route `docs/adr/0024` built and this
   * one never removes.
   */
  private val Literal: Set[String] =
    Set(Natural.NumberZero, Peano.NumeralOne, Peano.NumeralBit0, Peano.NumeralBit1)

  /**
   * Whether the claim settles carrying `|- T` and nothing else, which is the control on the report.
   *
   * `Domain.Built.settle` refuses a claim that reaches the foundation when the bridges are empty,
   * so there is no asking it this by asking for nothing: what that refusal is about is a caller who
   * has not thought about the arithmetic, and truth is a bridge that has thought about it and
   * supplies no fact. An answer here means the foundation constants the claim names are inert in
   * its skeleton, and then every candidate settles it and none of them is the reason.
   */
  private def withoutArithmetic(
    built: Domain.Built,
    classical: Classical,
    goal: Term
  ): Option[Domain.Verdict] =
    classical.logic
      .over(built.theory)
      .flatMap(_.rules.truth)
      .toOption
      .flatMap(truth => carried(built.settle(classical, goal, Vector(truth))))

  private def search(built: Domain.Built, classical: Classical, library: Library, goal: Term): Found = {
    val about = built.reaches(goal).toVector.sorted
    val tried = candidates(built, library, goal)

    if (tried.length > Candidates)
      Found(
        Domain.Verdict.Refused(
          s"a claim whose foundation constants hold at most $Candidates lemmas between them, and " +
            s"${about.mkString(", ")} hold ${tried.length}: each candidate is a decision run of its " +
            "own, so this is a bound on the search rather than on the claim. Name the bridge and it " +
            "will be specialised at the terms this claim already names"
        ),
        Vector.empty,
        tried.length,
        Vector.empty
      )
    else {
      val attempts = tried.map(entry => (entry, built.settle(classical, goal, Vector(entry.theorem))))
      val carriedBy = attempts.flatMap { case (entry, verdict) => carried(verdict).map((entry, _)) }

      carriedBy.sortBy { case (entry, verdict) => (price(verdict), cutShort(verdict), entry.name) } match {
        case (entry, verdict) +: rest =>
          Found(verdict, Vector(entry), tried.length, rest.map(_._1))

        case _ =>
          val refuted = attempts.count {
            case (_, Domain.Verdict.Countermodel(_)) => true
            case _ => false
          }

          Found(
            Domain.Verdict.Refused(
              s"a claim of ${built.domain.name} that some one lemma about ${about.mkString(", ")} " +
                s"carries it into the foundation: ${plural(tried.length, "candidate")} tried, " +
                s"$refuted of them leaving the claim's skeleton with a countermodel. This search " +
                "tries a candidate on its own and never two together, so a claim needing two facts " +
                "at once is refused here and is not thereby out of reach: naming both settles it"
            ),
            Vector.empty,
            tried.length,
            Vector.empty
          )
      }
    }
  }

  /** Whether the claim names a term for every binder of the lemma, so an instance exists at all. */
  private def specialisable(built: Domain.Built, goal: Term, bridge: Kernel.Thm): Boolean =
    Logic.stripForall(bridge.conclusion) match {
      case Left(_) => true
      case Right((binders, _)) =>
        binders.forall(binder => built.subjectsOfType(goal, binder.ty).nonEmpty)
    }

  /** A verdict that reached a theorem, which is the only kind a bridge can be read off. */
  /**
   * Whether a candidate can change no decision this claim puts to it, for a reason in the lemma.
   *
   * A constant that neither the claim nor any axiom of the domain names cannot reach an atom of
   * the rest of the decision: the axioms' instances are built from the axioms and the claim's own
   * subterms, and the candidate's instances carry the constant wherever the lemma had it. So if
   * every atom of the lemma holding such a constant occurs with **one** polarity, each of those atoms
   * can be put to the value that satisfies it, `T` where it occurs positively and `F` where it occurs
   * negatively, and the rest of the decision does not notice. When the lemma then simplifies to `T`
   * it is a tautology after a substitution for atoms, every instance of it is one too, and the claim
   * follows with it exactly when it follows without it. That is the pure-literal rule, and it is
   * sound **intuitionistically** as well as classically, which is what makes it exact here rather
   * than for one of the two routes: substituting a formula for an atom preserves derivability in both
   * logics, and the simplification below uses only `~F = T`, `~T = F`, and the laws of `/\`, `\/` and
   * `==>` against `T` and `F`, all of them intuitionistic.
   *
   * **The polarity is per constant and not per atom**, and that is not caution. Two atoms of one
   * lemma that differ can become the same atom once the binders are specialised, `NUM_DIVIDES x y`
   * and `NUM_DIVIDES y x` at `x = y` being the one to picture; if they held one constant with two
   * polarities between them, fixing both would fix one atom twice. Asking that every atom holding
   * the constant has the same polarity rules that out whatever the specialisation does.
   *
   * What made it a decision rather than a tidy-up, on 2026-09-25: the retry claim's search space was
   * **64**, exactly half of [[Candidates]] and so exactly at the margin `BridgingSpec` asks for, and
   * three lemmas about divisibility landing in `Primes` took it to 67. Each of them concludes a
   * divisibility the claim cannot see, which is the shape this drops. A bound whose subject grows
   * with every lemma that mentions `<` on the way to saying something else is the bound on the wrong
   * thing that `Literal` was already written against, and this is the exact half of that repair.
   */
  private def inert(built: Domain.Built, goal: Term, bridge: Kernel.Thm): Boolean = {
    val present =
      constantNames(goal) ++ built.axioms.values.flatMap(axiom => constantNames(axiom.conclusion))
    val body = Logic.stripForall(bridge.conclusion).map(_._2).getOrElse(bridge.conclusion)
    val occurrences = atoms(body, positive = true)

    val pure: Set[String] = occurrences
      .flatMap { case (atom, positive) => (constantNames(atom) -- present).toVector.map(_ -> positive) }
      .groupMap(_._1)(_._2)
      .collect { case (name, polarities) if polarities.distinct.size == 1 => name }
      .toSet

    // An atom holding a pure constant has one polarity, because every atom holding that constant
    // does, so the value it is fixed at is read off any one of its occurrences.
    val fixed: Map[Term, Boolean] = occurrences
      .collect { case (atom, positive) if constantNames(atom).exists(pure.contains) => atom -> positive }
      .toMap

    pure.nonEmpty && valueOf(body, fixed).contains(true)
  }

  /** Every atom of a proposition with the polarity it occurs at, reading the five connectives. */
  private def atoms(term: Term, positive: Boolean): Vector[(Term, Boolean)] = term match {
    case Const(Logic.Truth, _) | Const(Logic.Falsity, _) => Vector.empty
    case App(Const(Logic.Negation, _), inner) => atoms(inner, !positive)
    case App(App(Const(Logic.Conjunction | Logic.Disjunction, _), left), right) =>
      atoms(left, positive) ++ atoms(right, positive)
    case App(App(Const(Logic.Implication, _), antecedent), consequent) =>
      atoms(antecedent, !positive) ++ atoms(consequent, positive)
    case atom => Vector(atom -> positive)
  }

  /** A proposition's value where the fixed atoms decide it, and nothing where they do not. */
  private def valueOf(term: Term, fixed: Map[Term, Boolean]): Option[Boolean] = term match {
    case Const(Logic.Truth, _) => Some(true)
    case Const(Logic.Falsity, _) => Some(false)
    case App(Const(Logic.Negation, _), inner) => valueOf(inner, fixed).map(!_)
    case App(App(Const(Logic.Conjunction, _), left), right) =>
      (valueOf(left, fixed), valueOf(right, fixed)) match {
        case (Some(false), _) | (_, Some(false)) => Some(false)
        case (Some(true), Some(true)) => Some(true)
        case _ => None
      }
    case App(App(Const(Logic.Disjunction, _), left), right) =>
      (valueOf(left, fixed), valueOf(right, fixed)) match {
        case (Some(true), _) | (_, Some(true)) => Some(true)
        case (Some(false), Some(false)) => Some(false)
        case _ => None
      }
    case App(App(Const(Logic.Implication, _), antecedent), consequent) =>
      (valueOf(antecedent, fixed), valueOf(consequent, fixed)) match {
        case (Some(false), _) | (_, Some(true)) => Some(true)
        case (Some(true), Some(false)) => Some(false)
        case _ => None
      }
    case atom => fixed.get(atom)
  }

  private def constantNames(term: Term): Set[String] = term match {
    case Const(name, _) => Set(name)
    case App(fn, argument) => constantNames(fn) ++ constantNames(argument)
    case Abs(_, inner) => constantNames(inner)
    case _ => Set.empty
  }

  private def carried(verdict: Domain.Verdict): Option[Domain.Verdict] = verdict match {
    case settled: Domain.Verdict.Settled => Some(settled)
    case cut: Domain.Verdict.CutShort => Some(cut)
    case _ => None
  }

  /** What the conclusion spends outside the domain, which is what "the cheapest bridge" means. */
  private def price(verdict: Domain.Verdict): Int = verdict match {
    case Domain.Verdict.Settled(_, spending) => spending.foundational.size
    case Domain.Verdict.CutShort(_, spending, _) => spending.foundational.size
    case _ => Int.MaxValue
  }

  /** Later than an answer of the same price whose free route was not truncated. */
  private def cutShort(verdict: Domain.Verdict): Int = verdict match {
    case Domain.Verdict.CutShort(_, _, _) => 1
    case _ => 0
  }

  /** One candidate rather than 1 candidates, which is a sentence somebody reads. */
  private def plural(count: Int, noun: String): String =
    if (count == 1) s"1 $noun" else s"$count ${noun}s"
}
