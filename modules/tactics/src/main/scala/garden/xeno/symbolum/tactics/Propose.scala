package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.Logic
import garden.xeno.symbolum.theories.{Library, Signature}

/**
 * The half of the discovery loop that proposes, which did not exist.
 *
 * `Discovery` screens a candidate and certifies it, `Ledger` remembers, `Oracle` checks the algebra
 * system's own answers, and `Novelty` ranks what comes out. Every one of those **takes** a candidate.
 * Until this file, a person or a model had to supply them, and "the system finds relations" was a
 * description of a loop with a hole where its first step should be.
 *
 * == Why this source and not a more exciting one ==
 *
 * The card that asked for a generator lists four sources in order of how much each has actually
 * discovered: integer relation detection, structural mutation of known theorems, mining the algebra
 * system, and closed forms for parametric families. The first has the real track record, and when
 * this file was written it was out of reach for two reasons that were not the same size: the model
 * evaluates in `Double`, and a relation among real constants cannot be stated in this theory at all.
 * `Algebraic` is the first, landed on 2026-09-13, and it got there by changing the subject rather
 * than the precision — an algebraic value needs no constant of its own, only reals whose powers are
 * whole numbers. This is the second, and it is still the one with a result on its first run.
 *
 * The fourth is `Family`, which landed on 2026-09-11 and works in a fragment with no decision
 * procedure, which is what makes its certified answers worth anything.
 *
 * **The third is not here and will not be, and that is a measurement.** Mining the algebra system
 * means running the normalisers over a population of generated expressions and proposing every pair
 * that normalises equal. Four hundred random expressions over `+`, `-`, `*` and small powers give
 * 905 such pairs, and every one of the first 120 put to `Novelty` comes back
 * [[Novelty.Standing.Immediate]]: settled at once by the ring normalisation, which is not news.
 *
 * It could not come back anything else. The pair was **selected** because the normaliser agreed,
 * and the normaliser decides that fragment, so certification was never in doubt and carries no
 * information. `docs/evaluation.md` makes the argument in general and this is it with a number on
 * it: a source that cannot produce a claim outside the region a procedure settles produces nothing
 * a person should read.
 *
 * It is also the one with a **result on the first run**, which is unusual for a generator: applied
 * to this repository's own library it asks, of every lemma, whether each of its hypotheses was
 * needed. A lemma that still proves without one was over-stated, and that is a finding about work
 * already done rather than a conjecture about work nobody has started.
 *
 * == What it does not do ==
 *
 * It does not invent. Every proposal is a known lemma with something removed or loosened, so the
 * space it explores is bounded by what is already there and nothing here will produce a statement
 * about an object the library does not mention. That is a real limit and it is the reason this is
 * the second source and not the last: what it buys is a working loop, measured end to end, into
 * which a better source can be dropped when the precision to run one exists.
 */
final class Propose private (val novelty: Novelty, val library: Library, val logic: Logic) {

  import Propose.*

  val reals: Signature = novelty.reals

  /**
   * Every lemma of the library with one hypothesis dropped, as a claim to put to the prover.
   *
   * A lemma with n antecedents gives n proposals. A lemma with none gives nothing, which is right:
   * there is no hypothesis to find unnecessary.
   *
   * == Distinct, and what it is distinct on ==
   *
   * `Order` re-exports the facts of `Positivity`, so `Library.entries` carries one row per
   * holding and three names are held twice: `ADD_POSITIVE`, `POSITIVE_NOT_ZERO` and `ZERO_LT_ONE`.
   * Without this the same claim is made twice from the same statement and put to the prover twice,
   * which is work done twice and two rows in every count downstream. `Recovery` was made distinct
   * on 2026-09-12 and this was left, with a note saying so; the note is discharged here.
   *
   * The object is the **proposal**, which carries the claim, so only genuinely identical proposals
   * merge. Two developments holding one name but different statements would still give two, which
   * is the right answer and is why this is not `distinctBy(_.from)`.
   */
  def weakenings: Vector[Proposal] =
    library.entries.flatMap { entry =>
      val statement = entry.theorem.conclusion

      Logic.stripForall(statement).toOption.toVector.flatMap { case (variables, body) =>
        val antecedents = peel(body, Vector.empty)._1

        antecedents.indices.toVector.flatMap { dropped =>
          rebuild(variables, antecedents.patch(dropped, Nil, 1), peel(body, Vector.empty)._2)
            .map(claim =>
              Proposal(entry.name, Source.Weakened, reals.show(antecedents(dropped)), claim)
            )
        }
      }
    }.distinct

  /**
   * Every lemma of the library with one binary operator swapped for another, as a claim.
   *
   * == Why this mutation and not a livelier one ==
   *
   * It is the only one on the card's list that can **rediscover**. Dropping a hypothesis makes a
   * lemma weaker and a weaker form of a lemma already held is not a lemma the library was missing;
   * generalising a numeral to a variable almost always produces something false. Substituting one
   * operator for another turns `!x y. x + y = y + x` into `!x y. x * y = y * x`, which is a
   * *different* lemma, and that is the shape a measurement of rediscovery needs: hide half the
   * library, mutate the other half, and count how many of the hidden ones come back.
   *
   * The table is four entries and is deliberately not a search over every pair of constants of the
   * right type. `+` for `*` and `<` for `<=` are the substitutions between operators that share
   * enough structure for the result to be worth screening; `+` for `sub` gives a false statement
   * from almost every input, and a generator whose output is nearly all false wastes the screen.
   *
   * == What it cannot do ==
   *
   * A lemma whose statement carries a lambda is skipped, and that is the whole `Series` half of the
   * library. Substituting inside a binder means rebuilding a term under it, and `Abs` is
   * `private[kernel]`: the public way back in is `Term.abs` over a free variable, which is the
   * dance `Matching` does and is more machinery than this mutation is worth. Stated rather than
   * worked around, and it is why the rediscovery figure is about the arithmetic half.
   */
  def substitutions: Vector[Proposal] =
    library.entries
      .flatMap { entry =>
        Swaps.toVector.flatMap { case (from, to) =>
          swapped(entry.theorem.conclusion, from, to)
            .filter(_ != entry.theorem.conclusion)
            .map(claim => Proposal(entry.name, Source.Substituted, s"$from became $to", claim))
        }
      }
      .distinct

  /** Every proposal this generator can make, from every source it has. */
  def proposals: Vector[Proposal] = weakenings ++ substitutions

  /**
   * Every proposal that reproduces a lemma the library holds and that did **not** come from it.
   *
   * This is the calibration the discovery card puts first and calls the test bench for everything
   * else: does the loop find the things we already know? If it does not find those it will not find
   * the others, and without this figure every claim about the loop is anecdote.
   *
   * == Why leave-one-out, and not the halved library the card describes ==
   *
   * The card says to hide half the library from the generator and count how many of the hidden ones
   * come back. This does the sharper thing, and it costs one pass instead of two. Every mutation
   * here is a function of **one** source lemma, so a proposal made from `L` is a proposal the
   * generator would have made from a library with every other lemma removed. Asking, of each
   * proposal, whether it states some lemma other than the one it was made from is therefore exactly
   * the leave-one-out question asked of every lemma at once, rather than of one arbitrary half.
   * The halved version also depends on where the split falls: `ADD_SYM` and `MUL_SYM` in the same
   * half makes that rediscovery impossible to observe, and no split can avoid every such pair.
   *
   * == What is counted and what is not ==
   *
   * `Library.stating` and not `Library.instantiating`, which is the difference between having
   * produced a lemma and having produced something that lemma implies. A dropped hypothesis very
   * often yields an instance of some unrelated general fact, and counting those would report a
   * rediscovery rate made almost entirely of coincidence.
   *
   * The source lemma is excluded **by name**. A name held by two developments is excluded from
   * both, which under-reports rather than over-reports and is the direction to err in here.
   *
   * == Why the result is made distinct, which the first run did not do ==
   *
   * `Order` re-exports the facts of `Positivity`, so several names are held by two developments
   * each and `Library.entries` carries one row per holding. That duplicates a recovery on both
   * ends: the mutation is made twice from the same statement, and the lemma it reaches is found
   * twice. The first run of this reported 19 where 13 mutations had happened, and three of the six
   * extra rows were the same sentence printed twice. The pair is the object here, not the row, so
   * the result is distinct on it.
   */
  def recoveries: Vector[Recovery] =
    proposals
      .flatMap { proposal =>
        library
          .stating(proposal.claim)
          .filter(_.name != proposal.from)
          .map(entry => Recovery(proposal, entry.name))
      }
      .distinct

  /**
   * The lemmas the operator substitution can mutate at all, by name.
   *
   * The denominator a rediscovery figure needs and does not have without it. Of the library's
   * entries, this source can only touch one that writes `+`, `*`, `<` or `le` and carries no
   * lambda, so a bare "twelve of two hundred and thirty-three" invites a reader to conclude that
   * the loop misses most of what it was shown, when most of what it was shown is not a statement
   * this source can produce anything from.
   */
  def mutable: Vector[String] = substitutions.map(_.from).distinct

  /**
   * Every proposal, put to the prover and ranked.
   *
   * The interesting answer is a proposal that comes back **certified**: the lemma holds without the
   * hypothesis that was dropped, so the hypothesis was never needed and the library over-states it.
   * Everything else is the ordinary outcome and is kept rather than filtered, because the count of
   * what came back uninteresting is what says whether the loop is worth running.
   */
  def audit: Vector[Finding] =
    proposals.map { proposal =>
      val reading = novelty.of(proposal.claim).toOption
      Finding(proposal, reading.map(_.standing), reading)
    }

  /* --------------------------------------------------------------- the plumbing */

  private def peel(current: Term, taken: Vector[Term]): (Vector[Term], Term) =
    logic.destImp(current) match {
      case Some((antecedent, consequent)) => peel(consequent, taken :+ antecedent)
      case None => (taken, current)
    }

  /**
   * The statement with one constant put in place of another, or nothing.
   *
   * `None` where the statement carries a lambda, for the reason the class comment gives, and where
   * the replacement does not type-check, which is the honest answer for a swap between constants
   * whose types differ.
   */
  private def swapped(statement: Term, from: String, to: String): Option[Term] =
    Logic.stripForall(statement).toOption.flatMap { case (variables, body) =>
      def go(term: Term): Option[Term] = term match {
        case Const(name, ty) if name == from => reals.theory.constant(to, ty).toOption
        case constant: Const => Some(constant)
        case App(fn, argument) =>
          for {
            left <- go(fn)
            right <- go(argument)
            applied <- Term.app(left, right).toOption
          } yield applied
        case Abs(_, _) => None
        case other => Some(other)
      }

      go(body).flatMap(replaced =>
        variables
          .foldRight(Right(replaced): Either[?, Term]) { (variable, acc) =>
            acc.flatMap(inner => logic.mkForall(variable, inner))
          }
          .toOption
      )
    }

  private def rebuild(
    variables: Vector[FVar],
    antecedents: Vector[Term],
    conclusion: Term
  ): Option[Term] = {
    val body = antecedents.foldRight(Right(conclusion): Either[?, Term]) { (antecedent, acc) =>
      acc.flatMap(inner => logic.mkImp(antecedent, inner))
    }

    body.toOption.flatMap { statement =>
      variables
        .foldRight(Right(statement): Either[?, Term]) { (variable, acc) =>
          acc.flatMap(inner => logic.mkForall(variable, inner))
        }
        .toOption
    }
  }
}

object Propose {

  /**
   * The operator substitutions this generator tries, and nothing else.
   *
   * Four, chosen rather than enumerated: a search over every pair of constants of the right type
   * would spend the screen on statements that are false by construction. See [[Propose.substitutions]].
   */
  val Swaps: Map[String, String] = Map(
    garden.xeno.symbolum.theories.Real.Addition -> garden.xeno.symbolum.theories.Real.Multiplication,
    garden.xeno.symbolum.theories.Real.Multiplication -> garden.xeno.symbolum.theories.Real.Addition,
    garden.xeno.symbolum.theories.Real.Order -> garden.xeno.symbolum.theories.Real.NonStrictOrder,
    garden.xeno.symbolum.theories.Real.NonStrictOrder -> garden.xeno.symbolum.theories.Real.Order
  )

  /**
   * Which mutation made a proposal, kept because the two mean different things about the answer.
   *
   * A weakening that comes back proved says the lemma it came from **over-states** its hypotheses,
   * which is a finding about work already done. A substitution that comes back proved says nothing
   * of the kind: it is a different lemma, and whether it is worth anything is the novelty scale's
   * question. Merging them made the first run report every proved substitution as an unnecessary
   * hypothesis, which is the shape of mistake this whole file is careful about.
   */
  enum Source {
    case Weakened, Substituted
  }

  /** A claim to put to the prover, where it came from, and what was done to it. */
  final case class Proposal(from: String, source: Source, change: String, claim: Term)

  /**
   * A lemma the library holds, produced by mutating a different one.
   *
   * Kept as a pair rather than as a set of names, because which lemma reached which is the part a
   * reader can check: `ADD_SYM` with `+` swapped for `*` is `MUL_SYM`, and that sentence is the
   * whole evidence that the loop is doing what it claims.
   */
  final case class Recovery(proposal: Proposal, reached: String)

  /** A proposal and what the prover made of it. */
  final case class Finding(
    proposal: Proposal,
    standing: Option[Novelty.Standing],
    reading: Option[Novelty.Reading]
  ) {

    /**
     * Whether the hypothesis that was dropped turned out to be unnecessary.
     *
     * **Proved outright, and charging nothing.** The first version of this asked the novelty
     * standing alone and reported, on its first run, that `~(x = 0)` is unnecessary in
     * `MUL_INVERSE`. It is not. `Field` proves `x * inv x = 1` **assuming** `~(x = 0)`, `Cost`
     * reports that as `Conditional`, and `Novelty` folds `Conditional` into `Earned` because it did
     * cost more than the minimum. So the hypothesis had not gone anywhere: it had moved from the
     * left of the arrow to the left of the turnstile, and a reading that looked only at the
     * standing could not see the difference.
     *
     * That is the exact merge this repository is built not to make, made by me, and caught by
     * running the thing rather than by reading it back. The report is consulted now and not the
     * standing: `Proved` with an empty condition list, and nothing else.
     */
    def unnecessary: Boolean =
      proposal.source == Source.Weakened && reading.map(_.report).exists { report =>
        report.outcome == Cost.Outcome.Proved && report.conditions.isEmpty
      }

    /**
     * Whether the proposal is a lemma the library did not already hold, and was certified.
     *
     * The substitution source's own reading of "worth something", and it is not the same question
     * as [[unnecessary]]. `Novelty` answers it: a claim the library holds comes back `Known`, one
     * the ring normalisation settles at once comes back `Immediate`, and what is left is a theorem
     * that cost more than the cheapest procedure could have.
     */
    def gained: Boolean =
      proposal.source == Source.Substituted && standing.contains(Novelty.Standing.Earned)
  }

  /** Over the standard chain, with its own library as the thing to audit. */
  lazy val standard: Propose = {
    val chain = garden.xeno.symbolum.theories.Chain.standard
    new Propose(Novelty.standard, Library.of(chain), chain.logic)
  }

  /** Over a development of one's own. */
  def apply(novelty: Novelty, library: Library, logic: Logic): Propose =
    new Propose(novelty, library, logic)
}
