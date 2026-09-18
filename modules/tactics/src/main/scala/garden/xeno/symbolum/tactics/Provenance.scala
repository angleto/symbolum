package garden.xeno.symbolum.tactics

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*
import garden.xeno.symbolum.theories.{Linarith, RealTheory}

/**
 * Where an assumption came from, kept beside a proof rather than inside it.
 *
 * A sequent carries propositions. `0 < x` is a proposition and "ARS 2022, table 4" is not, and the
 * distance between them is the whole of this file: a reader who is shown `a <= 60 * b |- ...` has
 * been shown a formula, and what they wanted was the measurement the formula came from. Without
 * something like this the left of the turnstile is a list of formulas instead of a trail back to
 * the data.
 *
 * == Why it is outside the kernel, and must stay there ==
 *
 * A citation is not a proposition and there is nothing to check about it. Putting it inside a
 * theorem would make it something the kernel carries and cannot verify, which is the one kind of
 * content the trusted base must not hold: everything a `Kernel.Thm` carries is believed because a
 * rule built it, and "ISPRA Tab. 3.1" is believed because somebody typed it. So this is a table
 * beside the proof, keyed by the proposition, and a theorem is exactly as trustworthy with it as
 * without.
 *
 * == Why it reads `Linarith.support` and not a theorem's hypotheses ==
 *
 * They are different questions and only one of them is the one a reader is asking. A sequent's
 * hypothesis list is an upper bound: a premise the derivation never touched still sits in it, so
 * attributing sources to it would credit a measurement that took no part in the conclusion.
 * `Linarith.support` is exact, because a certificate names its own support and a hypothesis weighed
 * by zero is not in it. Told that five measurements give a conclusion, the useful answer is which
 * three of them did, and this is that answer with the measurements named instead of the formulas.
 *
 * == The four things a trail keeps apart ==
 *
 * A premise with a source, a premise with none, a source for a premise the proof did not need, and
 * a source for a premise the goal does not make. The second is the reason this is a
 * [[Provenance.Trail]] and not a map: a report that listed only what it could attribute would print
 * a tidy list of sources under a proof that also rests on something nobody said where they got.
 * That is the shape of mistake `Refutation` keeps seven outcomes apart to avoid, one level up, and
 * it is the same mistake, an absent answer read as a negative one.
 *
 * **The last two were one list until 2026-09-10** and they call for opposite things. A citation for
 * a premise the goal does make, weighed zero by the certificate, says the argument carries an
 * assumption it does not need: the thing to do is drop the assumption, and the register is right.
 * A citation for a proposition the goal never makes says the register has gone stale, usually
 * because the proposition beside it was reworded: the thing to do is fix the register, and the
 * argument is right. Reported together, neither reading is available, and the second is the one an
 * exception list exists to force.
 *
 * Telling them apart needs the goal's own premises, which is why [[attribute]] takes them.
 */
final class Provenance private (val reals: RealTheory, val entries: Vector[Provenance.Entry]) {

  import Provenance.*

  /**
   * The source cited for a proposition, matched as a term and not by resemblance.
   *
   * Exact equality after reading, which is stricter than it looks and is meant to be: `0 < x` and
   * `0 < x + 0` denote the same claim and are different terms, and a citation that attached to the
   * second because it looked like the first would attach to the wrong thing exactly when a reader
   * has stopped checking. A citation that stops matching shows up as unused rather than drifting.
   */
  def source(proposition: Term): Option[String] =
    entries.find(_.proposition == proposition).map(_.source)

  /**
   * What a proof rests on, with the sources named.
   *
   * The premises come in the order the certificate reports them, which is the order they were
   * written in the goal, so two runs of the same question read the same way.
   */
  def attribute(
    assumed: Vector[Term],
    support: Vector[(Term, BigInt)],
    opened: Set[FVar] = Set.empty
  ): Trail = {
    val premises = support.map { case (proposition, weight) =>
      source(proposition) match {
        case Some(cited) => Premise.Cited(proposition, cited, weight)
        case None if Term.freeVariables(proposition).exists(opened.contains) =>
          Premise.Unnameable(proposition, weight)
        case None => Premise.Uncited(proposition, weight)
      }
    }

    val used = support.map(_._1).toSet
    val stated = assumed.toSet
    val unused = entries.filterNot(entry => used.contains(entry.proposition))

    Trail(
      premises,
      idle = unused.filter(entry => stated.contains(entry.proposition)),
      stale = unused.filterNot(entry => stated.contains(entry.proposition))
    )
  }

  /**
   * The trail for a goal, from the proof of it.
   *
   * The goal is proved first and the theorem thrown away, so a goal that does not follow gets a
   * refusal here rather than a list of sources for a conclusion nobody has.
   *
   * **A goal with leading quantifiers used to be refused outright**, and that was too blunt. The
   * argument for the refusal was right about the danger and wrong about its extent: a universal
   * goal's premises come back naming the variables the procedure opened its quantifiers into, those
   * variables did not exist when the citation was written, so such a premise would read as "nobody
   * said where this came from" when the truth is "no citation could ever have named it", and the
   * two are opposite things.
   *
   * But only the premises that **mention an opened variable** have that problem. A goal `!t. 0 < f
   * t ==> ...` whose register cites facts about `f` cites propositions that survive the stripping
   * untouched, and refusing the whole goal threw those away with the rest. So the goal is opened,
   * and a premise naming an opened variable gets [[Provenance.Premise.Unnameable]] rather than
   * [[Provenance.Premise.Uncited]]: the third case exists because merging it into the second is the
   * failure the refusal was protecting against, and refusing everything was a heavy way to avoid
   * one merge.
   */
  def trail(linarith: Linarith, goal: Term): Either[TacticError, Trail] =
    for {
      opened <- TacticError.lift(Logic.stripForall(goal))
      support <- TacticError.lift(linarith.support(goal))
    } yield attribute(stated(opened._2), support, opened._1.toSet)

  /**
   * The premises the goal states, as written.
   *
   * The same reading `Linarith` gives the goal, so a citation compares against the term the support
   * would have named. A goal that is not an implication states none, and then every citation is
   * stale, which is the right answer: nothing was assumed.
   *
   * **Public since 2026-09-11**, because an argument is many goals and the register question is
   * asked of all of them at once: a citation unused by one claim of a document is not stale, it is
   * used by another claim. `Argument` needs this to tell the two apart.
   */
  def stated(goal: Term): Vector[Term] =
    reals.logic.destImp(goal) match {
      case None => Vector.empty
      case Some((antecedent, _)) => conjuncts(antecedent)
    }

  private def conjuncts(term: Term): Vector[Term] =
    reals.logic.destConj(term) match {
      case Some((left, right)) => conjuncts(left) ++ conjuncts(right)
      case None => Vector(term)
    }

  /** The same, for a goal written in the theory's notation. */
  def trail(linarith: Linarith, text: String): Either[TacticError, Trail] =
    TacticError.lift(reals.proposition(text)).flatMap(trail(linarith, _))

  /**
   * The trail as text, with every proposition read back.
   *
   * Through [[Readback]] rather than through the printer, and for the reason that file exists: a
   * reader comparing a source against a premise is comparing text, and text that does not read back
   * as the term is text about a different premise. A trail is read exactly when somebody is
   * checking, so it is the last place to show a rendering.
   */
  def report(trail: Trail): Either[TacticError, String] = {
    def line(proposition: Term, label: String, weight: BigInt): Either[TacticError, String] =
      Readback.of(reals, proposition).map { text =>
        val times = if (weight == 1) "" else s" (weighed $weight)"
        s"  $label: $text$times"
      }

    for {
      rests <- traverse(trail.premises) {
        case Premise.Cited(proposition, cited, weight) => line(proposition, cited, weight)
        case Premise.Uncited(proposition, weight) => line(proposition, Uncited, weight)
        case Premise.Unnameable(proposition, weight) => line(proposition, Unnameable, weight)
      }

      idle <- traverse(trail.idle)(entry =>
        Readback.of(reals, entry.proposition).map(text => s"  ${entry.source}: $text")
      )

      stale <- traverse(trail.stale)(entry =>
        Readback.of(reals, entry.proposition).map(text => s"  ${entry.source}: $text")
      )
    } yield {
      val head = if (rests.isEmpty) "rests on nothing" else s"rests on:\n${rests.mkString("\n")}"
      val withIdle =
        if (idle.isEmpty) head else s"$head\nassumed and not needed:\n${idle.mkString("\n")}"
      if (stale.isEmpty) withIdle
      else s"$withIdle\ncited and not assumed:\n${stale.mkString("\n")}"
    }
  }

  private def traverse[A](
    items: Vector[A]
  )(f: A => Either[TacticError, String]): Either[TacticError, Vector[String]] =
    items.foldLeft[Either[TacticError, Vector[String]]](Right(Vector.empty)) { (acc, item) =>
      for {
        done <- acc
        next <- f(item)
      } yield done :+ next
    }
}

object Provenance {

  /** How a premise nobody cited is written, in one place so a reader can search for it. */
  val Uncited: String = "uncited"

  /** One assumption, and where it came from. */
  final case class Entry(proposition: Term, source: String)

  /**
   * What a premise no citation could have named is labelled as, in the page a person reads.
   *
   * Deliberately not the word used for an uncited premise: a reader who confuses the two goes
   * looking for a source that cannot exist.
   */
  val Unnameable: String = "no citation can name this: it mentions a quantified variable"

  /**
   * A premise a proof rested on, cited or not.
   *
   * Two cases and not an `Option`, because the two are read differently: a caller pattern-matching
   * on this cannot forget the second, and a caller mapping over an `Option` can.
   */
  enum Premise:
    case Cited(proposition: Term, source: String, weight: BigInt)
    case Uncited(proposition: Term, weight: BigInt)

    /**
     * A premise no citation could have named, because it mentions a variable the goal's quantifier
     * opened.
     *
     * Kept apart from [[Uncited]] for the reason this whole file keeps things apart: "nobody said
     * where this came from" is a criticism of the register, and "no citation could name this" is a
     * fact about the shape of the claim. A reader who acts on the first when the second is true goes
     * looking for a source that cannot exist.
     */
    case Unnameable(proposition: Term, weight: BigInt)

  /**
   * What a proof rested on, and what was cited for it that it did not use.
   *
   * `idle` is a citation for a premise the goal states and the certificate weighed zero: the
   * argument assumes something it does not need, and the register is right. `stale` is a citation
   * for a proposition the goal does not state at all: the register is out of date, usually because
   * the proposition beside it was reworded, and the argument is right.
   *
   * They were one list called `unused` until 2026-09-10, on the argument that what the label
   * claimed was only what both of them are. That was true of the label and useless to the reader:
   * one of them is fixed in the paper and the other in the register, and a reader shown the union
   * has to work out which for every line.
   */
  final case class Trail(premises: Vector[Premise], idle: Vector[Entry], stale: Vector[Entry])

  /**
   * A register, from propositions written in the theory's notation to their sources.
   *
   * The propositions are read rather than taken as terms, so what is cited is what the reader read,
   * and a citation whose proposition does not parse is a refusal rather than an entry nobody will
   * ever match.
   *
   * **Two sources for one assumption is refused.** It is a question for a person — which of the two
   * is the measurement this rests on — and answering it by keeping the last would answer it by the
   * order the register happened to be written in.
   */
  def of(
    reals: RealTheory,
    citations: Vector[(String, String)]
  ): Either[TacticError, Provenance] =
    citations
      .foldLeft[Either[TacticError, Vector[Entry]]](Right(Vector.empty)) { (acc, citation) =>
        val (text, source) = citation
        for {
          entries <- acc
          proposition <- TacticError.lift(reals.proposition(text))
          _ <-
            if (entries.exists(_.proposition == proposition))
              Left(
                FromLogic(
                  NotOfForm(s"a register citing each assumption once; $text is cited twice", proposition)
                )
              )
            else Right(())
        } yield entries :+ Entry(proposition, source)
      }
      .map(new Provenance(reals, _))
}
