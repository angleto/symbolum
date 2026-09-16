package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * Every named theorem a development holds, in one place, so that a reader can find one.
 *
 * To use a lemma here you have to know the `String` key of the map it lives in, and there are nine
 * such maps across the theories with no listing anywhere. Lean has `exact?`, `apply?`, `rw?`,
 * Loogle and Moogle; HOL Light has `search`. This has neither, and at the size this development is
 * the cheap answer dominates the expensive one: the whole library fits in a page, so printing it is
 * most of what a reader needs, and matching on the conclusion is tens of lines on top.
 *
 * == Read-only, and that is a decision rather than a stage ==
 *
 * Nothing here feeds a rewriter. The audit that asked for this named the hazard in the same breath:
 * a union that hands a rule set to `Ring` mixes theorems from developments with different axioms,
 * which is exactly the case `docs/adr/0008`'s constant origin covers for **defined** constants and
 * does not cover for declared ones. So an entry records the development it came from, the union is
 * for looking and printing, and a caller that wants to rewrite with a lemma asks the development
 * that owns it. Making that a type rather than a convention is what keeps the hazard out.
 *
 * == First order, like the matcher underneath ==
 *
 * [[matching]] finds a lemma whose conclusion the pattern matches, and `Matching.matchTerm` is
 * first order by its own docstring. A pattern with a predicate variable in it will not match, which
 * is the same limit the automation has everywhere and is recorded rather than worked around here.
 */
final class Library private (val entries: Vector[Library.Entry]) {

  /** Every name, sorted, which is what a listing is. */
  def names: Vector[String] = entries.map(_.name).sorted

  /**
   * Every entry of that name, which is more than one more often than it looks.
   *
   * `Order` re-exports the facts of `Positivity`, so three names are held by two developments each,
   * and a lookup returning the first would pick by map iteration order. Returning all of them is
   * the honest answer and makes the overlap visible instead of arbitrary.
   */
  def named(name: String): Vector[Library.Entry] = entries.filter(_.name == name)

  /** The names held by more than one development, which is a fact about the developments. */
  def shared: Vector[String] =
    entries.groupBy(_.name).collect { case (name, held) if held.size > 1 => name }.toVector.sorted

  /**
   * Every lemma whose conclusion the pattern matches, under the pattern's own variables.
   *
   * The variables of the pattern are what it may bind, so `x + y = y + x` searched with `x` and `y`
   * free finds commutativity and `0 + 1 = 1 + 0` finds nothing, which is the useful way round: a
   * caller looking for a lemma writes the shape, not an instance.
   *
   * **The same is true of the types, and it is the direction a caller will not expect.** The query
   * is the pattern and the lemma is the target, matching solves only the **pattern's** type
   * variables, so `FST (PAIR x:num y:num) = x` finds nothing and `FST (PAIR x:'a y:'b) = x` finds
   * `FST_PAIR`. Measured on the standard chain rather than reasoned about. It is the same rule as
   * for the terms — a query at an instance does not find the general statement — and it is worth
   * writing down because [[instantiating]] runs the match the other way round and therefore does
   * find a polymorphic lemma at a concrete goal.
   */
  def matching(pattern: Term): Vector[Library.Entry] = {
    val variables = Term.freeVariables(pattern)

    entries.filter { entry =>
      Logic
        .stripForall(entry.theorem.conclusion)
        .toOption
        .map(_._2)
        .exists(body => Matching.matchTerm(variables, pattern, body).isDefined)
    }
  }

  /**
   * Every lemma whose name contains the text, which is the other half of how anybody finds one.
   *
   * HOL Light's `search` takes a name fragment and a conclusion pattern, and the two answer
   * different questions: somebody who half remembers a name uses the first, and somebody who knows
   * the shape and not the name uses the second. Case is ignored because a caller half remembering a
   * name does not remember its case.
   */
  def whose(fragment: String): Vector[Library.Entry] =
    entries.filter(_.name.toLowerCase.contains(fragment.toLowerCase))

  /**
   * Every lemma that mentions the constant, by name.
   *
   * The question a reader actually asks, which is neither of the two above: "what do I have about
   * `Sum`". A name rather than a term, because a caller asking this does not have a term yet.
   */
  def about(constant: String): Vector[Library.Entry] =
    entries.filter(entry => Library.mentions(entry.theorem.conclusion, constant))

  /**
   * Whether some lemma held here IS the goal, once its own quantifiers are instantiated.
   *
   * The question that turns a listing into something a prover can use, and the one a reader asks
   * first: do I already have this? `!x. 0 <= x * x` is `SQUARE_NONNEG`, a lemma this library holds,
   * and the decision procedures do not reach it as a goal, so before 2026-09-10 asking for it got a
   * refusal from a system that had it written down. That is the same shape as the curried
   * implication the entry point could not read: the tactics could not use the theorems standing
   * beside them.
   *
   * Matching is first order, so a lemma whose statement quantifies over a predicate will not be
   * found this way. Same limit as everywhere else here, and recorded rather than worked around.
   *
   * The lemma is the **pattern** here and the goal is the target, which is the opposite of
   * [[matching]] and is what makes a polymorphic lemma reachable: `FST_PAIR` is stated over `'a`,
   * the goal is about `num`, and only the lemma's type variables are solved. A caller turning this
   * answer into a theorem instantiates the types before the terms; `Apply.to` is where that is done
   * and `Matching.Instantiation.instance` carries the argument for why it is sound.
   */
  def instantiating(goal: Term): Vector[Library.Entry] =
    entries.filter(entry => Library.instantiatesTo(entry.theorem.conclusion, goal))

  /**
   * Which lemmas held here the goal **is**, rather than merely an instance of.
   *
   * [[instantiating]] answers "is this already implied by something I hold", which is the question
   * a prover asks. This answers "is this the same statement", which is the question a measurement
   * of rediscovery asks, and the two are not the same: `!x. x + 0 = x` is an instance of
   * `!x y. x + y = y + x` composed with nothing, but it is not that lemma, and a generator that
   * produced it has not produced `ADD_SYM`.
   *
   * Mutual instantiation is the test, which is alpha-equivalence up to the naming of the leading
   * universals and no more. It is deliberately not equality of terms: the binders are locally
   * nameless (`docs/adr/0002`) so two statements that differ only in the order their quantifiers
   * were introduced are already equal, but two that differ in which variable stands where are not,
   * and mutual matching is what settles those.
   */
  def stating(goal: Term): Vector[Library.Entry] =
    instantiating(goal).filter(entry => Library.instantiatesTo(goal, entry.theorem.conclusion))

  /**
   * Which lemmas held here a proof actually rested on, by name.
   *
   * The question the surprise scale needs and could not ask. "What is this believed on" has an
   * answer, `Derivation.axiomsOf`, and it is coarse: almost everything arithmetic reaches most of
   * the sixteen. **Which of the named lemmas took part** is the finer signal, and a proof that
   * reaches one no earlier proof reached went somewhere earlier proofs did not.
   *
   * A name held by two developments comes back twice, for the reason [[named]] gives, and that is
   * the honest answer: the fact took part and both developments claim it.
   *
   * What this does **not** answer is "no earlier theorem touched it", which needs a memory of what
   * earlier theorems touched. That is the ledger's, not this class's: nothing here remembers.
   */
  def restingOn(theorem: Kernel.Thm): Vector[Library.Entry] = {
    val used = Derivation.restingOn(theorem, entries.map(_.theorem.conclusion).toSet)
    entries.filter(entry => used.contains(entry.theorem.conclusion))
  }

  /** Every lemma from one development, which is how a caller finds what it may rewrite with. */
  def from(development: String): Vector[Library.Entry] =
    entries.filter(_.development == development)

  /**
   * The listing, as the page a reader scans.
   *
   * Grouped by development and printed in the signature's own notation, because a lemma printed in
   * the kernel's is a lemma about a claim the reader did not write.
   *
   * `Signature.legible` rather than `show`, so that every line of the generated document is text
   * that reads back as the theorem it names. Until 2026-09-12 fourteen of them were not: the
   * polymorphic lemmas of `Product` and `Word` printed `prod(a, b)`, which the parser refuses, and
   * two of them print a free variable at the outermost level and need the annotated form even now
   * that they do not. `NotationRoundTripSpec` asserts it over the whole document.
   *
   * A statement no form of which reads back is listed with [[Library.NotReadable]] in front of it
   * rather than silently, because a reader copying a line out of this document has no way to tell
   * a statement that cannot be read from one that can. Nothing in the library is in that state
   * today and the test says which population it interrogated to say so.
   */
  def listing(signature: Signature): String =
    entries
      .groupBy(_.development)
      .toVector
      .sortBy(_._1)
      .map { case (development, held) =>
        val lines = held.sortBy(_.name).map { entry =>
          val statement = signature
            .legible(entry.theorem.conclusion)
            .getOrElse(s"${Library.NotReadable} ${signature.show(entry.theorem.conclusion)}")
          s"  ${entry.name.padTo(24, ' ')} $statement"
        }
        s"## $development\n\n${lines.mkString("\n")}"
      }
      .mkString("\n\n")
}

object Library {

  /**
   * What marks a statement in the listing that cannot be read back through the signature it was
   * printed with.
   *
   * A marker rather than an omission: a lemma missing from the document is a lemma nobody finds,
   * and a lemma whose statement cannot be parsed is one a reader must not paste into `Ask`.
   */
  val NotReadable: String = "[not readable back]"

  /**
   * One named theorem, and which development holds it.
   *
   * The development is not decoration. Two developments can hold a name each, and a caller that
   * wants to rewrite with a lemma has to ask the one that owns it rather than the union, for the
   * reason the class comment gives.
   */
  final case class Entry(development: String, name: String, theorem: Kernel.Thm)

  /**
   * The library of a chain: every development it assembled, and what it assumed.
   *
   * The axioms are in it, and that is not a category error. A reader searching for what they have
   * about `x + y` wants `ADD_SYM` whether it was assumed or derived, and the entry says which by
   * naming the development it came from. What the axioms must not do is disappear into the same
   * bucket as the theorems, which is why they are labelled rather than merged.
   */
  def of(chain: Chain): Library =
    new Library(
      // `Classical` is not a development of `modules/theories` and was therefore reached by nothing
      // here until 2026-09-12, which made nine proved or defined things invisible: the excluded
      // middle, the two De Morgans, double negation, `T` is not `F`, extensionality, the two
      // equations that make the conditional usable, and the conditional's own definition.
      // `Find COND` answered "nothing" to all three of its questions on the day `COND` landed, and
      // that is how this was found rather than by reading the code.
      //
      // **The axioms are deliberately NOT here**, and that is not an omission: `RestsOn` says why,
      // and a reader searching for what they have about `x + y` is not looking for the choice
      // operator. `RestsOnSpec` asserts that the reach report's library holds names this one does
      // not, so adding them would make that assertion vacuous rather than true.
      //
      // **And the label is `Classical, derived` rather than `Classical`**, which matters more than
      // it looks. `RestsOn` already uses `Classical` for the classical AXIOMS and puts that label
      // in its foundational bucket. Two libraries carrying one label with opposite meanings is how
      // a derived theorem gets reported as something the system asks you to believe, and the
      // excluded middle is exactly the theorem that would have been.
      collect("Classical, derived", chain.classical.facts) ++
        collect("Classical, defined", chain.classical.definitions) ++
        collect("Real, assumed", chain.reals.axioms) ++
        collect("Real, defined", chain.reals.definitions) ++
        collect("Positivity", chain.ring.positivity.facts) ++
        collect("Order", chain.order.facts) ++
        collect("Natural", chain.naturals.facts) ++
        collect("Peano", chain.peano.facts) ++
        collect("Series", chain.series.facts) ++
        // The five that were beside the chain until 2026-09-12. `Bounded` is not among them and is
        // not missing: it holds no `facts` map at all, because it proves a caller's statement
        // rather than a statement of its own. A development with nothing to collect is the one case
        // where absence here is correct, and it is written down so that the next reader counting
        // five names and finding four stops here rather than in `Chain`.
        collect("Divisibility", chain.divisibility.facts) ++
        collect("Modular", chain.modular.facts) ++
        collect("Product", chain.product.facts) ++
        collect("Word", chain.word.facts) ++
        // The sixth, and not one of the five. `Matrix` was written after the move and went into the
        // chain as it was written, so it has never been a development whose facts were in no
        // library; it is listed for the same reason the four above are, which is that a development
        // collected nowhere is a development `docs/lemmas.md` does not mention.
        collect("Matrix", chain.matrix.facts) ++
        collect("Rotation", chain.rotation.facts) ++
        // Joined on 2026-09-13, and the reason it was missing is the reason the five above were:
        // it was not in the chain, so it was not collected, so `docs/lemmas.md` did not list it.
        // Seventeen facts about `max`, `min`, `abs` and `sgn`, and the file that holds them calls
        // itself the choice axiom's first use outside the foundation.
        collect("Magnitude", chain.magnitude.facts) ++
        collect("Coding", chain.coding.facts) ++
        // The arithmetisation, joined on 2026-09-14 as the chain's last link. It is collected
        // here for the reason every development above is: one that is in no library is one
        // `docs/lemmas.md` does not mention, which has happened twice.
        collect("Numbering", chain.numbering.facts) ++
        collect("Language", chain.language.facts) ++
        collect("Provability", chain.provability.facts) ++
        collect("Primes", chain.primes.facts) ++
        collect("Deduction", chain.deduction.facts) ++
        // The two that landed on 2026-09-15, listed here in the same breath as they were written
        // rather than after somebody noticed: `Magnitude` and `Coding` were each invisible for a
        // few hours because a development in the chain but not collected here is a development
        // `docs/lemmas.md` does not mention, and `ChainCoverageSpec` exists because that happened
        // twice.
        collect("Limit", chain.limit.facts) ++
        collect("Transcendental", chain.transcendental.facts) ++
        // Landed 2026-09-16 and collected in the same change, for the reason the two above give:
        // `Magnitude` and `Coding` were each invisible for a few hours because a development in the
        // chain but not collected here is one `docs/lemmas.md` does not mention.
        collect("Concatenation", chain.concatenation.facts)
    )

  /** A library over developments a caller names itself. */
  def of(developments: Vector[(String, Map[String, Kernel.Thm])]): Library =
    new Library(developments.flatMap { case (name, facts) => collect(name, facts) })

  private def collect(development: String, facts: Map[String, Kernel.Thm]): Vector[Entry] =
    facts.toVector.map { case (name, theorem) => Entry(development, name, theorem) }

  /**
   * Whether the lemma, with its leading universals instantiated, is exactly the goal.
   *
   * Both are stripped of their leading quantifiers and the bodies matched, then the goal's own
   * bound variables are what the match may not touch: `!x. 0 <= x * x` matches `!y. 0 <= y * y`
   * because they are the same statement, and it does not match `!x. 0 <= x * 2` because no
   * instantiation of the lemma's variable gives that.
   */
  private[theories] def instantiatesTo(lemma: Term, goal: Term): Boolean =
    (Logic.stripForall(lemma), Logic.stripForall(goal)) match {
      case (Right((held, lemmaBody)), Right((_, goalBody))) =>
        Matching.matchTerm(held.toSet, lemmaBody, goalBody).isDefined
      case _ => false
    }

  /** Whether a term names the constant anywhere inside it, at any type. */
  private[theories] def mentions(term: Term, constant: String): Boolean = term match {
    case Const(name, _) => name == constant
    case App(fn, argument) => mentions(fn, constant) || mentions(argument, constant)
    case Abs(_, body) => mentions(body, constant)
    case _ => false
  }
}
