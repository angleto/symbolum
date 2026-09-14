package garden.xeno.symbolum.logic

import garden.xeno.symbolum.kernel.*

/**
 * What a derivation did, at the size the person who wrote it was thinking in.
 *
 * A theorem records its derivation and that record is at the size the **kernel** works in, which is
 * not the same size at all. Measured over the library on 2026-09-13: the median lemma is 4651
 * kernel inferences, 70% of the nodes are congruence, equality elimination, transitivity and
 * reflexivity, and collapsing the graph at every node that is a named lemma still leaves 791
 * anonymous steps in the median. So a proof read back out of `Derivation` is a table of tens of
 * thousands of rows, and the account a reader wants is not in it: it was in the author's head and
 * in the shape of the `for` comprehension that wrote the proof down.
 *
 * This is where that shape is kept. One [[Step]] per line of a derivation, holding the rule that
 * was applied, what it was applied to, and what came out, so a derivation of ABS_TRIANGLE is
 * eighteen lines rather than 7559 inferences.
 *
 * == It is not part of any proof, and that is the whole of its safety ==
 *
 * A step is a description of an inference, not the inference: the theorem it holds was built by the
 * kernel and would exist unchanged if nothing here recorded anything. So the same argument
 * `Provenance` is written under applies, one level down: a wrong entry here is a report that
 * misdescribes a proof, never a proof that is wrong, and nothing in the trusted base consults it.
 *
 * It is deliberately **not** attached to `Kernel.Thm`. A theorem is a value the rules pass around
 * and copy; a script is an account of one derivation, and there is no such thing as the account of
 * a theorem, since the same sequent can be reached three ways in one file. So a script is returned
 * beside the theorem by the derivation that wrote it, and a caller that does not want one does not
 * pay for one.
 *
 * == What it cannot do ==
 *
 * Say **why**. "Specialise ADD_LE at x, abs x, y, abs y" is what happened and is not the sentence a
 * textbook writes, which would be "both terms are below their own magnitudes, so the sum is". The
 * gap between those is authored prose, and a generated document must mark which of the two it is
 * showing rather than let a reader take the first for the second.
 */
final case class Step(
  /** The operation, named for a reader rather than for the API: `specialise`, `modus ponens`. */
  rule: String,
  /** What the operation was given besides its premises: the arguments of a specialisation. */
  detail: Option[String],
  /**
   * The theorems it was applied to, as theorems.
   *
   * Not as names and not as indices, because at the moment a step is recorded neither is known: a
   * premise is a named lemma of some development, or the result of an earlier step, or neither,
   * and which of the three it is depends on a library the derivation has never heard of.
   * [[Script.render]] is where that is decided, and it is decided by looking.
   */
  premises: Vector[Kernel.Thm],
  /** What came out. */
  result: Kernel.Thm,
  /**
   * A name this step's caller has for a premise no library holds.
   *
   * Found by the first run of the spike rather than designed, and the case is exact: a rewriting
   * step is driven by `|- min x y = x + y - max x y`, which is the definition of `min` **unfolded**
   * at two arguments. The definition is held under a name and that equation is not, so the account
   * printed a bare sequent in the middle of an otherwise cited derivation. The caller of
   * [[Recorder.rewrite]] already says what it calls the rule, so the name exists at exactly the
   * point where the theorem does; what was missing was anywhere to put it.
   *
   * Deliberately per step and not a table on the script: two derivations can call the same
   * equation different things, and the one that used it is the one that gets to say.
   */
  names: Map[Kernel.Thm, String] = Map.empty
)

/** The steps of one derivation, in the order they were run. */
final case class Script(steps: Vector[Step]) {

  /** How many steps, which is the figure a spike is measuring. */
  def size: Int = steps.size

  /**
   * The same account with a line that is already in it not written a second time.
   *
   * Needed because accounts **compose**: three facts about `abs` are the three about `max` at `x`
   * and `-x`, so the account of the triangle inequality is built by replaying the account of each
   * of them, and the derivation of `max` is common to all three. Without this the reader is shown
   * the existence proof for `max` three times in one page.
   *
   * A line is the same line when its rule, its detail, its premises and its conclusion all agree,
   * and theorems compare by sequent, so a replayed step matches the one it replays. Two genuinely
   * different steps that agree on all four prove the same thing from the same things by the same
   * rule, and printing the second adds nothing to what a reader can check.
   */
  def tidy: Script = Script(steps.distinct)

  /**
   * The derivation as a numbered list, with each premise named where it can be named.
   *
   * Three ways a premise is referred to, tried in this order, and the order is the point: a lemma
   * the reader can look up, then a step of this derivation, then the sequent written out because
   * neither of the first two applies. Nothing is ever referred to by a name that resolves to
   * something else: the table is keyed by the sequent, so a premise reported as `ADD_LE` is a
   * theorem whose statement is `ADD_LE`'s, however it was obtained.
   *
   * Where two steps end at the same sequent the **first** is the one referred to. A derivation that
   * reaches one statement twice by two routes is describing the second one as the first, which is
   * wrong about the route and right about the fact; keeping both would give a reader two step
   * numbers for one statement and no way to choose.
   */
  /**
   * What the steps themselves name, which a caller's table does not hold.
   *
   * Merged **under** the caller's table in [[render]], so a theorem a library holds keeps the
   * library's name: those are the names a reader can look up, and a local one is a description.
   */
  def localNames: Map[Kernel.Thm, String] =
    steps.foldLeft(Map.empty[Kernel.Thm, String])((found, step) => found ++ step.names)

  def render(notation: Notation, held: Map[Kernel.Thm, String]): String =
    lines(held, Script.sequent(notation, _))
      .map(line => f"${line.number}%3d. ${line.head}\n      ${line.sequent}")
      .mkString("\n")

  /**
   * The account as numbered lines, with the sequents rendered by whatever the caller reads in.
   *
   * [[render]] is one presentation of this and a generated page is another, and the part they must
   * not each have their own copy of is **which name a premise is referred to by**. That decision is
   * here: a lemma the reader can look up, then a step of this account, then the sequent written
   * out. Two implementations of it would drift, and the drift would be a page citing something a
   * reader cannot find while the terminal cites it correctly.
   */
  def lines(held: Map[Kernel.Thm, String], sequent: Kernel.Thm => String): Vector[Script.Line] = {
    val names = localNames ++ held

    val earlier: Map[Kernel.Thm, Int] =
      steps.zipWithIndex.foldLeft(Map.empty[Kernel.Thm, Int]) { case (found, (step, position)) =>
        if (found.contains(step.result)) found else found + (step.result -> (position + 1))
      }

    def reference(theorem: Kernel.Thm): String =
      names
        .get(theorem)
        .orElse(earlier.get(theorem).map(position => s"step $position"))
        .getOrElse(sequent(theorem))

    steps.zipWithIndex.map { case (step, position) =>
      val from =
        if (step.premises.isEmpty) None
        else Some("from " + step.premises.map(reference).mkString(" and "))
      Script.Line(
        position + 1,
        (Vector(Some(step.rule), step.detail, from).flatten).mkString(" "),
        sequent(step.result),
        step.premises.flatMap(names.get).toSet
      )
    }
  }
}

object Script {

  /**
   * One line of an account: its number, what was done, what came out, and what it cited by name.
   *
   * `cites` is the names and not the theorems, because it exists for a page that wants to say which
   * lemmas an account leans on without resolving them a second time and possibly differently.
   */
  final case class Line(number: Int, head: String, sequent: String, cites: Set[String])

  /** A sequent in the notation a reader of the terminal reads. */
  def sequent(notation: Notation, theorem: Kernel.Thm): String = {
    val conclusion = Show.show(notation, theorem.conclusion)
    val left = theorem.hypotheses.map(Show.show(notation, _)).mkString(", ")
    if (left.isEmpty) s"|- $conclusion" else s"$left |- $conclusion"
  }

  /** The empty account, which is what a derivation nobody recorded has. */
  val nothing: Script = Script(Vector.empty)

  /**
   * A lookup table from a statement to the name it is held under.
   *
   * Keyed by the theorem and therefore by the sequent, since that is what `Kernel.Thm` compares by.
   * A development hands in its own facts maps and whatever it was built on; a premise that is in
   * none of them is referred to by its statement, which is the honest answer rather than a blank.
   */
  def names(held: Vector[Map[String, Kernel.Thm]]): Map[Kernel.Thm, String] =
    held.foldLeft(Map.empty[Kernel.Thm, String]) { (found, facts) =>
      facts.foldLeft(found) { case (table, (name, theorem)) =>
        if (table.contains(theorem)) table else table + (theorem -> name)
      }
    }
}

/**
 * A value produced by a derivation, with the account of how it was produced.
 *
 * The reason this exists rather than a mutable recorder is the shape of the code it has to fit: a
 * derivation here is a `for` comprehension over `Either[LogicError, Kernel.Thm]`, one bind per
 * step, and the whole value of the spike this was written for is that **the shape does not have to
 * change**. A derivation records itself by taking its operations from a [[Recorder]] instead of
 * from `Rules` and `Conv` directly; every `<-` stays where it was.
 *
 * **A refusal keeps the steps that came before it**, which is not an accident of the definition.
 * The question a reader asks about a derivation that stopped is where it got to, and an `Either`
 * answers with the error alone. Here the account survives the failure and can be printed under it.
 */
final case class Recorded[+A](steps: Vector[Step], value: Either[LogicError, A]) {

  def map[B](f: A => B): Recorded[B] = Recorded(steps, value.map(f))

  def flatMap[B](f: A => Recorded[B]): Recorded[B] = value match {
    case Left(error) => Recorded(steps, Left(error))
    case Right(held) =>
      val next = f(held)
      Recorded(steps ++ next.steps, next.value)
  }

  /** The account, whether or not the derivation got to the end. */
  def script: Script = Script(steps)

  /** The theorem and its account, for a caller that wants both, or the refusal. */
  def both: Either[LogicError, (A, Script)] = value.map((_, script))
}

object Recorded {

  /** A value that is not a step of the mathematics: parsing a term, looking a fact up. */
  def quiet[A](value: Either[LogicError, A]): Recorded[A] = Recorded(Vector.empty, value)

  /** A value already in hand. */
  def pure[A](value: A): Recorded[A] = Recorded(Vector.empty, Right(value))
}
