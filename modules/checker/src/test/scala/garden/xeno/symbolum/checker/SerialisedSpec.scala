package garden.xeno.symbolum.checker

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.kernel.*

/**
 * A proof that left this process as text, and came back checked.
 *
 * `ReplaySpec` is the in-process reading: it holds a `Kernel.Thm` and reads the terms out of it
 * with the kernel's extractors, which `docs/architecture.md` named as the part of the gap that
 * route cannot close. This is the other route. What crosses is characters, and everything on this
 * side of them is `Parse` and `Check`, neither of which names a kernel type.
 *
 * What that buys, stated exactly so nobody claims more: the extractors are out of the argument. The
 * writer is not, and cannot be, since something has to put the proof down. A writer that writes
 * down a proof other than the one derived produces a table that fails to check, which is the whole
 * of what a checker can do about a writer.
 */
class SerialisedSpec extends AnyFlatSpec with Matchers {

  /**
   * The verdict over the text, with the axioms checked against the theory rather than only counted.
   *
   * The theory is passed since 2026-09-11, and the reason is a shape that used to pass: the walk
   * accepts an axiom step because accepting it is what an axiom step is, so a proof naming `F` as
   * an axiom came back `Holds`. Whether the theory asserts it is a question with an answer, and
   * `ReplaySpec` carries the case.
   */
  private def checked(entry: Replayed.Entry): Check.Holds = {
    val name = entry.label
    Check.text(Proof.write(entry.theorem), entry.theory) match {
      case Right(verdict: Check.Holds) => verdict
      case Right(Check.Fails(step, rule, why)) =>
        fail(s"$name: the checker refused a $rule step, expecting $why, on ${step.conclusion}")
      case Right(Check.RestsOnUnvouched(axiom, _)) =>
        fail(s"$name: the proof rests on $axiom, which the theory does not assert")
      case Left(why) => fail(s"$name: the text did not read as a proof: $why")
    }
  }

  /**
   * The same proofs `ReplaySpec` reads in this process, and the list lives in neither file.
   *
   * It used to be a copy here, one proof shorter than that one and both shorter than the table in
   * `docs/evaluation.md`. What made that worth repairing rather than tidying is the count in the
   * document: "theorems replayed in the suite" is a claim about a list, and it said nine while
   * three different lists were being replayed.
   */
  private val cases: Vector[Replayed.Entry] = Replayed.entries

  "Every proof" should "check when it arrives as text and nothing else" in {
    // Every step, cited facts' included: the text holds a cited fact's proof under its citation,
    // so what is checked is the whole graph, which the in-process reading also walks. The report's
    // own count stops at a citation since `docs/adr/0047` and is the smaller of the two.
    cases.foreach { entry =>
      withClue(s"${entry.label}: ") {
        val inProcess = Check.proof(entry.theorem, entry.theory) match {
          case holds: Check.Holds => holds.steps
          case other => fail(s"$other")
        }
        checked(entry).steps shouldBe inProcess
        checked(entry).steps should be >= Derivation.size(entry.theorem)
      }
    }
  }

  it should "include proofs that cite a published fact, so the citation is checked as text" in {
    // The guard against the test above passing because no proof here crosses a boundary.
    val citing = cases.filter(entry => Proof.write(entry.theorem).linesIterator.exists(_.contains(" cite ")))

    citing should not be empty
    info(s"${citing.size} of ${cases.size} cite a published fact")
  }

  it should "reach the same axioms it reaches in this process" in {
    // Two readings of the same proof agreeing about what is believed. The set is what
    // `docs/evaluation.md` reports per theorem, so a serialised route that lost an axiom would make
    // that table wrong rather than merely different.
    cases.foreach { entry =>
      val overText = checked(entry).axioms
      val inProcess = Check.proof(entry.theorem, entry.theory) match {
        case holds: Check.Holds => holds.axioms
        case other => fail(s"${entry.label}: $other")
      }

      withClue(s"${entry.label}: ") { overText shouldBe inProcess }
    }
  }

  "The text" should "carry a term once however many steps use it" in {
    // The property that decides whether this is usable at all. A proof of tens of thousands of
    // inferences over a handful of terms is small; the same proof with the terms copied into every
    // step is not, and the difference is the reason the format numbers its records.
    //
    // **Measured against what the alternative would cost, since 2026-09-11**, and the reason it
    // changed is worth reading. It used to compare the term records with the step count, which is a
    // proxy and was a good one only while a proof carried a great deal of redundant reflexivity:
    // those steps reuse terms, so more of them made the ratio look better. The rewriter stopped
    // building them, the proof lost a third of its nodes, the vocabulary did not shrink with it,
    // and the proxy inverted while the property it stood for was untouched. So the property is
    // measured directly: the records against the nodes the steps would have written out on their
    // own.
    val theorem = Replayed.entry(Replayed.Serialised).theorem
    val text = Proof.write(theorem)

    val terms = text.linesIterator.count(_.startsWith("t "))
    val steps = text.linesIterator.count(_.startsWith("s "))

    // The text replays every cited fact and `Derivation.size` counts the proof's own part, which
    // `docs/adr/0047` separates; the two agreed on this proof while the sixteen of the reals were
    // asserted and it cited nothing. Since `docs/adr/0053` it cites the ones it uses, and the count
    // the text has to match is the checker's, which replays the same way.
    steps shouldBe (Check.proof(theorem) match {
      case Check.Holds(counted, _) => counted
      case other => fail(s"the checker refused the proof: $other")
    })

    val written = Replayed.nodesOf(theorem)
    terms should be < written / 10

    info(
      s"$steps steps, $terms distinct terms against $written nodes written out, " +
        f"a sharing factor of ${written.toDouble / terms}%.1f; ${text.length} characters, " +
        f"${text.length.toDouble / steps}%.1f characters a step"
    )
  }

  it should "be refused rather than half-read when it is damaged" in {
    // Every one of these is a text that is not a proof, and none of them can be a false theorem:
    // a table that does not parse never reaches a rule check. What they guard is that the reader
    // says so instead of falling over, which is the contract every other refusing thing here keeps.
    val text = Proof.write(Replayed.entry("`0 < 1`").theorem)

    Check.text("") should be a Symbol("left")
    Check.text("proof 2\nend 0") should be a Symbol("left")
    Check.text(text.replace("end", "stop")) should be a Symbol("left")
    Check.text(text.linesIterator.filterNot(_.startsWith("t 0 ")).mkString("\n")) should be a
      Symbol("left")
  }

  it should "refuse a step whose premises are not the number its rule takes" in {
    // `Parse` checks the arity rather than leaving `Check` to meet a `Vector` of the wrong length,
    // because the two produce different reports: one says the text is malformed and the other says
    // a proof step is wrong, and only the second is a claim about mathematics.
    val text = Proof.write(Replayed.entry("`0 < 1`").theorem)
    val damaged = text.linesIterator
      .map(line => if (line.startsWith("s ") && line.contains(" trans ")) line.replaceFirst(" ; \\d+ \\d+ ;", " ; ;") else line)
      .mkString("\n")

    if (damaged != text) Check.text(damaged) should be a Symbol("left")
  }

  "A step the writer got wrong" should "be caught, which is what makes the text worth checking" in {
    // The writer is the one thing this route still shares with the kernel, so the question worth
    // asking of it is what happens when it is wrong. A conclusion swapped for another term is the
    // simplest form of wrong, and the rule check catches it: what the step claims is no longer an
    // instance of the rule it names.
    val theorem = Replayed.entry("`(x + 1)^2` expanded").theorem
    val text = Proof.write(theorem)

    val lines = text.linesIterator.toVector
    val last = lines.lastIndexWhere(_.startsWith("s "))
    val fields = lines(last).split(' ').toVector
    val forged = (fields.dropRight(1) :+ "0").mkString(" ")

    Check.text(lines.updated(last, forged).mkString("\n")) match {
      case Right(Check.Fails(_, _, _)) => succeed
      case Left(_) => succeed
      case Right(holds) => fail(s"a forged conclusion was accepted: $holds")
    }
  }

  "The reader" should "name no type of the kernel, which is the whole of what this route buys" in {
    // `Read.scala` is the in-process bridge and is allowed to; `Parse.scala` is this route and is
    // not. Asserted by reading the file, because the property is about what the source says and a
    // compile-time check would pass on an import that is merely unused.
    val source = java.nio.file.Files.readString(
      java.nio.file.Paths.get("modules/checker/src/main/scala/garden/xeno/symbolum/checker/Parse.scala")
    )

    Vector("garden.xeno.symbolum.kernel", "Kernel.", "Term.", "Type.", "Derivation.").foreach { name =>
      withClue(s"`Parse.scala` names $name: ") { source.contains(name) shouldBe false }
    }
  }
}
