package garden.xeno.symbolum.theories

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The command that writes `docs/reading-register.md`: what has been read, and by whom, and against
 * what.
 *
 * `docs/architecture.md` says where a change is dangerous and the second entry is the axioms: *"a
 * mis-stated axiom makes everything provable, and the only test that fails is the pinned copy in
 * `RealSpec`, which fails because the text changed and not because it is wrong"*, and the same
 * paragraph extends that to the definitions and to the notation. So for three populations in this
 * repository **the whole defence is a person reading**, and until this file was written nothing
 * recorded whether anyone had.
 *
 * That is the gap: forty-five findings had reviewed the machinery and none had reviewed the
 * content. A register does not close it. What it does is make the reading a thing with a state:
 * every statement starts at `NOT READ` and stays there until somebody writes down that they read
 * it, when, and against which source, and nothing can leave the list by accident.
 *
 * == What this is not ==
 *
 * **Nothing here checks that an axiom, a definition or a precedence is right.** If such a check
 * were possible the square would not be unprotected and no register would be needed; a test that
 * appeared to check it would be worse than none, because it would retire the reading. The guard in
 * `RegisterSpec` checks exactly one thing: that every statement in the three populations has a row.
 * A row saying `NOT READ` is the true statement about this repository and it is the one this
 * command writes.
 *
 * It does not check the attestations either. Nobody can verify from here that a person read a line,
 * or that the source they name says what the row says. The register records a claim and puts a name
 * against it, which is what a register is for.
 *
 * == The three populations, and which one each row comes from ==
 *
 *  - **The axioms**, taken from `Chain.standard.widest.theory.axioms`, which is the whole chain and
 *    not one development. The distinction bit this project on 2026-09-11, when a spec asserted a
 *    lemma was absent by asking `Library.of(Chain.standard)` and stayed green while the lemma
 *    existed beside the chain. "Absent from this register" and "absent from the system" are two
 *    claims and only the first is made here. What makes the first worth something is the scan
 *    `RealSpec` runs over the sources for `Kernel.assertAxiom`, the one non-conservative kernel
 *    operation: outside the kernel's own file exactly three call it. So an axiom outside the
 *    chain's signature would have to come from one of three named places.
 *
 *    This paragraph named the operation by a fourteen-word periphrasis until 2026-09-12, and the
 *    reason is worth one sentence because the reason was a defect: the scan read the file whole,
 *    comments included, so naming the operation here put this file in the trusted base and turned
 *    the suite red. It strips comments now and lists the files that only discuss the rule
 *    separately from the files that use it, which is why this sentence can be written at all.
 *  - **The definitions**, taken from `Chain.standard.widest.theory.definitions`, which is every
 *    constant the chain defines: the eight connectives, the numerals, the abbreviations of the
 *    reals, and everything the developments above them introduce. A definition is conservative and
 *    adds nothing to the trusted base, and that is not the reason to read it: it decides what the
 *    axioms *mean*. `x - y` is `x + -y` because a definition says so, and an axiom about
 *    subtraction states whatever that definition makes it state.
 *  - **The notation**, taken from `Chain.standard.widest.notation`, one row per operator and one for
 *    the rule about application. `NotationRoundTripSpec` checks `parse(show(t)) == t`, which is the
 *    notation's consistency with itself and not that a reader would group an axiom string the way
 *    the parser does. An `==>` binding tighter than `/\` would pass that test and would read every
 *    conditional axiom in the repository as a different statement.
 *
 * == Where the attestations live, and why not here ==
 *
 * In `docs/reading-register-attestations.txt`, a hand-maintained side file keyed by the same key
 * the table prints, which this reads and folds into the generated table.
 *
 * The alternative was a column inside the generated block that the generator parses out of the
 * previous version of its own output and carries forward. It was rejected for one reason: the
 * generated block opens with `<!-- generated, do not edit below this line -->`, and an arrangement
 * whose only way to record a reading is to edit below that line is a document that contradicts
 * itself in the first instruction it gives. The mechanical cost is the same either way; what
 * differs is that a person adding a row to the side file is doing the documented thing, and a
 * person editing the generated table is doing the thing the marker forbids, in a block that the
 * next run of this command overwrites.
 *
 * What the side file does not cover: a key that changes spelling loses its attestation, because the
 * attestation was keyed by the old one. That is deliberate and it is the safe direction. A renamed
 * axiom is a changed axiom until somebody says otherwise, so it should go back to `NOT READ`, and
 * the orphaned line is surfaced rather than dropped: `RegisterSpec` fails on an attestation whose
 * key is in no row, naming it.
 *
 * == What it replaces, and what it leaves alone ==
 *
 * Only what lies between the two markers, on the model of [[Lemmas]], which is the shape this
 * repository already uses for a part-generated document. The splicing is written again here rather
 * than shared with that object: generalising its refusal messages, which name `docs/lemmas.md`,
 * would mean editing a file that is being extended in another worktree at the same time, and a
 * merge conflict in the one thing that decides where a generator writes over a document is a poor
 * trade for twenty lines.
 */
object Register {

  /** Where the register goes, relative to the repository root. */
  val Document: String = "docs/reading-register.md"

  /** Where the attestations are kept by hand, relative to the repository root. */
  val Attestations: String = "docs/reading-register-attestations.txt"

  /** The command that runs this, written here so that the document and the message cannot drift. */
  val Command: String = "sbt \"theories/runMain garden.xeno.symbolum.theories.Register\""

  /** The line above the generated table, in the document. */
  val Start: String = "<!-- generated, do not edit below this line -->"

  /** The line below it. */
  val End: String = "<!-- end generated -->"

  /** What a row says when nobody has attested to reading it, which is every row today. */
  val Unread: String = "NOT READ"

  /**
   * One statement a person has to read, and the key the attestation file uses for it.
   *
   * The key is spelled with spaces rather than slashes because two of the populations have
   * constants named `/\` and `\/`, and a path-shaped key holding a slash is a key nobody can read
   * back.
   */
  final case class Row(key: String, statement: String)

  /** Somebody's claim to have read one statement. */
  final case class Attestation(reader: String, when: String, source: String)

  /* --------------------------------------------------------------- the populations */

  /**
   * The name of each axiom the chain holds, by the statement it asserts.
   *
   * Built from the three developments that assert one rather than by parsing their source text,
   * because the map each of them keeps is what the kernel actually accepted, and a name taken from
   * a text that is re-parsed here would agree with the theory only as long as the parse does.
   */
  private def axiomNames(chain: Chain): Map[Term, String] =
    (chain.classical.axioms ++ chain.naturals.axioms ++ chain.reals.axioms).map {
      case (name, theorem) => theorem.conclusion -> name
    }

  /**
   * Axioms the chain holds that no development claims by name.
   *
   * The register is keyed by name, so an axiom without one cannot have a row, and dropping it
   * silently is the exact failure this file exists to prevent. It is empty and the generator
   * refuses to write while it is not.
   */
  def unnamedAxioms(chain: Chain): Vector[Term] = {
    val named = axiomNames(chain)
    chain.widest.theory.axioms.toVector.filterNot(named.contains)
  }

  /** The axioms, in the order the chain asserted them, which is the order a reader checks them in. */
  def axiomRows(chain: Chain): Vector[Row] = {
    val named = axiomNames(chain)
    chain.widest.theory.axioms.toVector.flatMap { statement =>
      named.get(statement).map(name => Row(s"axiom $name", chain.widest.show(statement)))
    }
  }

  /**
   * Every constant the chain defines, with the body that defines it, sorted by name.
   *
   * Sorted rather than in the order they were introduced, because a `Theory` holds its definitions
   * in a map and the order is gone by the time anything can read it. That is a loss: the order the
   * definitions arrive in is the order they are readable in, since each may mention the ones before
   * it. A reader working through this section looks a name up rather than reading top to bottom.
   */
  def definitionRows(chain: Chain): Vector[Row] =
    chain.widest.theory.definitions.toVector.sortBy(_._1).map { case (name, body) =>
      Row(s"definition $name", s"$name = ${chain.widest.show(body)}")
    }

  /**
   * The precedence table, one row per spelling, and one for the rule that is not in the table.
   *
   * Application is that one. It binds tighter than every declared operator, it is why `f x + 1` is
   * `(f x) + 1`, and it is a constant of the grammar rather than an entry of the notation, so a
   * register generated from the notation alone would leave the tightest binding in the language
   * unlisted.
   *
   * The structural symbols, `(`, `)`, `.`, `,`, `:` and `->`, are deliberately not rows: none of
   * them has a precedence to get wrong.
   */
  def notationRows(chain: Chain): Vector[Row] = {
    val notation = chain.widest.notation

    val infixes = notation.infix.map { operator =>
      val shape =
        if (operator.flipped) s"`x ${operator.symbol} y` is `${operator.constant} y x`"
        else s"`x ${operator.symbol} y` is `${operator.constant} x y`"
      val grouping = if (operator.rightAssociative) "right-associative" else "left-associative"
      val fixed = operator.fixedType.map(ty => s", at the fixed type `${Show.show(ty)}`").getOrElse("")
      val direction = if (operator.flipped) ", read only, never printed" else ""
      // Named by its symbol AND its constant, which is the numerals' rule two rows down applied
      // where `docs/adr/0018` made it necessary: one symbol may now stand for more than one
      // constant, so `notation infix +` is two statements and a reader cannot attest to a
      // statement that is silently two. Unconditional rather than only where a symbol is
      // overloaded, because a label that changed the day somebody overloaded its symbol would
      // carry an existing attestation over to a statement nobody had read.
      Row(
        s"notation infix ${operator.symbol} via ${operator.constant}",
        s"$shape, precedence ${operator.precedence}, $grouping$fixed$direction"
      )
    }

    val prefixes = notation.prefix.map { operator =>
      Row(
        s"notation prefix ${operator.symbol}",
        s"`${operator.symbol} x` is `${operator.constant} x`, precedence ${operator.precedence}"
      )
    }

    val binders = notation.binders.map { binder =>
      val built = binder.constant match {
        case Some(constant) => s"`${constant} (\\x. body)`"
        case None => "a lambda"
      }
      Row(
        s"notation binder ${binder.symbol}",
        s"`${binder.symbol}x. body` is $built, and the body extends as far right as it can"
      )
    }

    // Named by the encoding's `one` and not "notation numerals" flat, which is what it was until
    // 2026-09-12. There was one encoding then, so one label was one row; `num` got numerals that
    // day and two rows arrived under one name, which this document reads as one statement. A reader
    // attesting to having checked "notation numerals" would have attested to one of two spellings
    // with nothing saying which, and the other would have gone unread invisibly. `RegisterSpec`
    // counts the rows against the notation and is what caught it.
    val numerals = notation.numerals.map { spelling =>
      Row(
        s"notation numerals via ${spelling.one}",
        s"a digit string is read in binary through `${spelling.zero}`, `${spelling.one}`, " +
          s"`${spelling.bit0}` and `${spelling.bit1}`: `12` is `${spelling.bit0} (${spelling.bit0} " +
          s"(${spelling.bit1} ${spelling.one}))`"
      )
    }

    val application = Vector(
      Row(
        "notation application",
        s"`f x` binds tighter than every operator above, at precedence ${Notation.ApplicationPrecedence}"
      )
    )

    infixes ++ prefixes ++ binders ++ numerals ++ application
  }

  /** Every row of the register, which is every statement nothing but a reader checks. */
  def rows(chain: Chain): Vector[Row] =
    axiomRows(chain) ++ definitionRows(chain) ++ notationRows(chain)

  /**
   * The constants the chain declares and never defines, with their types.
   *
   * Not rows, and listed anyway. A register that printed the definitions and stopped would leave a
   * reader unable to tell a constant that has no row because nobody has to read it from one that
   * has no row because somebody forgot, and those are the two cases this closes: every constant of
   * the widest signature is either a definition above or a name here, which `RegisterSpec` asserts.
   *
   * Three kinds end up here and the reasons differ. `+`, `*`, `<`, `inv`, `neg`, `0` and `1` are
   * declared by the reals and their whole meaning is the axioms above, which are rows; `select` is
   * the same arrangement over `SELECT`. The abstraction and representation of each defined type,
   * `mk_num` and `dest_num` and their four siblings, are introduced by `Kernel.defineType` together
   * with two theorems relating them, and a theorem is proved rather than read. Equality is the
   * kernel's and is in the primitive theory before any of this starts.
   */
  def declaredConstants(chain: Chain): Vector[(String, String)] = {
    val theory = chain.widest.theory
    theory.undefinedConstants.toVector.sorted.map(name => (name, Show.show(theory.constants(name))))
  }

  /* ------------------------------------------------------------- the attestations */

  /**
   * The attestations, by key, or the first line that is not one.
   *
   * Refused rather than skipped, and by line number, because the failure mode of a tolerant parser
   * here is a reading that somebody performed and recorded and that the table then prints as
   * `NOT READ`. All four fields have to be filled: an attestation without a source is a claim that
   * the statement was read against nothing.
   */
  def attestations(text: String): Either[String, Map[String, Attestation]] = {
    val entries = text.linesIterator.zipWithIndex.toVector
      .map { case (line, index) => (line.trim, index + 1) }
      .filter { case (line, _) => line.nonEmpty && !line.startsWith("#") }

    entries.foldLeft(Right(Map.empty[String, Attestation]): Either[String, Map[String, Attestation]]) {
      case (accumulated, (line, number)) =>
        accumulated.flatMap { seen =>
          line.split("\\|", -1).map(_.trim).toVector match {
            case fields @ Vector(key, reader, when, source) if fields.forall(_.nonEmpty) =>
              if (seen.contains(key)) Left(s"$Attestations line $number: `$key` is attested twice")
              else Right(seen.updated(key, Attestation(reader, when, source)))

            case fields =>
              Left(
                s"$Attestations line $number: expected `key | read by | when | against which source`, " +
                  s"four fields all filled, and got ${fields.size}"
              )
          }
        }
    }
  }

  /**
   * Attestations whose key is in no row, which is what a rename leaves behind.
   *
   * Named rather than ignored. A line here means somebody's reading has lost the statement it was
   * about, and the two repairs, re-key it or read the new statement, are decisions for the person
   * who made the rename.
   */
  def orphaned(rows: Vector[Row], attested: Map[String, Attestation]): Vector[String] = {
    val keys = rows.map(_.key).toSet
    attested.keys.toVector.sorted.filterNot(keys.contains)
  }

  /* ------------------------------------------------------------------ the listing */

  private def table(rows: Vector[Row], attested: Map[String, Attestation]): String = {
    val head = Vector("| Key | Statement | Read by | When | Against |", "| --- | --- | --- | --- | --- |")
    val body = rows.map { row =>
      attested.get(row.key) match {
        case None => s"| `${row.key}` | ${row.statement} | **$Unread** |  |  |"
        case Some(entry) =>
          s"| `${row.key}` | ${row.statement} | ${entry.reader} | ${entry.when} | ${entry.source} |"
      }
    }
    (head ++ body).mkString("\n")
  }

  /**
   * The generated part of the document.
   *
   * The statement of an axiom is printed through the chain's widest signature rather than quoted
   * from the source text, so that what a reader checks against a textbook is what the kernel holds
   * and not what somebody typed beside it. A definition body is printed the same way.
   *
   * **One known defect shows through here and is not repaired in this file.** The printer omits the
   * type annotation on a free variable at the outermost level, and fourteen polymorphic lemmas do
   * not read back through the parser; a repair is in hand elsewhere. Nothing in the three
   * populations is affected by the first, since an axiom is closed and a definition body is closed,
   * and rows that are affected by the second are still exactly what the theory holds: this table is
   * compared as text and is never parsed back.
   */
  def listing(chain: Chain, attested: Map[String, Attestation]): String = {
    val axioms = axiomRows(chain)
    val definitions = definitionRows(chain)
    val notation = notationRows(chain)
    val declared = declaredConstants(chain)

    Vector(
      s"## The axioms (${axioms.size})",
      "",
      "In the order the chain asserts them, which is the order `Theory.axioms` reports.",
      "",
      table(axioms, attested),
      "",
      s"## The definitions (${definitions.size})",
      "",
      "Every constant the chain defines, by name. Each is conservative and each decides what an",
      "axiom mentioning it means.",
      "",
      table(definitions, attested),
      "",
      s"## The notation (${notation.size})",
      "",
      "One row per spelling the parser and the printer share, and one for application, which has a",
      "precedence and is not an entry of the table.",
      "",
      table(notation, attested),
      "",
      s"## Declared and never defined (${declared.size})",
      "",
      "Not rows, and listed so that a constant with no row is a constant somebody decided about. The",
      "seven of the reals and `select` are declared and say nothing by themselves: their whole meaning",
      "is the axioms above, which are rows. The abstraction and representation of each defined type",
      "arrive from `Kernel.defineType` with two theorems relating them, and a theorem is proved rather",
      "than read. Equality is the kernel's, and is in the theory before any of this starts.",
      "",
      declared.map { case (name, ty) => s"- `$name : $ty`" }.mkString("\n")
    ).mkString("\n")
  }

  /** The same, over the standard chain and the attestations on disk. */
  def listing(): Either[String, String] =
    for {
      text <- readAttestations()
      attested <- attestations(text)
      chain = Chain.standard
      rows = Register.rows(chain)
      _ <- refuseUnnamed(chain)
      _ <- refuseOrphaned(rows, attested)
    } yield listing(chain, attested)

  private def refuseUnnamed(chain: Chain): Either[String, Unit] = {
    val unnamed = unnamedAxioms(chain)
    if (unnamed.isEmpty) Right(())
    else
      Left(
        s"the chain holds ${unnamed.size} axiom(s) no development names, so they can have no row: " +
          unnamed.map(chain.widest.show).mkString("; ")
      )
  }

  private def refuseOrphaned(rows: Vector[Row], attested: Map[String, Attestation]): Either[String, Unit] = {
    val lost = orphaned(rows, attested)
    if (lost.isEmpty) Right(())
    else Left(s"$Attestations attests to statements that are in no row: ${lost.mkString(", ")}")
  }

  private def readAttestations(): Either[String, String] = {
    val path = Paths.get(Attestations)
    if (!Files.exists(path)) Left(s"$Attestations does not exist, and an absent file is not an empty one")
    else Right(new String(Files.readAllBytes(path), StandardCharsets.UTF_8))
  }

  /* ------------------------------------------------------------------- the writing */

  /**
   * The document with its generated part replaced, or why it could not be.
   *
   * Separated from the writing so that the guard can ask the same question without a file on disk
   * being involved. A document with no markers, or with them the wrong way round, is refused by
   * name rather than overwritten: this writes over somebody's document and the one thing it must
   * not do is guess where.
   */
  def spliced(document: String, generated: String): Either[String, String] = {
    val start = document.indexOf(Start)
    val end = document.indexOf(End)

    if (start < 0) Left(s"$Document has no `$Start` marker, and this will not guess where to write")
    else if (end < 0) Left(s"$Document has no `$End` marker, and this will not guess where to stop")
    else if (end < start) Left(s"$Document has its markers the wrong way round")
    else
      Right(
        document.substring(0, start + Start.length) + "\n\n" + generated + "\n\n" +
          document.substring(end)
      )
  }

  /** What the generated part of a document currently holds, for a caller comparing the two. */
  def generatedPartOf(document: String): Either[String, String] =
    spliced(document, "").map { _ =>
      val start = document.indexOf(Start) + Start.length
      val end = document.indexOf(End)
      document.substring(start, end).trim
    }

  def main(arguments: Array[String]): Unit = {
    val path: Path = Paths.get(if (arguments.isEmpty) Document else arguments(0))

    if (!Files.exists(path)) {
      System.err.println(s"$path does not exist; this replaces a section, it does not create a file")
      sys.exit(1)
    }

    val document = new String(Files.readAllBytes(path), StandardCharsets.UTF_8)

    listing().flatMap(generated => spliced(document, generated)) match {
      case Left(why) =>
        System.err.println(why)
        sys.exit(1)

      case Right(updated) =>
        if (updated == document) println(s"$path is already what the code says")
        else {
          Files.write(path, updated.getBytes(StandardCharsets.UTF_8))
          println(s"$path rewritten")
        }
    }
  }
}
