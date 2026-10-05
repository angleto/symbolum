package garden.xeno.symbolum.theories

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import garden.xeno.symbolum.logic.*

/**
 * The guard that keeps `docs/reading-register.md` from going quietly backwards.
 *
 * `Register` writes the register; this is the half that makes it a measurement. A new axiom, a new
 * law, a new definition or a new spelling has to appear in the document, as `NOT READ`, before this passes,
 * which is the same discipline `DocumentationSpec` applies to the kernel directory: a file landing
 * there has to be put in one of two lists deliberately or the build stops.
 *
 * == What it does not check ==
 *
 * **That any of these statements is correct.** Nothing here reads an axiom against a source and
 * nothing here could. If a test could settle that, the square would not be unprotected and the
 * register would not exist; a test that appeared to settle it would be worse than none, because a
 * green build is exactly what stops a person from doing the reading it was standing in for.
 *
 * **That an attestation is true.** A line in the side file is somebody's claim. Nothing here
 * verifies that they read the statement, or that the source they name says what the row says.
 *
 * **That the system holds no axiom outside the chain.** The population this interrogates is named
 * in each assertion below, and it is `Chain.standard.widest`. An axiom asserted over a theory built
 * outside the chain would not be in it. That gap is covered elsewhere and by a different question:
 * `RealSpec` scans the sources for `Kernel.assertAxiom` and asserts that the files calling it are
 * exactly the ones its two lists name, those asserting an axiom of their own and those asserting
 * one a caller handed them. The pair of checks is the claim; neither half is.
 *
 * The 2026-09-11 defect is why that paragraph is written out rather than assumed. A spec asserted a
 * lemma was missing by asking `Library.of(Chain.standard)`, stayed green, and the lemma had been
 * proved an hour earlier in a development beside the chain. An absence is only ever an absence from
 * some population, and a test that asserts one without naming which is a test that will one day be
 * green about the wrong thing.
 */
class RegisterSpec extends AnyFlatSpec with Matchers {

  private val chain = Chain.standard
  private val rows = Register.rows(chain)

  private def document(): String =
    new String(Files.readAllBytes(Paths.get(Register.Document)), StandardCharsets.UTF_8)

  /* ---------------------------------------------------------------- the axioms */

  "The register" should "hold every axiom the whole chain asserts, and not one development's" in {
    // The population, named: `Chain.standard.widest.theory.axioms`. `NaturalSpec` measures what
    // each configuration pays for, sixteen over the reals alone and three over the naturals alone,
    // and this is the nineteen a development holding both is asked to believe. A register built
    // over `Real.standard` would be a register of sixteen and would look complete.
    val statements = chain.widest.theory.axioms.toVector

    withClue("the chain holds an axiom no development names, so it can have no row: ") {
      Register.unnamedAxioms(chain) shouldBe empty
    }

    val listed = Register.axiomRows(chain).map(_.key)
    listed.size shouldBe statements.size

    // Spelled as the sum rather than as a number, so that an axiom added to either of the two files
    // that may assert one moves this without anybody editing it. The number it comes to is the three
    // `CLAUDE.md` describes, and the literal is here so that a change to the trusted base cannot pass
    // as a change to a sum. It was nineteen, the sixteen of the reals among them, until
    // `docs/adr/0053` proved those.
    statements.size shouldBe Classical.Axioms.size + Natural.Axioms.size
    statements.size shouldBe 3

    // The sixteen of the reals are not among them since `docs/adr/0053`: they are theorems, and they
    // are rows under `law`, which the next test holds.
    val missing = (Classical.Axioms.map(_._1) ++ Natural.Axioms.map(_._1))
      .filterNot(name => listed.contains(s"axiom $name"))
    withClue(s"asserted by a development and not in the register: ${missing.mkString(", ")}\n") {
      missing shouldBe empty
    }
  }

  /* ------------------------------------------------------------------- the laws */

  it should "hold every law of the reals, once each, and none of them as an axiom" in {
    // The population that went missing. From 2026-09-27 until 2026-10-05 the sixteen had no row:
    // the axioms are read off `theory.axioms`, a theorem is not there, and the comment above said
    // their reading was the seven primitives' definitions. Those say `real_add` is `CUT_ADD`, which
    // is not a statement about what a complete ordered field is, and that is the one question about
    // the sixteen no derivation answers. Seen red on 2026-10-05 with the population emptied, naming
    // all sixteen: `tools/verify/perturb-register-laws.sh`.
    val listed = Register.lawRows(chain).map(_.key)

    val missing = Real.Laws.map(_._1).filterNot(name => listed.contains(s"law $name"))
    withClue(s"a law of the reals not in the register: ${missing.mkString(", ")}\n") {
      missing shouldBe empty
    }

    // Read from the declaration rather than from the map it collapses into, so that a name written
    // twice in `Real.Laws` shows up here instead of disappearing into one key.
    listed.distinct.size shouldBe listed.size
    listed.size shouldBe Real.Laws.size
    listed.size shouldBe chain.reals.laws.size

    // The literal, for the same reason the axioms carry one: an interface that lost a law would
    // otherwise pass as a smaller sum.
    listed.size shouldBe 16

    // A law is a theorem, and the register does not count one as believed.
    val asserted = chain.widest.theory.axioms.toSet
    Real.Laws.map(_._1).filter(name => asserted.contains(chain.reals.laws(name).conclusion)) shouldBe empty
  }

  /* ------------------------------------------------------------ the definitions */

  it should "hold every constant the chain defines" in {
    // The other thing a reader has to check and nothing else does. A definition adds nothing to the
    // trusted base and decides what every axiom mentioning it means, which is why it is in the same
    // document as the axioms rather than in a lesser one.
    val defined = chain.widest.theory.definitions.keys.toVector.sorted
    val listed = Register.definitionRows(chain).map(_.key).toSet

    val missing = defined.filterNot(name => listed.contains(s"definition $name"))
    withClue(s"defined by the chain and not in the register: ${missing.mkString(", ")}\n") {
      missing shouldBe empty
    }

    listed.size shouldBe defined.size
  }

  it should "account for every constant of the signature, defined or not" in {
    // The closure that makes the section above readable as an absence. Without it, a constant with
    // no row could be one nobody has to read or one that fell through, and the document gives a
    // reader no way to tell which. Every constant the widest signature declares is either a
    // definition row or a name in the declared list, and the second carries the reason it is not a
    // row: a declaration says nothing, and what it means is an axiom that is a row or a theorem
    // that was proved.
    val constants = chain.widest.theory.constants.keys.toVector.sorted
    val defined = chain.widest.theory.definitions.keys.toSet
    val declared = Register.declaredConstants(chain).map(_._1).toSet

    val unaccounted = constants.filterNot(name => defined.contains(name) || declared.contains(name))
    withClue(s"in the signature and in neither list: ${unaccounted.mkString(", ")}\n") {
      unaccounted shouldBe empty
    }

    // Disjoint as well as covering, so that a constant cannot be counted in both and look accounted
    // for twice.
    defined.intersect(declared) shouldBe empty
    defined.size + declared.size shouldBe constants.size
  }

  /* --------------------------------------------------------------- the notation */

  it should "hold every spelling the parser and the printer share" in {
    // Including the flipped ones. `>` and `>=` are read and never printed, so a reader who never
    // sees one in a printed statement can still write one in a goal, and what it means is decided
    // by a row of this table like everything else.
    val notation = chain.widest.notation
    val listed = Register.notationRows(chain).map(_.key).toSet

    // `via ${constant}` since `docs/adr/0018`: one symbol may stand for more than one constant,
    // so the key that used to be the symbol alone is now two statements under one name. The
    // numerals' row three lines down has carried its own discriminator since the day `num` got
    // numerals, and this is the same fix arriving at the operators.
    notation.infix.foreach(operator =>
      listed should contain(s"notation infix ${operator.symbol} via ${operator.constant}"))
    notation.prefix.foreach(operator => listed should contain(s"notation prefix ${operator.symbol}"))
    notation.binders.foreach(binder => listed should contain(s"notation binder ${binder.symbol}"))
    // One row per encoding, named by its `one`. A single flat "notation numerals" label put two
    // spellings under one statement on the day `num` got numerals, and the count below is what said
    // so: a reader cannot attest to a statement that is silently two.
    notation.numerals.foreach(spelling =>
      listed should contain(s"notation numerals via ${spelling.one}"))
    notation.numerals.map(_.one).distinct.size shouldBe notation.numerals.size

    // Application is not an entry of the notation and has a precedence, so a register generated
    // from the notation alone would leave the tightest binding in the language off the list.
    listed should contain("notation application")

    listed.size shouldBe
      notation.infix.size + notation.prefix.size + notation.binders.size + notation.numerals.size + 1
  }

  /* ------------------------------------------------- the document, against the code */

  "docs/reading-register.md" should "be what the command produces, not something that resembles it" in {
    // The assertion that makes the three above bite. A statement added anywhere in the chain
    // changes the generated text and this goes red naming the command, which is the thing whoever
    // added it needs to know at the moment they need it.
    val generated = Register.generatedPartOf(document()).fold(why => fail(why), identity)
    val expected = Register.listing().fold(why => fail(why), identity)

    withClue(s"${Register.Document} is not what the code says; run:\n  ${Register.Command}\n") {
      generated shouldBe expected.trim
    }
  }

  it should "carry a row for every statement, and say of each whether anybody has read it" in {
    val generated = Register.generatedPartOf(document()).fold(why => fail(why), identity)

    // The keys and not the document. `should include` on a page of markdown prints the page when it
    // fails, and a failure nobody can read is one somebody reruns with a narrower command instead of
    // acting on.
    val missing = rows.map(_.key).filterNot(key => generated.contains(s"`$key`"))
    withClue(s"in the chain and not in ${Register.Document}: ${missing.mkString(", ")}\n") {
      missing shouldBe empty
    }

    rows.size shouldBe
      Register.axiomRows(chain).size + Register.lawRows(chain).size +
        Register.definitionRows(chain).size + Register.notationRows(chain).size
  }

  /* ------------------------------------------------------------ the attestations */

  "An attestation" should "survive the regeneration that rewrites the table around it" in {
    // The whole reason the attestations are a side file rather than a column somebody edits inside
    // a block marked "do not edit below this line". Generated twice with one reading recorded: the
    // statement is printed from the code and the reading is printed from the file, and neither has
    // to know about the other.
    val reading = Register.Attestation("A Reader", "2026-01-01", "Some Book, 2nd ed., section 4")
    val key = "axiom SELECT"
    rows.map(_.key) should contain(key)

    val listing = Register.listing(chain, Map(key -> reading))
    listing.linesIterator.find(_.startsWith(s"| `$key` |")) shouldBe
      Some(s"| `$key` | !f:'a -> bool. !x:'a. f x ==> f (select f) | A Reader | 2026-01-01 | Some Book, 2nd ed., section 4 |")

    // And every other row is untouched by it.
    val unread = Register.listing(chain, Map.empty)
    unread.linesIterator.count(_.contains("A Reader")) shouldBe 0
    unread.linesIterator.count(_.contains(Register.Unread)) shouldBe rows.size
  }

  it should "be refused by line number when it is not one, rather than printed as unread" in {
    // A tolerant parser here fails in the direction that costs the most: somebody does the reading,
    // records it in a line with a field missing, and the table goes on saying NOT READ.
    Register.attestations("# a comment\n\n  \n") shouldBe Right(Map.empty)

    Register.attestations("a | b | c").left.map(_.contains("line 1")) shouldBe Left(true)
    Register.attestations("a | b | c").left.map(_.contains("got 3")) shouldBe Left(true)
    Register.attestations("# c\na | b |  | d").left.map(_.contains("line 2")) shouldBe Left(true)
    Register
      .attestations("a | b | c | d\na | e | f | g")
      .left
      .map(_.contains("attested twice")) shouldBe Left(true)

    Register.attestations("k | who | when | where") shouldBe
      Right(Map("k" -> Register.Attestation("who", "when", "where")))
  }

  it should "be named rather than dropped when the statement it was about is gone" in {
    // The failure a rename produces. The attestation goes back to NOT READ, which is the safe
    // direction, and the line that lost its statement is surfaced so that whoever made the rename
    // decides: re-key it, or read the new statement.
    val stale = Register.Attestation("A Reader", "2026-01-01", "Some Book")
    Register.orphaned(rows, Map("axiom NO_SUCH_AXIOM" -> stale)) shouldBe Vector("axiom NO_SUCH_AXIOM")
    Register.orphaned(rows, Map("axiom SELECT" -> stale)) shouldBe empty
  }

  it should "be on disk in a file that exists, since an absent file is not an empty one" in {
    Files.exists(Paths.get(Register.Attestations)) shouldBe true
    Register.attestations(
      new String(Files.readAllBytes(Paths.get(Register.Attestations)), StandardCharsets.UTF_8)
    ).isRight shouldBe true
  }

  /* ------------------------------------------------------------------ the markers */

  "The generator" should "be refused rather than guess where to write when the markers are not there" in {
    // It writes over somebody's document and the one thing it must not do is decide for itself
    // where the generated part begins. Each refusal names which marker was the problem, because a
    // document missing the closing one and a document missing the opening one are repaired
    // differently.
    Register.spliced("no markers here", "x").left.map(_.contains("no `")) shouldBe Left(true)
    Register.spliced(s"${Register.Start}\nbody", "x").left.map(_.contains(Register.End)) shouldBe Left(true)
    Register
      .spliced(s"${Register.End}\nbody\n${Register.Start}", "x")
      .left
      .map(_.contains("wrong way round")) shouldBe Left(true)

    Register.spliced(s"head\n${Register.Start}\nold\n${Register.End}\ntail", "new") shouldBe
      Right(s"head\n${Register.Start}\n\nnew\n\n${Register.End}\ntail")

    Register.generatedPartOf(s"head\n${Register.Start}\n\nold\n\n${Register.End}\ntail") shouldBe Right("old")
    Register.generatedPartOf("nothing").isLeft shouldBe true
  }
}
