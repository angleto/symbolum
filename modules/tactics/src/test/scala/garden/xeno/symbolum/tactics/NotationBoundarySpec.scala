package garden.xeno.symbolum.tactics

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Which refusals write a term into their own prose, as a census rather than as a habit.
 *
 * A `LogicError` carries values and the surface renders them, which is the rule
 * `LogicError.NotEqualTo` states in its own words: only the caller knows which notation its reader
 * is using. Several cases also carry a `String`, and a `String` is where that rule is bypassed
 * without anybody noticing, because the field's type says nothing about it. `Propositional` is in
 * `modules/logic`, which knows no notation at all, and it rendered the falsifying atoms itself with
 * the kernel's printer: somebody who asked about `x = 99` was shown
 * `(x = (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 1)))))))`. That site is repaired, and this file exists
 * rather than only the fix because it was the second such repair asked for in one day.
 *
 * == The two assertions, and why one of them is worth much more than the other ==
 *
 * The first is exact and has no reading behind it: **nothing above `modules/kernel` may name
 * `Printer`**. The kernel's printer knows no theory and cannot be given one, so a term it renders
 * reaches a reader in the encoding rather than in the notation they wrote. Measured on 2026-09-15,
 * there was exactly one reference to it above the kernel in the whole tree, and it was this defect.
 * Zero is therefore an equality rather than a floor.
 *
 * It is stated over the file rather than over the prose field on purpose, and that is the
 * correction this file needed after its first version ran. Written as "no prose field may contain
 * `Printer.show`" it passed on the very site it was written for, because the call was one level
 * down in a private helper and the prose interpolated the helper. An assertion that cannot see a
 * function call is not an assertion about what a program does.
 *
 * The second is [[Classified]], and it is a **reading** written down. It catches what the first
 * cannot -- `reals.show` at the point of refusal, and a bare `$term` paying `toString` -- and it is
 * worth what the readings in it are worth. Its entries are what the census found, one line each.
 *
 * == The four things the scan cannot do ==
 *
 *   1. **It is syntactic, not typed.** It can say a prose field is not a string literal; it cannot
 *      say that what is interpolated is a `Term`. There is no `semanticdb` in this build, which is
 *      what would make that half mechanical, so it is [[Classified]] instead and a wrong entry
 *      there is caught by nothing.
 *   2. **Prose built in a helper is invisible to it.** `LinearForm.obstacleIn` returns an
 *      `Option[String]` already rendered through `reals.show`, and the two sites that raise it
 *      interpolate `$obstacle` and `$named`. The scan sees an identifier. Both are recorded below
 *      as what they are, and the first assertion is what covers this class in the one place it can.
 *   3. **It reads construction sites, not messages.** Every case's own `message` interpolates its
 *      terms, deliberately: that is the last-resort rendering for a caller with no theory, which is
 *      what `Remedy.write` falls back to. The defect is prose frozen where the refusal is raised,
 *      after which the values are gone and no surface can render them.
 *   4. **A `Type` in prose is not a crossing.** A type has exactly one rendering:
 *      `Show.show(ty: Type)` takes no notation, and `Remedy` writes types that way at its own
 *      surface with no theory in hand. So the question this census was asked, "a `Term` or a
 *      `Type`", has two different answers, and six sites that look like crossings are not.
 *
 * == Why the table is keyed by file and expression ==
 *
 * By expression alone it would be wrong: `left` is a `BigInt` in `Order.scala` and a `Term` in
 * `Limit.scala`, and one entry would let the other through. By file and line it would churn on
 * every edit above it, and it did: the repair this file ships with moves two lines of
 * `Propositional.scala` up by one. File and expression survives a line moving and still separates
 * the two meanings of a common name.
 */
class NotationBoundarySpec extends AnyFlatSpec with Matchers {

  /**
   * Every module with sources, read off the filesystem rather than written out.
   *
   * It was written out until 2026-09-15 and named nine of the ten that have a `src/main`. Both
   * conclusions below survived the omission, because the module left out holds no `LogicError` and
   * no `Printer` at all -- which is exactly why nobody would have noticed: a scan that skips a
   * directory with nothing in it returns the same answer as a scan that reads it, and goes on
   * returning it after somebody puts something there. The one missed was `dist`, whose single file
   * is the distribution's REPL, a surface a reader actually types at and the likeliest place for
   * the next term rendered where the refusal is raised.
   *
   * A hand-written list is the defect this whole file is about wearing different clothes: a census
   * keyed on a spelling of the population rather than on the population.
   */
  private def moduleRoots: Vector[Path] = {
    val modules = Paths.get("modules")
    val stream = Files.list(modules)
    try
      stream
        .iterator()
        .asScala
        .toVector
        .map(_.resolve("src/main"))
        .filter(Files.isDirectory(_))
        .sortBy(_.toString)
    finally stream.close()
  }

  /**
   * The prose field of each refusal that has one, by its position in the constructor.
   *
   * Five of the nine hold the **name** of something in the code, which their own declarations say:
   * `MissingDefinition.name` is a constant, `BoundReached.limit` names the constant that stopped
   * the search, and `NoCloser.driver`, `MissingHypothesis.rule` and `DoesNotFollow.procedure` name
   * the code that refused. The four that are free descriptions are where a term can land, and they
   * are what [[Classified]] covers. The other five are scanned too, because the first assertion is
   * about a file and does not care which field a rendering reached.
   */
  private val ProseField: Map[String, Int] = Map(
    "NotOfForm" -> 0,
    "DoesNotFollow" -> 1,
    "BoundReached" -> 0,
    "SyntaxError" -> 0,
    "TypeError" -> 0,
    "MissingDefinition" -> 0,
    "EscapingVariable" -> 1,
    "MissingHypothesis" -> 1,
    "NoCloser" -> 1
  )

  /** The four whose field is a description of a shape rather than the name of something. */
  private val Describes = Set("NotOfForm", "SyntaxError", "TypeError", "EscapingVariable")

  /** What a thing interpolated into a description turns out to be. */
  private enum Verdict {

    /** A name of something in the code: a constant, a limit, a procedure, a variable. */
    case Name

    /** A count or a numeral, arriving as a number rather than as a term. */
    case Number

    /** Text: the claim's own source, or another refusal's message passed through unchanged. */
    case Text

    /**
     * A `Type`, which is not a crossing.
     *
     * A type has one rendering and no notation chooses it. `Remedy` writes `Show.show(declared)` at
     * its own surface with no theory in hand, so nothing a reader could have chosen differently is
     * decided by writing one here.
     */
    case TypeOnly

    /**
     * A `Term`, rendered where the refusal is raised and the reader's notation is not known.
     *
     * Debt on the record. Every one of them is repaired the same way and `SkeletonFailsAt` is the
     * first: the refusal carries the term and the surface renders it.
     */
    case Crossing
  }

  /**
   * Every expression the scan finds in a description field, with what it is.
   *
   * An entry the scan no longer finds fails as loudly as a site the table does not hold. The two
   * are one obligation seen from its two sides, and without the second a table nobody prunes stops
   * being readable and then stops being read.
   */
  private val Classified: Map[(String, String), (Verdict, String)] = Map(
    ("Bounded.scala", "Natural.TypeName") -> (Verdict.Name, "the name of the type num"),
    ("Bounded.scala", "index.name") -> (Verdict.Name, "the bound variable's name"),
    ("Bounded.scala", "position") -> (Verdict.Number, "which instance of the walk"),
    ("Classical.scala", "variable.name") -> (Verdict.Name, "the variable's name"),
    ("Coding.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Coefficient.scala", "reals.show(rule.lhs)") ->
      (Verdict.Crossing, "a rewrite rule's left side, in the raiser's notation and not the reader's"),
    ("Collatz.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "MarkedClosed") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "StepInhabited") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "entry.label") ->
      (Verdict.Name, "a rule's name in the source that owns it, R1 or A3 or B2"),
    ("Collatz.scala", "label") ->
      (Verdict.Name, "a rule's name in the source that owns it, asked for rather than read off"),
    ("Collatz.scala", "FamilyWithTail") -> (Verdict.Name, "the lemma's published name"),
    // The rows that landed with the measure, the class it holds on and the instantiation. Most are
    // the same reading as the three above them, a published name compared against what came out of
    // the derivation; `Natural.TypeName` is the name of the type `num`, which is the reading
    // `Bounded.scala` already carries for the same expression, and `expected` is a count.
    //
    // A ninth site arrived with them and is not here, deliberately. It passed a description built
    // from a boolean, which this table has no reading for and which the `Unrendered` table below
    // has none for either, so the refusal was rewritten as two refusals with a literal each.
    ("Collatz.scala", "AnchoredClosed") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "PotentialCountedStep") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "PotentialPlainStep") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "RunPotential") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "RunInhabited") -> (Verdict.Name, "the lemma's published name"),
    // The four that landed with the family's closed form and its quadratic bound, and they are the
    // block above's reading again: each site writes `s"$Name as it is written"` and compares a
    // published name against the conclusion the derivation produced.
    ("Collatz.scala", "StemLength") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "PotentialOfFamily") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "FamilyAtOne") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "FamilyBounded") -> (Verdict.Name, "the lemma's published name"),
    ("Collatz.scala", "Natural.TypeName") -> (Verdict.Name, "the name of the type num"),
    ("Collatz.scala", "expected") ->
      (Verdict.Number, "how many clauses the disjunction being walked was expected to have"),
    ("Collatz.scala", "other.size") ->
      (Verdict.Number, "how many witnesses an existential nest opened, where the shape expected four"),
    ("Collatz.scala", "Rules.size") -> (Verdict.Number, "how many rules the table holds"),
    ("Collatz.scala", "position") -> (Verdict.Number, "which letter of a written-out word"),
    ("Collatz.scala", "lower") -> (Verdict.Number, "the smaller of two positions being compared"),
    ("Collatz.scala", "size") -> (Verdict.Number, "how many letters the word has"),
    ("Collatz.scala", "letters.size") -> (Verdict.Number, "how many letters the word has"),
    ("Collatz.scala", "letters.size - 1") ->
      (Verdict.Number, "the last position of a written-out word"),
    ("Deduction.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    // The four `Domain.scala` sites landed with `docs/adr/0028` and are the interpretation's two
    // refusals. None is a crossing: a domain's own name and a constant's name are names, the joined
    // list is names, and a `Type` has one rendering that no notation chooses, which is what
    // `TypeOnly` says about `Remedy` further down.
    ("Domain.scala", "domain.name") -> (Verdict.Name, "the domain's own name, as its description gives it"),
    ("Domain.scala", "(strangeTypes ++ strangeConstants).toVector.sorted.mkString(\", \")") ->
      (Verdict.Name, "the names an interpretation gave a meaning to that the domain does not declare"),
    ("Domain.scala", "name") -> (Verdict.Name, "the interpreted constant's own name"),
    ("Domain.scala", "answered") ->
      (Verdict.TypeOnly, "what an interpreted constant answers, where a proposition was wanted"),
    ("Digits.scala", "value") ->
      (Verdict.Number, "the value asked for, which is not a numeral of `num` when it is negative"),
    ("Digits.scala", "leftCore._2") ->
      (Verdict.Number, "how many successors one side of a numeral lemma lifted out"),
    ("Digits.scala", "rightCore._2") ->
      (Verdict.Number, "the same for the other side, which has to be the same number"),
    ("Digits.scala", "left") ->
      (Verdict.Number, "the value asked to be below the other, when it is not"),
    ("Digits.scala", "right") ->
      (Verdict.Number, "the value it was asked to be below"),
    ("Prove.scala", "reals.show(computed.conclusion)") ->
      (Verdict.Crossing,
        "the equation the constant actually evaluates to, rendered where the refusal is raised; " +
          "this prover's signature IS the one the goal was read in, so the notation is right, and " +
          "it is on this list because the repair every crossing gets applies here too -- a refusal " +
          "that carried the theorem would let the surface render it and would let a caller read the " +
          "value as a term rather than out of a sentence"),
    ("Value.scala", "constant") ->
      (Verdict.Name, "the constant a caller asked for a value of"),
    ("Value.scala", "reachable.mkString(\", \")") ->
      (Verdict.Name, "the constants the table does have a row for, which is what the caller wanted"),
    ("Value.scala", "route.arity") ->
      (Verdict.Number, "how many arguments the constant takes"),
    // `supplied` and not `arguments.size`, since 2026-09-18: the two refusals about a missing row
    // and a wrong arity are written once now and reached from both callers, so the count arrives as
    // a parameter. `given` would have been the natural name and is a reserved word in Scala 3.
    ("Value.scala", "supplied") ->
      (Verdict.Number, "how many arguments the constant was given"),
    ("Value.scala", "divisor") ->
      (Verdict.Number, "the value asked to divide the other"),
    ("Value.scala", "multiple") ->
      (Verdict.Number, "the value it does not divide"),
    ("Value.scala", "left") -> (Verdict.Number, "the left argument of a Bezout combination"),
    ("Value.scala", "right") -> (Verdict.Number, "the right argument of one"),
    ("Value.scala", "answer") -> (Verdict.Number, "the greatest common divisor it is a combination for"),
    ("Value.scala", "bound") -> (Verdict.Number, "how many multipliers were tried before giving up"),
    ("Value.scala", "numerator") ->
      (Verdict.Number, "the numerator of the rational a floor was asked about"),
    ("Value.scala", "denominator") ->
      (Verdict.Number, "its denominator, which has to be positive"),
    ("Divisibility.scala", "parts._1") ->
      (Verdict.Crossing, "the antecedent of an implication an assembly had to match"),
    ("Field.scala", "reals.show(denominator)") ->
      (Verdict.Crossing, "a denominator, in the raiser's notation"),
    ("Forward.scala", "target") ->
      (Verdict.Crossing, "the operator's own clause, in the building notation and not a reader's"),
    ("Language.scala", "Axioms(which)._1") -> (Verdict.Name, "an axiom's published name"),
    ("Language.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Language.scala", "payload") -> (Verdict.Crossing, "a code's payload, which is a term"),
    ("Limit.scala", "Show.show(notation, target)") ->
      (Verdict.Crossing, "the goal, rendered at the raiser against a notation it chose itself"),
    ("Limit.scala", "left") -> (Verdict.Crossing, "the term a congruence was to replace"),
    ("Linarith.scala", "LinearForm.factorsOf(atom).length") ->
      (Verdict.Number, "how many unknowns a product has"),
    ("Linarith.scala", "named") ->
      (Verdict.Crossing, "a sentence LinearForm.obstacleIn has already rendered through reals.show"),
    ("Linarith.scala", "reals.show(atom)") ->
      (Verdict.Crossing, "an atom, in the raiser's notation"),
    ("Linarith.scala", "reals.show(unread)") ->
      (Verdict.Crossing, "a hypothesis, in the raiser's notation"),
    ("Logic.scala", "missing.keys.mkString(\", \")") ->
      (Verdict.Name, "the constants a theory does not declare, by name"),
    ("Magnitude.scala", "Classical.Select") -> (Verdict.Name, "the choice constant's name"),
    ("Magnitude.scala", "MaxName") -> (Verdict.Name, "the constant this file would declare"),
    ("Matrix.scala", "Constructor") -> (Verdict.Name, "the constructor constant's name"),
    ("Matrix.scala", "expected") -> (Verdict.Crossing, "the entry an assembled law was to reach"),
    ("Matrix.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Matrix.scala", "other.size") -> (Verdict.Number, "how many component equations arrived"),
    ("Modular.scala", "fallback") -> (Verdict.Crossing, "the disjunct an assembly was to reach"),
    ("Modular.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Modular.scala", "parts._1") -> (Verdict.Crossing, "the antecedent of an implication"),
    ("Modular.scala", "wanted") -> (Verdict.Crossing, "the equation an assembly was to reach"),
    ("Numbering.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Numeral.scala", "value") -> (Verdict.Number, "the numeral asked for, as a BigInt"),
    ("Order.scala", "left") ->
      (Verdict.Number, "a BigInt: the signature is less(left: BigInt, right: BigInt)"),
    ("Parser.scala", "Show.show(a)") -> (Verdict.TypeOnly, "a type in a unification failure"),
    ("Parser.scala", "Show.show(b)") -> (Verdict.TypeOnly, "the other type in the same failure"),
    ("Parser.scala", "Show.show(ty)") ->
      (Verdict.TypeOnly, "a type with no numerals at it, and an occurs check"),
    ("Parser.scala", "if (undetermined.size == 1) \"\" else \"s\"") -> (Verdict.Text, "a plural"),
    ("Parser.scala", "name") -> (Verdict.Name, "a constant the theory does not declare"),
    // Both from `docs/adr/0018`: a symbol may stand for more than one constant, and when the type
    // settles at none of them or at nothing, the refusal names the symbol. It is the symbol as
    // written in the claim, which is a spelling of the reader's own notation rather than a term
    // crossing a boundary, so it is a `Name` for the same reason the constant above is.
    ("Parser.scala", "symbol") -> (Verdict.Name, "the operator symbol a claim was written with"),
    ("Parser.scala", "notation.numerals.map(_.one).mkString(\" and no \")") ->
      (Verdict.Name, "the names of the numeral encodings this theory has"),
    ("Parser.scala", "open.mkString(\", \")") ->
      (Verdict.Name, "the names whose type is still undetermined"),
    ("Parser.scala", "text") ->
      (Verdict.Text, "the token the reader expected, from the claim's own text"),
    ("Parser.scala", "text(index)") -> (Verdict.Text, "the character the lexer stopped at"),
    ("Parser.scala", "undetermined.size") -> (Verdict.Number, "how many types are still open"),
    ("Parser.scala", "value") -> (Verdict.Number, "the numeral whose type is undetermined"),
    ("Peano.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Peano.scala", "AddMonotoneBoth") -> (Verdict.Name, "the lemma's published name"),
    ("Polynomial.scala", "reals.show(rule.lhs)") ->
      (Verdict.Crossing, "a rewrite rule's left side, in the raiser's notation"),
    ("Primes.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Product.scala", "chosenType") -> (Verdict.TypeOnly, "the type a choice was made at"),
    ("Product.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Provability.scala", "StepShift") -> (Verdict.Name, "the lemma's published name"),
    ("Provability.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Provability.scala", "statementName") -> (Verdict.Name, "the lemma's published name"),
    ("Prove.scala", "obstacle") ->
      (Verdict.Crossing, "a sentence LinearForm.obstacleIn has already rendered through reals.show"),
    ("Provenance.scala", "text") -> (Verdict.Text, "an assumption's own text, cited twice"),
    ("Quotient.scala", "what") ->
      (Verdict.Text, "which of the equivalence's three theorems was wanted, from a literal here"),
    ("Rules.scala", "body") -> (Verdict.Crossing, "the pattern a target failed to match"),
    ("Rules.scala", "domain") -> (Verdict.TypeOnly, "the type an existential ranges over"),
    ("Rules.scala", "leftCase.conclusion") ->
      (Verdict.Crossing, "the conclusion the other case of a split reached"),
    ("Rules.scala", "proposition") -> (Verdict.Crossing, "what a negation negates"),
    ("Rules.scala", "reduced") ->
      (Verdict.Crossing, "a beta-reduced application the caller's theorem had to match"),
    ("Semiring.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    ("Successor.scala", "Natural.TypeName") -> (Verdict.Name, "the name of the type num"),
    ("Successor.scala", "leftValue") -> (Verdict.Number, "a numeral's value, as a BigInt"),
    ("Transcendental.scala", "left") -> (Verdict.Crossing, "the term a congruence was to replace"),
    ("Word.scala", "name") -> (Verdict.Name, "the lemma's published name"),
    // The same site as the line above, in the development that joined the chain on 2026-09-16:
    // every published fact is compared against its written text before the development is handed
    // out, and the refusal names which one did not match.
    ("Concatenation.scala", "name") -> (Verdict.Name, "the lemma's published name")
  )

  /**
   * A description that interpolates nothing and is still not a literal.
   *
   * A bare identifier or a concatenation. Three of the four pass another refusal's own message
   * straight through, which is the laundering the scan cannot see into: whatever that message
   * rendered is what arrives. They are listed because a list of what a scan cannot decide is the
   * only honest form the undecided can take.
   */
  private val Unrendered: Map[(String, String), (Verdict, String)] = Map(
    ("Propositional.scala", "why") ->
      (Verdict.Text, "Verdict.Undecided's and Verdict.Refused's own sentences, passed through"),
    ("Prove.scala", "why") -> (Verdict.Text, "Address.Nobody's own sentence, passed through"),
    ("Language.scala", "what") ->
      (Verdict.Text, "a caller's own description of the shape it wanted"),
    // The sentence this replaced was a literal interpolating `scheme.binders.size`, and it had a
    // row in `Classified` until `Prose.count` arrived in it on 2026-09-18: the call does not fit
    // the line, so the description is a name now and the scan sees an identifier. That is the
    // class this table exists for, and what is named here is what the name holds.
    ("Language.scala", "wanted") ->
      (Verdict.Text, "a sentence built here from a literal and a count of the scheme's binders"),
    ("Quotient.scala", "what") ->
      (Verdict.Text, "which of the equivalence's three theorems was wanted, from a literal here"),
    ("Language.scala", "s\"two branches that differ only by the function\"") ->
      (Verdict.Text, "a constant sentence written with an interpolator it does not use")
  )

  /* ------------------------------------------------------------------- the scanner */

  /**
   * The index just past the string literal opening at `from`.
   *
   * Interpolation is why this is not a loop looking for the next quote, and the first version of
   * this file was that loop. `s"... ${xs.mkString(", ")}"` holds a quote and a comma inside the
   * interpolation; a scanner that ends the string at the inner quote leaves that comma at depth
   * zero and splits the argument list on it. Four sites in this tree are shaped that way and one of
   * them came out truncated. It was found by putting the extracted table beside a second pass, not
   * by reading the scanner again.
   */
  private def stringEnd(text: String, from: Int): Int =
    if (text.startsWith("\"\"\"", from)) {
      val close = text.indexOf("\"\"\"", from + 3)
      if (close < 0) text.length else close + 3
    } else {
      def walk(at: Int): Int =
        if (at >= text.length) text.length
        else if (text.charAt(at) == '\\') walk(at + 2)
        else if (text.charAt(at) == '$' && at + 1 < text.length && text.charAt(at + 1) == '{')
          walk(braceEnd(text, at + 1))
        else if (text.charAt(at) == '"') at + 1
        else walk(at + 1)
      walk(from + 1)
    }

  /** The index just past the brace group opening at `from`, skipping the strings inside it. */
  private def braceEnd(text: String, from: Int): Int = {
    def walk(at: Int, depth: Int): Int =
      if (at >= text.length) text.length
      else
        text.charAt(at) match {
          case '"' => walk(stringEnd(text, at), depth)
          case '{' => walk(at + 1, depth + 1)
          case '}' if depth == 1 => at + 1
          case '}' => walk(at + 1, depth - 1)
          case _ => walk(at + 1, depth)
        }
    walk(from, 0)
  }

  /** The same text with every string literal blanked, so what is left is only code. */
  private def blanked(text: String): String = {
    val out = text.toCharArray
    def walk(at: Int): Unit =
      if (at < text.length) {
        if (text.charAt(at) == '"') {
          val stop = stringEnd(text, at)
          (at until stop).foreach(out(_) = ' ')
          walk(stop)
        } else walk(at + 1)
      }
    walk(0)
    new String(out)
  }

  /** The argument list of the application whose `(` is at `open`, split where the compiler would. */
  private def arguments(source: String, open: Int): Option[Vector[String]] = {
    val mask = blanked(source)
    def close(at: Int, depth: Int): Int =
      if (at >= mask.length) -1
      else
        mask.charAt(at) match {
          case '(' => close(at + 1, depth + 1)
          case ')' if depth == 1 => at
          case ')' => close(at + 1, depth - 1)
          case _ => close(at + 1, depth)
        }

    val shut = close(open, 0)
    if (shut < 0) None
    else {
      val inside = source.substring(open + 1, shut)
      val cuts = blanked(inside).zipWithIndex
        .foldLeft((Vector.empty[Int], 0)) { case ((at, depth), (char, index)) =>
          char match {
            case '(' | '[' | '{' => (at, depth + 1)
            case ')' | ']' | '}' => (at, depth - 1)
            case ',' if depth == 0 => (at :+ index, depth)
            case _ => (at, depth)
          }
        }
        ._1
      Some(((-1 +: cuts) :+ inside.length).sliding(2).toVector.map {
        case Vector(from, to) => inside.substring(from + 1, to)
        case _ => ""
      })
    }
  }

  /** Every `$x` and `${ ... }` in a description, the second by matching braces rather than a regex. */
  private def expressionsIn(prose: String): Vector[String] = {
    val identifier = """[A-Za-z_][A-Za-z0-9_]*""".r
    def walk(at: Int, found: Vector[String]): Vector[String] =
      if (at >= prose.length - 1) found
      else if (prose.charAt(at) != '$') walk(at + 1, found)
      else if (prose.charAt(at + 1) == '{') {
        val stop = braceEnd(prose, at + 1)
        walk(stop, found :+ prose.substring(at + 2, stop - 1).trim)
      } else
        identifier.findPrefixOf(prose.substring(at + 1)) match {
          case Some(name) => walk(at + 1 + name.length, found :+ name)
          case None => walk(at + 1, found)
        }
    walk(0, Vector.empty)
  }

  private final case class Site(file: String, line: Int, refusal: String, prose: String) {
    def describes: Boolean = Describes.contains(refusal)
    def literal: Boolean = prose.matches("\"(?:[^\"\\\\]|\\\\.)*\"")
    def at: String = s"$file:$line ($refusal)"
  }

  private def sitesIn(path: Path): Vector[Site] = {
    val source = Files.readString(path)
    val mask = blanked(source)
    val newlines = mask.zipWithIndex.collect { case ('\n', index) => index }.toVector

    ProseField.toVector.flatMap { case (refusal, field) =>
      s"""\\b$refusal\\s*\\(""".r
        .findAllMatchIn(mask)
        .filterNot(found =>
          """\bcase\s+$""".r.findFirstIn(mask.substring(math.max(0, found.start - 10), found.start)).isDefined
        )
        .flatMap { found =>
          arguments(source, found.end - 1)
            .filter(_.length > field)
            .map(args =>
              Site(
                path.getFileName.toString,
                newlines.count(_ < found.start) + 1,
                refusal,
                args(field).trim.replaceAll("\\s+", " ")
              )
            )
        }
        .toVector
    }
  }

  private def mainSources(root: Path): Vector[Path] = {
    val stream = Files.walk(root)
    try stream.iterator().asScala.toVector.filter(_.toString.endsWith(".scala"))
    finally stream.close()
  }

  private lazy val sources: Vector[Path] = moduleRoots.flatMap(mainSources)

  private lazy val sites: Vector[Site] =
    sources.filterNot(_.getFileName.toString == "LogicError.scala").flatMap(sitesIn)

  /** The description fields whose prose is not a plain literal: what [[Classified]] is about. */
  private lazy val descriptions: Vector[Site] =
    sites.filter(site => site.describes && !site.literal)

  /* ------------------------------------------------- the scan can see something */

  // A census with no subjects is green, so the floors come first and are read off a measurement
  // rather than chosen: 1126 construction sites over nine modules on 2026-09-15, 942 of them with
  // literal prose. Half of each is a floor a tree that had lost its sources could not clear.
  "The scan" should "have found the refusals, which is how a census like this passes for free" in {
    val all = sources.flatMap(sitesIn)
    withClue(s"construction sites found: ${all.size}\n") {
      all.size should be >= 560
    }

    val literal = all.count(_.literal)
    withClue(s"sites whose prose is a literal: $literal\n") {
      literal should be >= 470
    }

    // And the roots, because the list above is derived now and a derivation can return nothing.
    // Ten modules carry a `src/main` on 2026-09-15; `aggregate` is an sbt project with no sources
    // and is not one. A floor rather than an equality: modules are added, and this is not a budget.
    withClue(s"module roots found: ${moduleRoots.map(_.toString).mkString(", ")}\n") {
      moduleRoots.size should be >= 10
    }

    info(s"${all.size} construction sites over ${moduleRoots.size} modules, " +
      s"$literal of them with literal prose")
  }

  it should "split an argument list where the compiler would, on the shapes that break a regex" in {
    val comma = """NotOfForm(s"a comma, and a paren ) inside a message", found)"""
    arguments(comma, comma.indexOf('(')).map(_.map(_.trim)) shouldBe
      Some(Vector("s\"a comma, and a paren ) inside a message\"", "found"))

    val nested = """NotOfForm(s"at ${showAt(a, b)}", Term.app(f, x))"""
    arguments(nested, nested.indexOf('(')).map(_.map(_.trim)) shouldBe
      Some(Vector("s\"at ${showAt(a, b)}\"", "Term.app(f, x)"))

    // The case that was got wrong, which is why it is asserted rather than trusted: a quote and a
    // comma inside an interpolation, which a scanner that ends the string at the inner quote splits
    // in the wrong place and hands back half an argument.
    val inner = """NotOfForm(s"no ${xs.mkString(", ")} here", found)"""
    arguments(inner, inner.indexOf('(')).map(_.map(_.trim)) shouldBe
      Some(Vector("s\"no ${xs.mkString(\", \")} here\"", "found"))
  }

  it should "read an interpolation where it is written and nowhere else" in {
    expressionsIn("""s"a proof of $reduced"""") shouldBe Vector("reduced")
    expressionsIn("""s"at ${reals.show(atom)} exactly"""") shouldBe Vector("reals.show(atom)")
    expressionsIn("""s"${xs.mkString(", ")} and ${ys.size}"""") shouldBe
      Vector("xs.mkString(\", \")", "ys.size")
    expressionsIn(""""a plain sentence with no holes"""") shouldBe empty
  }

  /* ------------------------------------------------- the assertion with no reading behind it */

  /**
   * The kernel's printer, which nothing above the kernel may name.
   *
   * `Printer` renders a term with no theory and cannot be given one, so what it writes is the
   * encoding: `99` comes out as `(BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 1))))))`. Above the kernel the
   * printer to reach for is `Show`, which takes a `Notation`, and at the surface it is
   * `Remedy.write`, which takes the reader's theory when there is one.
   *
   * Zero, and an equality rather than a floor, because there is no acceptable number of them. It
   * was one on 2026-09-15 and that one was this card's defect: a private helper in `Propositional`
   * that the prose of a `NotOfForm` interpolated. Stated over the file rather than over the prose
   * field, which is what lets it see a call the prose does not contain.
   */
  "Nothing above modules/kernel" should "name the kernel's printer" in {
    val printer = """\bPrinter\b""".r

    val found = for {
      root <- moduleRoots.filterNot(_.startsWith(Paths.get("modules/kernel")))
      path <- mainSources(root)
      (line, index) <- Files.readString(path).linesIterator.zipWithIndex
      if printer.findFirstIn(line).isDefined
    } yield s"$path:${index + 1}: ${line.trim}"

    withClue(s"${found.size} reference(s):\n${found.mkString("\n")}\n") {
      found shouldBe empty
    }
  }

  /* ---------------------------------------------------------------------- the census */

  "Every expression a refusal writes into a description" should "be one somebody has classified" in {
    val unclassified = for {
      site <- descriptions
      expression <- expressionsIn(site.prose)
      if !Classified.contains((site.file, expression))
    } yield s"${site.at} interpolates `$expression`"

    withClue(
      s"${unclassified.distinct.size} unclassified site(s). Add each to Classified, saying what " +
        s"it is:\n${unclassified.distinct.mkString("\n")}\n"
    ) {
      unclassified shouldBe empty
    }
  }

  it should "still be there, so an entry is pruned when its site goes" in {
    val found = (for {
      site <- descriptions
      expression <- expressionsIn(site.prose)
    } yield (site.file, expression)).toSet

    val stale = Classified.keySet.diff(found).toVector.sorted
    withClue(s"${stale.size} entr(y/ies) in Classified the scan no longer finds:\n" +
      s"${stale.mkString("\n")}\n") {
      stale shouldBe empty
    }
  }

  "A description that interpolates nothing and is not a literal" should "be listed with what it is" in {
    val unlisted = descriptions
      .filter(site => expressionsIn(site.prose).isEmpty)
      .filterNot(site => Unrendered.contains((site.file, site.prose)))
      .map(site => s"${site.at} passes `${site.prose.take(70)}`")

    withClue(s"${unlisted.size} unlisted site(s):\n${unlisted.mkString("\n")}\n") {
      unlisted shouldBe empty
    }
  }

  it should "still be there, for the reason the table above is pruned" in {
    val found = descriptions.map(site => (site.file, site.prose)).toSet
    val stale = Unrendered.keySet.diff(found).toVector.sorted
    withClue(s"${stale.size} stale entr(y/ies) in Unrendered:\n${stale.mkString("\n")}\n") {
      stale shouldBe empty
    }
  }

  /* ------------------------------------------- what the table cannot be wrong about */

  // The table is a reading and a reading can be wrong. This is the one cross-check on it that is
  // not: an expression that calls a renderer has rendered something, so it is a Crossing or a
  // TypeOnly and cannot be a Name, a Number or a Text. It is what catches an entry classified in a
  // hurry, and it is the whole of what a syntactic scan can say about a table of types.
  "An expression that calls a renderer" should "be classified as rendering something" in {
    val renderers = """\b(Printer\.show|Show\.show|\w+\.show)\s*\(""".r

    val misfiled = Classified.collect {
      case ((file, expression), (verdict, _))
          if renderers.findFirstIn(expression).isDefined &&
            verdict != Verdict.Crossing && verdict != Verdict.TypeOnly =>
        s"$file: `$expression` is filed as $verdict"
    }.toVector.sorted

    withClue(s"${misfiled.size}:\n${misfiled.mkString("\n")}\n") {
      misfiled shouldBe empty
    }
  }

  /* -------------------------------------------------------------------- the debt, counted */

  // Reported rather than pinned at a number: the two pairs of assertions above already fail on a
  // crossing added and on one removed, and a third number to update would be a number somebody
  // updates without reading. What this is for is a reader of the run, because the count is the size
  // of the repair `SkeletonFailsAt` is the first instance of.
  "The crossings" should "be reported, so the size of what is left is visible" in {
    val crossings = Classified.collect {
      case ((file, expression), (Verdict.Crossing, why)) => s"  $file: $expression -- $why"
    }.toVector.sorted

    info(s"${crossings.size} expression(s) still render a term where the refusal is raised:")
    crossings.foreach(info(_))

    // Not empty, and saying so is the point: this is a record of debt, and an assertion that it had
    // gone would have to be written on the day the last one goes rather than assumed now.
    crossings should not be empty
  }
}
