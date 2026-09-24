package garden.xeno.symbolum.tactics

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import garden.xeno.symbolum.tactics.DocumentBlocks.{Block, Compiles, Fate, NotRun, Prepared, Runs}

/**
 * Every Scala block of `docs/proving.md`, compiled as the document holds it.
 *
 * == What this closes ==
 *
 * The guide's excerpt promised, until 2026-09-16, that "every example below is executed by
 * `DocumentationSpec`, so an example that stops working fails the build". What that spec runs is a
 * program written beside each assertion, which is the answer being checked and is worth checking;
 * it is not the text the document prints. The two are written twice and drift, and the front page
 * is where that was measured: a block whose first line did not compile anywhere sat beside a green
 * assertion for as long as both existed, because the assertion evaluated a different spelling.
 * `ReadmeSpec` closed it for `README.md` on 2026-09-16 and this closes it for the guide, which
 * holds more blocks than the front page.
 *
 * The two guards are a pair and neither is the strong version of the other. This one says the text
 * is a program; `DocumentationSpec` says the program gives the answer printed beside it.
 *
 * == A prelude is the prose, written down ==
 *
 * A block that uses a name an earlier block or the prose around it established gets that name from
 * [[Blocks]] and never from the document, so what is compiled is the prelude and then the block's
 * own text unaltered. Every character this guard protects is a character `docs/proving.md` holds.
 *
 * Writing the preludes is also the measurement nobody had taken, on the forty-seven blocks the
 * document held on 2026-09-16. **Nine of them use a name the document never defines anywhere**:
 * `search`, `chain`, `claim`, `cost`, `left`, `right`, `pi` with the four `S_j`, `reads`, and
 * `linarith`. In each case the prose says what the
 * name is and the reader is expected to build it, which is a fair thing for a guide to do and is
 * not the same as a block they can paste. The preludes here are written from those sentences, so
 * they are a reading of the prose and the one place this file could be wrong about the document
 * without going red.
 *
 * == Compiled and not run, which is the third fate ==
 *
 * The blocks registered as `Compiles` compile and are deliberately not executed, each saying why
 * beside itself. Some would write a file into the working directory a test was started from, and
 * the rest are computations another spec owns and times. Excusing them from compiling as well would
 * give up the guard for the defect this file exists to catch in order to avoid a cost that is only
 * in the running.
 *
 * == What it costs ==
 *
 * Ten seconds for the whole suite on 2026-09-16, on a machine carrying two other sbt runs: one
 * compilation of the forty-seven blocks the document held that day, forty-three of them then
 * executed, several of which prove something. That is the number that decided the shape rather
 * than an argument: a per-block compilation was measured at 34 seconds for the first and about a
 * second for each after it, so
 * forty-seven of them arithmetically comes to about eighty seconds against these ten, and running
 * the four excused blocks would have added on top the two slow computations `RelationSpec` and
 * `AlgebraicSpec` already pay for once. Where that would have put this suite in the module's
 * ranking is not measured and is not claimed.
 */
class GuideBlocksSpec extends AnyFlatSpec with Matchers {

  private val Document = "docs/proving.md"

  private val Kernelled = "import garden.xeno.symbolum.kernel._\n"
  private val Logics = "import garden.xeno.symbolum.logic._\n"
  private val Theories = "import garden.xeno.symbolum.theories._\n"
  private val Tactics = "import garden.xeno.symbolum.tactics._\n"
  private val Algebra = "import garden.xeno.symbolum._\nimport garden.xeno.symbolum.Dsl._\n"

  /** What a reader of the guide has imported by the time the proof side's examples start. */
  private val Prover = Kernelled + Logics + Theories + Tactics

  /** The same, with the real theory the guide calls `reals` throughout. */
  private val Reals = Prover + "val reals = Real.standard\n"

  /**
   * Every Scala block of the guide, by a line that identifies it, and what happens to it.
   *
   * Keyed by a line of its own text and not by its position, for `ReadmeSpec`'s reason: inserting a
   * block renumbers every block after it, and each would then be run under the prelude and the
   * reason belonging to its predecessor. Both directions are asserted below.
   */
  private val Blocks: Vector[(String, Fate)] = Vector(
    // The opening example, which carries its own import.
    "val theorem = Ring.standard.prove(\"!x:real. (x + 1) * (x + 1) = x * x + 2 * x + 1\")" ->
      Runs(""),

    // Stating a proposition.
    "Parser.proposition(Logic.standard.theory, \"x = y\")" -> Runs(Logics),

    // The tactics, one section each. All of these are bare calls under the guide's imports.
    "Ring.standard.prove(\"!x:real y:real. (x - y) * (x + y) = x * x - y * y\")" -> Runs(Theories),
    "Field.standard.prove(\"!x:real y:real. (x * y) / y = x\")" -> Runs(Theories),

    // Discharging `Field`'s side condition. The prose above it names `Order.nonZero` and says the
    // denominator is known positive; `theorem` is the block two above, and `derived` is what that
    // sentence describes, built here because the document does not build it.
    "discharged <- rules.disch(theorem.hypotheses.head, theorem)" -> Runs(
      Prover +
        "val order = Order.standard\n" +
        "val reals = order.reals\n" +
        "val rules = reals.logic.rules\n" +
        "val theorem = Field.standard.prove(\"!x:real y:real. (x * y) / y = x\").toOption.get\n" +
        "val y = Term.variable(\"y\", TyApp(\"real\", Nil))\n" +
        "val positive = LogicError.lift(Kernel.assume(" +
        "reals.proposition(\"0 < y:real\").toOption.get)).toOption.get\n" +
        "val derived = rules.spec(y, order.nonZero.toOption.get)" +
        ".flatMap(rules.mp(_, positive)).toOption.get\n"),

    "Linarith.standard.prove(\"!x:real y:real z:real. x < y /\\\\ y < z ==> x < z\")" ->
      Runs(Theories),
    "Linarith.standard.prove(\"!x:real y:real. 0 < x /\\\\ 0 < y ==> 0 < x * y\")" -> Runs(Theories),
    "Linarith.standard.prove(\"!x:real y:real. 0 <= x /\\\\ 0 <= y ==> 0 <= x * y\")" ->
      Runs(Theories),
    "Linarith.standard.prove(\"!e:real. e / 3 + e / 3 + e / 3 <= e\")" -> Runs(Theories),
    "Linarith.standard.support(" -> Runs(Theories),
    "Arithmetic.standard.add(1000, 1000)" -> Runs(Theories),
    "Order.standard.zeroLessOne" -> Runs(Theories),

    // Using a lemma the development already holds.
    "val order = Order.standard" -> Runs(Prover),
    "val reals = Order.standard.reals" -> Runs(Prover),
    "  \"?s:real. (!x:real. x < 1 ==> x <= s)" -> Runs(
      Prover +
        "val reals = Order.standard.reals\n" +
        "val logic = reals.logic.over(reals.theory).toOption.get\n"),
    "Apply.candidates(logic, Order.standard.facts.toVector, goal)" -> Runs(
      Prover +
        "val reals = Order.standard.reals\n" +
        "val logic = reals.logic.over(reals.theory).toOption.get\n" +
        "val goal = reals.proposition(\"0 < inv 2\").toOption.get\n"),
    "Consistency.standard.reading(" -> Runs(Tactics),

    // Proving by hand: three derivations, each self-contained under the imports.
    "val reals = Real.standard" -> Runs(Prover),
    "val logic = Logic.standard" -> Runs(Prover),
    "val classical = Classical.standard" -> Runs(Prover),

    // The bridge to the algebra half, which carries its own imports.
    "Oracle.standard.certifyExpansion((x + 1) * (x + 1))" -> Runs(""),
    "val candidates = Vector((x + 1) * (x + 1), x*x + Num(2)*x + Num(1), x*x + Num(1))" -> Runs(
      Algebra + Tactics + "val x = Var(\"x\")\n"),

    // Refuting.
    "val premise = reals.proposition(\"0 < x:real\")" -> Runs(Reals),
    "val cycle = Vector(\"x:real < y:real\", \"y:real < z:real\", \"z:real < x:real\")" ->
      Runs(Reals),

    // The one whose subject is a declared type. The prose above it says `risk : entity -> real`
    // over a model that sizes `entity` at three, and `search` is a `Refutation` over that model;
    // the document names neither, so both are built here from that sentence.
    "search.satisfying(Vector(\"0 < x:real\", \"x:real < 1\", \"risk a < risk b\").map(reads))" -> Runs(
      Prover +
        "val extended = Real.standard.extended(\n" +
        "  Vector(\"entity\" -> 0),\n" +
        "  Vector(\"risk\" -> Type.fun(TyApp(\"entity\", Nil), TyApp(\"real\", Nil)),\n" +
        "         \"a\" -> TyApp(\"entity\", Nil),\n" +
        "         \"b\" -> TyApp(\"entity\", Nil))).toOption.get\n" +
        "val search = Refutation(Evaluate.over(extended, Model.Reals.sizing(\"entity\", 3)))\n" +
        "def reads(text: String): Term = extended.proposition(text).toOption.get\n"),

    // The model that answers over `num`, where `chain` and `claim` are the prose's.
    "Refutation(Evaluate.over(chain.reals, Model.Numbers))" -> Runs(
      Prover +
        "val chain = Chain.standard\n" +
        "val claim = chain.widest.proposition(\n" +
        "  \"!x:num y:num. real_of_num (x + y) = real_of_num x * real_of_num y\").toOption.get\n"),

    // What would have to be assumed.
    "Abduce.standard.missing(\"!x:real y:real. 0 < x ==> 0 < x * y\")" -> Runs(Tactics),
    "Abduce.standard.missing(\"!x:real y:real. 0 < x /\\\\ x * y = 1 ==> 2 < x\")" -> Runs(Tactics),

    // Deciding a quantified claim.
    "Quantified.standard.decide(\"!x:real. ?y:real. x < y\")   // Holds" -> Runs(Tactics),
    "Quantified.standard.decide(\"!x:real y:real. x < y ==> ?z:real. x < z /\\\\ z < y\")" ->
      Runs(Tactics),

    // Where a claim came from.
    "val register = Provenance.of(reals, Vector(" -> Runs(Reals),

    // What one claim costs.
    "val cost = Cost.standard" -> Runs(Tactics),
    "println(cost.render(cost.of(\"!x:real. 0 < x ==> 1 < x\").toOption.get).toOption.get)" ->
      Runs(Tactics + "val cost = Cost.standard\n"),

    // The ledger and the sweep, which are the two that write where they are started from.
    "val ledger = Ledger.at(Paths.get(\"run.tsv\"))" -> Compiles(
      Algebra + Tactics + "import java.nio.file.Paths\n" +
        "val x = Var(\"x\")\n" +
        "val left = (x + Num(1)) * (x + Num(1))\n" +
        "val right = x * x + Num(2) * x + Num(1)\n",
      "it settles an identity into a ledger at `run.tsv`, a path relative to wherever the suite " +
        "was started, so running it here would write a file into the working directory and " +
        "append to it again on every run. `DocumentationSpec` runs the same call against a " +
        "temporary directory, which is the shape a test may have and not the shape a reader is " +
        "shown"),
    "val sweep = Sweep(Propose.standard, Ledger.at(Paths.get(\"run.tsv\")))" -> Compiles(
      Tactics + "import java.nio.file.Paths\n",
      "the same `run.tsv` in the working directory as the block above, and the sweep writes to it " +
        "rather than only reading: `DocumentationSpec` runs this one against a temporary " +
        "directory and asserts the shape of the report it produces"),

    // Guessing a closed form.
    "Family.standard.of(\"\\\\i:num. real_of_num i * real_of_num i\")" -> Runs(Tactics),
    "Family.standard.of(\"\\\\i:num. Power 2 i\")" -> Runs(Tactics),

    // The integer relation detector. The five numbers are pi and four BBP sums, which the prose
    // names and the document does not compute; `RelationSpec` computes them and times the search.
    "Relation.among(Vector(pi, s1, s4, s5, s6), digits = 200)" -> Compiles(
      "import garden.xeno.symbolum.Relation\n" +
        "val pi, s1, s4, s5, s6 = BigDecimal(0)\n",
      "the five values are pi and the BBP sums `S_j` at two hundred digits, which the document " +
        "names in the sentence under it and does not compute; the computation and its timing are " +
        "`RelationSpec`'s, and the placeholders here are zero because what this guard is asking " +
        "is whether the call is still the call the document prints"),
    "Algebraic.standard.of(Vector(Root(2, 2), Root(2, 3), Root(2, 5)))" -> Compiles(
      Tactics + "import garden.xeno.symbolum.tactics.Algebraic.Root\n",
      "the search it runs is the one the comment beside it reports at 111048 inferences, and " +
        "`AlgebraicSpec` already runs exactly these three roots and asserts what comes back; " +
        "running it again here would buy a second copy of a slow measurement"),

    // What to do about a refusal.
    "val refusal = Prove.standard(\"!x:real y:real. (x * y) / y = x\").swap.toOption.get" ->
      Runs(Reals),
    "val decided = Quantified.standard.decide(\"!x:real. ?y:real. x < y\").toOption.get" ->
      Runs(Tactics),

    // What a reader is shown.
    "val goal = reals.proposition(\"!x:real y:real. x < y ==> x + 1 < y + 1\").toOption.get" ->
      Runs(Reals),

    // Extending the theory with a domain of your own.
    "val extended = Real.standard.extended(" -> Runs(Prover),
    "  arithmetic <- Arithmetic.construct(extended)" -> Runs(
      Prover +
        "val extended = Real.standard.extended(\n" +
        "  Vector(\"agent\" -> 0),\n" +
        "  Vector(\"selectivity\" -> TyApp(\"real\", Nil))).toOption.get\n"),

    // The worked argument, whose `reads` is the prose's: the text read against the domain theory.
    "val theory = Vector(\"tierTwo\", \"gated\", \"reviewed\", \"signed\", \"auditable\")" -> Runs(Prover),

    // The same argument with a negation in it, which is one call rather than a fold: a `Domain`
    // value, built, and a claim settled against it. Self-contained under the guide's imports.
    "val onChange = Type.fun(TyApp(\"change\", Nil), Type.Bool)" -> Runs(Prover),

    "val register = Provenance.of(extended, Vector(" -> Runs(
      Prover +
        "val extended = Real.standard.extended(\n" +
        "  Vector(\"agent\" -> 0),\n" +
        "  Vector(\"selectivity\" -> TyApp(\"real\", Nil))).toOption.get\n" +
        "val cost = Cost.standard\n" +
        "val linarith = Arithmetic.construct(extended)\n" +
        "  .flatMap(Ring.construct)\n" +
        "  .flatMap(Order.construct)\n" +
        "  .flatMap(Linarith.construct).toOption.get\n"),

    // Adding a lemma of your own.
    "val statement = reals.proposition(\"x:real * (y:real + 1) = x * y + x\")" -> Runs(Reals)
  )

  /* ------------------------------------------------------------------ reading the document */

  private def guide: String = DocumentBlocks.read(Document)

  private def blocksOf(markdown: String): Vector[Block] = DocumentBlocks.blocksOf(Document, markdown)

  /* ------------------------------------------------------------------ the registry agrees */

  "Every Scala block of the guide" should "be named exactly once by this file, and name one block" in {
    val blocks = blocksOf(guide)

    val unclaimed = blocks.filterNot { block =>
      Blocks.exists { case (key, _) => block.text.contains(key) }
    }
    withClue(s"blocks no entry of `Blocks` names, by first line:\n" +
      s"${unclaimed.map(block => s"  line ${block.line}: ${block.text.linesIterator.next()}").mkString("\n")}\n") {
      unclaimed shouldBe empty
    }

    val orphaned = Blocks.map(_._1).filterNot(key => blocks.exists(_.text.contains(key)))
    withClue(s"entries naming no block of $Document: ${orphaned.mkString(", ")}\n") {
      orphaned shouldBe empty
    }

    val ambiguous = Blocks.map(_._1).filter(key => blocks.count(_.text.contains(key)) > 1)
    withClue(s"entries naming more than one block: ${ambiguous.mkString(", ")}\n") {
      ambiguous shouldBe empty
    }

    info(s"${blocks.size} scala blocks in $Document")
  }

  it should "give a reason for every one it does not run" in {
    Blocks.collect {
      case (key, Compiles(_, reason)) => (key, reason)
      case (key, NotRun(reason)) => (key, reason)
    }.foreach { case (key, reason) =>
      withClue(s"the reason given for `$key` is too short to be one: ") {
        reason.length should be > 60
      }
    }
  }

  /* -------------------------------------------------------------------- compiling and running */

  "Every block of the guide" should "compile as the document holds it, and run where it is run" in {
    val blocks = blocksOf(guide)

    def textOf(key: String): String =
      blocks.find(_.text.contains(key)).map(_.text).getOrElse(fail(s"no block holds `$key`"))

    val prepared = Blocks.collect {
      case (key, Runs(prelude)) => Prepared(key, prelude, textOf(key), run = true)
      case (key, Compiles(prelude, _)) => Prepared(key, prelude, textOf(key), run = false)
    }

    val outcome = DocumentBlocks.outcome("guideblocks", prepared)

    withClue(s"${outcome.errors} error(s), in the block(s) keyed by " +
      s"${outcome.blamed.mkString("; ")}\n${outcome.said}\n") {
      outcome.errors shouldBe 0
    }
    withClue(s"${outcome.threw.size} block(s) threw:\n${outcome.threw.mkString("\n")}\n") {
      outcome.threw shouldBe empty
    }

    info(s"${prepared.size} blocks compiled and ${prepared.count(_.run)} run from $Document")
  }
}
