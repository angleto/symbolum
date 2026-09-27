package garden.xeno.symbolum.theories

import java.nio.file.{Files, Paths}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import scala.jdk.CollectionConverters.*

/**
 * Every file of this module is accounted for, so a development nobody assembled cannot stay quiet.
 *
 * Twice in two days a development was built, proved, green and **invisible**: `Magnitude` on
 * 2026-09-13 held seventeen facts that were in no library and in no document, and `Coding` held
 * `NUM_FACT` and four more the same evening. Neither was a broken test. `LibrarySpec` compares the
 * library against a sum over the developments `Library.of` names, and `RegisterSpec` against what
 * the chain assembles, so both are green **by construction** on anything outside the chain, and
 * outside the chain is exactly where the defect lives. `LibrarySpec`'s own comment says it: *"the
 * sum above is what would have caught it had anybody added `Magnitude` to the list; nothing catches
 * a development nobody ever put on either"*.
 *
 * == Why this is a file listing and not a search for a call ==
 *
 * The obvious guard greps for `defineConstant` and asks which of those files `Chain` names. It was
 * tried on 2026-09-13 and it fails in **both** directions, which is the measurement that decided
 * the shape here. It accuses `Recursion`, whose `Kernel.defineConstant` declares the **caller's**
 * constant and none of its own, and `Register`, which names the method in a docstring. And it
 * **misses `Coding`**, the one real case, because `Coding` introduces `NUM_FACT` through
 * `Recursion.define` rather than through a call of its own.
 *
 * A guard with two false positives is disabled by somebody who decides. A guard that misses the
 * only true case is green for ever and nobody decides anything, which is worse, and that is the
 * one a search for the call gives.
 *
 * == The population comes from the directory ==
 *
 * The thing being defended against is a development **nobody put on any list**, so a list is the
 * one place the population cannot come from. It is read off the directory, and [[Accounted]] has to
 * cover it exactly: a file with no entry fails, and an entry naming no file fails. A list that must
 * cover an enumerated population cannot go quiet; a list that **is** the population can.
 *
 * What this does not do, stated so nobody reads it as more: it does not check that a development in
 * the chain is **collected** by `Library.of`, which is `LibrarySpec`'s sum, nor that what it
 * declares reaches `Chain.widest`, which is `ChainSpec`'s. It checks that somebody classified the
 * file, which is the step that was skipped both times.
 */
class ChainCoverageSpec extends AnyFlatSpec with Matchers {

  /** What a file is, and there are only three answers. */
  enum Standing {

    /** `Chain.construct` builds it, so its facts and constants are assembled. */
    case InTheChain

    /** It declares no constant and holds no fact of its own: a procedure, a driver, a schema. */
    case DeclaresNothing

    /** Not a development: a generator, a document, an interface, a table, a tactic over the reals. */
    case NotADevelopment

    /**
     * It declares constants and `Chain.construct` deliberately does **not** build it.
     *
     * The fourth answer, added 2026-09-16 with `Collatz`, and the one to think about before
     * reaching for: a development outside the chain is unreachable from `Ask`, from `Find` and
     * from the library, which is usually a defect rather than a decision. What makes it a
     * decision here is that the constants describe **one object of one investigation** rather
     * than mathematics anyone might want, and the widest signature is what every goal in this
     * repository is typed against. Eleven rewrite rules of one Collatz encoding do not belong in
     * the vocabulary a question about the reals is asked in.
     *
     * A development taking this standing owes its own spec, because nothing else will build it.
     */
    case BesideTheChain
  }

  import Standing.*

  /**
   * Every file under `modules/theories/src/main`, with what it is.
   *
   * Written by hand on purpose: the entry is the place a reader says why a file is outside the
   * chain, and the two defects this exists for are both a file that was never asked the question.
   * A new development lands here red, with a message naming it, and the author chooses one of three
   * answers rather than discovering months later that nothing ever looked.
   */
  private val AccountedEntries: Vector[(String, Standing)] = Vector(
    "Arithmetic" -> InTheChain,
    "Bounded" -> InTheChain,
    "Coding" -> InTheChain,
    "Numbering" -> InTheChain,
    "Language" -> InTheChain,
    "Provability" -> InTheChain,
    "Deduction" -> InTheChain,
    // 2026-09-25. `NUM_VALUE`, `NUM_TRUE` and the triangle's graph, between `provability` and
    // `limit`. It was written first beside the chain, and the question this spec asked is what
    // moved it: a truth predicate for the embedded arithmetic is not one investigation's object.
    "Truth" -> InTheChain,
    // Beside the chain and declaring nothing until 2026-09-25, and a link since: a statement about
    // every refutation of a family is written with `RES_REFUTATION` and `RES_WIDTH`, which have to
    // be where the links above can see them. `ResolvingSpec` asserts the constants.
    "Resolving" -> InTheChain,
    "Primes" -> InTheChain,
    "Limit" -> InTheChain,
    "Transcendental" -> InTheChain,
    "Inductive" -> InTheChain,
    "Reaching" -> InTheChain,
    "Forward" -> InTheChain,
    "Integer" -> InTheChain,
    "Inclusion" -> InTheChain,
    // 2026-09-23. It declares three constants and no type: `docs/adr/0038` decides that a list
    // here is an orientation on `word` rather than a carrier, so what it adds to the chain is
    // cons, a head, a tail and the induction that descends from the left.
    "Listing" -> InTheChain,
    // 2026-09-23, the same day and the link above this one's consumer. It declares one constant,
    // `LIST_FOLD`, defined by `LIST_RECURSION`, which is what makes that theorem something this
    // repository spends rather than something it holds.
    "Folding" -> InTheChain,
    // 2026-09-24. It declares one constant, `sqrt`, and the theorem that spends `COMPLETENESS` a
    // third time to say what it names exists.
    "Root" -> InTheChain,
    "Continuity" -> InTheChain,
    "Logarithm" -> InTheChain,
    "Derivative" -> InTheChain,
    "Integral" -> InTheChain,
    "Collatz" -> BesideTheChain,
    "Divisibility" -> InTheChain,
    "Induct" -> InTheChain,
    "Magnitude" -> InTheChain,
    "Matrix" -> InTheChain,
    "Modular" -> InTheChain,
    "Natural" -> InTheChain,
    "Order" -> InTheChain,
    "Peano" -> InTheChain,
    "Product" -> InTheChain,
    "Real" -> InTheChain,
    "Ring" -> InTheChain,
    "Rotation" -> InTheChain,
    "Series" -> InTheChain,
    "Successor" -> InTheChain,
    "Word" -> InTheChain,
    "Concatenation" -> InTheChain,

    // Beside the chain and correctly so: each produces a theorem or a procedure on request and
    // introduces no constant, which is the reason `Bounded`'s own docstring gives for sitting where
    // it does. `Coding` was put here by mistake for a few hours and is the reason this file exists:
    // it introduces `NUM_FACT`, so the reason that covers these never covered it.
    // Not a development: HALF of one. `docs/adr/0016`'s phase 0 split `Peano` by whether a stage
    // can be stated without the reals, and this file is the stages that cannot, `real_of_num`
    // and the floor among them. `InTheChain` was written here first and the test below refused it,
    // correctly: the constants are declared into `Peano`'s theory and the facts are published in
    // `Peano.facts`, so what reaches `Chain.widest` and `Library.of` does so as `Peano`'s and this
    // file is a field of nothing. When the chain is reordered at `docs/adr/0016`'s phase 5 and
    // these become a development above `Order`, this entry becomes `InTheChain` and `Chain` gains
    // the field that makes it true.
    "Embedding" -> NotADevelopment,

    // Not a development: half of `Transcendental`, for `Embedding`'s reason and not `Monotone`'s.
    // It declares nothing, and the facts it derives, the two alternating series' absolute
    // convergence and `SIN_COS_SQUARED`, are published in `Transcendental.facts` under names
    // `Transcendental` declares, so what reaches `Library.of` does so as that development's. It is
    // a file of its own because the derivation is a third the length of the file it belongs to.
    "Trigonometric" -> NotADevelopment,

    // Not a development, for `Trigonometric`'s reason: the derivation of the extreme value theorem
    // and the gluing under it, whose facts are the map `ExtremeValue.prove` returns and are
    // published in `Continuity.facts` under names `Continuity` declares. A file of its own because
    // it is longer than the file it belongs to.
    "ExtremeValue" -> NotADevelopment,

    // Not a development, for `ExtremeValue`'s reason: continuity relative to `[a, b]` and the
    // interval theorems in that form, published in `Continuity.facts`, and the same for the
    // derivative's, published in `Derivative.facts`. Each declares nothing of its own.
    "Within" -> NotADevelopment,
    "DerivativeWithin" -> NotADevelopment,

    // Not a development, for `DerivativeWithin`'s reason: the derivation of the power's slope and of
    // Taylor's theorem, whose facts are the map `TaylorExpansion.prove` returns and are published
    // by `Derivative`. It declares nothing.
    "TaylorExpansion" -> NotADevelopment,

    // Not a development, for the same reason: the derivation of L'Hopital's rule, published by
    // `Derivative` under `LHOPITAL`. It declares nothing; the limit it is stated with is `Continuity`'s.
    "LHopitalRule" -> NotADevelopment,

    // Not a development, for the same reason: the derivation that a continuous function has an
    // integral, whose facts are published in `Integral.facts` under names `Integral` declares.
    "Integrability" -> NotADevelopment,

    // Not a development, for `Trigonometric`'s reason: half of `Limit`. It declares nothing, and
    // the criteria it derives are published in `Limit.facts` under names `Limit` declares, so what
    // reaches `Library.of` does so as that development's.
    "Criteria" -> NotADevelopment,

    // Not a development, for `Criteria`'s reason: the polynomial-times-geometric criteria, whose
    // facts `Limit` publishes under names it declares. A file of its own because what it needs
    // beyond `Criteria` is the embedding of `num` in the reals, which nothing in `Criteria` does.
    "Degrees" -> NotADevelopment,

    // Not a development, for `Criteria`'s reason: the binomial theorem on `num` and Fermat's little
    // theorem, whose facts `Primes` publishes under names it declares. A file of its own
    // because it is an induction toolkit over `NUM_SUM` that nothing else in `Primes` needs.
    "Freshman" -> NotADevelopment,

    // Not a development, for `Freshman`'s reason: the permutation of a finite product and Euler's
    // theorem, whose facts `Primes` publishes under names it declares. The one constant the
    // statement needs, `NUM_TOTIENT`, is `Modular`'s.
    "Euler" -> NotADevelopment,

    // Not a development, for `Freshman`'s reason: the p-adic valuation, whose facts
    // `Primes` publishes under names it declares. The constant, `NUM_VALUATION`, is `Modular`'s.
    "Valuation" -> NotADevelopment,

    // Not a development, for `Freshman`'s reason: the integral's forms with continuity relative to
    // `[a, b]` and the three congruences they are carried by, which `Integral` publishes.
    "IntegralWithin" -> NotADevelopment,

    // Not a development, for `Freshman`'s reason: parts and the change of variables with the
    // derivatives relative to `[a, b]`, and the tangent extension they are carried by.
    "IntegralRulesWithin" -> NotADevelopment,

    // Not a development, for `Euler`'s reason: Wilson's theorem and the product over paired indices
    // it needs, whose facts `Primes` publishes under names it declares. 2026-09-26.
    "Wilson" -> NotADevelopment,

    // A procedure, for `Monotone`'s reason: handed a goal it returns a theorem about the CALLER's
    // series, built out of facts `Limit` and `Transcendental` already publish. No constant, no
    // fact of its own, and `Prove` reaches it through the chain it is constructed from.
    "Convergence" -> DeclaresNothing,

    // Not a development: a function of the chain that proves one fact about one investigation's
    // series and declares nothing. It is not `BesideTheChain`, which is for a development that
    // declares constants; what it shares with `Collatz` is the reason its fact is not in the
    // library, which `Conjugacy` gives in its first paragraph, and `ConjugacySpec` builds it.
    "Conjugacy" -> NotADevelopment,

    // 2026-09-25, `Conjugacy`'s standing for `Conjugacy`'s reason: a function of the chain proving
    // a lower bound on resolution refutations of the pigeonhole principle, a family of clauses one
    // investigation is about, declaring nothing. The injection bound it proves on the way belongs in
    // `Peano`, and the file says so. `PigeonholeSpec` builds it.
    "Pigeonhole" -> NotADevelopment,

    // 2026-09-26, `Pigeonhole`'s standing for its reason: the width bound on the principle over an
    // expanding bipartite graph, declaring nothing, built on `Pigeonhole`'s moves and injection
    // bound. `ExpanderPigeonholeSpec` builds it.
    "ExpanderPigeonhole" -> NotADevelopment,

    "Descent" -> DeclaresNothing,

    // Beside the chain, and the classification is the one this file exists to make somebody choose.
    // It is a procedure: handed an operator it returns `|- MONOTONE f`, built entirely out of the
    // caller's own logic and `Inductive`'s definition of `MONOTONE`. It declares no type, no
    // constant and no definition, and it holds no fact of its own, which is why nothing of it could
    // be missing from `Library.of` the way `Magnitude`'s seventeen were. `InTheChain` is wrong for
    // it for a reason worth writing down rather than leaving to the reader: what it produces is a
    // theorem about the CALLER's operator, so there is no theory for `Chain.construct` to extend
    // and no signature for `Chain.widest` to gain.
    "Monotone" -> DeclaresNothing,

    "Recursion" -> DeclaresNothing,

    // A procedure over `Modular`'s characterisation lemmas, which declares nothing and publishes
    // nothing: what it hands back is an equation about a constant `Modular` already defined, at
    // arguments the caller chose. `Library.of` has nothing to collect from it for the same reason
    // it has nothing to collect from `Semiring`.
    "Value" -> DeclaresNothing,

    // `Semiring`'s standing, and the entry is worth a line because the file plainly holds facts:
    // a table of them, proved when it is built. They are a procedure's rule table and not a
    // development's library — the same position `Arithmetic`'s numeral lemmas are in over the
    // reals — so there is no theory for `Chain.construct` to extend and nothing `Library.of` could
    // be missing. What would change this entry is a consumer wanting `NUM_ADD_BIT0_BIT1` by name,
    // and then it belongs in `Peano` rather than here.
    "Digits" -> DeclaresNothing,
    "Semiring" -> DeclaresNothing,

    // `Recursion`'s standing for `Recursion`'s reason, and the reason is worth repeating because
    // the file looks like a counterexample to it. `Quotient` calls `Kernel.defineType` and
    // `Kernel.defineConstant`, so it plainly declares things; what it does not declare is anything
    // OF ITS OWN. The type, the projection and every lifted operation are named by the caller and
    // land in the caller's theory, and the facts it returns are about the caller's relation.
    // There is no `Quotient.standard` to put in a chain and nothing here for `Chain.construct` to
    // build, which is the same position `Recursion` is in one primitive along.
    "Quotient" -> DeclaresNothing,

    // `Quotient`'s standing, for `Quotient`'s reason, one type former along: `Datatype` calls
    // `Kernel.defineType` and `Kernel.defineConstant`, and everything it declares — the type, its
    // two bijections, the constructors and any function `defineRecursive` names — is named by the
    // caller and lands in the caller's theory. Its universe of trees is a term and not a constant,
    // which `docs/adr/0042` decides, so there is nothing of its own for `Chain.construct` to build.
    "Datatype" -> DeclaresNothing,

    // The steps a hand derivation over `num` is made of, shared by the files that write one. It
    // declares nothing and holds no fact: each function is a sequence of derived rules.
    "Steps" -> DeclaresNothing,

    // The same moves in direct style, which `Pigeonhole` wrote first and `Wilson` needed where no
    // chain exists yet. It declares nothing and holds no fact: each move is a derived rule or a
    // sequence of them over the ground it is handed. 2026-09-26.
    "Moves" -> DeclaresNothing,

    // A procedure, `Semiring`'s generalisation: handed constants and laws, it derives rules and
    // returns a normaliser, and every theorem it produces is about the caller's operations. It
    // declares nothing, so there is nothing for `Chain.construct` to extend; `Semiring` and
    // `Integer.ring` are its two instances.
    "CommutativeRing" -> DeclaresNothing,

    // A derivation inside `Fraction`'s construction and not a development: `RAT_LT` and
    // `RAT_OF_NUM` are defined by `Fraction.construct` before it is called, the facts it returns are
    // published by `Fraction` under `Fraction.Statements`, and it has no theory of its own to hand on.
    // It is a file of its own for size, which is `Ordering`'s position one step along.
    "Density" -> DeclaresNothing,

    // Beside the chain by decision and not as a debt, which is the line that separates it from
    // `Fraction`: `pterm` is a second syntax of arithmetic beside the coded one `Language` holds,
    // and in the chain every `PVAR` would sit next to a `NUM_CODE` in `Find` for a reader who asked
    // about neither. It is `Datatype`'s consumer, and `SyntaxSpec` is the spec the standing asks.
    "Syntax" -> BesideTheChain,

    // `Recursion`'s standing again: a theorem and nothing declared. What it proves is about the
    // caller's measure and step, and the constant a caller names by it is the caller's.
    "WellFounded" -> DeclaresNothing,

    // `Fraction`'s standing, a debt and not a decision: Euclid's algorithm is arithmetic anyone
    // would want, and wiring it into the chain moves `Chain.widest`, the reading register and the
    // guide's map. The other half of the debt is the theorem it is for, `NUM_EUCLID_GCD = NUM_GCD` off
    // both zero, which the file's own docstring names as not yet proved. `EuclidAlgorithmSpec` is the spec.
    "EuclidAlgorithm" -> BesideTheChain,

    // `Collatz`'s standing, and by decision rather than as a debt: its constants describe one
    // language, FRACTRAN, and nothing below it or in the tactic surface asks about a program of
    // fractions. `docs/adr/0054` is the record, and `FractranSpec` is the spec.
    "Fractran" -> BesideTheChain,

    // Not a development, for `Freshman`'s reason: FRACTRAN read as a register machine, whose one
    // theorem `Fractran` publishes under a name it declares, over the constant it defines.
    "FractranRegisters" -> NotADevelopment,

    // In the chain since phase 5 of `docs/adr/0007`, both of them: `Real.construction` builds the
    // rationals and the cuts below the reals, and `docs/adr/0053` made the cuts' type the reals' one
    // type. Both were beside the chain as a debt until then, `rat` being mathematics anyone would
    // want. Their facts were collected by neither `Library.of` nor `Reach.library` until 2026-09-27,
    // so `Ask` and `Find` reached no lemma about `rat` or about a cut; Mycelium card `e4a90d43`
    // collected both, and `RestsOnSpec` holds the two lists together.
    "Fraction" -> InTheChain,
    "Cut" -> InTheChain,

    // `Domain`'s standing, one level up: a search over a library for the theorem that carries a
    // domain claim into arithmetic. It declares nothing, holds no fact of its own, and every
    // theorem it hands back was built by `Domain.Built.settle` out of the caller's own domain
    // theory, so there is nothing here for `Chain.construct` to extend and nothing `Library.of`
    // could be missing. `docs/adr/0027` is why it is a file rather than a mode of that method.
    "Bridging" -> DeclaresNothing,

    // Beside the chain and it must STAY beside it, which is the one entry here whose reason is a
    // soundness argument rather than a classification. It declares nothing OF ITS OWN: what it
    // builds is a caller's domain theory, over a base the caller hands it. `docs/adr/0019` decided
    // that two theories axiomatising one name still produce constants that compare equal, so a
    // domain theory in the chain would be exactly the arrangement `SoundnessAttackSpec` derives
    // `|- F` from.
    "Domain" -> DeclaresNothing,

    "Certificate" -> NotADevelopment,
    "Chain" -> NotADevelopment,
    "Coefficient" -> NotADevelopment,
    "Counterpart" -> NotADevelopment,
    "Essay" -> NotADevelopment,
    "Examples" -> NotADevelopment,
    "Farkas" -> NotADevelopment,
    "Field" -> NotADevelopment,
    "Foundation" -> NotADevelopment,
    "Generated" -> NotADevelopment,
    "Guide" -> NotADevelopment,
    "Lemmas" -> NotADevelopment,
    "Library" -> NotADevelopment,
    "Linarith" -> NotADevelopment,
    "LinearForm" -> NotADevelopment,
    "Numeral" -> NotADevelopment,
    "Polynomial" -> NotADevelopment,
    // Landed on `7.0` with `06fbd17` and left this gate red, which is the defect this table exists
    // for met on the day it was written. `NotADevelopment` on the file's own argument rather than
    // on a guess: it declares no type, no constant and no axiom, it is one function that renders
    // English for a generated page, and its docstring puts it beside `Essay` and `Spellings`, both
    // of which are classified that way here already.
    "Prose" -> NotADevelopment,
    "Positivity" -> NotADevelopment,
    "Register" -> NotADevelopment,
    "RestsOn" -> NotADevelopment,
    "Signature" -> NotADevelopment,
    "Spellings" -> NotADevelopment,
    // The Gram decomposition behind `Linarith`'s squares, `docs/adr/0056`: untrusted, like `LinearForm`.
    "SumOfSquares" -> NotADevelopment,
    "Theorems" -> NotADevelopment
  )

  /**
   * The same accounting as a map, which is what the two assertions below look a file up in.
   *
   * The declaration above was a `Map(...)` literal until 2026-09-19, and the reason it is a
   * `Vector` projected here is what a repeated file name does to **this** table in particular. A
   * map literal keeps the **last** row, so two rows for one file with two different `Standing`s
   * resolve to whichever was written second, and the disagreement between them — the one thing a
   * reader of this table would want to be told about — is what disappears.
   *
   * **How much of that the three older assertions already catch was measured rather than assumed,
   * and the first answer was wrong.** The two about accounting are agreements between two readings
   * of the *names*, and a `Standing` is not a name, so a repeated file passes both: it is in
   * `keySet`, so nothing is unaccounted, and it is on disk, so nothing is stale. But the third,
   * the agreement with `Chain`, reads `Accounted.collect { case (name, InTheChain) => name }`, so
   * a duplicate that moves a file **out of** `InTheChain` does make it red. Perturbed on
   * 2026-09-19: `"Bounded" -> InTheChain` duplicated as `NotADevelopment` fails two tests, and
   * `"Embedding" -> NotADevelopment` duplicated as `DeclaresNothing` fails this one and no other.
   *
   * So what this guard adds is not "the only thing that can see a duplicate". It is the case the
   * other three are blind to, which is every duplicate among the entries that are **not** in the
   * chain, and on 2026-09-19 that was the large majority of the table. Those are exactly the
   * entries whose `Standing` nothing else reads.
   *
   * **No file is named twice**, measured on 2026-09-19 by the assertion below. The size of the
   * table is not written here: it moves whenever a development lands, which is the whole purpose
   * of the accounting above, and the assertion prints it when it fails.
   */
  private val Accounted: Map[String, Standing] = AccountedEntries.toMap

  "The accounting" should "not have absorbed a file named twice" in {
    val repeated =
      AccountedEntries.map(_._1).groupBy(identity).filter(_._2.size > 1).keys.toVector.sorted
    withClue(
      s"named twice in `AccountedEntries`, so one of the two standings is gone: " +
        s"${repeated.mkString(", ")}\n"
    )(Accounted.size shouldBe AccountedEntries.size)

    // And it is not passing because the table is empty, which is the one way an equality between
    // two sizes holds for free. About half of what the table held on 2026-09-19; a floor and not a
    // pin, because a development landing is what makes this table grow.
    AccountedEntries.size should be >= 33
  }

  private val directory =
    Paths.get("modules/theories/src/main/scala/garden/xeno/symbolum/theories")

  private val onDisk: Set[String] = {
    val stream = Files.list(directory)
    try
      stream
        .iterator()
        .asScala
        .map(_.getFileName.toString)
        .filter(_.endsWith(".scala"))
        .map(_.dropRight(".scala".length))
        .toSet
    finally stream.close()
  }

  "Every file of this module" should "be accounted for, and the accounting name a file" in {
    onDisk should not be empty

    val unaccounted = (onDisk -- Accounted.keySet).toVector.sorted
    withClue(
      s"a development nobody classified is how `Magnitude` and `Coding` went missing; say what " +
        s"${unaccounted.mkString(", ")} is, in `Accounted`:\n"
    )(unaccounted shouldBe empty)

    val stale = (Accounted.keySet -- onDisk).toVector.sorted
    withClue(s"`Accounted` names files that are gone: ${stale.mkString(", ")}\n")(stale shouldBe empty)
  }

  it should "agree with `Chain` about which developments it builds" in {
    // The chain's head, the construction below the reals, is `Real.construction` since phase 5b,
    // and `Chain.construct` builds the naturals and calls it before its own comprehension starts; so
    // the comprehension's arrows are read in both places, and the two calls that open the chain are
    // read as what they are. `Real` builds itself inside its own construction, unprefixed.
    val source = Files.readString(directory.resolve("Chain.scala"))
    val real = Files.readString(directory.resolve("Real.scala"))
    val head = real.slice(real.indexOf("def construction("), real.indexOf("lazy val constructed"))
    def arrows(text: String): Set[String] =
      "<- ([A-Z][A-Za-z]*)\\.construct".r.findAllMatchIn(text).map(_.group(1)).toSet
    val opening =
      (if (source.contains("Natural.construct(classical).flatMap(Real.construction(")) Set("Natural", "Real") else Set.empty) ++
        (if (head.contains("<- construct(classical.logic, cuts)")) Set("Real") else Set.empty)
    val built = arrows(source) ++ arrows(head) ++ opening

    // Read off `Chain.scala` rather than off the `Chain` value, because what is being checked is
    // that the classification above and the construction agree, and a classification checked
    // against the thing it classifies would be checking itself.
    val claimed = Accounted.collect { case (name, InTheChain) => name }.toSet

    withClue(s"claimed in the chain but not built by it: ${(claimed -- built).toVector.sorted}\n")(
      (claimed -- built) shouldBe empty
    )
    withClue(s"built by the chain but not claimed: ${(built -- claimed).toVector.sorted}\n")(
      (built -- claimed) shouldBe empty
    )
  }

  /**
   * What sits beside the chain declares nothing, which is the reason it is allowed to be there, and
   * `Descent` and `Semiring` are the two built here to show it.
   *
   * Asserted rather than described, because it is the reason `Coding` did not qualify and nobody
   * noticed. A development that starts declaring a constant fails here and has to move.
   */
  it should "hold nothing of its own in what sits beside the chain" in {
    val chain = Chain.standard
    val assembled = chain.widest.theory.constants.keySet

    val descent = Descent.construct(chain.peano, chain.induct)
    descent.isRight shouldBe true

    val semiring = Semiring.construct(chain.peano)
    semiring.isRight shouldBe true

    // Neither builds a theory of its own, so there is nothing for the chain to be missing. Stated
    // as what is assembled rather than as what they hold, so the assertion fails if either ever
    // gains a signature.
    assembled should contain("NUM_FACT")
    assembled should contain("abs")
  }
}
