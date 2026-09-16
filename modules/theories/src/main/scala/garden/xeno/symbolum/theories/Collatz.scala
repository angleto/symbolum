package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The rewriting system $$S_2$$, its counted sub-relation, its potential and its marked words.
 *
 * Source: `collatz@8b991e5`, `code/referee/checks_rewriting.py` lines 9 to 15, which is where the
 * eleven rules are written down and is the repository that owns them. Nothing here was transcribed
 * by eye: the rule table below was **generated** from those lines, and the letters, the splits and
 * the potential all follow the same source.
 *
 * == Why this is a development of its own and not part of `Forward` ==
 *
 * `Forward` is generic in the system: `WORD_RFC R` is about any `R`. This file is the one `R` that
 * one investigation is about. Keeping them apart is what lets the closure be reused and what keeps
 * a reader of `WORD_RFC` from thinking the eleven rules are part of what a closure is.
 *
 * == The alphabet, and why the digits are not named ==
 *
 * Seven letters, encoded as numbers, and the three digits are **0, 1 and 2 themselves**. That is
 * the decision worth knowing before reading anything below: `c` is a digit exactly when `c < 3`,
 * which is one comparison rather than a three-way disjunction, and it is what makes [[Potential]]
 * one `NUM_SUM` over the positions. The other four letters are the numerals above the digits, and
 * they are named because a reader meeting `3` in a rule has no way to know it is `f`.
 *
 * The cost of the encoding is that a letter is a number and nothing stops a term naming the letter
 * `9`. Nothing below cares: every rule names its letters, and a word over letters this system has
 * no rule for is a word no rule applies to, which is a normal form and not an error.
 *
 * == The three groups, which is the structure part C uses ==
 *
 * `D` is the two rules that consume the marker, `A` the six that commute a digit past a letter, and
 * `B` the three that act at the head. [[Counted]] is `A` alone, and it is what a potential-function
 * argument instantiates as the counted sub-relation of `REACH`: every `A`-step moves one digit one
 * place nearer the head, so it drops [[Potential]] by exactly one, and no other rule lowers it.
 *
 * **The direction of that second condition is the one this repository has already got backwards
 * once.** `REACH_POTENTIAL` asks that no uncounted step LOWERS the measure, not that none raises
 * it. Two of the eleven do raise it, so the version with the inequality the other way round is
 * true, unusable, and was what a card carried until it was measured against the source.
 */
final class Collatz private (
  val forward: Forward,
  val theory: Theory,
  val notation: Notation,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  /** The logic, reading and building against **this** theory rather than the one below it. */
  val logic: Logic = forward.inductive.classical.logic
    .over(theory)
    .fold(
      error => throw new IllegalStateException(s"the logic does not extend: ${error.message}"),
      identity
    )

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** A derived fact of this development, by name. Nothing here is asserted. */
  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Collatz {

  /* ------------------------------------------------------------------ the alphabet */

  /** The letter `f`, which is `3`: the digits are 0, 1 and 2 and the rest sit above them. */
  val F: String = "S2_F"

  /** The letter `t`, which is `4`. */
  val T: String = "S2_T"

  /** The head marker `/`, which is `5`. Every word of the system starts with it. */
  val Head: String = "S2_HEAD"

  /** The tail marker `.`, which is `6`. A marked word ends with it and holds no other. */
  val Tail: String = "S2_TAIL"

  /* ------------------------------------------------------------------ the system */

  /** `S2 l r` — `l -> r` is one of the eleven rules. */
  val Name: String = "S2"

  /** `S2_COUNTED l r` — `l -> r` is one of the six commutation rules, which is `A`. */
  val Counted: String = "S2_COUNTED"

  /** `S2_PHI w` — the sum, over the digit occurrences of `w`, of the distance from the head. */
  val Potential: String = "S2_PHI"

  /** `S2_MARKED w` — exactly one tail marker, and it is the last letter. */
  val Marked: String = "S2_MARKED"

  /**
   * `S2_TAILFREE u` — no letter of `u` is the tail marker.
   *
   * The ninth constant, and the one the closure of the marked class is written with rather than a
   * convenience. A marked word is a tail-free word with one marker on the end, so every statement
   * about how a step moves through a marked word splits into a statement about the piece holding
   * the marker and a statement about the pieces that do not. Without a name for the second the two
   * halves are the same quantified formula written out twice, which is how a lemma about the first
   * half ends up being proved again inside a proof about the second.
   */
  val TailFree: String = "S2_TAILFREE"

  /* ------------------------------------------------------------------ the facts */

  /** `|- !l r. S2_COUNTED l r ==> S2 l r` — the counted rules are rules. */
  val CountedIsRule: String = "S2_COUNTED_IS_RULE"

  /** `|- ?l r. S2 l r` — the system is inhabited, so nothing below is vacuously true. */
  val Inhabited: String = "S2_INHABITED"

  /**
   * `|- ~(S2 (WORD_SINGLETON S2_HEAD) (WORD_SINGLETON S2_HEAD))`.
   *
   * The refusal, and the reason it is the fact worth having rather than a courtesy. A relation that
   * held of everything would make `WORD_RFC S2` the set of all words and every statement downstream
   * true and empty. This is what says the eleven are eleven rules rather than a relation nobody
   * constrained, and it is derived by unfolding and refuting each of the eleven disjuncts on the
   * length of the words involved.
   */
  val Refused: String = "S2_REFUSED"

  /**
   * `|- !u v. S2_TAILFREE (WORD_CONCAT u v) = (S2_TAILFREE u /\ S2_TAILFREE v)`.
   *
   * Tail-freeness is a property of every letter, so it splits over a concatenation with nothing
   * left over. Both directions are needed and neither is the interesting one: a step takes
   * `x l y` to `x r y`, so the left-hand reading takes the context apart and the right-hand one
   * puts it back with the other rule side in the middle.
   */
  val TailFreeConcat: String = "S2_TAILFREE_CONCAT"

  /**
   * `|- !u v. 0 < WORD_LENGTH v ==> (S2_MARKED (WORD_CONCAT u v) = (S2_TAILFREE u /\ S2_MARKED v))`.
   *
   * The same split for the marked class, and the hypothesis is what makes it true. With `v` empty
   * the left-hand side is `S2_MARKED u`, which says nothing about `v` at all, and the right-hand
   * side asks `S2_MARKED WORD_EMPTY`, which is false: the equation would read `S2_MARKED u = F`
   * for every `u`. So the condition is not a technicality about where the marker sits, it is the
   * whole difference between a decomposition and a false statement.
   */
  val MarkedConcat: String = "S2_MARKED_CONCAT"

  /* ------------------------------------------------------------------ the types */

  private val Numbers: Type = TyApp(Natural.TypeName, Nil)
  private val Words: Type = TyApp(Word.TypeName, List(Numbers))

  private val LeftSide: FVar = Term.variable("l", Words)
  private val RightSide: FVar = Term.variable("r", Words)

  private val LengthType: Type = Type.fun(Words, Numbers)
  private val NthType: Type = Type.fun(Words, Type.fun(Numbers, Numbers))
  private val ConcatType: Type = Type.fun(Words, Type.fun(Words, Words))
  private val OrderType: Type = Type.fun(Numbers, Type.fun(Numbers, Type.Bool))
  private val BinaryNumbers: Type = Type.fun(Numbers, Type.fun(Numbers, Numbers))

  /* ------------------------------------------------------------------ the rule table */

  /** Which of the source's three groups a rule belongs to. */
  enum Group {

    /** `D`: the two rules that consume a digit next to the tail marker. */
    case Consumes

    /** `A`: the six that commute a digit one place towards the head. This is the counted one. */
    case Commutes

    /** `B`: the three that act at the head marker. */
    case AtTheHead
  }

  /**
   * One rule, with its letters named rather than spelled into a string.
   *
   * The table is the source of both things this development does with a rule, and it became a
   * table on 2026-09-16 for the second of them. The text of the definition is generated from it,
   * which is what it was for when the rules landed; a **proof** about one rule needs that rule's
   * two words as terms, and before the table existed the only place a rule was written down was
   * inside a string that had already been concatenated to ten others.
   *
   * A letter is spelled the way this theory spells it: a digit is its own numeral and the other
   * four are the constants that name them, which is [[Letters]] read from the other side.
   */
  final case class Rule(label: String, group: Group, left: Vector[String], right: Vector[String])

  /**
   * The eleven rules, in the source's own order: `RULES = D + A + B`.
   *
   * Source: `collatz@8b991e5`, `code/referee/checks_rewriting.py` lines 9 to 15. The spellings
   * below are that file's, letter for letter, and the order is that file's `D + A + B`.
   *
   * **What says this is faithful is a measurement and not care.** The text this table generates
   * was compared, character for character, against the hand-written literal it replaced, which was
   * itself generated from those lines when the rules landed; the two agree exactly, up to the
   * trailing space the literal ended with. A table that had moved a letter would have produced a
   * different string and the comparison would have said so. That check reads a second repository,
   * so it is a dated measurement rather than a gate, and what guards the table from here on is
   * `CollatzSpec`: eleven disjuncts counted off the definition, and the eleven left-hand sides
   * derived pairwise distinct.
   */
  val Rules: Vector[Rule] = Vector(
    rule("R1", Group.Consumes, "ff.", "0."),
    rule("R2", Group.Consumes, "t.", "2."),
    rule("A1", Group.Commutes, "t0", "1t"),
    rule("A2", Group.Commutes, "f0", "0f"),
    rule("A3", Group.Commutes, "t1", "2f"),
    rule("A4", Group.Commutes, "f1", "0t"),
    rule("A5", Group.Commutes, "f2", "1f"),
    rule("A6", Group.Commutes, "t2", "2t"),
    rule("B1", Group.AtTheHead, "/0", "/t"),
    rule("B2", Group.AtTheHead, "/1", "/ff"),
    rule("B3", Group.AtTheHead, "/2", "/ft")
  )

  /** `A`, the six that [[Counted]] is defined by, taken from the table rather than written twice. */
  val CountedRules: Vector[Rule] = Rules.filter(_.group == Group.Commutes)

  private def rule(label: String, group: Group, left: String, right: String): Rule =
    Rule(label, group, spell(left), spell(right))

  /** A word of the source's alphabet, as the letters this theory names them by. */
  private def spell(word: String): Vector[String] =
    word.map {
      case 'f' => F
      case 't' => T
      case '/' => Head
      case '.' => Tail
      case digit => digit.toString
    }.toVector

  /* ------------------------------------------------------------------ the text */

  private def singletonText(letter: String): String = s"WORD_SINGLETON ($letter:num)"

  /**
   * A word as a left-nested concatenation of one-letter words.
   *
   * Left-nested rather than right-nested because that is the shape the hand-written literal had,
   * and the shape decides which of `WORD_CONCAT_NTH_LEFT` and `WORD_CONCAT_NTH_RIGHT` reads which
   * letter. Every rule of this system has at least two letters, so the fold never meets an empty
   * word; a word with none would be `WORD_EMPTY` and is not something the table can hold.
   */
  private def wordText(letters: Vector[String]): String =
    letters.map(singletonText).reduceLeft((built, next) => s"WORD_CONCAT ($built) ($next)")

  /** A rule set as the disjunction of its clauses, which is how both relations are defined. */
  private def disjunctionText(rules: Vector[Rule]): String =
    "\\l:word(num). \\r:word(num). " +
      rules
        .map(entry => s"(l = ${wordText(entry.left)} /\\ r = ${wordText(entry.right)})")
        .mkString(" \\/ ")

  private val SystemBody: String = disjunctionText(Rules)

  private val CountedBody: String = disjunctionText(CountedRules)

  /**
   * `S2_PHI w` — the distance from the head, summed over the digit occurrences.
   *
   * The digits are `0`, `1` and `2` themselves, so "is a digit" is one comparison rather than a
   * three-way disjunction, which is what keeps this a single `NUM_SUM` over the positions.
   */
  private val PotentialBody: String =
    "\\w:word(num). NUM_SUM (\\i:num. COND (WORD_NTH w i < 3) (NUM_SUB i 1) 0) (WORD_LENGTH w)"

  private val TailFreeBody: String =
    "\\w:word(num). !i:num. i < WORD_LENGTH w ==> ~(WORD_NTH w i = S2_TAIL)"

  /** `S2_MARKED w` — positive length, the last letter is the marker, and no earlier letter is. */
  private val MarkedBody: String =
    "\\w:word(num). 0 < WORD_LENGTH w /\\ " +
      "WORD_NTH w (NUM_SUB (WORD_LENGTH w) 1) = S2_TAIL /\\ " +
      "(!i:num. i < NUM_SUB (WORD_LENGTH w) 1 ==> ~(WORD_NTH w i = S2_TAIL))"

  /** The four letters that are not digits, in the order they are declared. */
  val Letters: Vector[(String, String)] =
    Vector(F -> "3", T -> "4", Head -> "5", Tail -> "6")

  /** Every definition this development introduces, as text, in dependency order. */
  val Bodies: Vector[(String, String)] =
    Letters.map { case (name, value) => name -> s"($value:num)" } ++
      Vector(
        Name -> SystemBody,
        Counted -> CountedBody,
        Potential -> PotentialBody,
        Marked -> MarkedBody,
        TailFree -> TailFreeBody
      )

  /** Every statement this development publishes, as text. */
  val Statements: Vector[(String, String)] = Vector(
    CountedIsRule -> "!l:word(num). !r:word(num). S2_COUNTED l r ==> S2 l r",
    Inhabited -> "?l:word(num). ?r:word(num). S2 l r",
    Refused ->
      ("~(S2 (WORD_SINGLETON (S2_HEAD:num)) (WORD_SINGLETON (S2_HEAD:num)))"),
    TailFreeConcat ->
      ("!u:word(num). !v:word(num). S2_TAILFREE (WORD_CONCAT u v) = " +
        "(S2_TAILFREE u /\\ S2_TAILFREE v)"),
    MarkedConcat ->
      ("!u:word(num). !v:word(num). 0 < WORD_LENGTH v ==> " +
        "(S2_MARKED (WORD_CONCAT u v) = (S2_TAILFREE u /\\ S2_MARKED v))")
  )

  /* ------------------------------------------------------------------ construction */

  /**
   * The development, built over [[Forward]] so that a claim about `WORD_RFC S2` is typable.
   *
   * Eight constants and no axiom. The four letters are defined before the rules that name them,
   * which is why [[Bodies]] is a vector rather than a map: a constant is reachable only from the
   * theory it was declared into, so the order is the construction and not a presentation choice.
   */
  def construct(
    forward: Forward,
    naturals: Natural,
    peano: Peano,
    base: Theory,
    notation: Notation
  ): Either[LogicError, Collatz] = {
    val introduced = Bodies.foldLeft[Either[LogicError, (Theory, Map[String, Kernel.Thm])]](
      Right((base, Map.empty))
    ) { (accumulated, entry) =>
      val (name, text) = entry
      for {
        state <- accumulated
        (theory, defined) = state
        body <- Parser.term(theory, notation, text)
        introduced <- LogicError.lift(Kernel.defineConstant(theory, name, body))
        (extended, definition) = introduced
      } yield (extended, defined + (name -> definition))
    }

    for {
      state <- introduced
      (theory, definitions) = state
      logic <- forward.inductive.classical.logic.over(theory)

      countedIsRule <- countedAreRules(logic, theory, notation, definitions)
      inhabited <- inhabitedProof(logic, theory, notation, definitions)
      refused <- refusal(
        logic, naturals, forward.concatenation, peano, theory, notation, definitions)

      numbers <- Arithmetic.of(peano, naturals)
      tailFreeDefinition <- definitions.get(TailFree).toRight(MissingDefinition(TailFree))
      markedDefinition <- definitions.get(Marked).toRight(MissingDefinition(Marked))
      tailFreeConcat <- tailFreeSplits(
        logic,
        theory,
        forward.inductive.classical,
        forward.concatenation,
        numbers,
        tailFreeDefinition
      )
      markedConcat <- markedSplits(
        logic,
        theory,
        forward.inductive.classical,
        forward.concatenation,
        numbers,
        tailFreeDefinition,
        markedDefinition
      )

      facts = Map(
        CountedIsRule -> countedIsRule,
        Inhabited -> inhabited,
        Refused -> refused,
        TailFreeConcat -> tailFreeConcat,
        MarkedConcat -> markedConcat
      )

      // Every statement checked against the text a reader reads it by, here rather than in the
      // spec, which is what `Concatenation.construct` does and for the same reason: a development
      // that built something other than what it says it built must not be handed out.
      _ <- Statements.foldLeft[Either[LogicError, Unit]](Right(())) { (accumulated, entry) =>
        val (name, text) = entry
        for {
          _ <- accumulated
          expected <- Parser.proposition(theory, notation, text)
          proved <- facts.get(name).toRight(MissingDefinition(name))
          _ <-
            if (proved.conclusion == expected && proved.hypotheses.isEmpty) Right(())
            else Left(NotOfForm(s"$name as it is written", proved.conclusion))
        } yield ()
      }
    } yield new Collatz(forward, theory, notation, definitions, facts)
  }

  /* ------------------------------------------------------------------ the arithmetic */

  /**
   * The facts about `num` the proofs below reach for, fetched once instead of threaded one by one.
   *
   * A record rather than a dozen parameters, which is what `Concatenation` does for the same reason
   * and for a set that overlaps this one: a proof about positions in a concatenation is an argument
   * about sums, differences and an order, and the word part of it is three lemmas.
   */
  private final case class Arithmetic(
    atMostSum: Kernel.Thm,
    belowThenAtMost: Kernel.Thm,
    addStrictlyMonotone: Kernel.Thm,
    addCancelsStrictOrder: Kernel.Thm,
    atMostFromNotBelow: Kernel.Thm,
    minusThenPlus: Kernel.Thm,
    addCommutative: Kernel.Thm,
    addAtSuccessor: Kernel.Thm,
    subAtZero: Kernel.Thm,
    subSuccessors: Kernel.Thm,
    oneIsSuccessorOfZero: Kernel.Thm,
    successorPositive: Kernel.Thm,
    belowSuccessor: Kernel.Thm,
    notBelowZero: Kernel.Thm,
    strictTransitive: Kernel.Thm,
    zeroOrSuccessor: Kernel.Thm
  )

  private object Arithmetic {

    def of(peano: Peano, naturals: Natural): Either[LogicError, Arithmetic] =
      for {
        atMostSum <- peano.fact(Peano.AtMostSum)
        belowThenAtMost <- peano.fact(Peano.BelowThenAtMost)
        addStrictlyMonotone <- peano.fact(Peano.AddStrictlyMonotone)
        addCancelsStrictOrder <- peano.fact(Peano.AddCancelsStrictOrder)
        atMostFromNotBelow <- peano.fact(Peano.AtMostFromNotBelow)
        minusThenPlus <- peano.fact(Peano.MinusThenPlus)
        addCommutative <- peano.fact(Peano.AddCommutative)
        addAtSuccessor <- peano.fact(Peano.AddAtSuccessor)
        subAtZero <- peano.fact(Peano.SubAtZero)
        subSuccessors <- peano.fact(Peano.SubSuccessors)
        oneIsSuccessorOfZero <- peano.fact(Peano.NumeralOneIsSuccessorOfZero)
        successorPositive <- peano.fact(Peano.SuccessorPositive)
        belowSuccessor <- peano.fact(Peano.BelowSuccessor)
        notBelowZero <- peano.fact(Peano.NotBelowZero)
        strictTransitive <- peano.fact(Peano.StrictTransitive)
        zeroOrSuccessor <- naturals.fact(Natural.ZeroOrSuccessor)
      } yield Arithmetic(
        atMostSum,
        belowThenAtMost,
        addStrictlyMonotone,
        addCancelsStrictOrder,
        atMostFromNotBelow,
        minusThenPlus,
        addCommutative,
        addAtSuccessor,
        subAtZero,
        subSuccessors,
        oneIsSuccessorOfZero,
        successorPositive,
        belowSuccessor,
        notBelowZero,
        strictTransitive,
        zeroOrSuccessor
      )
  }

  /* ------------------------------------------------------------------ the plumbing */

  /**
   * A polymorphic lemma of the word, read at the one type this development has words of.
   *
   * `Concatenation` is about `word('a)` and everything here is about `word(num)`, so every lemma
   * borrowed from it is instantiated on the way in. Done once, at the point the fact is fetched,
   * rather than at each `specAll`: an uninstantiated lemma specialised at a word of numbers is a
   * refusal naming the two types, and the refusal names the argument rather than the lemma.
   */
  private def atNumbers(theorem: Kernel.Thm): Kernel.Thm =
    Kernel.instType(Map(Classical.TypeVariable -> Numbers), theorem)

  private def leftOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._1).toRight(NotOfForm("an equation", theorem.conclusion))

  /** `|- R b c` from `|- b = a` and `|- R a c`: the relation's FIRST argument replaced. */
  private def carryLeft(
    relation: Term,
    equation: Kernel.Thm,
    other: Term,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      reversed <- Conv.sym(equation)
      moved <- Conv.apTerm(relation, reversed).flatMap(Conv.apThm(_, other))
      result <- LogicError.lift(Kernel.eqMp(moved, fact))
    } yield result

  /** `|- R i b` from `|- a = b` and `|- R i a`: the relation's SECOND argument replaced. */
  private def carryRight(
    relation: Term,
    left: Term,
    equation: Kernel.Thm,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      partial <- LogicError.lift(Term.app(relation, left))
      moved <- Conv.apTerm(partial, equation)
      result <- LogicError.lift(Kernel.eqMp(moved, fact))
    } yield result

  /** The `=` of a type, recovered from an equation built at it rather than named. */
  private def equalityAt(sample: Term, other: Term): Either[LogicError, Term] =
    LogicError.lift(Term.eq(sample, other)).flatMap {
      case App(App(equality, _), _) => Right(equality)
      case built => Left(NotOfForm("an equation", built))
    }

  /** `|- ~(b = c)` from `|- a = b` and `|- ~(a = c)`. */
  private def carryLeftNegated(
    logic: Logic,
    equation: Kernel.Thm,
    other: Term,
    fact: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      sides <- Term.destEq(equation.conclusion).toRight(NotOfForm("an equation", equation.conclusion))
      equality <- equalityAt(sides._1, other)
      moved <- Conv.apTerm(equality, equation).flatMap(Conv.apThm(_, other))
      negated <- Conv.apTerm(logic.negation, moved)
      result <- LogicError.lift(Kernel.eqMp(negated, fact))
    } yield result

  /**
   * `|- !i. i < b ==> c`, from a proof of `c` under the assumption `i < b`.
   *
   * The binder, the guard and the consequent are read out of the statement the caller asks for
   * rather than rebuilt, and what the step returns is checked against the consequent before it is
   * discharged. A step that proved something else would otherwise be generalised into a theorem
   * that is true and is not the claim, which is the failure `Bounded.prove` ends with the same
   * check against.
   */
  private def underTheBound(
    logic: Logic,
    statement: Term
  )(
    step: (FVar, Kernel.Thm) => Either[LogicError, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      predicate <- logic
        .destForallPredicate(statement)
        .toRight(NotOfForm("a claim about every index", statement))
      domain <- Type
        .destFun(Term.typeOf(predicate))
        .map(_._1)
        .toRight(NotOfForm("a predicate", predicate))
      index = Conv.freshVariable("i", domain, Term.freeVariables(statement))
      applied <- LogicError.lift(Term.app(predicate, index))
      body <- Conv.betaRoot(applied).flatMap(rightOf)
      parts <- logic.destImp(body).toRight(NotOfForm("an implication under the quantifier", body))
      (guard, consequent) = parts
      assumed <- LogicError.lift(Kernel.assume(guard))
      proved <- step(index, assumed)
      _ <-
        if (proved.conclusion == consequent) Right(())
        else Left(NotOfForm("the claim at this index as it is written", proved.conclusion))
      result <- rules.disch(guard, proved).flatMap(rules.gen(index, _))
      _ <-
        if (result.conclusion == statement) Right(())
        else Left(NotOfForm("the bounded claim as it is written", result.conclusion))
    } yield result
  }

  /* ------------------------------------------------------------------ the marked class */

  /**
   * [[TailFreeConcat]]: tail-freeness splits over a concatenation with nothing left over.
   *
   * Both halves are the same two lemmas used in opposite directions. Going left to right, an index
   * into `u` is an index into `u v` by `WORD_CONCAT_NTH_LEFT` and an index into `v` is the shifted
   * one by `WORD_CONCAT_NTH_RIGHT`; going right to left, an index into `u v` is one or the other,
   * and which it is comes from an excluded middle on `i < |u|` with the difference `i - |u|`
   * placed by `NUM_SUB_ADD`. That is the same shape `Concatenation.associativity` has and a third
   * of the size, because there are two blocks rather than three and no index arithmetic survives
   * into the answer.
   */
  private def tailFreeSplits(
    logic: Logic,
    theory: Theory,
    classical: Classical,
    concatenation: Concatenation,
    numbers: Arithmetic,
    tailFreeDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val v = Term.variable("v", Words)

    for {
      length <- concatenation.fact(Concatenation.Length).map(atNumbers)
      nthLeft <- concatenation.fact(Concatenation.NthLeft).map(atNumbers)
      nthRight <- concatenation.fact(Concatenation.NthRight).map(atNumbers)

      concatConstant <- LogicError.lift(theory.constant(Concatenation.Name, ConcatType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, LengthType))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, NthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, OrderType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, BinaryNumbers))
      minus <- LogicError.lift(theory.constant(Peano.Subtraction, BinaryNumbers))
      marker <- LogicError.lift(theory.constant(Tail, Numbers))

      joined <- LogicError.lift(Term.appAll(concatConstant, List(u, v)))
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))
      sizeU <- LogicError.lift(Term.app(lengthConstant, u))
      sizeV <- LogicError.lift(Term.app(lengthConstant, v))
      total <- LogicError.lift(Term.appAll(plus, List(sizeU, sizeV)))
      lengths <- rules.specAll(length, List(u, v))

      openedJoined <- Conv.unfold(tailFreeDefinition, List(joined))
      openedU <- Conv.unfold(tailFreeDefinition, List(u))
      openedV <- Conv.unfold(tailFreeDefinition, List(v))
      claimJoined <- leftOf(openedJoined)
      claimU <- leftOf(openedU)
      claimV <- leftOf(openedV)
      everyJoinedTerm <- rightOf(openedJoined)
      everyUTerm <- rightOf(openedU)
      everyVTerm <- rightOf(openedV)
      both <- logic.mkConj(claimU, claimV)

      /* right to left: the whole word is tail-free, so each block is */
      assumedJoined <- LogicError.lift(Kernel.assume(claimJoined))
      everyJoined <- LogicError.lift(Kernel.eqMp(openedJoined, assumedJoined))
      widened <- Conv.sym(lengths)

      onU <- underTheBound(logic, everyUTerm) { (i, below) =>
        for {
          atMost <- rules.specAll(numbers.atMostSum, List(sizeU, sizeV))
          pair <- rules.conjIntro(below, atMost)
          belowSum <- rules
            .specAll(numbers.belowThenAtMost, List(i, sizeU, total))
            .flatMap(rules.mp(_, pair))
          inJoined <- carryRight(strictOrder, i, widened, belowSum)
          notMarker <- rules.spec(i, everyJoined).flatMap(rules.mp(_, inJoined))
          entry <- rules.specAll(nthLeft, List(u, v, i)).flatMap(rules.mp(_, below))
          result <- carryLeftNegated(logic, entry, marker, notMarker)
        } yield result
      }

      onV <- underTheBound(logic, everyVTerm) { (i, below) =>
        for {
          shifted <- LogicError.lift(Term.appAll(plus, List(sizeU, i)))
          belowSum <- rules
            .specAll(numbers.addStrictlyMonotone, List(sizeU, i, sizeV))
            .flatMap(rules.mp(_, below))
          inJoined <- carryRight(strictOrder, shifted, widened, belowSum)
          notMarker <- rules.spec(shifted, everyJoined).flatMap(rules.mp(_, inJoined))
          entry <- rules.specAll(nthRight, List(u, v, i)).flatMap(rules.mp(_, below))
          result <- carryLeftNegated(logic, entry, marker, notMarker)
        } yield result
      }

      tailFreeU <- Conv.sym(openedU).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, onU)))
      tailFreeV <- Conv.sym(openedV).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, onV)))
      backward <- rules.conjIntro(tailFreeU, tailFreeV)

      /* left to right: each block is tail-free, so the whole word is */
      assumedBoth <- LogicError.lift(Kernel.assume(both))
      fromU <- rules
        .conjElim1(assumedBoth)
        .flatMap(held => LogicError.lift(Kernel.eqMp(openedU, held)))
      fromV <- rules
        .conjElim2(assumedBoth)
        .flatMap(held => LogicError.lift(Kernel.eqMp(openedV, held)))

      onJoined <- underTheBound(logic, everyJoinedTerm) { (i, below) =>
        for {
          inSum <- carryRight(strictOrder, i, lengths, below)
          belowU <- LogicError.lift(Term.appAll(strictOrder, List(i, sizeU)))

          insideU <- LogicError.lift(Kernel.assume(belowU))
          entryLeft <- rules.specAll(nthLeft, List(u, v, i)).flatMap(rules.mp(_, insideU))
          notU <- rules.spec(i, fromU).flatMap(rules.mp(_, insideU))
          firstCase <- Conv
            .sym(entryLeft)
            .flatMap(equation => carryLeftNegated(logic, equation, marker, notU))

          notInsideU <- logic.mkNot(belowU)
          assumedOutside <- LogicError.lift(Kernel.assume(notInsideU))
          atLeast <- rules
            .specAll(numbers.atMostFromNotBelow, List(i, sizeU))
            .flatMap(rules.mp(_, assumedOutside))
          difference <- LogicError.lift(Term.appAll(minus, List(i, sizeU)))
          restored <- rules
            .specAll(numbers.minusThenPlus, List(i, sizeU))
            .flatMap(rules.mp(_, atLeast))
          commuted <- rules.specAll(numbers.addCommutative, List(difference, sizeU))
          placed <- Conv.sym(commuted).flatMap(Conv.trans(_, restored))
          sumBelow <- carryLeft(strictOrder, placed, total, inSum)
          inV <- rules
            .specAll(numbers.addCancelsStrictOrder, List(sizeU, difference, sizeV))
            .flatMap(rules.mp(_, sumBelow))
          entryRight <- rules
            .specAll(nthRight, List(u, v, difference))
            .flatMap(rules.mp(_, inV))
          atIndex <- Conv
            .apTerm(nthOfJoined, placed)
            .flatMap(Conv.sym)
            .flatMap(Conv.trans(_, entryRight))
          notV <- rules.spec(difference, fromV).flatMap(rules.mp(_, inV))
          secondCase <- Conv
            .sym(atIndex)
            .flatMap(equation => carryLeftNegated(logic, equation, marker, notV))

          cases <- classical.excludedMiddleAt(belowU)
          settled <- rules.disjElim(cases, firstCase, secondCase)
        } yield settled
      }

      forward <- Conv
        .sym(openedJoined)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, onJoined)))

      equated = Kernel.deductAntisym(forward, backward)
      result <- rules.genAll(equated, List(u, v))
    } yield result
  }

  /**
   * `|- WORD_NTH w (NUM_SUB k 1) = WORD_NTH w j` where `|- k = SUC j`: the last position, placed.
   *
   * Truncated subtraction is why this is a lemma of its own rather than a step: `k - 1` is not `j`
   * for a `k` nothing says is positive, and every statement about a marked word reads its last
   * letter at `|w| - 1`. Written `SUC j` the arithmetic is three rewrites and no side condition,
   * which is the whole reason the caller obtains a successor from `NUM_CASES` first.
   */
  private def lastPosition(
    logic: Logic,
    theory: Theory,
    numbers: Arithmetic,
    size: Kernel.Thm,
    predecessor: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      minus <- LogicError.lift(theory.constant(Peano.Subtraction, BinaryNumbers))
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(Numbers, Numbers))
      )
      one <- leftOf(numbers.oneIsSuccessorOfZero)
      spelled <- LogicError.lift(Term.app(successor, predecessor))

      atSuccessor <- Conv.apTerm(minus, size).flatMap(Conv.apThm(_, one))
      partial <- LogicError.lift(Term.app(minus, spelled))
      unfolded <- Conv.apTerm(partial, numbers.oneIsSuccessorOfZero)
      peeled <- rules.specAll(numbers.subSuccessors, List(predecessor, zero))
      collapsed <- rules.spec(predecessor, numbers.subAtZero)
      result <- Conv
        .trans(atSuccessor, unfolded)
        .flatMap(Conv.trans(_, peeled))
        .flatMap(Conv.trans(_, collapsed))
    } yield result
  }

  /**
   * [[MarkedConcat]]: a marked word is a tail-free block and a marked block, and the tail is where
   * the marker is.
   *
   * Everything here runs at `|v| = SUC k`, obtained from `NUM_CASES` against the hypothesis, and
   * that is the decision worth knowing before reading it: the two positions the statement is about
   * are `|v| - 1` and `|u v| - 1`, and over a truncated subtraction neither is anything until the
   * length is known to be a successor. Written `SUC k` they are `k` and `|u| + k`, and the two
   * entry lemmas of `Concatenation` meet at exactly that pair, `WORD_CONCAT_NTH_RIGHT` being
   * already stated at a shifted index.
   *
   * The zero case is not an awkward corner, it is the statement being false there: `WORD_CONCAT u
   * WORD_EMPTY` is `u`, so the left-hand side would be `S2_MARKED u` and the right-hand side would
   * ask `S2_MARKED WORD_EMPTY`, which has no last letter. The hypothesis is what the proof spends
   * to close that branch, and it spends it against `NUM_NOT_LT_ZERO` rather than by a case split.
   */
  private def markedSplits(
    logic: Logic,
    theory: Theory,
    classical: Classical,
    concatenation: Concatenation,
    numbers: Arithmetic,
    tailFreeDefinition: Kernel.Thm,
    markedDefinition: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    val u = Term.variable("u", Words)
    val v = Term.variable("v", Words)

    for {
      length <- concatenation.fact(Concatenation.Length).map(atNumbers)
      nthLeft <- concatenation.fact(Concatenation.NthLeft).map(atNumbers)
      nthRight <- concatenation.fact(Concatenation.NthRight).map(atNumbers)

      concatConstant <- LogicError.lift(theory.constant(Concatenation.Name, ConcatType))
      lengthConstant <- LogicError.lift(theory.constant(Word.Length, LengthType))
      nthConstant <- LogicError.lift(theory.constant(Word.Nth, NthType))
      strictOrder <- LogicError.lift(theory.constant(Peano.StrictOrder, OrderType))
      plus <- LogicError.lift(theory.constant(Peano.Addition, BinaryNumbers))
      minus <- LogicError.lift(theory.constant(Peano.Subtraction, BinaryNumbers))
      successor <- LogicError.lift(
        theory.constant(Natural.NumberSuccessor, Type.fun(Numbers, Numbers))
      )
      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      marker <- LogicError.lift(theory.constant(Tail, Numbers))

      joined <- LogicError.lift(Term.appAll(concatConstant, List(u, v)))
      nthOfJoined <- LogicError.lift(Term.app(nthConstant, joined))
      nthOfV <- LogicError.lift(Term.app(nthConstant, v))
      sizeU <- LogicError.lift(Term.app(lengthConstant, u))
      sizeV <- LogicError.lift(Term.app(lengthConstant, v))
      total <- LogicError.lift(Term.appAll(plus, List(sizeU, sizeV)))
      lengths <- rules.specAll(length, List(u, v))

      positiveTerm <- LogicError.lift(Term.appAll(strictOrder, List(zero, sizeV)))
      positive <- LogicError.lift(Kernel.assume(positiveTerm))

      openedJoined <- Conv.unfold(markedDefinition, List(joined))
      openedV <- Conv.unfold(markedDefinition, List(v))
      openedU <- Conv.unfold(tailFreeDefinition, List(u))
      claimJoined <- leftOf(openedJoined)
      claimV <- leftOf(openedV)
      claimU <- leftOf(openedU)
      both <- logic.mkConj(claimU, claimV)
      equation <- LogicError.lift(Term.eq(claimJoined, both))

      /* the length is a successor, or the hypothesis is false */
      cases <- rules.spec(sizeV, numbers.zeroOrSuccessor)
      emptyBranch <- {
        for {
          disjuncts <- logic
            .destDisj(cases.conclusion)
            .toRight(NotOfForm("a disjunction", cases.conclusion))
          (isZero, _) = disjuncts
          assumed <- LogicError.lift(Kernel.assume(isZero))
          carried <- carryRight(strictOrder, zero, assumed, positive)
          nothing <- rules.spec(zero, numbers.notBelowZero)
          absurd <- rules.notElim(nothing, carried)
          result <- rules.falsityElim(equation, absurd)
        } yield result
      }

      successorBranch <- {
        val predecessor = Conv.freshVariable(
          "k",
          Numbers,
          Term.freeVariables(equation) ++ Term.freeVariables(sizeV)
        )

        for {
          disjuncts <- logic
            .destDisj(cases.conclusion)
            .toRight(NotOfForm("a disjunction", cases.conclusion))
          (_, isSuccessor) = disjuncts
          existential <- LogicError.lift(Kernel.assume(isSuccessor))
          predicate <- logic
            .destExistsPredicate(isSuccessor)
            .toRight(NotOfForm("an existential", isSuccessor))
          applied <- LogicError.lift(Term.app(predicate, predecessor))
          instance <- Conv.betaRoot(applied).flatMap(rightOf)
          size <- LogicError.lift(Kernel.assume(instance))

          proved <- markedSplitsAtSuccessor(
            logic,
            theory,
            classical,
            numbers,
            Split(u, v, joined, nthOfJoined, nthOfV, sizeU, sizeV, total, predecessor),
            (strictOrder, plus, minus, successor, marker),
            (lengths, nthLeft, nthRight),
            (openedJoined, openedV, openedU),
            (positive, size)
          )
          result <- rules.existsElim(existential, predecessor, proved)
        } yield result
      }

      settled <- rules.disjElim(cases, emptyBranch, successorBranch)
      discharged <- rules.disch(positiveTerm, settled)
      result <- rules.genAll(discharged, List(u, v))
    } yield result
  }

  /** The words, the readers and the sizes one proof about a split needs, gathered. */
  private final case class Split(
    u: Term,
    v: Term,
    joined: Term,
    nthOfJoined: Term,
    nthOfV: Term,
    sizeU: Term,
    sizeV: Term,
    total: Term,
    predecessor: Term
  )

  /** [[MarkedConcat]] with the tail's length known to be `SUC k`, which is where it is provable. */
  private def markedSplitsAtSuccessor(
    logic: Logic,
    theory: Theory,
    classical: Classical,
    numbers: Arithmetic,
    words: Split,
    constants: (Term, Term, Term, Term, Term),
    joins: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    opened: (Kernel.Thm, Kernel.Thm, Kernel.Thm),
    premises: (Kernel.Thm, Kernel.Thm)
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    import words.{u, v, joined, nthOfJoined, nthOfV, sizeU, sizeV, total, predecessor}
    val (strictOrder, plus, minus, successor, marker) = constants
    val (lengths, nthLeft, nthRight) = joins
    val (openedJoined, openedV, openedU) = opened
    val (positive, size) = premises

    for {
      claimJoined <- leftOf(openedJoined)
      claimV <- leftOf(openedV)
      claimU <- leftOf(openedU)
      both <- logic.mkConj(claimU, claimV)

      /* the two positions the statement reads, placed against the successor */
      markerV <- lastPosition(logic, theory, numbers, size, predecessor)
      shifted <- LogicError.lift(Term.appAll(plus, List(sizeU, predecessor)))
      partialU <- LogicError.lift(Term.app(plus, sizeU))
      sumIsSuccessor <- Conv
        .apTerm(partialU, size)
        .flatMap(step =>
          rules.specAll(numbers.addAtSuccessor, List(sizeU, predecessor)).flatMap(Conv.trans(step, _))
        )
      joinedIsSuccessor <- Conv.trans(lengths, sumIsSuccessor)
      markerJoined <- lastPosition(logic, theory, numbers, joinedIsSuccessor, shifted)

      /* `k < |v|`, which every reading of the tail needs */
      belowSpelled <- rules.spec(predecessor, numbers.belowSuccessor)
      inTail <- Conv
        .sym(size)
        .flatMap(equation => carryRight(strictOrder, predecessor, equation, belowSpelled))

      entryAtMarker <- rules
        .specAll(nthRight, List(u, v, predecessor))
        .flatMap(rules.mp(_, inTail))

      everyUTerm <- rightOf(openedU)
      markedJoinedTerm <- rightOf(openedJoined)
      markedVTerm <- rightOf(openedV)
      joinedParts <- threeParts(logic, markedJoinedTerm)
      (_, _, everyJoinedTerm) = joinedParts
      tailParts <- threeParts(logic, markedVTerm)
      (_, _, everyTailTerm) = tailParts

      /* left to right: the whole word is marked, so the tail is and the front is tail-free */
      assumedJoined <- LogicError.lift(Kernel.assume(claimJoined))
      markedJoined <- LogicError.lift(Kernel.eqMp(openedJoined, assumedJoined))
      restJoined <- rules.conjElim2(markedJoined)
      atMarkerJoined <- rules.conjElim1(restJoined)
      everyJoined <- rules.conjElim2(restJoined)

      atShifted <- Conv
        .apTerm(nthOfJoined, markerJoined)
        .flatMap(Conv.sym)
        .flatMap(Conv.trans(_, atMarkerJoined))
      atTail <- Conv.sym(entryAtMarker).flatMap(Conv.trans(_, atShifted))
      atMarkerTail <- Conv.apTerm(nthOfV, markerV).flatMap(Conv.trans(_, atTail))

      everyTail <- underTheBound(logic, everyTailTerm) { (i, below) =>
        for {
          belowPredecessor <- carryRight(strictOrder, i, markerV, below)
          pair <- rules.conjIntro(belowPredecessor, inTail)
          belowTail <- rules
            .specAll(numbers.strictTransitive, List(i, predecessor, sizeV))
            .flatMap(rules.mp(_, pair))
          entry <- rules.specAll(nthRight, List(u, v, i)).flatMap(rules.mp(_, belowTail))
          moved <- rules
            .specAll(numbers.addStrictlyMonotone, List(sizeU, i, predecessor))
            .flatMap(rules.mp(_, belowPredecessor))
          atIndex <- LogicError.lift(Term.appAll(plus, List(sizeU, i)))
          inRange <- Conv
            .sym(markerJoined)
            .flatMap(equation => carryRight(strictOrder, atIndex, equation, moved))
          notMarker <- rules.spec(atIndex, everyJoined).flatMap(rules.mp(_, inRange))
          result <- carryLeftNegated(logic, entry, marker, notMarker)
        } yield result
      }

      markedTail <- rules
        .conjIntro(atMarkerTail, everyTail)
        .flatMap(rules.conjIntro(positive, _))
        .flatMap(held => Conv.sym(openedV).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, held))))

      everyFront <- underTheBound(logic, everyUTerm) { (i, below) =>
        for {
          atMost <- rules.specAll(numbers.atMostSum, List(sizeU, predecessor))
          pair <- rules.conjIntro(below, atMost)
          belowShifted <- rules
            .specAll(numbers.belowThenAtMost, List(i, sizeU, shifted))
            .flatMap(rules.mp(_, pair))
          inRange <- Conv
            .sym(markerJoined)
            .flatMap(equation => carryRight(strictOrder, i, equation, belowShifted))
          notMarker <- rules.spec(i, everyJoined).flatMap(rules.mp(_, inRange))
          entry <- rules.specAll(nthLeft, List(u, v, i)).flatMap(rules.mp(_, below))
          result <- carryLeftNegated(logic, entry, marker, notMarker)
        } yield result
      }

      tailFreeFront <- Conv
        .sym(openedU)
        .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, everyFront)))
      backward <- rules.conjIntro(tailFreeFront, markedTail)

      /* right to left: a tail-free front and a marked tail make a marked word */
      assumedBoth <- LogicError.lift(Kernel.assume(both))
      fromFront <- rules
        .conjElim1(assumedBoth)
        .flatMap(held => LogicError.lift(Kernel.eqMp(openedU, held)))
      fromTail <- rules
        .conjElim2(assumedBoth)
        .flatMap(held => LogicError.lift(Kernel.eqMp(openedV, held)))
      restTail <- rules.conjElim2(fromTail)
      atMarkerOfTail <- rules.conjElim1(restTail)
      everyOfTail <- rules.conjElim2(restTail)

      zero <- LogicError.lift(theory.constant(Natural.NumberZero, Numbers))
      atMost <- LogicError.lift(theory.constant(Peano.NonStrictOrder, OrderType))
      commuted <- rules.specAll(numbers.addCommutative, List(sizeV, sizeU))
      atMostTotal <- rules
        .specAll(numbers.atMostSum, List(sizeV, sizeU))
        .flatMap(fact => carryRight(atMost, sizeV, commuted, fact))
      positiveSum <- rules
        .conjIntro(positive, atMostTotal)
        .flatMap(pair =>
          rules
            .specAll(numbers.belowThenAtMost, List(zero, sizeV, total))
            .flatMap(rules.mp(_, pair))
        )
      positiveJoined <- Conv
        .sym(lengths)
        .flatMap(equation => carryRight(strictOrder, zero, equation, positiveSum))

      atTailMarker <- Conv.apTerm(nthOfV, markerV).flatMap(Conv.sym).flatMap(Conv.trans(_, atMarkerOfTail))
      atJoinedMarker <- Conv
        .trans(entryAtMarker, atTailMarker)
        .flatMap(step => Conv.apTerm(nthOfJoined, markerJoined).flatMap(Conv.trans(_, step)))

      everyOfJoined <- underTheBound(logic, everyJoinedTerm) { (i, below) =>
        for {
          belowShifted <- carryRight(strictOrder, i, markerJoined, below)
          belowU <- LogicError.lift(Term.appAll(strictOrder, List(i, sizeU)))

          insideU <- LogicError.lift(Kernel.assume(belowU))
          entryLeft <- rules.specAll(nthLeft, List(u, v, i)).flatMap(rules.mp(_, insideU))
          notFront <- rules.spec(i, fromFront).flatMap(rules.mp(_, insideU))
          firstCase <- Conv
            .sym(entryLeft)
            .flatMap(equation => carryLeftNegated(logic, equation, marker, notFront))

          notInsideU <- logic.mkNot(belowU)
          assumedOutside <- LogicError.lift(Kernel.assume(notInsideU))
          atLeast <- rules
            .specAll(numbers.atMostFromNotBelow, List(i, sizeU))
            .flatMap(rules.mp(_, assumedOutside))
          difference <- LogicError.lift(Term.appAll(minus, List(i, sizeU)))
          restored <- rules
            .specAll(numbers.minusThenPlus, List(i, sizeU))
            .flatMap(rules.mp(_, atLeast))
          swapped <- rules.specAll(numbers.addCommutative, List(difference, sizeU))
          placed <- Conv.sym(swapped).flatMap(Conv.trans(_, restored))
          sumBelow <- carryLeft(strictOrder, placed, shifted, belowShifted)
          belowPredecessor <- rules
            .specAll(numbers.addCancelsStrictOrder, List(sizeU, difference, predecessor))
            .flatMap(rules.mp(_, sumBelow))
          pair <- rules.conjIntro(belowPredecessor, inTail)
          belowTail <- rules
            .specAll(numbers.strictTransitive, List(difference, predecessor, sizeV))
            .flatMap(rules.mp(_, pair))
          entryRight <- rules
            .specAll(nthRight, List(u, v, difference))
            .flatMap(rules.mp(_, belowTail))
          atIndex <- Conv
            .apTerm(nthOfJoined, placed)
            .flatMap(Conv.sym)
            .flatMap(Conv.trans(_, entryRight))
          belowMarker <- Conv
            .sym(markerV)
            .flatMap(equation => carryRight(strictOrder, difference, equation, belowPredecessor))
          notTail <- rules.spec(difference, everyOfTail).flatMap(rules.mp(_, belowMarker))
          secondCase <- Conv
            .sym(atIndex)
            .flatMap(equation => carryLeftNegated(logic, equation, marker, notTail))

          split <- classical.excludedMiddleAt(belowU)
          settled <- rules.disjElim(split, firstCase, secondCase)
        } yield settled
      }

      forward <- rules
        .conjIntro(atJoinedMarker, everyOfJoined)
        .flatMap(rules.conjIntro(positiveJoined, _))
        .flatMap(held => Conv.sym(openedJoined).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, held))))

      result = Kernel.deductAntisym(forward, backward)
    } yield result
  }

  /** `p /\ (q /\ r)` taken apart, which is the shape [[MarkedBody]] has. */
  private def threeParts(logic: Logic, term: Term): Either[LogicError, (Term, Term, Term)] =
    for {
      outer <- logic.destConj(term).toRight(NotOfForm("a conjunction", term))
      (first, rest) = outer
      inner <- logic.destConj(rest).toRight(NotOfForm("a conjunction", rest))
      (second, third) = inner
    } yield (first, second, third)

  /* ------------------------------------------------------------------ the proofs */

  private def statement(
    theory: Theory,
    notation: Notation,
    name: String
  ): Either[LogicError, Term] =
    Statements
      .collectFirst { case (label, text) if label == name => text }
      .toRight(MissingDefinition(name))
      .flatMap(text => Parser.proposition(theory, notation, text))

  /**
   * [[CountedIsRule]]: every clause of `S2_COUNTED` is a clause of `S2`.
   *
   * The two definitions are disjunctions over the same shape and the six of `A` are literally six
   * of the eleven, so the proof is: unfold both, assume the six-way disjunction, and in each case
   * introduce the matching disjunct of the eleven. The rewriter does the unfolding and `Minimal`
   * does the propositional step, which is the one place in this file where a search is used at all
   * and it costs nothing: the fragment is a disjunction of conjunctions of equations with no
   * negation in it.
   */
  private def countedAreRules(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      target <- statement(theory, notation, CountedIsRule)
      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      counted <- definitions.get(Counted).toRight(MissingDefinition(Counted))
      rules <- unfoldingRules(logic, Vector(system, counted))

      // Minimal decides a propositional fragment, so the two quantifiers come off first and go
      // back on at the end. What is left between them is a disjunction of conjunctions of
      // equations with no negation in it, which is exactly the fragment, and it costs no axiom --
      // the reason this proof is not `Propositional`, which would decide the same goal and charge
      // `SELECT` for a classical step it does not need.
      body <- strippedBody(logic, target)
      opened <- Rewrite.rewrite(rules, body).flatMap(rightOf)
      proved <- Minimal(logic).prove(opened)
      inBody <- shapeBack(logic, rules, body, proved)
      result <- logic.rules.gen(RightSide, inBody).flatMap(logic.rules.gen(LeftSide, _))
    } yield result

  private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
    Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

  private def unfoldingRules(
    logic: Logic,
    definitions: Vector[Kernel.Thm]
  ): Either[LogicError, Vector[Rewrite.Rule]] =
    definitions.foldLeft[Either[LogicError, Vector[Rewrite.Rule]]](Right(Vector.empty)) {
      (accumulated, definition) =>
        for {
          rules <- accumulated
          rule <- Rewrite.Rule.of(logic, definition)
        } yield rules :+ rule
    }

  private def shapeBack(
    logic: Logic,
    rules: Vector[Rewrite.Rule],
    target: Term,
    proved: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    Rewrite.rewrite(rules, target).flatMap(Conv.sym).flatMap(eq => LogicError.lift(Kernel.eqMp(eq, proved)))

  /**
   * [[Inhabited]]: the system relates something to something.
   *
   * The guard against the whole file being vacuous, and it is the cheapest of the three: `R1` is a
   * clause of the definition, so the proof is to unfold, supply that clause by reflexivity on both
   * sides, and close the two existentials at its own two words.
   */
  private def inhabitedProof(
    logic: Logic,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      target <- statement(theory, notation, Inhabited)
      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      rules <- unfoldingRules(logic, Vector(system))
      opened <- Rewrite.rewrite(rules, target).flatMap(rightOf)

      // By hand and not by a search: this is an existential, and none of the three procedures in
      // this repository takes a quantifier. The witnesses are `R1`'s own two words, so each side
      // closes by reflexivity and the only work is putting the pair under the two binders.
      left <- Parser.term(theory, notation, RuleOneLeft, Words)
      right <- Parser.term(theory, notation, RuleOneRight, Words)
      witnessed <- firstDisjunctAt(logic, opened, left, right)
      result <- shapeBack(logic, rules, target, witnessed)
    } yield result

  /**
   * The innermost body of `?l r. c1 \/ rest` proved at two witnesses, by reflexivity on `R1`.
   *
   * The disjunction is right-nested and `R1` is the first clause, so the proof is one
   * `disjIntro1` over a conjunction of two reflexivities, closed under the two existentials.
   */
  private def firstDisjunctAt(
    logic: Logic,
    existential: Term,
    left: Term,
    right: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      outer <- logic.destExistsPredicate(existential).toRight(NotOfForm("an existential", existential))
      atLeft <- LogicError.lift(Term.app(outer, left))
      openedLeft <- Conv.betaRoot(atLeft).flatMap(rightOf)
      inner <- logic.destExistsPredicate(openedLeft).toRight(NotOfForm("an existential", openedLeft))
      atRight <- LogicError.lift(Term.app(inner, right))
      body <- Conv.betaRoot(atRight).flatMap(rightOf)

      sides <- logic.destDisj(body).toRight(NotOfForm("a disjunction", body))
      (clause, rest) = sides
      pair <- logic.destConj(clause).toRight(NotOfForm("a conjunction", clause))
      (leftEq, rightEq) = pair
      leftTerm <- Term.destEq(leftEq).map(_._1).toRight(NotOfForm("an equation", leftEq))
      rightTerm <- Term.destEq(rightEq).map(_._1).toRight(NotOfForm("an equation", rightEq))
      both <- rules.conjIntro(Conv.refl(leftTerm), Conv.refl(rightTerm))
      chosen <- rules.disjIntro1(rest, both)

      closedInner <- rules.existsIntro(inner, right, chosen)
      closedOuter <- rules.existsIntro(outer, left, closedInner)
    } yield closedOuter
  }

  /** `R1`'s two words, which are the witnesses [[Inhabited]] uses, taken from the table. */
  private val RuleOneLeft: String = wordText(Rules.head.left)

  private val RuleOneRight: String = wordText(Rules.head.right)

  /**
   * [[Refused]]: the head letter on its own does not rewrite to itself.
   *
   * The half that says the eleven are a constraint. Every clause of the definition equates `l` to a
   * word of length two or three, and `WORD_SINGLETON` has length one, so each disjunct dies on the
   * lengths. `Minimal` cannot take this one: it refuses a goal with a negation in it, and this goal
   * is a negation of a disjunction of eleven conjunctions of equations between words.
   *
   * So it goes to `Propositional` instead, over the length facts as atoms. What that costs is
   * written where this repository writes such things rather than hidden: the classical decision
   * closes with double negation and charges `SELECT`, where the intuitionistic one charges nothing.
   * The trade is taken here because the alternative is eleven hand refutations that differ only in
   * which numeral they compare, and because a refusal that costs one foundational axiom is still a
   * refusal the kernel checked.
   */
  private def refusal(
    logic: Logic,
    naturals: Natural,
    concatenation: Concatenation,
    peano: Peano,
    theory: Theory,
    notation: Notation,
    definitions: Map[String, Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] =
    for {
      target <- statement(theory, notation, Refused)
      system <- definitions.get(Name).toRight(MissingDefinition(Name))
      rules <- unfoldingRules(logic, Vector(system))
      lengthRules <- lengthRuleSet(logic, concatenation, peano)
      opened <- Rewrite.rewrite(rules, target).flatMap(rightOf)

      // `Propositional` was tried here first and refuses, correctly and with the right message:
      // the atoms are uninterpreted, so the skeleton of eleven disjuncts is satisfiable and the
      // refusal says so rather than guessing. Nothing about words is propositional, which is the
      // whole content of this lemma, so the eleven are refuted one at a time on their lengths.
      disjunction <- logic.destNot(opened).toRight(NotOfForm("a negation", opened))
      contradiction <- refuteDisjunction(logic, naturals, lengthRules, disjunction)
      negated <- logic.rules.notIntro(disjunction, contradiction)
      result <- shapeBack(logic, rules, target, negated)
    } yield result

  /**
   * Every disjunct refuted, and the disjunction with it.
   *
   * Right-nested, so this walks the spine: refute the head clause, recurse on the tail, and put
   * the two cases together with `disjElim` at falsity. Eleven clauses and one shape, because every
   * clause of this system says the left side **is** a particular word.
   */
  private def refuteDisjunction(
    logic: Logic,
    naturals: Natural,
    lengthRules: Vector[Rewrite.Rule],
    disjunction: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    logic.destDisj(disjunction) match {
      case None => refuteClause(logic, naturals, lengthRules, disjunction)
      case Some((clause, rest)) =>
        for {
          here <- refuteClause(logic, naturals, lengthRules, clause)
          there <- refuteDisjunction(logic, naturals, lengthRules, rest)
          assumed <- LogicError.lift(Kernel.assume(disjunction))
          split <- rules.disjElim(assumed, here, there)
        } yield split
    }
  }

  /**
   * One clause refuted on the length of the word its left conjunct names.
   *
   * The clause is `l = w /\ r = w'` with `l` already the one-letter word this lemma is about. So
   * the left conjunct equates a word of length one with a word of length two or three, and what
   * refutes it is applying `WORD_LENGTH` to both sides and asking `Successor` whether the two
   * numerals differ. No case analysis on the letters is needed and none is done: the letters could
   * all be equal and the clause would still be false.
   */
  private def refuteClause(
    logic: Logic,
    naturals: Natural,
    lengthRules: Vector[Rewrite.Rule],
    clause: Term
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      parts <- logic.destConj(clause).toRight(NotOfForm("a conjunction", clause))
      (equation, _) = parts
      assumed <- LogicError.lift(Kernel.assume(clause))
      leftHalf <- rules.conjElim1(assumed)

      sides <- Term.destEq(equation).toRight(NotOfForm("an equation", equation))
      _ = sides
      lengthOf <- lengthFunction(logic)

      applied <- Conv.apTerm(lengthOf, leftHalf)
      computed <- Rewrite.inTheorem(lengthRules, applied)
      numerals <- Term.destEq(computed.conclusion).toRight(NotOfForm("an equation", computed.conclusion))
      (shortLength, longLength) = numerals

      falsity <- refuteSuccessors(logic, naturals, computed)
    } yield falsity
  }

  /**
   * `SUC^m 0 = SUC^n 0` with `m < n` refuted, by peeling the common successors off.
   *
   * `Successor.distinct` is the obvious tool and it is the wrong one here: it reads a numeral in
   * the bit encoding, and what the length rules produce is successor form, so it refuses with
   * "expected a numeral of num, found (SUC ZERO)". Converting to the bit encoding to ask it would
   * be a conversion in order to reach a procedure that then converts back.
   *
   * What refutes it directly is the two Peano facts the naturals already derive: strip the
   * successors both sides share with `NUM_SUC_INJECTIVE` until one side is `0`, and close with
   * `NUM_SUC_NOT_ZERO`. It terminates because each step removes one successor from each side and
   * the sides differ in how many they have.
   */
  private def refuteSuccessors(
    logic: Logic,
    naturals: Natural,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    def peel(current: Kernel.Thm): Either[LogicError, Kernel.Thm] = {
      val sides = Term.destEq(current.conclusion)
      sides match {
        case None => Left(NotOfForm("an equation", current.conclusion))
        case Some((left, right)) =>
          (successorOf(left), successorOf(right)) match {
            case (Some(innerLeft), Some(innerRight)) =>
              for {
                injective <- naturals.fact(Natural.SuccessorInjective)
                // The INNER terms, not the sides: the lemma is `SUC x = SUC y ==> x = y`, so what
                // it is specialised at is what sits under each successor. Passing the sides builds
                // a true instance about two taller numbers whose antecedent nothing here proves,
                // which is what the first version did and what the refusal named.
                stripped <- rules.specAll(injective, List(innerLeft, innerRight))
                smaller <- rules.mp(stripped, current)
                result <- peel(smaller)
              } yield result

            // One side has run out of successors, so the other is `SUC something = 0` up to
            // symmetry, which is the fact the naturals publish.
            case (Some(_), None) => closeAgainstZero(logic, naturals, current)
            case (None, Some(_)) => Conv.sym(current).flatMap(closeAgainstZero(logic, naturals, _))
            case (None, None) =>
              Left(NotOfForm("two numerals of different height", current.conclusion))
          }
      }
    }

    peel(equation)
  }

  private def successorOf(term: Term): Option[Term] = term match {
    case App(Const(Natural.NumberSuccessor, _), argument) => Some(argument)
    case _ => None
  }

  private def closeAgainstZero(
    logic: Logic,
    naturals: Natural,
    equation: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] =
    for {
      notZero <- naturals.fact(Natural.SuccessorNotZero)
      sides <- Term.destEq(equation.conclusion).toRight(NotOfForm("an equation", equation.conclusion))
      (left, _) = sides
      inner <- successorOf(left).toRight(NotOfForm("a successor", left))
      instance <- logic.rules.spec(inner, notZero)
      falsity <- logic.rules.notElim(instance, equation)
    } yield falsity

  /** `WORD_LENGTH` at this development's word type, ready to be applied to both sides. */
  private def lengthFunction(logic: Logic): Either[LogicError, Term] =
    LogicError.lift(logic.theory.constant(Word.Length, Type.fun(Words, Numbers)))

  /** `!l r. body` minus its two leading quantifiers, which is what a propositional search takes. */
  private def strippedBody(logic: Logic, target: Term): Either[LogicError, Term] =
    for {
      outer <- logic.destForallPredicate(target).toRight(NotOfForm("a quantified claim", target))
      atLeft <- LogicError.lift(Term.app(outer, LeftSide))
      openedLeft <- Conv.betaRoot(atLeft).flatMap(rightOf)
      inner <- logic.destForallPredicate(openedLeft).toRight(NotOfForm("a quantified claim", openedLeft))
      atRight <- LogicError.lift(Term.app(inner, RightSide))
      body <- Conv.betaRoot(atRight).flatMap(rightOf)
    } yield body

  /**
   * What turns a concatenation of singletons into a numeral: the two length facts and the two
   * equations that evaluate the addition.
   *
   * `WORD_CONCAT_LENGTH` turns the word into a sum, `WORD_SINGLETON_LENGTH` turns each summand into
   * `SUC 0`, and `NUM_ADD_SUC` with `NUM_ADD_ZERO` walk the sum down to a numeral in successor
   * form, which is the form `Successor.distinct` reads. Four rules and no search.
   */
  private def lengthRuleSet(
    logic: Logic,
    concatenation: Concatenation,
    peano: Peano
  ): Either[LogicError, Vector[Rewrite.Rule]] =
    for {
      concatLength <- concatenation.fact(Concatenation.Length)
      singletonLength <- concatenation.fact(Concatenation.SingletonLength)
      addSuc <- peano.fact(Peano.AddAtSuccessor)
      addZero <- peano.fact(Peano.AddAtZero)
      rules <- unfoldingRules(logic, Vector(concatLength, singletonLength, addSuc, addZero))
    } yield rules
}
