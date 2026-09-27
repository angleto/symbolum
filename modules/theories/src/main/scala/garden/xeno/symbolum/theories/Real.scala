package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The real numbers, as a complete ordered field built from the cuts on the rationals.
 *
 * Until phase 5 of `docs/adr/0007` this file asserted the sixteen propositions of [[Real.Axioms]],
 * and they were the whole of what this system asked anyone to believe about a domain.
 * `docs/adr/0004` recorded why they were asserted, and `docs/adr/0053` is what supersedes it: the
 * type `real` is `Cut`'s, each primitive constant is defined as the operation on cuts it names, and
 * each of the sixteen is proved under its old name. `axiom` still answers under those names,
 * because they are what every consumer asks for; what it hands back rests on choice, eta and
 * infinity, which the naturals and the rationals already cost, and on nothing else.
 *
 * == What is defined, and what is proved ==
 *
 * Defined: the seven primitives, each an alias of `Cut`'s (`real_add` is `CUT_ADD`), and the five
 * abbreviations over them, subtraction, division, the non-strict order and the two numeral bits.
 * Proved: the field laws, the order and completeness, each from a fact of `Cut` read through the
 * aliases, and five of them by a short argument written here.
 */
final class RealTheory private[theories] (
  val logic: Logic,
  val theory: Theory,
  val notation: Notation,
  val axioms: Map[String, Kernel.Thm],
  val definitions: Map[String, Kernel.Thm]
) extends Signature {

  /** The equation defining `name`, as proved when the constant was introduced. */
  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  /** The axiom named, as a theorem with no hypotheses. */
  def axiom(name: String): Either[LogicError, Kernel.Thm] =
    axioms.get(name).toRight(MissingDefinition(name))

  /**
   * The same theory with types and constants of a domain declared over it.
   *
   * This is how a development about something other than numbers is written without leaving the
   * arithmetic behind: declare `agent` and `payoff : agent -> real`, and everything downstream,
   * [[Arithmetic]] through [[Linarith]], builds over the result because each of those takes what it
   * is built on as an argument. What comes back is a `RealTheory`, so it is not a second kind of
   * thing that the tactics would have to learn about.
   *
   * == It costs nothing to believe ==
   *
   * Declaring is conservative: a theory full of undeclared-meaning constants proves exactly what
   * the empty one proves, so the trusted base does not move. A domain model states its assumptions as hypotheses of the theorems
   * that use them, not as axioms; `docs/proving.md` says how, and why the two are not the same.
   *
   * == What it does not give you ==
   *
   * A declared type cannot be said to be inhabited. `?x:agent. T` is not derivable and asserting it
   * would be an axiom, which is the price of the conservativity above: every domain type may, as
   * far as the theory knows, have one element.
   *
   * No notation, either. A declared constant is read and printed by its name, so `payoff a` is an
   * application like any other; an infix operator of one's own would mean a notation of one's own,
   * which is a larger thing and is not this.
   */
  def extended(
    types: Vector[(String, Int)],
    constants: Vector[(String, Type)]
  ): Either[LogicError, RealTheory] =
    for {
      withTypes <- types.foldLeft(Right(theory): Either[LogicError, Theory]) {
        case (acc, (name, arity)) =>
          acc.flatMap(current => LogicError.lift(current.declareTypeOperator(name, arity)))
      }
      withConstants <- constants.foldLeft(Right(withTypes): Either[LogicError, Theory]) {
        case (acc, (name, ty)) =>
          acc.flatMap(current => LogicError.lift(current.declareConstant(name, ty)))
      }
    } yield new RealTheory(logic, withConstants, notation, axioms, definitions)
}

object Real {

  val TypeName: String = "real"

  /**
   * The encoding's zero and one, which were the strings `"0"` and `"1"` until 2026-09-16.
   *
   * The same defect `docs/adr/0018` renamed the four operations for, and it was left behind because
   * these two belong to a different decision: `docs/adr/0012` is how a numeral is elaborated, and
   * touching these while implementing the operators' overloading would have settled the interaction
   * between two records in one commit. They are renamed here, separately, for the reason 0018 gives
   * about the others: a reader meeting `0` in a list of constants cannot tell a spelling from a
   * name, and since 2026-09-12 two encodings are declared, so `0` names one of them and not the
   * other.
   *
   * **What made this look like the case where a symbol SHOULD be the name, and is not.** The
   * obvious objection is that `0` must print as `0`, so its constant had better be called `0`. It
   * does not depend on the name at all: `Show` asks `notation.valueOfNumeral` **before** it reaches
   * the case that prints a constant's name, so a term any encoding recognises comes out as digits
   * whatever its constants are called. Measured before renaming, along with the two that matter as
   * much: nothing anywhere compares a constant's name to `"0"` or `"1"`, and the parser picks
   * between the two encodings by the **type** `one` was declared at, never by its spelling.
   */
  val Zero: String = "real_zero"
  val One: String = "real_one"

  /**
   * The four operations whose symbol used to be their name.
   *
   * `Addition` was the string `"+"` until `docs/adr/0018`, so the reals' addition was a constant
   * **named** `+`, and `*` and `<` the same. That was harmless while one type owned the symbols and
   * became a trap the moment two did: a reader meeting `+` in a list of constants, in
   * `docs/reading-register.md` or in a refusal, cannot tell whether it is a spelling or a name.
   * `NonStrictOrder` was already `"le"` and is renamed only so the four read alike.
   *
   * The symbols are unchanged and live where they belong, in the notation below. Nothing a reader
   * of a statement sees moves: `x + y` still prints `x + y`, because the printer is keyed by
   * constant and asks the notation what to spell it with.
   */
  val Addition: String = "real_add"
  val Multiplication: String = "real_mul"
  val Order: String = "real_lt"
  val NonStrictOrder: String = "real_le"

  val Negation: String = "neg"
  val Inverse: String = "inv"
  val Subtraction: String = "sub"
  val Division: String = "div"
  val Bit0: String = "BIT0"
  val Bit1: String = "BIT1"

  /**
   * The type of a real number, as one declaration everything else cites.
   *
   * Public since 2026-09-11, when [[Linarith]] was split and the copy it carried under the name
   * `realType` had to go somewhere. It was already this object's own private `real`, and making it
   * visible is the difference between one spelling of the type and two. Fifteen other files still
   * build `TyApp(Real.TypeName, Nil)` into a private `val` of their own; those are older than this
   * and are left alone rather than converged in a change about linear arithmetic.
   */
  val realType: Type = TyApp(TypeName, Nil)

  /**
   * Precedences, above those of the logic so that arithmetic binds tighter than any connective.
   *
   * `x + y = y + x` has to read as `(x + y) = (y + x)`, so `+` sits above equality; `x + y * z`
   * has to read as `x + (y * z)`, so multiplication sits above addition; and unary negation binds
   * tightest of all so that `-x * y` is `(-x) * y`.
   *
   * Three of the four are public since `docs/adr/0018`, and that is the record's shape rather than
   * a convenience. A symbol carries one precedence however many constants it stands for, because
   * the reader picks the precedence before anything is known about types and therefore cannot pick
   * it per candidate. So a development that overloads one of these symbols must declare it at the
   * precedence written here, and reading it from here is what makes "the same" mechanical instead
   * of a number copied and left to drift. Negation is not overloaded and stays private.
   */
  val OrderPrecedence: Int = 50
  val AdditionPrecedence: Int = 60
  val MultiplicationPrecedence: Int = 70
  private val NegationPrecedence: Int = 80

  /**
   * The abbreviations, in the order they are introduced.
   *
   * Each is a definitional extension and adds nothing to the trusted base: every theorem
   * mentioning one has a counterpart that does not.
   */
  private val Definitions: Vector[(String, String)] = Vector(
    // The binary numerals: `2` is `BIT0 1`, `3` is `BIT1 1`, `12` is `BIT0 (BIT0 (BIT1 1))`.
    // Definitions, so the numerals cost nothing in the trusted base, and stated over the reals
    // because that is the only type THIS development has. The sentence that used to follow said
    // there was no separate type of naturals to embed and that introducing one would need type
    // definitions the kernel did not have; both halves stopped being true on 2026-09-10, and
    // `Peano` declares a second encoding of exactly this shape over `num` since 2026-09-12. What
    // survives is the scope: these four names are the reals' and a development that wants numerals
    // at another type declares its own, which is why the parser picks by type rather than by
    // finding one table.
    Bit0 -> "\\x:real. x + x",
    Bit1 -> "\\x:real. (x + x) + 1",
    Subtraction -> "\\x:real y:real. x + -y",
    Division -> "\\x:real y:real. x * inv y",
    NonStrictOrder -> "\\x:real y:real. x < y \\/ x = y"
  )

  /**
   * The sixteen statements of a complete ordered field, by name, each proved by [[construct]].
   *
   * They were asserted until phase 5, and this list was then the only check on them: a mis-stated
   * axiom makes everything provable and every test would still pass. A mis-stated one now fails to
   * be proved, so the construction refuses to build; what reading them against a textbook still
   * checks is that they say what a complete ordered field is, which no derivation can.
   */
  val Axioms: Vector[(String, String)] = Vector(
    // A field.
    "ADD_SYM" -> "!x:real y:real. x + y = y + x",
    "ADD_ASSOC" -> "!x:real y:real z:real. (x + y) + z = x + (y + z)",
    "ADD_ZERO" -> "!x:real. x + 0 = x",
    "ADD_INVERSE" -> "!x:real. x + -x = 0",
    "MUL_SYM" -> "!x:real y:real. x * y = y * x",
    "MUL_ASSOC" -> "!x:real y:real z:real. (x * y) * z = x * (y * z)",
    "MUL_ONE" -> "!x:real. x * 1 = x",
    "MUL_INVERSE" -> "!x:real. ~(x = 0) ==> x * inv x = 1",
    "DISTRIBUTE" -> "!x:real y:real z:real. x * (y + z) = x * y + x * z",
    "ONE_NOT_ZERO" -> "~(1 = 0)",

    // Ordered, and the order agrees with the operations.
    "LT_IRREFLEXIVE" -> "!x:real. ~(x < x)",
    "LT_TRANSITIVE" -> "!x:real y:real z:real. x < y /\\ y < z ==> x < z",
    "LT_TOTAL" -> "!x:real y:real. x < y \\/ x = y \\/ y < x",
    "LT_ADD" -> "!x:real y:real z:real. x < y ==> x + z < y + z",
    "LT_MUL" -> "!x:real y:real. 0 < x /\\ 0 < y ==> 0 < x * y",

    // Complete: a non-empty set with an upper bound has a least one. Stated over predicates,
    // because a set is a predicate and this logic has no separate notion of one.
    "COMPLETENESS" ->
      ("!P:real->bool. (?x:real. P x) /\\ (?b:real. !x:real. P x ==> x <= b) ==> " +
        "(?s:real. (!x:real. P x ==> x <= s) /\\ (!b:real. (!x:real. P x ==> x <= b) ==> s <= b))")
  )

  /** The notation: how each constant is written. */
  def notation: Notation =
    Notation.standard
      .withInfix("<", Order, OrderPrecedence)
      .withInfix("<=", NonStrictOrder, OrderPrecedence)
      // `>` and `>=` are read and never written. The theory has one order relation and gains no
      // constant here: `a > b` builds the same term as `b < a`, to the node, so every lemma about
      // `<` covers it and there is nothing new to axiomatise. Added 2026-09-09, after a session
      // checking a corpus wrote `30 > 10` and was told "cannot read the character '>'" -- true,
      // and no help at all, since what it needed to know was that the relation is spelled the
      // other way round.
      .withFlippedInfix(">", Order, OrderPrecedence)
      .withFlippedInfix(">=", NonStrictOrder, OrderPrecedence)
      .withInfix("+", Addition, AdditionPrecedence)
      .withInfix("-", Subtraction, AdditionPrecedence)
      .withInfix("*", Multiplication, MultiplicationPrecedence)
      .withInfix("/", Division, MultiplicationPrecedence)
      .withPrefix("-", Negation, NegationPrecedence)
      .withNumerals(Zero, One, Bit0, Bit1)

  /**
   * What the reals are built from, one link each, the reals last.
   *
   * The naturals, the arithmetic of `num` that names no real, the pairs, the integers, the
   * rationals and the cuts: the order is `docs/adr/0016`'s, and it is the head of `Chain` too, which
   * builds its own over the logic it is handed and shares this one when that logic is the standard.
   */
  final class Construction private[theories] (
    val naturals: Natural,
    val pure: PureArithmetic,
    val product: Product,
    val integers: Integer,
    val fractions: Fraction,
    val cuts: Cut,
    val reals: RealTheory
  )

  /** The construction over a classical logic and the naturals built on it. */
  def construction(classical: Classical, naturals: Natural): Either[LogicError, Construction] =
    for {
      pure <- Peano.pure(naturals)
      product <- Product.construct(classical, pure.theory, pure.notation)
      integers <- Integer.construct(classical, pure, product, product.theory, pure.notation)
      fractions <- Fraction.construct(classical, integers, product, pure)
      cuts <- Cut.construct(fractions, pure)
      reals <- construct(classical.logic, cuts)
    } yield new Construction(naturals, pure, product, integers, fractions, cuts, reals)

  /**
   * The construction over the standard classical logic, built once.
   *
   * A failure is a defect in the construction rather than a condition a caller could handle, so it
   * is raised; [[construction]] is public so a test can assert it succeeds without provoking an
   * initialisation error to find out.
   */
  lazy val constructed: Construction =
    construction(Classical.standard, Natural.standard).fold(
      error => throw new IllegalStateException(s"the reals do not build: ${error.message}"),
      identity
    )

  /**
   * The theory of the reals, as the construction leaves it.
   *
   * It sat over `Logic.standard` with its sixteen asserted until phase 5, so a development about the
   * reals was not asked to believe the choice operator; a construction cannot offer that, since the
   * cuts are carved and the rationals quotiented, and both spend choice. What it asks instead is the
   * three the naturals cost, which is fewer than the sixteen it replaces.
   */
  lazy val standard: RealTheory = constructed.reals

  /** The sixteen statements, as the terms the construction proved. */
  lazy val sixteen: Set[Term] = Axioms.map { case (name, _) => standard.axioms(name).conclusion }.toSet

  /**
   * What a theorem spends, the sixteen read as the reals' interface: the foundation's axioms it
   * reaches outside them, and those of the sixteen it rests on. It is what `Derivation.axiomsOf`
   * answered while the sixteen were asserted, and `Derivation.axiomsOf` with an interface is why it
   * still can; a theorem built over another construction of the reals is read the same way, since
   * its sixteen are the same terms.
   */
  def spent(theorem: Kernel.Thm): Set[Term] = Derivation.axiomsOf(theorem, sixteen)

  /**
   * The seven primitive constants, each defined as the operation of `Cut` it names.
   *
   * An alias rather than a renaming: `Cut` publishes its facts about `CUT_ADD`, and what the
   * statements of [[Axioms]] say about `real_add` is the same fact once the definition is unfolded.
   */
  private val Aliases: Vector[(String, String)] = Vector(
    Zero -> "CUT_OF_RAT RAT_ZERO",
    One -> "CUT_OF_RAT RAT_ONE",
    Addition -> "CUT_ADD",
    Multiplication -> "CUT_MUL",
    Negation -> "CUT_NEG",
    Inverse -> "CUT_INV",
    Order -> "CUT_LT"
  )

  /**
   * The axioms that are a fact of `Cut` word for word once the aliases, `<` and `<=` are unfolded.
   *
   * The five absent are proved in [[Constructed]]: `ONE_NOT_ZERO` from the injectivity of the
   * embedding, and the four about the strict order from the facts about `CUT_LE` it abbreviates.
   */
  private val Readings: Map[String, String] = Map(
    "ADD_SYM" -> Cut.AddCommutative,
    "ADD_ASSOC" -> Cut.AddAssociative,
    "ADD_ZERO" -> Cut.AddZero,
    "ADD_INVERSE" -> Cut.AddNegation,
    "MUL_SYM" -> Cut.MulCommutative,
    "MUL_ASSOC" -> Cut.MulAssociative,
    "MUL_ONE" -> Cut.MulOne,
    "MUL_INVERSE" -> Cut.MulInverse,
    "DISTRIBUTE" -> Cut.MulDistributive,
    "LT_MUL" -> Cut.LessMul,
    "COMPLETENESS" -> Cut.Complete
  )

  /**
   * The reals built from the cuts: the same constants, the same notation and the same sixteen
   * statements, and not one of them asserted.
   *
   * `cuts.theory` already holds the type `real`, carved by `Cut` out of `rat -> bool`, so nothing is
   * declared here. Each primitive constant is defined as the operation it names, the
   * abbreviations of [[Definitions]] follow exactly as over an asserted theory, and each statement
   * of [[Axioms]] is proved: unfolded to a statement about the cuts and compared, as a term, with
   * the theorem that proves it. `axiom` still answers under the sixteen names, which is what every
   * consumer asks for; what it hands back is a theorem that rests on the foundation, choice, eta and
   * infinity, and on nothing about the reals. Each is cited under its name, as every published fact
   * is, so a report over a proof stops at `ADD_SYM` rather than walking into the cuts, which is what
   * it showed while the sixteen were axioms. `docs/adr/0053` is the decision.
   */
  def construct(logic: Logic, cuts: Cut): Either[LogicError, RealTheory] = {
    val syntax = notation

    def alias(theory: Theory): Either[LogicError, (Theory, Map[String, Kernel.Thm])] =
      Aliases.foldLeft(
        Right((theory, Map.empty[String, Kernel.Thm])): Either[LogicError, (Theory, Map[String, Kernel.Thm])]
      ) {
        case (acc, (name, text)) =>
          for {
            current <- acc
            body <- Parser.term(current._1, cuts.notation, text)
            extended <- LogicError.lift(Kernel.defineConstant(current._1, name, body))
          } yield (extended._1, current._2.updated(name, extended._2))
      }

    def define(theory: Theory): Either[LogicError, (Theory, Map[String, Kernel.Thm])] =
      Definitions.foldLeft(
        Right((theory, Map.empty[String, Kernel.Thm])): Either[LogicError, (Theory, Map[String, Kernel.Thm])]
      ) {
        case (acc, (name, text)) =>
          for {
            current <- acc
            body <- Parser.term(current._1, syntax, text)
            extended <- LogicError.lift(Kernel.defineConstant(current._1, name, body))
          } yield (extended._1, current._2.updated(name, extended._2))
      }

    for {
      aliased <- alias(cuts.theory)
      defined <- define(aliased._1)
      theory = defined._1
      definitions = aliased._2 ++ defined._2
      constructed = new Constructed(cuts)
      unfolding <- constructed.unfolding(definitions)
      axioms <- Axioms.foldLeft(Right(Map.empty[String, Kernel.Thm]): Either[LogicError, Map[String, Kernel.Thm]]) {
        case (acc, (name, text)) =>
          for {
            done <- acc
            statement <- Parser.proposition(theory, syntax, text)
            source <- Readings.get(name) match {
              case Some(fact) => cuts.fact(fact)
              case None => constructed.proof(name)
            }
            proved <- unfolding.carry(name, statement, source)
          } yield done.updated(name, proved)
      }
    } yield new RealTheory(logic, theory, syntax, Published.cite(axioms), definitions)
  }

  /**
   * What turns a fact about the cuts into one of the sixteen, and the five that are not a fact of
   * `Cut` as they stand.
   *
   * Unfolding goes one way only, from the statement towards the cuts: the aliases and `<=` first,
   * then `CUT_LT` into the negation of `CUT_LE` it abbreviates, and last `x < y \/ x = y` into
   * `CUT_LE x y`, which is the one step that is a lemma rather than a definition and is proved here
   * as [[Constructed.atMost]]. The source theorem's conclusion is unfolded by the same conversion,
   * so a fact of `Cut` written with `CUT_LT` and one written with `~(CUT_LE ...)` meet at one term,
   * and the comparison of the two normal forms is the whole check.
   */
  private final class Constructed(cuts: Cut) {
    private val rules = cuts.logic.rules
    private val x = Term.variable("x", Cut.Classes)
    private val y = Term.variable("y", Cut.Classes)
    private val z = Term.variable("z", Cut.Classes)

    private def prop(text: String): Either[LogicError, Term] = cuts.proposition(text)
    private def fact(name: String): Either[LogicError, Kernel.Thm] = cuts.fact(name)
    private def assume(text: String): Either[LogicError, Kernel.Thm] =
      prop(text).flatMap(t => LogicError.lift(Kernel.assume(t)))

    /** Nothing is sorted: every rule here is used left to right, so the order is never consulted. */
    private val unordered: Ordering[Term] = Ordering.by(_.toString)

    private def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
      Term.destEq(theorem.conclusion).map(_._2).toRight(NotOfForm("an equation", theorem.conclusion))

    final class Unfolding(first: Rewrite.Conversion, second: Rewrite.Conversion) {
      private def normalForm(term: Term): Either[LogicError, Kernel.Thm] =
        for {
          outer <- first(term)
          middle <- rightOf(outer)
          inner <- second(middle)
          both <- Conv.trans(outer, inner)
        } yield both

      def carry(name: String, statement: Term, source: Kernel.Thm): Either[LogicError, Kernel.Thm] =
        for {
          wanted <- normalForm(statement)
          held <- second(source.conclusion)
          reading <- rightOf(wanted)
          reached <- rightOf(held)
          _ <- Either.cond(
            reading == reached,
            (),
            NotOfForm(s"$name read on the cuts", reached)
          )
          onCuts <- LogicError.lift(Kernel.eqMp(held, source))
          back <- Conv.sym(wanted)
          result <- LogicError.lift(Kernel.eqMp(back, onCuts))
        } yield result
    }

    def unfolding(definitions: Map[String, Kernel.Thm]): Either[LogicError, Unfolding] =
      for {
        outer <- (Aliases.map(_._1) :+ NonStrictOrder).foldLeft(Right(Vector.empty): Either[LogicError, Vector[Kernel.Thm]]) {
          (acc, name) => acc.flatMap(done => definitions.get(name).toRight(MissingDefinition(name)).map(done :+ _))
        }
        outerRules <- Rewrite.Rule.all(cuts.logic, outer)
        lessThan <- cuts.definition(Cut.LessThan)
        between <- atMost
        innerRules <- Rewrite.Rule.all(cuts.logic, Vector(lessThan, between))
      } yield new Unfolding(
        Rewrite.normaliser(outerRules, Vector.empty, unordered),
        Rewrite.normaliser(innerRules, Vector.empty, unordered)
      )

    /** `!x y. (~(CUT_LE y x) \/ x = y) = CUT_LE x y`: the non-strict order, read on the cuts. */
    def atMost: Either[LogicError, Kernel.Thm] =
      for {
        either <- prop("~(CUT_LE y x) \\/ x = y")
        atMostTerm <- prop("CUT_LE x y")
        above <- prop("CUT_LE y x")
        notAbove <- prop("~(CUT_LE y x)")
        equal <- prop("(x:real) = (y:real)")
        // From the disjunction to the order: a cut not above `x` is above it, by totality, and an
        // equal one is reflexivity.
        heldEither <- LogicError.lift(Kernel.assume(either))
        heldNotAbove <- LogicError.lift(Kernel.assume(notAbove))
        total <- fact(Cut.AtMostTotal).flatMap(rules.specAll(_, List(x, y)))
        heldAtMost <- LogicError.lift(Kernel.assume(atMostTerm))
        heldAbove <- LogicError.lift(Kernel.assume(above))
        absurd <- rules.notElim(heldNotAbove, heldAbove)
        fromAbove <- rules.falsityElim(atMostTerm, absurd)
        fromNotAbove <- rules.disjElim(total, heldAtMost, fromAbove)
        heldEqual <- LogicError.lift(Kernel.assume(equal))
        reflexive <- fact(Cut.AtMostReflexive).flatMap(rules.spec(x, _))
        moved <- atMostTerm match {
          case App(relation, _) => Conv.apTerm(relation, heldEqual)
          case other => Left(NotOfForm("a comparison", other))
        }
        fromEqual <- LogicError.lift(Kernel.eqMp(moved, reflexive))
        forwards <- rules.disjElim(heldEither, fromNotAbove, fromEqual)
        // Back: where `y <= x` as well, antisymmetry gives the equation; otherwise the left side.
        antisymmetric <- fact(Cut.AtMostAntisymmetric).flatMap(rules.specAll(_, List(x, y)))
        equation <- rules.mp(antisymmetric, heldAtMost).flatMap(rules.mp(_, heldAbove))
        rightCase <- rules.disjIntro2(notAbove, equation)
        leftCase <- rules.disjIntro1(equal, heldNotAbove)
        backwards <- cuts.classical.cases(above, rightCase, leftCase)
        both = Kernel.deductAntisym(backwards, forwards)
        result <- rules.genAll(both, List(x, y))
      } yield result

    def proof(name: String): Either[LogicError, Kernel.Thm] = name match {
      case "ONE_NOT_ZERO" => oneNotZero
      case "LT_IRREFLEXIVE" => irreflexive
      case "LT_TRANSITIVE" => transitive
      case "LT_TOTAL" => total
      case "LT_ADD" => additive
      case other => Left(MissingDefinition(other))
    }

    /** `~(CUT_OF_RAT RAT_ONE = CUT_OF_RAT RAT_ZERO)`, from injectivity and the rationals' own. */
    private def oneNotZero: Either[LogicError, Kernel.Thm] =
      for {
        collapse <- prop("CUT_OF_RAT RAT_ONE = CUT_OF_RAT RAT_ZERO")
        held <- LogicError.lift(Kernel.assume(collapse))
        one <- cuts.term("RAT_ONE", Fraction.Classes)
        zero <- cuts.term("RAT_ZERO", Fraction.Classes)
        units <- fact(Cut.OfRationalInjective).flatMap(rules.specAll(_, List(one, zero))).flatMap(rules.mp(_, held))
        swapped <- Conv.sym(units)
        absurd <- cuts.fractions.fact(Fraction.UnitsDistinct).flatMap(rules.notElim(_, swapped))
        result <- rules.notIntro(collapse, absurd)
      } yield result

    /** `!x. ~~(CUT_LE x x)`, which is `~(x < x)` unfolded. */
    private def irreflexive: Either[LogicError, Kernel.Thm] =
      for {
        denial <- prop("~(CUT_LE x x)")
        held <- LogicError.lift(Kernel.assume(denial))
        reflexive <- fact(Cut.AtMostReflexive).flatMap(rules.spec(x, _))
        absurd <- rules.notElim(held, reflexive)
        result <- rules.notIntro(denial, absurd).flatMap(rules.gen(x, _))
      } yield result

    /** `x < y /\ y < z ==> x < z` unfolded: were `z <= x`, totality puts `x <= y` and so `z <= y`. */
    private def transitive: Either[LogicError, Kernel.Thm] =
      for {
        both <- prop("~(CUT_LE y x) /\\ ~(CUT_LE z y)")
        held <- LogicError.lift(Kernel.assume(both))
        notYX <- rules.conjElim1(held)
        notZY <- rules.conjElim2(held)
        zx <- prop("CUT_LE z x")
        heldZX <- LogicError.lift(Kernel.assume(zx))
        total <- fact(Cut.AtMostTotal).flatMap(rules.specAll(_, List(x, y)))
        heldXY <- assume("CUT_LE x y")
        zy <- fact(Cut.AtMostTransitive).flatMap(rules.specAll(_, List(z, x, y)))
          .flatMap(rules.mp(_, heldZX)).flatMap(rules.mp(_, heldXY))
        first <- rules.notElim(notZY, zy)
        heldYX <- assume("CUT_LE y x")
        second <- rules.notElim(notYX, heldYX)
        absurd <- rules.disjElim(total, first, second)
        denied <- rules.notIntro(zx, absurd)
        result <- rules.disch(both, denied).flatMap(rules.genAll(_, List(x, y, z)))
      } yield result

    /** `x < y \/ x = y \/ y < x` unfolded, by cases on `y <= x` and then on `x <= y`. */
    private def total: Either[LogicError, Kernel.Thm] =
      for {
        above <- prop("CUT_LE y x")
        below <- prop("CUT_LE x y")
        notAbove <- prop("~(CUT_LE y x)")
        notBelow <- prop("~(CUT_LE x y)")
        equal <- prop("(x:real) = (y:real)")
        rest <- prop("x = y \\/ ~(CUT_LE x y)")
        heldNotAbove <- LogicError.lift(Kernel.assume(notAbove))
        whenNotAbove <- rules.disjIntro1(rest, heldNotAbove)
        heldAbove <- LogicError.lift(Kernel.assume(above))
        heldBelow <- LogicError.lift(Kernel.assume(below))
        equation <- fact(Cut.AtMostAntisymmetric).flatMap(rules.specAll(_, List(x, y)))
          .flatMap(rules.mp(_, heldBelow)).flatMap(rules.mp(_, heldAbove))
        whenBelow <- rules.disjIntro1(notBelow, equation).flatMap(rules.disjIntro2(notAbove, _))
        heldNotBelow <- LogicError.lift(Kernel.assume(notBelow))
        whenNotBelow <- rules.disjIntro2(equal, heldNotBelow).flatMap(rules.disjIntro2(notAbove, _))
        whenAbove <- cuts.classical.cases(below, whenBelow, whenNotBelow)
        split <- cuts.classical.cases(above, whenAbove, whenNotAbove)
        result <- rules.genAll(split, List(x, y))
      } yield result

    /** `x < y ==> x + z < y + z` unfolded: adding `-z` to `y + z <= x + z` gives `y <= x`. */
    private def additive: Either[LogicError, Kernel.Thm] =
      for {
        notAbove <- prop("~(CUT_LE y x)")
        held <- LogicError.lift(Kernel.assume(notAbove))
        shifted <- prop("CUT_LE (CUT_ADD y z) (CUT_ADD x z)")
        heldShifted <- LogicError.lift(Kernel.assume(shifted))
        yz <- cuts.term("CUT_ADD y z", Cut.Classes)
        xz <- cuts.term("CUT_ADD x z", Cut.Classes)
        negZ <- cuts.term("CUT_NEG z", Cut.Classes)
        added <- fact(Cut.AtMostAdd).flatMap(rules.specAll(_, List(yz, xz, negZ))).flatMap(rules.mp(_, heldShifted))
        cancel <- cancellation
        cancelRules <- Rewrite.Rule.all(cuts.logic, Vector(cancel))
        tidied <- Rewrite.normaliser(cancelRules, Vector.empty, unordered)(added.conclusion)
        above <- LogicError.lift(Kernel.eqMp(tidied, added))
        absurd <- rules.notElim(held, above)
        denied <- rules.notIntro(shifted, absurd)
        result <- rules.disch(notAbove, denied).flatMap(rules.genAll(_, List(x, y, z)))
      } yield result

    /** `!x z. CUT_ADD (CUT_ADD x z) (CUT_NEG z) = x`, from the group laws `Cut` publishes. */
    private def cancellation: Either[LogicError, Kernel.Thm] =
      for {
        negZ <- cuts.term("CUT_NEG z", Cut.Classes)
        associated <- fact(Cut.AddAssociative).flatMap(rules.specAll(_, List(x, z, negZ)))
        inverse <- fact(Cut.AddNegation).flatMap(rules.spec(z, _))
        addX <- cuts.term("CUT_ADD x", Type.fun(Cut.Classes, Cut.Classes))
        inside <- Conv.apTerm(addX, inverse)
        zero <- fact(Cut.AddZero).flatMap(rules.spec(x, _))
        result <- Conv.trans(associated, inside).flatMap(Conv.trans(_, zero)).flatMap(rules.genAll(_, List(x, z)))
      } yield result
  }
}
