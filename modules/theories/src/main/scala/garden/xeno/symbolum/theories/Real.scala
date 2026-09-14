package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * The real numbers, as a complete ordered field asserted by axiom.
 *
 * This is where the trusted base grows for the first time since the kernel. Everything before it
 * is definitional: the logic's eight connectives add no axiom, and neither does anything derived
 * from them. The propositions in [[Real.Axioms]] are believed rather than proved, and they are the
 * whole of what this system asks anyone to believe beyond the ten inference rules.
 *
 * The decision to assert them rather than construct the reals from the naturals is recorded, with
 * what it costs, in `docs/adr/0004-reals-axiomatised-not-constructed.md`. The short version: the
 * construction is months of work upstream of every result the project wants, and the risk it
 * removes is bounded here by three things instead. The axioms are in one file. They are written in
 * the concrete syntax a person can check against a textbook rather than as builder calls nobody
 * reads. And a test pins the printed form of each of them and scans the sources for any other
 * call of `assertAxiom`, so the list can neither change nor grow by accident.
 *
 * == What is asserted and what is defined ==
 *
 * Asserted: the field operations, the order, and completeness. Defined, and therefore adding
 * nothing to what has to be believed: subtraction, division and the non-strict order, each an
 * abbreviation for a combination of the asserted ones.
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
   * the empty one proves, so the sixteen axioms stay sixteen and `RealSpec`'s scan still finds
   * `assertAxiom` in one file. A domain model states its assumptions as hypotheses of the theorems
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
  val Zero: String = "0"
  val One: String = "1"
  val Addition: String = "+"
  val Multiplication: String = "*"
  val Negation: String = "neg"
  val Inverse: String = "inv"
  val Order: String = "<"
  val Subtraction: String = "sub"
  val Division: String = "div"
  val NonStrictOrder: String = "le"
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

  private val binary: Type = Type.fun(realType, Type.fun(realType, realType))
  private val relation: Type = Type.fun(realType, Type.fun(realType, Type.Bool))

  /**
   * Precedences, above those of the logic so that arithmetic binds tighter than any connective.
   *
   * `x + y = y + x` has to read as `(x + y) = (y + x)`, so `+` sits above equality; `x + y * z`
   * has to read as `x + (y * z)`, so multiplication sits above addition; and unary negation binds
   * tightest of all so that `-x * y` is `(-x) * y`.
   */
  private val OrderPrecedence: Int = 50
  private val AdditionPrecedence: Int = 60
  private val MultiplicationPrecedence: Int = 70
  private val NegationPrecedence: Int = 80

  /**
   * The constants this theory introduces without defining them.
   *
   * Declaring a constant is conservative: an uninterpreted name proves nothing. What these cost is
   * paid by the axioms below, which say what they mean.
   */
  private val Declarations: Vector[(String, Type)] = Vector(
    Zero -> realType,
    One -> realType,
    Addition -> binary,
    Multiplication -> binary,
    Negation -> Type.fun(realType, realType),
    Inverse -> Type.fun(realType, realType),
    Order -> relation
  )

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
   * The axioms, by name.
   *
   * Read them against a source. That is the point of writing them this way, and it is the only
   * check there is on this list: a mis-stated axiom makes everything provable, and every test in
   * this repository would still pass.
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
      .withInfix(Order, Order, OrderPrecedence)
      .withInfix("<=", NonStrictOrder, OrderPrecedence)
      // `>` and `>=` are read and never written. The theory has one order relation and gains no
      // constant here: `a > b` builds the same term as `b < a`, to the node, so every lemma about
      // `<` covers it and there is nothing new to axiomatise. Added 2026-09-09, after a session
      // checking a corpus wrote `30 > 10` and was told "cannot read the character '>'" -- true,
      // and no help at all, since what it needed to know was that the relation is spelled the
      // other way round.
      .withFlippedInfix(">", Order, OrderPrecedence)
      .withFlippedInfix(">=", NonStrictOrder, OrderPrecedence)
      .withInfix(Addition, Addition, AdditionPrecedence)
      .withInfix("-", Subtraction, AdditionPrecedence)
      .withInfix(Multiplication, Multiplication, MultiplicationPrecedence)
      .withInfix("/", Division, MultiplicationPrecedence)
      .withPrefix("-", Negation, NegationPrecedence)
      .withNumerals(Zero, One, Bit0, Bit1)

  /**
   * The theory.
   *
   * Built once. A failure is a defect in this file rather than a condition a caller could handle,
   * so it is raised; [[construct]] is public so a test can assert it succeeds without provoking an
   * initialisation error to find out.
   */
  lazy val standard: RealTheory =
    construct().fold(
      error => throw new IllegalStateException(s"the theory of the reals does not build: ${error.message}"),
      identity
    )

  /** Build the theory over the plain logic: declare, define, then assert. */
  def construct(): Either[LogicError, RealTheory] =
    construct(Logic.standard, Logic.standard.theory)

  /**
   * The same, over a theory that already holds something else.
   *
   * The reals and the naturals were two chains from one root until 2026-09-10, and a chain cannot
   * see the other's names: `Natural.standard.theory` cannot read a theorem about the reals and the
   * reals cannot read one about the naturals, so no theory existed in which a function from one to
   * the other could even be stated. Measured, not argued: the two share exactly `bool`, `fun` and
   * the nine logical constants, agreeing on every one of them, which is why mixing their theorems
   * happens to be harmless and why nothing detects that it is.
   *
   * This is how they are put in one chain instead. A caller wanting both builds the reals over
   * `Classical`, and the naturals over the result, and everything then lives in one signature.
   *
   * **`Real.standard` deliberately does not do that.** It stays over `Logic.standard`, which has no
   * axioms, so a development about the reals is not asked to believe the choice operator. The two
   * configurations are the point rather than an oversight, and `ClassicalSpec` asserts the first.
   */
  def construct(logic: Logic, base: Theory): Either[LogicError, RealTheory] = {
    val syntax = notation

    def declare(theory: Theory): Either[LogicError, Theory] =
      Declarations.foldLeft(LogicError.lift(theory.declareTypeOperator(TypeName, 0))) {
        case (acc, (name, ty)) => acc.flatMap(current => LogicError.lift(current.declareConstant(name, ty)))
      }

    def define(
      theory: Theory
    ): Either[LogicError, (Theory, Map[String, Kernel.Thm])] =
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

    def assert(theory: Theory): Either[LogicError, (Theory, Map[String, Kernel.Thm])] =
      Axioms.foldLeft(Right((theory, Map.empty[String, Kernel.Thm])): Either[LogicError, (Theory, Map[String, Kernel.Thm])]) {
        case (acc, (name, text)) =>
          for {
            current <- acc
            statement <- Parser.proposition(current._1, syntax, text)
            asserted <- LogicError.lift(Kernel.assertAxiom(current._1, statement))
          } yield (asserted._1, current._2.updated(name, asserted._2))
      }

    for {
      declared <- declare(base)
      defined <- define(declared)
      result <- assert(defined._1)
    } yield new RealTheory(logic, result._1, syntax, result._2, defined._2)
  }
}
