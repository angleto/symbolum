package garden.xeno.symbolum.theories

import garden.xeno.symbolum.kernel.*
import garden.xeno.symbolum.logic.*

/**
 * What a term of the embedded theory is worth and whether a formula of it is true, as two
 * recursions on codes, and the first representation built on them.
 *
 * `docs/adr/0040` is the decision this file is the first half of. A representation of one of the
 * constants the Goedel stack uses is a formula of the object language together with a proof that
 * it says what the constant says; this file makes "says" a definition, `NUM_TRUE`, so that the
 * second half is a statement in this logic about a code and not a sentence in a docstring. What
 * turns a true formula into a provable one is completeness for bounded formulas, proved once and
 * above this file; until it is proved, what is here is the semantic half of every representation
 * and nothing about provability, which is said again where it could be misread.
 *
 * == The two recursions ==
 *
 * `NUM_VALUE t e` is the value of the term coded by `t` when variable `j` stands for `e j`, and
 * `NUM_TRUE p e` is whether the formula coded by `p` holds there. Both take the code FIRST and the
 * environment second, and both are recursions whose answer is a **function of the environment**
 * rather than recursions with the environment as a parameter. For the value that is a choice; for
 * the truth it is forced: the quantifier's clause asks for the body at a DIFFERENT environment,
 * `e` with `j` sent to `n`, and a recursion with the environment fixed outside it cannot say that.
 * The value is written the same way so that the two read alike and a clause of one is never
 * applied to its arguments in the other's order.
 *
 * Both are `Language`'s course-of-values recursion, through the same construction the
 * substitutions and the freeness clauses use, and the one thing that construction had to learn
 * for them is a branch that is an abstraction: the admissibility proof now carries its congruence
 * under a binder, which is the only change this development made below itself.
 *
 * **Neither asks whether the code is well formed**, and that is on purpose. A code that is not a
 * term is worth zero and a code that is not a formula is false, as the substitutions leave such a
 * code alone: every statement that matters here is about a code some other fact already says is a
 * formula, and a truth predicate that refused a non-formula would have to carry `NUM_FORM` into
 * every clause for nothing.
 *
 * == The first representation ==
 *
 * `NUM_TRI_GRAPH` is the code of `v0 + v0 = v1 * S v1`, and [[Truth.TriangleGraphTrue]] says it
 * holds at an environment exactly when `e 0 = NUM_TRI (e 1)`. Variable `0` is the value and
 * variable `1` the argument, which is the convention every representation above will follow. It is
 * quantifier-free because `NUM_TRI n` is the unique solution of `2x = n(n+1)`, so the division the
 * closed form wants is never written; that is the reason `Numbering` defined the triangle by
 * recursion rather than as a quotient, spent a second time.
 *
 * What it does NOT say, since this is the sentence a reader would round up: that PA proves
 * `v0 + v0 = v1 * S v1` at the numerals of `NUM_TRI n` and `n`. That is `Deduction`'s kind of
 * statement and it follows from completeness for bounded formulas, which is not here.
 */
final class Truth private (
  val language: Language,
  val theory: Theory,
  val notation: Notation,
  val logic: Logic,
  val definitions: Map[String, Kernel.Thm],
  val facts: Map[String, Kernel.Thm]
) extends Signature {

  def definition(name: String): Either[LogicError, Kernel.Thm] =
    definitions.get(name).toRight(MissingDefinition(name))

  def fact(name: String): Either[LogicError, Kernel.Thm] =
    facts.get(name).toRight(MissingDefinition(name))
}

object Truth {

  /** The value of a term: `NUM_VALUE t e`. */
  val ValueName: String = "NUM_VALUE"

  /** Whether a formula holds: `NUM_TRUE p e`. */
  val TrueName: String = "NUM_TRUE"

  /** The code of `v0 + v0 = v1 * S v1`, whose truth is the graph of `NUM_TRI`. */
  val TriangleGraphName: String = "NUM_TRI_GRAPH"

  val ValueVariable: String = "NUM_VALUE_VAR"
  val ValueZero: String = "NUM_VALUE_ZERO"
  val ValueSuccessor: String = "NUM_VALUE_SUC"
  val ValueSum: String = "NUM_VALUE_ADD"
  val ValueProduct: String = "NUM_VALUE_MUL"

  /**
   * `|- !n e. NUM_VALUE (NUM_NUMERAL n) e = n`
   *
   * The numeral of `n` is worth `n` wherever it is read, which is what makes a numeral a name for
   * its number rather than a code that happens to be built from it. It is the fact every
   * representation spends when it is asked about a concrete argument.
   */
  val ValueNumeral: String = "NUM_VALUE_NUMERAL"

  val TrueEquality: String = "NUM_TRUE_EQ"
  val TrueNegation: String = "NUM_TRUE_NOT"
  val TrueImplication: String = "NUM_TRUE_IMP"

  /**
   * `|- !e j p. NUM_TRUE (NUM_CODE 8 (NUM_PAIR j p)) e =`
   *   `(!n. NUM_TRUE p (\k. COND (k = j) n (e k)))`
   *
   * The quantifier, and the clause that decided the shape of both recursions: the body is read at
   * the environment that agrees with `e` everywhere except at `j`, where it answers `n`.
   */
  val TrueUniversal: String = "NUM_TRUE_ALL"

  /**
   * `|- !n. NUM_TRI n + NUM_TRI n = n * SUC n`
   *
   * The closed form without the division, and the fact the representation stands on.
   */
  val TriangleDoubled: String = "NUM_TRI_DOUBLE"

  /**
   * `|- !e. NUM_TRUE NUM_TRI_GRAPH e = (e 0 = NUM_TRI (e 1))`
   *
   * The graph of the triangle, as the truth of a formula of the object language. Both directions:
   * the left-to-right half is the uniqueness of the solution of `2x = n(n+1)` and is the half a
   * reader should check, since the right-to-left one only evaluates.
   */
  val TriangleGraphTrue: String = "NUM_TRI_GRAPH_TRUE"

  /**
   * The step of the value, as text.
   *
   * Tag `1` has no branch: zero falls through to the last one with every code that is not a term,
   * and both are worth zero.
   */
  val ValueStepText: String =
    "\\f:num -> (num -> num) -> num. \\s:num. " +
      "COND (s = NUM_CODE 0 (NUM_PAYLOAD s)) " +
      "     (\\e:num -> num. e (NUM_PAYLOAD s)) " +
      "     (COND (s = NUM_CODE 2 (NUM_PAYLOAD s)) " +
      "           (\\e:num -> num. SUC (f (NUM_PAYLOAD s) e)) " +
      "           (COND (s = NUM_CODE 3 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                           (NUM_SND (NUM_PAYLOAD s)))) " +
      "                 (\\e:num -> num. NUM_ADD (f (NUM_FST (NUM_PAYLOAD s)) e) " +
      "                                        (f (NUM_SND (NUM_PAYLOAD s)) e)) " +
      "                 (COND (s = NUM_CODE 4 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                                 (NUM_SND (NUM_PAYLOAD s)))) " +
      "                       (\\e:num -> num. NUM_MUL (f (NUM_FST (NUM_PAYLOAD s)) e) " +
      "                                              (f (NUM_SND (NUM_PAYLOAD s)) e)) " +
      "                       (\\e:num -> num. ZERO))))"

  /**
   * The step of the truth, as text.
   *
   * The equality clause calls the value and does not recurse, which is why the value is defined
   * first and costs this recursion's admissibility proof nothing, as `NUM_FORM`'s equality clause
   * costs its own nothing.
   */
  val TrueStepText: String =
    "\\f:num -> (num -> num) -> bool. \\s:num. " +
      "COND (s = NUM_CODE 5 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) (NUM_SND (NUM_PAYLOAD s)))) " +
      "     (\\e:num -> num. NUM_VALUE (NUM_FST (NUM_PAYLOAD s)) e = " +
      "                    NUM_VALUE (NUM_SND (NUM_PAYLOAD s)) e) " +
      "     (COND (s = NUM_CODE 6 (NUM_PAYLOAD s)) " +
      "           (\\e:num -> num. ~(f (NUM_PAYLOAD s) e)) " +
      "           (COND (s = NUM_CODE 7 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                           (NUM_SND (NUM_PAYLOAD s)))) " +
      "                 (\\e:num -> num. f (NUM_FST (NUM_PAYLOAD s)) e ==> " +
      "                                f (NUM_SND (NUM_PAYLOAD s)) e) " +
      "                 (COND (s = NUM_CODE 8 (NUM_PAIR (NUM_FST (NUM_PAYLOAD s)) " +
      "                                                 (NUM_SND (NUM_PAYLOAD s)))) " +
      "                       (\\e:num -> num. !n:num. f (NUM_SND (NUM_PAYLOAD s)) " +
      "                          (\\k:num. COND (k = NUM_FST (NUM_PAYLOAD s)) n (e k))) " +
      "                       (\\e:num -> num. F))))"

  /**
   * `v0 + v0 = v1 * S v1`, coded.
   *
   * Written out rather than built from a tree, because it is one formula and a reader checks it
   * against the sentence above by eye: tag `5` is the equality, `3` the sum, `4` the product, `2`
   * the successor and `0` a variable, as `Language` says.
   */
  val TriangleGraphText: String =
    "NUM_CODE 5 (NUM_PAIR " +
      "(NUM_CODE 3 (NUM_PAIR (NUM_CODE 0 0) (NUM_CODE 0 0))) " +
      "(NUM_CODE 4 (NUM_PAIR (NUM_CODE 0 1) (NUM_CODE 2 (NUM_CODE 0 1)))))"

  /** What every derived fact says, as text, in the order they are derived. */
  val Statements: Vector[(String, String)] = Vector(
    ValueVariable -> "!e:num -> num. !j:num. NUM_VALUE (NUM_CODE 0 j) e = e j",
    ValueZero -> "!e:num -> num. NUM_VALUE (NUM_CODE 1 0) e = ZERO",
    ValueSuccessor ->
      "!e:num -> num. !s:num. NUM_VALUE (NUM_CODE 2 s) e = SUC (NUM_VALUE s e)",
    ValueSum ->
      ("!e:num -> num. !a:num. !b:num. " +
        "NUM_VALUE (NUM_CODE 3 (NUM_PAIR a b)) e = NUM_ADD (NUM_VALUE a e) (NUM_VALUE b e)"),
    ValueProduct ->
      ("!e:num -> num. !a:num. !b:num. " +
        "NUM_VALUE (NUM_CODE 4 (NUM_PAIR a b)) e = NUM_MUL (NUM_VALUE a e) (NUM_VALUE b e)"),
    ValueNumeral -> "!e:num -> num. !n:num. NUM_VALUE (NUM_NUMERAL n) e = n",
    TrueEquality ->
      ("!e:num -> num. !a:num. !b:num. " +
        "NUM_TRUE (NUM_CODE 5 (NUM_PAIR a b)) e = (NUM_VALUE a e = NUM_VALUE b e)"),
    TrueNegation -> "!e:num -> num. !p:num. NUM_TRUE (NUM_CODE 6 p) e = ~(NUM_TRUE p e)",
    TrueImplication ->
      ("!e:num -> num. !p:num. !q:num. " +
        "NUM_TRUE (NUM_CODE 7 (NUM_PAIR p q)) e = (NUM_TRUE p e ==> NUM_TRUE q e)"),
    TrueUniversal ->
      ("!e:num -> num. !j:num. !p:num. " +
        "NUM_TRUE (NUM_CODE 8 (NUM_PAIR j p)) e = " +
        "(!n:num. NUM_TRUE p (\\k:num. COND (k = j) n (e k)))"),
    TriangleDoubled -> "!n:num. NUM_ADD (NUM_TRI n) (NUM_TRI n) = NUM_MUL n (SUC n)",
    TriangleGraphTrue -> "!e:num -> num. NUM_TRUE NUM_TRI_GRAPH e = (e 0 = NUM_TRI (e 1))"
  )

  /** Over the standard chain. */
  lazy val standard: Truth =
    construct(Chain.standard).fold(
      error =>
        throw new IllegalStateException(s"the truth of the object language does not build: $error"),
      identity
    )

  /**
   * Over a chain of one's own, extending what the embedded theory can prove.
   *
   * Beside the chain rather than in it, as `Collatz` is and for a narrower reason: nothing in the
   * chain consumes it yet. It extends `provability.theory` so that completeness, when it lands,
   * can state that a true formula is a provable one in one signature.
   */
  def construct(chain: Chain): Either[LogicError, Truth] = {
    val language = chain.language
    val numbering = chain.numbering
    val provability = chain.provability
    val numbers = TyApp(Natural.TypeName, Nil)
    val environments = Type.fun(numbers, numbers)

    for {
      descent <- Descent.construct(numbering.peano, chain.induct)
      recursion <- descent.theorem
      baseLogic <- numbering.logic.over(provability.theory)

      withValue <- Language.defineShaped(
        numbering, recursion, provability.theory, provability.notation, baseLogic,
        ValueName, ValueStepText, Type.fun(environments, numbers), Nil)
      (valueTheory, valueDefinition, valueNamed) = withValue
      valueLogic <- numbering.logic.over(valueTheory)

      withTruth <- Language.defineShaped(
        numbering, recursion, valueTheory, provability.notation, valueLogic,
        TrueName, TrueStepText, Type.fun(environments, Type.Bool), Nil)
      (truthTheory, truthDefinition, truthNamed) = withTruth
      truthLogic <- numbering.logic.over(truthTheory)

      graphBody <- Parser.term(truthTheory, provability.notation, TriangleGraphText, numbers)
      withGraph <- LogicError.lift(Kernel.defineConstant(truthTheory, TriangleGraphName, graphBody))
      (theory, graphDefinition) = withGraph
      logic <- numbering.logic.over(theory)

      statements = new Statements(theory, provability.notation)
      projections <- Vector(
        Numbering.PayloadOfCode, Numbering.FirstOfPair, Numbering.SecondOfPair
      ).foldLeft[Either[LogicError, Vector[Rewrite.Rule]]](Right(Vector.empty)) { (carried, name) =>
        for {
          found <- carried
          fact <- numbering.fact(name)
          rule <- Rewrite.Rule.of(logic, fact)
        } yield found :+ rule
      }
      clauses = new Clauses(numbering, logic, chain.successor, projections, statements)

      valueVariable <- clauses.at(valueNamed, ValueVariable, Type.fun(environments, numbers))
      valueZero <- clauses.at(valueNamed, ValueZero, Type.fun(environments, numbers))
      valueSuccessor <- clauses.at(valueNamed, ValueSuccessor, Type.fun(environments, numbers))
      valueSum <- clauses.at(valueNamed, ValueSum, Type.fun(environments, numbers))
      valueProduct <- clauses.at(valueNamed, ValueProduct, Type.fun(environments, numbers))
      numeralAtZero <- language.fact(Language.NumeralAtZero)
      numeralAtSuccessor <- language.fact(Language.NumeralAtSuccessor)
      valueNumeral <- numeralValue(
        logic, statements, chain.naturals, numeralAtZero, numeralAtSuccessor, valueZero,
        valueSuccessor)

      trueEquality <- clauses.at(truthNamed, TrueEquality, Type.fun(environments, Type.Bool))
      trueNegation <- clauses.at(truthNamed, TrueNegation, Type.fun(environments, Type.Bool))
      trueImplication <- clauses.at(truthNamed, TrueImplication, Type.fun(environments, Type.Bool))
      trueUniversal <- clauses.at(truthNamed, TrueUniversal, Type.fun(environments, Type.Bool))

      semiring <- Semiring.construct(numbering.peano)
      doubled <- triangleDoubled(logic, statements, chain.naturals, numbering, semiring)
      graph <- triangleGraph(
        logic, statements, numbering, graphDefinition, doubled,
        Vector(valueVariable, valueSuccessor, valueSum, valueProduct, trueEquality))
    } yield new Truth(
      language,
      theory,
      provability.notation,
      logic,
      Map(
        ValueName -> valueDefinition,
        TrueName -> truthDefinition,
        TriangleGraphName -> graphDefinition
      ),
      Map(
        ValueVariable -> valueVariable,
        ValueZero -> valueZero,
        ValueSuccessor -> valueSuccessor,
        ValueSum -> valueSum,
        ValueProduct -> valueProduct,
        ValueNumeral -> valueNumeral,
        TrueEquality -> trueEquality,
        TrueNegation -> trueNegation,
        TrueImplication -> trueImplication,
        TrueUniversal -> trueUniversal,
        TriangleDoubled -> doubled,
        TriangleGraphTrue -> graph
      )
    )
  }

  /** The published statements, parsed against the widest theory of this development. */
  private final class Statements(theory: Theory, notation: Notation) {

    def statement(name: String): Either[LogicError, Term] =
      Statements
        .collectFirst { case (key, text) if key == name => text }
        .toRight(MissingDefinition(name))
        .flatMap(Parser.proposition(theory, notation, _))

    def checked(name: String, theorem: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        expected <- statement(name)
        _ <-
          if (theorem.conclusion == expected) Right(())
          else Left(NotOfForm(s"the statement published for $name", theorem.conclusion))
        _ <-
          if (theorem.hypotheses.isEmpty) Right(())
          else Left(NotOfForm(s"$name with nothing assumed", theorem.conclusion))
      } yield theorem
  }

  /**
   * One clause of either recursion, read off the recursion equation at a code of the right shape.
   *
   * The code is taken from the published statement rather than written a second time here: the
   * statement is `!e x1 .. xk. HEAD code e = answer`, so specialising the recursion at `code`,
   * taking the projections off and settling the shape tests gives `HEAD code = \e. answer'`, and
   * applying both sides to `e` and reducing is the clause. The comparison with the statement at the
   * end is what says `answer'` was the answer intended.
   */
  private final class Clauses(
    numbering: Numbering,
    logic: Logic,
    successor: Successor,
    projections: Vector[Rewrite.Rule],
    statements: Statements
  ) {
    private val rules = logic.rules

    def at(named: Kernel.Thm, name: String, answers: Type): Either[LogicError, Kernel.Thm] =
      for {
        statement <- statements.statement(name)
        stripped <- Logic.stripForall(statement)
        (variables, body) = stripped
        environment <- variables.headOption
          .toRight(NotOfForm("a claim about every environment", statement))
        sides <- Term.destEq(body).toRight(NotOfForm("an equation", body))
        code <- sides._1 match {
          case App(App(_, coded), _) => Right(coded)
          case other => Left(NotOfForm("a code read at an environment", other))
        }
        instance <- rules.spec(code, named)
        cleaned <- Rewrite.inTheorem(projections, instance)
        settled <- Language.settleGuards(numbering, logic, successor, answers, cleaned)
        applied <- Conv.apThm(settled, environment)
        reduced <- Conv
          .betaNormalise(applied.conclusion)
          .flatMap(equation => LogicError.lift(Kernel.eqMp(equation, applied)))
        general <- rules.genAll(reduced, variables.toList)
        result <- statements.checked(name, general)
      } yield result
  }

  /** [[ValueNumeral]], by induction on the number with the two numeral equations. */
  private def numeralValue(
    logic: Logic,
    statements: Statements,
    naturals: Natural,
    atZero: Kernel.Thm,
    atSuccessor: Kernel.Thm,
    valueZero: Kernel.Thm,
    valueSuccessor: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    /** `NUM_VALUE a e = NUM_VALUE b e` from `a = b`. */
    def read(equation: Kernel.Thm, head: Term, environment: Term): Either[LogicError, Kernel.Thm] =
      Conv.apTerm(head, equation).flatMap(Conv.apThm(_, environment))

    for {
      statement <- statements.statement(ValueNumeral)
      induction <- naturals.fact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)
      value <- LogicError.lift(logic.theory.constant(
        ValueName,
        Type.fun(TyApp(Natural.TypeName, Nil),
          Type.fun(Type.fun(TyApp(Natural.TypeName, Nil), TyApp(Natural.TypeName, Nil)),
            TyApp(Natural.TypeName, Nil)))))
      environment <- Logic.stripForall(statement).flatMap(stripped =>
        stripped._1.headOption.toRight(NotOfForm("a claim about every environment", statement)))
      proved <- driver.proveBy(
        statement,
        _ =>
          for {
            moved <- read(atZero, value, environment)
            there <- rules.spec(environment, valueZero)
            result <- Conv.trans(moved, there)
          } yield result,
        step =>
          for {
            recurrence <- rules.spec(step.variable, atSuccessor)
            moved <- read(recurrence, value, environment)
            inner <- recurrence.conclusion match {
              case App(App(_, _), App(App(_, _), numeral)) => Right(numeral)
              case other => Left(NotOfForm("a numeral built by a successor", other))
            }
            there <- rules.specAll(valueSuccessor, List(environment, inner))
            successorHead <- there.conclusion match {
              case App(App(_, _), App(head, _)) => Right(head)
              case other => Left(NotOfForm("a successor", other))
            }
            carried <- Conv.apTerm(successorHead, step.hypothesis)
            result <- Conv.trans(moved, there).flatMap(Conv.trans(_, carried))
          } yield result
      )
      result <- statements.checked(ValueNumeral, proved)
    } yield result
  }

  /**
   * [[TriangleDoubled]], by induction.
   *
   * The step is where the semiring cannot go alone: it reads `SUC k` as an atom, so the successor
   * of the successor is a different atom and nothing relates them. `NUM_MUL_SUC` and `NUM_SUC_MUL`
   * take every product with a successor apart first, and after that both sides are sums of
   * `k * k`, `k` and `SUC k`, which is the semiring's. The hypothesis is about `T + T` with `T`
   * the triangle at `k`, a subterm the unfolded goal does not contain, so the semiring first puts
   * the goal's left side into the form `(T + T) + (SUC k + SUC k)` and the hypothesis is carried
   * into the left summand by congruence.
   */
  private def triangleDoubled(
    logic: Logic,
    statements: Statements,
    naturals: Natural,
    numbering: Numbering,
    semiring: Semiring
  ): Either[LogicError, Kernel.Thm] = {
    val peano = numbering.peano

    def rightOf(theorem: Kernel.Thm): Either[LogicError, Term] =
      Term.destEq(theorem.conclusion).map(_._2)
        .toRight(NotOfForm("an equation", theorem.conclusion))

    def sidesOf(goal: Term): Either[LogicError, (Term, Term)] =
      Term.destEq(goal).toRight(NotOfForm("an equation", goal))

    /** `left = right` through a common normal form reached from each side. */
    def meet(fromLeft: Kernel.Thm, fromRight: Kernel.Thm): Either[LogicError, Kernel.Thm] =
      for {
        leftValue <- rightOf(fromLeft)
        rightValue <- rightOf(fromRight)
        middle <- semiring.prove(leftValue, rightValue)
        back <- Conv.sym(fromRight)
        result <- Conv.trans(fromLeft, middle).flatMap(Conv.trans(_, back))
      } yield result

    for {
      statement <- statements.statement(TriangleDoubled)
      induction <- naturals.fact(Natural.Induction)
      driver = Induct.overNaturals(logic, induction)
      triangle <- Vector(Numbering.TriangleAtZero, Numbering.TriangleAtSuccessor)
        .foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (carried, name) =>
          carried.flatMap(found => numbering.fact(name).map(found :+ _))
        }
        .flatMap(Rewrite.Rule.all(logic, _))
      products <- Vector(Peano.MulAtSuccessor, Peano.SuccessorTimes)
        .foldLeft[Either[LogicError, Vector[Kernel.Thm]]](Right(Vector.empty)) { (carried, name) =>
          carried.flatMap(found => peano.fact(name).map(found :+ _))
        }
        .flatMap(Rewrite.Rule.all(logic, _))

      proved <- driver.proveBy(
        statement,
        goal =>
          for {
            sides <- sidesOf(goal)
            left <- Rewrite.rewrite(triangle, sides._1)
            right <- Rewrite.rewrite(products, sides._2)
            result <- meet(left, right)
          } yield result,
        step =>
          for {
            sides <- sidesOf(step.goal)
            left <- Rewrite.rewrite(triangle, sides._1)
            leftValue <- rightOf(left)
            hypothesis <- sidesOf(step.hypothesis.conclusion)
            (doubled, _) = hypothesis
            grouped <- leftValue match {
              case App(App(plus, App(App(_, _), successorOfK)), _) =>
                for {
                  twice <- LogicError.lift(Term.appAll(plus, List(successorOfK, successorOfK)))
                  target <- LogicError.lift(Term.appAll(plus, List(doubled, twice)))
                  proof <- semiring.prove(leftValue, target)
                  carried <- Conv.apTerm(plus, step.hypothesis).flatMap(Conv.apThm(_, twice))
                } yield (proof, carried)
              case other => Left(NotOfForm("a sum of two sums", other))
            }
            (regrouped, carried) = grouped
            carriedValue <- rightOf(carried)
            unfolded <- Rewrite.rewrite(products, carriedValue)
            fromLeft <- Conv.trans(left, regrouped)
              .flatMap(Conv.trans(_, carried))
              .flatMap(Conv.trans(_, unfolded))
            right <- Rewrite.rewrite(products, sides._2)
            result <- meet(fromLeft, right)
          } yield result
      )
      result <- statements.checked(TriangleDoubled, proved)
    } yield result
  }

  /**
   * [[TriangleGraphTrue]].
   *
   * The graph's truth is first evaluated: unfolding the constant and rewriting with the value and
   * truth clauses gives `NUM_TRUE NUM_TRI_GRAPH e = (e 0 + e 0 = e 1 * SUC (e 1))`. What is left
   * is an equivalence between two propositions about numbers, and its two halves are different
   * kinds of fact. From right to left it is [[TriangleDoubled]] at `e 1` with `e 0` rewritten.
   * From left to right it is the uniqueness of the solution: `x + x = y + y` gives `x = y`, which
   * is doubling cancelled, `NUM_MUL_TWO` turning each side into a product by two and
   * `NUM_MUL_CANCEL_LEFT` taking the two off.
   */
  private def triangleGraph(
    logic: Logic,
    statements: Statements,
    numbering: Numbering,
    graphDefinition: Kernel.Thm,
    doubled: Kernel.Thm,
    evaluation: Vector[Kernel.Thm]
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules

    for {
      statement <- statements.statement(TriangleGraphTrue)
      stripped <- Logic.stripForall(statement)
      environment <- stripped._1.headOption
        .toRight(NotOfForm("a claim about every environment", statement))
      sides <- Term.destEq(stripped._2).toRight(NotOfForm("an equation", stripped._2))
      (truthOfGraph, meaning) = sides

      evaluating <- Rewrite.Rule.all(logic, graphDefinition +: evaluation)
      evaluated <- Rewrite.rewrite(evaluating, truthOfGraph)
      equation <- Term.destEq(evaluated.conclusion).map(_._2)
        .toRight(NotOfForm("an equation", evaluated.conclusion))
      halves <- Term.destEq(equation).toRight(NotOfForm("an equation between numbers", equation))
      (twice, _) = halves
      plus <- twice match {
        case App(App(head, _), _) => Right(head)
        case other => Left(NotOfForm("a sum", other))
      }
      meaningSides <- Term.destEq(meaning).toRight(NotOfForm("an equation", meaning))
      (value, triangleOfArgument) = meaningSides
      argument <- triangleOfArgument match {
        case App(_, inner) => Right(inner)
        case other => Left(NotOfForm("the triangle of an argument", other))
      }
      atArgument <- rules.spec(argument, doubled)

      // From right to left, under `e 0 = NUM_TRI (e 1)`: `e 0 + e 0` is the doubled triangle.
      assumedMeaning <- LogicError.lift(Kernel.assume(meaning))
      firstSummand <- Conv.apTerm(plus, assumedMeaning).flatMap(Conv.apThm(_, value))
      plusTriangle <- LogicError.lift(Term.app(plus, triangleOfArgument))
      secondSummand <- Conv.apTerm(plusTriangle, assumedMeaning)
      forward <- Conv.trans(firstSummand, secondSummand).flatMap(Conv.trans(_, atArgument))

      // From left to right, under the evaluated equation: `x + x = n * SUC n` and
      // `T + T = n * SUC n` give `x + x = T + T`, and doubling cancels.
      assumedEquation <- LogicError.lift(Kernel.assume(equation))
      same <- Conv.sym(atArgument).flatMap(Conv.trans(assumedEquation, _))
      backward <- cancelDoubling(logic, numbering.peano, value, triangleOfArgument, same)

      equivalence = Kernel.deductAntisym(forward, backward)
      atEnvironment <- Conv.trans(evaluated, equivalence)
      general <- rules.gen(environment, atEnvironment)
      result <- statements.checked(TriangleGraphTrue, general)
    } yield result
  }

  /** `x = y` from `x + x = y + y`. */
  private def cancelDoubling(
    logic: Logic,
    peano: Peano,
    x: Term,
    y: Term,
    doubled: Kernel.Thm
  ): Either[LogicError, Kernel.Thm] = {
    val rules = logic.rules
    for {
      two <- peano.fact(Peano.TimesTwo)
      xTwice <- rules.spec(x, two)
      yTwice <- rules.spec(y, two)
      symmetric <- peano.fact(Peano.MulCommutative)
      two0 <- xTwice.conclusion match {
        case App(App(_, App(App(_, _), factor)), _) => Right(factor)
        case other => Left(NotOfForm("a product by two", other))
      }
      xSwap <- rules.specAll(symmetric, List(two0, x))
      ySwap <- rules.specAll(symmetric, List(two0, y))
      // `2 * x = x + x = y + y = 2 * y`
      xProduct <- Conv.trans(xSwap, xTwice)
      yProduct <- Conv.trans(ySwap, yTwice)
      backwards <- Conv.sym(yProduct)
      products <- Conv.trans(xProduct, doubled).flatMap(Conv.trans(_, backwards))
      cancel <- peano.fact(Peano.MulCancelsLeft)
      positive <- positiveTwo(logic, peano, two0)
      result <- rules.specAll(cancel, List(two0, x, y))
        .flatMap(rules.mp(_, positive))
        .flatMap(rules.mp(_, products))
    } yield result
  }

  /** `0 < SUC (SUC 0)`. */
  private def positiveTwo(logic: Logic, peano: Peano, two: Term): Either[LogicError, Kernel.Thm] =
    two match {
      case App(_, inner) =>
        peano.fact(Peano.SuccessorPositive).flatMap(logic.rules.spec(inner, _))
      case other => Left(NotOfForm("a successor", other))
    }
}
